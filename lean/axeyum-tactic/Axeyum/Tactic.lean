import Lean
import Axeyum.Protocol
import Axeyum.Shim
/-!
# `by axeyum` — ask Axeyum for a proof term, then let Lean check it

The tactic is four steps and one rule.

1. **Serialize.** The goal and the usable local hypotheses are already
   elaborated `Expr`s; `encodeExpr` writes them as JSON. No Lean source text
   crosses the boundary, so no Lean parser is needed on the Rust side.
2. **Ask.** The sidecar is spawned, handed the request on stdin, and answers
   on stdout. It carries its own hard timeout and always answers.
3. **Check the envelope.** `Axeyum.Protocol.parseResponse` accepts exactly two
   shapes; the environment identity must be the one we sent.
4. **Elaborate the term.** Lean parses it, elaborates it *against the goal's
   own type*, refuses metavariables and `sorryAx`, runs `Meta.check`, and only
   then assigns it.

**The rule: nothing the sidecar says is believed.** Its `status` does not
close a goal, its environment identity is a staleness check and not a
soundness one, and the only thing that ever closes a goal here is a term
Lean's own elaborator and kernel accepted. The tactic has no `sorry` path, no
`admit` path, and adds no axiom; `Tests/NatLinear.lean` asserts that from the
other side with `#print axioms`.

## Where the sidecar comes from

`AXEYUM_SIDECAR` in the environment, or the optional string argument
(`axeyum "path/to/sidecar"`). The argument exists for
`Tests/Mutations.lean`, which points the tactic at deliberately misbehaving
stubs: that is the only way to show the protocol checks and Lean's own
rejection are load-bearing rather than decorative.
-/

open Lean Elab Tactic Meta

namespace Axeyum

open Protocol

/-- Encode an already-elaborated `Expr` for the sidecar.

Only the node kinds the sidecar's translator can act on are encoded; anything
else returns a reason string and the tactic declines locally rather than
sending a request the sidecar would have to reject. `mdata` is stripped
(it carries elaborator bookkeeping, never mathematical content). -/
partial def encodeExpr (e : Expr) : MetaM (Except String Json) := do
  match e with
  | .mdata _ inner => encodeExpr inner
  | .bvar i => return .ok (Json.mkObj [("k", "bvar"), ("idx", Json.num i)])
  | .fvar fvarId =>
    match (← getLCtx).find? fvarId with
    | none => return .error "goal mentions a free variable not in the local context"
    | some decl =>
      if decl.userName.hasMacroScopes then
        return .error s!"goal mentions the inaccessible local `{decl.userName}`"
      else
        return .ok (Json.mkObj [("k", "fvar"), ("name", Json.str decl.userName.toString)])
  | .const name _ => return .ok (Json.mkObj [("k", "const"), ("name", Json.str name.toString)])
  | .app f a => do
    match ← encodeExpr f, ← encodeExpr a with
    | .ok jf, .ok ja => return .ok (Json.mkObj [("k", "app"), ("fn", jf), ("arg", ja)])
    | .error m, _ => return .error m
    | _, .error m => return .error m
  | .lit (.natVal n) => return .ok (Json.mkObj [("k", "nat"), ("value", Json.num n)])
  | .lit (.strVal _) => return .error "goal mentions a string literal"
  | .sort _ => return .error "goal mentions a sort"
  | .mvar _ => return .error "goal still has a metavariable"
  | .lam .. => return .error "goal mentions a lambda"
  | .forallE .. => return .error "goal is a binder (introduce it first)"
  | .letE .. => return .error "goal mentions a let"
  | .proj .. => return .error "goal mentions a structure projection"

/-- The local hypotheses worth sending: every non-inaccessible local whose
**type is a Prop** and whose type encodes. A local that does not encode is
skipped, not an error — a hypothesis the sidecar cannot read is simply a
hypothesis it will not use. -/
def encodeHypotheses : MetaM (Array Json) := do
  let mut out := #[]
  for decl in ← getLCtx do
    if decl.isImplementationDetail || decl.userName.hasMacroScopes then
      continue
    unless ← isProp decl.type do
      continue
    match ← encodeExpr decl.type with
    | .error _ => continue
    | .ok jty =>
      out := out.push (Json.mkObj [("name", Json.str decl.userName.toString), ("type", jty)])
  return out

/-- Run the sidecar on one request. Returns the raw response bytes.

`stderr` is captured and folded into the failure detail: a sidecar that dies
should say why in the tactic's error, not on a terminal nobody is reading. -/
def callSidecar (sidecar : String) (request : String) : IO (Except Failure String) := do
  let child ←
    try
      IO.Process.spawn {
        cmd := sidecar
        args := #[]
        stdin := .piped
        stdout := .piped
        stderr := .piped
      }
    catch ex =>
      return .error (.sidecarUnavailable s!"cannot spawn {sidecar}: {ex}")
  let (stdin, child) ← child.takeStdin
  stdin.putStr request
  stdin.flush
  -- Dropping the handle closes the sidecar's stdin, which is its signal that
  -- the request is complete. Without this it blocks reading forever and the
  -- tactic hangs instead of failing.
  let _ := stdin
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  if code != 0 && out.trimAscii.isEmpty then
    return .error (.sidecarUnavailable s!"{sidecar} exited {code}: {err.trimAscii}")
  return .ok out

/-- Parse, elaborate, check and assign the sidecar's term.

Every guard here is a rejection Lean performs, not one the protocol performs:
the term must parse, must elaborate at the goal's own type, must leave no
metavariable, must not mention `sorryAx`, and must survive `Meta.check`. -/
def assignTerm (goal : MVarId) (termStr : String) : TacticM (Except Failure Unit) :=
  goal.withContext do
    let env ← getEnv
    match Parser.runParserCategory env `term termStr "<axeyum-sidecar-response>" with
    | .error e => return .error (.termDidNotParse e)
    | .ok stx =>
      let ty ← goal.getType
      try
        -- `withoutErrToSorry` matters here, and not only for tidiness. By
        -- default a failed elaboration LOGS the error and returns a `sorryAx`
        -- placeholder, so a wrong term surfaced as two messages -- Lean's real
        -- diagnosis, plus this tactic reporting "the term mentions sorryAx",
        -- which reads as if the SIDECAR had sent a `sorry`. It had not. With
        -- this, a wrong term throws and is reported once, with Lean's own
        -- reason, and the `hasSorry` guard below is left to catch the case it
        -- is actually for: a sidecar that really did send `sorry`.
        let e ← Term.withoutErrToSorry <| Term.elabTermEnsuringType stx ty
        Term.synthesizeSyntheticMVarsNoPostponing
        let e ← instantiateMVars e
        if e.hasSorry then
          return .error (.termRejectedByLean "the term mentions sorryAx")
        if e.hasExprMVar then
          return .error (.termRejectedByLean "the term still has metavariables")
        check e
        let inferred ← inferType e
        unless ← isDefEq inferred ty do
          return .error (.termRejectedByLean
            s!"the term has type {← ppExpr inferred}, not the goal {← ppExpr ty}")
        goal.assign e
        return .ok ()
      catch ex =>
        return .error (.termRejectedByLean (← ex.toMessageData.toString))

/-- The whole tactic, as an `Except` so the caller decides how to report. -/
def run (sidecarOverride : Option String) : TacticM (Except Failure Unit) := do
  let sidecar ←
    match sidecarOverride with
    | some s => pure s
    | none =>
      match ← IO.getEnv "AXEYUM_SIDECAR" with
      | some s => pure s
      | none =>
        return .error (.sidecarUnavailable
          "AXEYUM_SIDECAR is not set and no path was given to `axeyum`")
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    match ← encodeExpr ty with
    | .error why => do
      logInfo s!"axeyum: the goal is outside the fragment the sidecar is asked about: {why}"
      return .error (.declined "unsupported")
    | .ok jgoal =>
      let hyps ← encodeHypotheses
      let request := Json.mkObj [
        ("protocol", Json.str protocolId),
        ("environment_id", Json.str environmentId),
        ("hypotheses", Json.arr hyps),
        ("goal", jgoal)
      ]
      match ← callSidecar sidecar request.compress with
      | .error f => return .error f
      | .ok raw =>
        match parseResponse raw with
        | .error f => return .error f
        | .ok (.declined reason) => return .error (.declined reason)
        | .ok (.accepted claimed term) =>
          if claimed != environmentId then
            return .error (.wrongEnvironment claimed environmentId)
          assignTerm goal term

/-- `by axeyum` — close the goal with a term Axeyum produced and Lean checked.

`axeyum "path"` overrides the sidecar for that one invocation; see the module
docs for why that exists. -/
syntax (name := axeyumTactic) "axeyum" (ppSpace str)? : tactic

@[tactic axeyumTactic]
def evalAxeyum : Tactic := fun stx => do
  -- `stx[1]` is the OPTIONAL node, not the string literal inside it. Reading
  -- `stx[1].isStrLit?` returns `none` for `axeyum "path"` as well as for bare
  -- `axeyum`, so every override silently fell back to `AXEYUM_SIDECAR` -- which
  -- made the whole mutation battery run against the REAL sidecar and pass by
  -- closing the goals it was supposed to fail on. Found by `#guard_msgs`
  -- reporting an empty message where an error was expected (2026-09-05).
  let override : Option String := stx[1][0].isStrLit?
  match ← run override with
  | .ok () => pure ()
  | .error f => throwError f.message

end Axeyum
