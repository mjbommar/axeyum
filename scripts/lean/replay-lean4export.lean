/-
Replay an official `lean4export` NDJSON 3.1.0 stream into the **real Lean
kernel**.

Usage (needs only the pinned toolchain; no lake project, no network):

    lean --run scripts/lean/replay-lean4export.lean <stream.ndjson>

Why this exists: `lean file.lean` on a rendered module runs the *elaborator* —
implicit-argument inference, universe unification, coercion insertion, code
generation — none of which bear on whether a proof term is well typed. This
script bypasses all of it. It parses the export format, rebuilds each
declaration, and hands it to `Lean.Environment.addDeclCore`, which is Lean's own
kernel type checker. Nothing is elaborated and nothing is compiled.

It starts from `mkEmptyEnvironment`, so the stream must be self-contained and
nothing can be silently satisfied by Lean's own `Init` (in particular the
quotient package is added from the stream, never inherited — adding it twice is
a kernel error).

Recursors and constructors carried by an `inductive` record are not handed to
`addDeclCore` — Lean generates them itself from the family declaration. Until
2026-08-18 that meant they were not checked at all: measured on the logic
prelude, 225 of 603 expression records (37% of the stream) were reachable ONLY
from a recursor type or an ι-reduction rule, so damaging any of them was
invisible to this script and Lean "accepted" bytes it never read. The old claim
that a later declaration mentioning the recursor would catch it is only true
when such a declaration exists, and in a small development it does not.

So every `inductive` record is now checked a second way: after `addDeclCore`
succeeds, each family, constructor and recursor the record carries is looked up
in the environment Lean just built and compared field by field against what
Lean's own kernel generated — arities, `cidx`, `k`, the ι-rules, and the types
themselves up to universe-parameter position and binder names. A disagreement
prints `LEAN KERNEL REGENERATION MISMATCH` and exits nonzero. This makes the
recursor half of the stream a real verdict rather than an unread field.

That comparison looks constants up in `env.toKernelEnv`, Lean's kernel
environment, and not in `Environment.find?`, the elaborator's view — which is
what makes a NESTED group's auxiliary recursor (`Rose.rec_1`) checkable at all.
See `inductiveAgreesWithLean` for the measurement; the short version is that
Lean's kernel does build it, `addDeclCore` just never announces it.
-/
import Lean
open Lean

private def jField (value : Json) (field : String) : IO Json :=
  IO.ofExcept (value.getObjVal? field)

private def jNat (value : Json) : IO Nat := IO.ofExcept value.getNat?
private def jStr (value : Json) : IO String := IO.ofExcept value.getStr?
private def jBool (value : Json) : IO Bool := IO.ofExcept value.getBool?
private def jArr (value : Json) : IO (Array Json) := IO.ofExcept value.getArr?

private def jFieldNat (value : Json) (field : String) : IO Nat := do
  jNat (← jField value field)

private def binderInfo : String → IO BinderInfo
  | "default" => pure .default
  | "implicit" => pure .implicit
  | "strictImplicit" => pure .strictImplicit
  | "instImplicit" => pure .instImplicit
  | other => throw (IO.userError s!"unknown binderInfo {other}")

private structure Tables where
  names : Array Name := #[Name.anonymous]
  levels : Array Level := #[Level.zero]
  exprs : Array Expr := #[]

/-- Read a JSON array of name-table indices. -/
private def nameList (tables : Tables) (value : Json) : IO (List Name) := do
  let entries ← jArr value
  let mut out := #[]
  for entry in entries do
    out := out.push tables.names[(← jNat entry)]!
  return out.toList

/-- A declaration's universe parameters are a name list; the spelling reads better. -/
private abbrev levelParams := nameList

private def levelArgs (tables : Tables) (value : Json) : IO (List Level) := do
  let entries ← jArr value
  let mut out := #[]
  for entry in entries do
    out := out.push tables.levels[(← jNat entry)]!
  return out.toList

private def hints (value : Json) : IO ReducibilityHints := do
  match value with
  | .str "opaque" => pure .opaque
  | .str "abbrev" => pure .abbrev
  | _ => pure (.regular (UInt32.ofNat (← jFieldNat value "regular")))

/-
`Environment.addDeclCore` — Lean's own kernel entry point — CHANGED ARITY
between the toolchain `lean-toolchain` pins (v4.30.0) and v4.34.0-rc1: a
`maxRecDepth : USize` was inserted after `maxHeartbeats`. A single spelling
therefore fails to *elaborate* on one of the two, which is what happened on the
development host on 2026-08-17: under 4.34 this script died with

    Application type mismatch: the argument `declaration` ... expected USize

before reading a byte of the stream, so `real_lean_kernel_replay` failed for a
reason unrelated to what it checks.

`first | exact … | exact …` resolves the arity AT ELABORATION TIME against
whichever Lean is running, and — this is the point — it fails loudly if neither
spelling type-checks, rather than silently degrading. Both zeros mean "no
limit"; Lean's own `Lean/Replay.lean` calls `addDeclCore 0 0 d none`.

This shim is deliberately the ONLY version-conditional construct in the file. If
a future toolchain changes anything else here, it must break visibly.
-/
private def addDeclKernelChecked (env : Environment) (declaration : Declaration) :
    Except Kernel.Exception Environment := by
  first
    | exact env.addDeclCore 0 0 declaration none true  -- Lean >= 4.34
    | exact env.addDeclCore 0 declaration none true    -- Lean 4.30 (pinned)

/-
Comparing an exported declaration against the one Lean's kernel generated needs
a normal form, because the two disagree on things a kernel does not care about:
universe parameters are chosen names, binder names are hints, and `BinderInfo`
is elaborator metadata that `addDeclCore` ignores. Universe parameters are
mapped to their POSITION in the declaration's own `levelParams`, so the
comparison is sensitive to their order (which is type-relevant — the motive
universe leads a recursor) but not to their spelling.
-/
private def positionOf (names : List Name) (needle : Name) : Option Nat :=
  let rec go : List Name → Nat → Option Nat
    | [], _ => none
    | head :: rest, i => if head == needle then some i else go rest (i + 1)
  go names 0

private def normLevel (params : List Name) : Level → Level
  | .zero => .zero
  | .succ l => .succ (normLevel params l)
  | .max a b => .max (normLevel params a) (normLevel params b)
  | .imax a b => .imax (normLevel params a) (normLevel params b)
  | .param n => match positionOf params n with
    | some i => .param (Name.mkNum `uparam i)
    | none => .param n
  | .mvar m => .mvar m

private partial def normExpr (params : List Name) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar f => .fvar f
  | .mvar m => .mvar m
  | .sort l => .sort (normLevel params l)
  | .const n us => .const n (us.map (normLevel params))
  | .app f a => .app (normExpr params f) (normExpr params a)
  | .lam _ t b _ => .lam .anonymous (normExpr params t) (normExpr params b) .default
  | .forallE _ t b _ => .forallE .anonymous (normExpr params t) (normExpr params b) .default
  | .letE _ t v b _ =>
      .letE .anonymous (normExpr params t) (normExpr params v) (normExpr params b) false
  | .lit l => .lit l
  | .mdata _ e => normExpr params e
  | .proj n i s => .proj n i (normExpr params s)

private structure Disagreement where
  what : String
  ours : String
  theirs : String

private def missing (what kind : String) : List Disagreement :=
  [{ what, ours := kind, theirs := "no such constant in the environment Lean built" }]

private def natAgrees (what : String) (ours theirs : Nat) : List Disagreement :=
  if ours == theirs then [] else [{ what, ours := toString ours, theirs := toString theirs }]

private def boolAgrees (what : String) (ours theirs : Bool) : List Disagreement :=
  if ours == theirs then [] else [{ what, ours := toString ours, theirs := toString theirs }]

private def nameAgrees (what : String) (ours theirs : Name) : List Disagreement :=
  if ours == theirs then [] else [{ what, ours := toString ours, theirs := toString theirs }]

private def namesAgree (what : String) (ours theirs : List Name) : List Disagreement :=
  if ours == theirs then []
  else [{ what, ours := toString ours, theirs := toString theirs }]

/-
Structural equality after normalization, falling back to Lean's own kernel
definitional equality.

The fallback is not a convenience: our importer's mirror of this check
(`validate_generated_recursor`) compares the exported and generated recursor
types with `def_eq`, so a mutant that produced a DEFEQ-but-not-syntactic variant
would be admitted by us and "refused" here on a difference no kernel cares
about — a fabricated violation in the one place that must not fabricate. Asking
`Kernel.isDefEqGuarded` puts both sides on the same criterion.
-/
private def typeAgrees (env : Environment) (what : String) (ourParams : List Name) (ourType : Expr)
    (theirParams : List Name) (theirType : Expr) : List Disagreement :=
  let a := normExpr ourParams ourType
  let b := normExpr theirParams theirType
  if a == b then []
  else if Lean.Kernel.isDefEqGuarded env {} a b then []
  else [{ what, ours := toString a, theirs := toString b }]

/--
Check every family, constructor and recursor an `inductive` record carries
against the constant Lean's kernel generated for it.

Returns the disagreements and how many constants were actually compared; an
empty disagreement list means the exported record and Lean's own regeneration
describe the same declarations.

**The lookup goes to `toKernelEnv`, not to `Environment.find?`, and that is the
whole reason a NESTED group can be checked here at all.** `Environment.find?`
is the *elaborator's* view: `addDeclCore` republishes only
`Declaration.getNames` into the async constant map, and that function's own
docstring says it "does not include ... auxiliary recursors computed by the
kernel for nested inductive types" — for `.inductDecl` it is
`t.name :: t.name ++ `rec :: ctors`. So `env.find? `Rose.rec_1` is `none` while
`env.constants.find? `Rose.rec_1` is the recursor Lean's kernel built, with its
two motives, three minors and both ι-rules. Measured 2026-08-18 on Lean 4.30.0:
under `Environment.find?` the three official nested fixtures each failed with
exactly one disagreement, "`Rose.rec_1`: no such constant"; under
`toKernelEnv.find?` all seventeen official fixtures replay clean and every
field of the auxiliary recursor is compared.

This matters because the earlier reading — "Lean does not regenerate the
auxiliary recursor, so those bytes cannot be checked" — would have justified an
exemption, and an exemption is how the 37% blind spot above was created in the
first place. The auxiliary recursor was never unread by Lean's kernel; it was
unread by this script.
-/
private def inductiveAgreesWithLean (env : Environment) (tables : Tables) (entry : Json) :
    IO (List Disagreement × Nat) := do
  let mut found : List Disagreement := []
  let mut compared := 0
  let types ← jArr (← jField entry "types")
  let ctors ← jArr (← jField entry "ctors")
  let recs ← jArr (← jField entry "recs")
  let kernelEnv := env.toKernelEnv
  let lookup (name : Name) : IO (Option ConstantInfo) := pure (kernelEnv.find? name)
  for family in types do
    let name := tables.names[(← jFieldNat family "name")]!
    let ourParams ← levelParams tables (← jField family "levelParams")
    match ← lookup name with
    | some (.inductInfo value) =>
      compared := compared + 1
      found := found
        ++ natAgrees s!"{name}.numParams" (← jFieldNat family "numParams") value.numParams
        ++ natAgrees s!"{name}.numIndices" (← jFieldNat family "numIndices") value.numIndices
        ++ natAgrees s!"{name}.numNested" (← jFieldNat family "numNested") value.numNested
        ++ boolAgrees s!"{name}.isRec" (← jBool (← jField family "isRec")) value.isRec
        -- `isReflexive` is deliberately NOT compared: our importer reads it and
        -- discards it as descriptive frontend metadata, and Lean's kernel
        -- derives its own. A difference there is something neither kernel would
        -- act on, so reporting it would manufacture a violation.
        ++ namesAgree s!"{name}.ctors" (← nameList tables (← jField family "ctors"))
             value.ctors
        ++ namesAgree s!"{name}.all" (← nameList tables (← jField family "all")) value.all
        ++ natAgrees s!"{name}.levelParams.length" ourParams.length value.levelParams.length
        ++ typeAgrees env s!"{name}.type" ourParams tables.exprs[(← jFieldNat family "type")]!
             value.levelParams value.type
    | _ => found := found ++ missing (toString name) "an inductive family"
  for ctor in ctors do
    let name := tables.names[(← jFieldNat ctor "name")]!
    let ourParams ← levelParams tables (← jField ctor "levelParams")
    match ← lookup name with
    | some (.ctorInfo value) =>
      compared := compared + 1
      found := found
        ++ nameAgrees s!"{name}.induct" tables.names[(← jFieldNat ctor "induct")]! value.induct
        ++ natAgrees s!"{name}.cidx" (← jFieldNat ctor "cidx") value.cidx
        ++ natAgrees s!"{name}.numParams" (← jFieldNat ctor "numParams") value.numParams
        ++ natAgrees s!"{name}.numFields" (← jFieldNat ctor "numFields") value.numFields
        ++ natAgrees s!"{name}.levelParams.length" ourParams.length value.levelParams.length
        ++ typeAgrees env s!"{name}.type" ourParams tables.exprs[(← jFieldNat ctor "type")]!
             value.levelParams value.type
    | _ => found := found ++ missing (toString name) "a constructor"
  for recursor in recs do
    let name := tables.names[(← jFieldNat recursor "name")]!
    let ourParams ← levelParams tables (← jField recursor "levelParams")
    match ← lookup name with
    | some (.recInfo value) =>
      compared := compared + 1
      found := found
        ++ natAgrees s!"{name}.numParams" (← jFieldNat recursor "numParams") value.numParams
        ++ natAgrees s!"{name}.numIndices" (← jFieldNat recursor "numIndices") value.numIndices
        ++ natAgrees s!"{name}.numMotives" (← jFieldNat recursor "numMotives") value.numMotives
        ++ natAgrees s!"{name}.numMinors" (← jFieldNat recursor "numMinors") value.numMinors
        ++ boolAgrees s!"{name}.k" (← jBool (← jField recursor "k")) value.k
        ++ namesAgree s!"{name}.all" (← nameList tables (← jField recursor "all")) value.all
        ++ natAgrees s!"{name}.levelParams.length" ourParams.length value.levelParams.length
        ++ typeAgrees env s!"{name}.type" ourParams tables.exprs[(← jFieldNat recursor "type")]!
             value.levelParams value.type
      let rules ← jArr (← jField recursor "rules")
      found := found ++ natAgrees s!"{name}.rules.length" rules.size value.rules.length
      for (rule, theirs) in rules.toList.zip value.rules do
        let ctor := tables.names[(← jFieldNat rule "ctor")]!
        found := found
          ++ nameAgrees s!"{name}.rule.{ctor}.ctor" ctor theirs.ctor
          ++ natAgrees s!"{name}.rule.{ctor}.nfields" (← jFieldNat rule "nfields") theirs.nfields
          ++ typeAgrees env s!"{name}.rule.{ctor}.rhs" ourParams
               tables.exprs[(← jFieldNat rule "rhs")]! value.levelParams theirs.rhs
    | _ => found := found ++ missing (toString name) "a recursor"
  return (found, compared)

def main (args : List String) : IO UInt32 := do
  -- A result that does not name its checker is not evidence: every run says
  -- which Lean kernel produced the verdict below, on stdout, unconditionally.
  IO.println s!"lean4export replay: checker Lean {Lean.versionString} (githash {Lean.githash})"
  -- `--emit-names <out>` writes the sorted names of every constant Lean's own
  -- kernel ended up holding. It exists so a caller can grade ONE declaration
  -- rather than inherit a grade from a count: `environment now holds N
  -- constants` is consistent with a stream in which the declaration a caller
  -- cares about was renamed, substituted, or absent while some other
  -- declaration made up the total. The list below comes out of
  -- `env.constants`, which is Lean's environment and not our stream, so a
  -- name in it was admitted by Lean's kernel and not merely transmitted.
  let some (path, namesOut) := (match args with
      | [p] => some (p, (none : Option String))
      | [p, "--emit-names", o] => some (p, some o)
      | _ => none)
    | IO.eprintln "usage: lean --run replay-lean4export.lean <stream.ndjson> \
[--emit-names <out>]"
      return 2
  let content ← IO.FS.readFile path
  let mut tables : Tables := {}
  let mut env ← mkEmptyEnvironment
  let mut pendingQuot := 0
  let mut declarations := 0
  let mut inductives := 0
  let mut regenerationCheck : Option Json := none
  let mut regenerationsChecked := 0
  -- Constants actually compared against Lean's regeneration. `regenerationsChecked`
  -- counts RECORDS, so it stays at 1 whether a group's whole surface was compared
  -- or a lookup silently found nothing; this counts what was really looked at.
  let mut constantsCompared := 0
  let mut lineNumber := 0
  for rawLine in content.splitOn "\n" do
    let line := rawLine.trimAscii.toString
    lineNumber := lineNumber + 1
    if line.isEmpty then continue
    let record ← IO.ofExcept (Json.parse line)
    if lineNumber == 1 then
      let header ← jField record "meta"
      let format ← jField header "format"
      let version ← jStr (← jField format "version")
      unless version == "3.1.0" do
        IO.eprintln s!"unsupported export format {version}"
        return 1
      continue
    -- Name, level, and expression records.
    if let .ok _ := record.getObjVal? "in" then
      let name ←
        if let .ok entry := record.getObjVal? "str" then
          pure (Name.mkStr tables.names[(← jFieldNat entry "pre")]! (← jStr (← jField entry "str")))
        else
          let entry ← jField record "num"
          pure (Name.mkNum tables.names[(← jFieldNat entry "pre")]! (← jFieldNat entry "i"))
      tables := { tables with names := tables.names.push name }
      continue
    if let .ok _ := record.getObjVal? "il" then
      let level ←
        if let .ok entry := record.getObjVal? "succ" then
          pure (Level.succ tables.levels[(← jNat entry)]!)
        else if let .ok entry := record.getObjVal? "max" then
          let pair ← jArr entry
          pure (Level.max tables.levels[(← jNat pair[0]!)]! tables.levels[(← jNat pair[1]!)]!)
        else if let .ok entry := record.getObjVal? "imax" then
          let pair ← jArr entry
          pure (Level.imax tables.levels[(← jNat pair[0]!)]! tables.levels[(← jNat pair[1]!)]!)
        else
          pure (Level.param tables.names[(← jFieldNat record "param")]!)
      tables := { tables with levels := tables.levels.push level }
      continue
    if let .ok _ := record.getObjVal? "ie" then
      let expr ←
        if let .ok entry := record.getObjVal? "bvar" then
          pure (Expr.bvar (← jNat entry))
        else if let .ok entry := record.getObjVal? "sort" then
          pure (Expr.sort tables.levels[(← jNat entry)]!)
        else if let .ok entry := record.getObjVal? "const" then
          pure (Expr.const tables.names[(← jFieldNat entry "name")]!
            (← levelArgs tables (← jField entry "us")))
        else if let .ok entry := record.getObjVal? "app" then
          pure (Expr.app tables.exprs[(← jFieldNat entry "fn")]!
            tables.exprs[(← jFieldNat entry "arg")]!)
        else if let .ok entry := record.getObjVal? "lam" then
          pure (Expr.lam tables.names[(← jFieldNat entry "name")]!
            tables.exprs[(← jFieldNat entry "type")]!
            tables.exprs[(← jFieldNat entry "body")]!
            (← binderInfo (← jStr (← jField entry "binderInfo"))))
        else if let .ok entry := record.getObjVal? "forallE" then
          pure (Expr.forallE tables.names[(← jFieldNat entry "name")]!
            tables.exprs[(← jFieldNat entry "type")]!
            tables.exprs[(← jFieldNat entry "body")]!
            (← binderInfo (← jStr (← jField entry "binderInfo"))))
        else if let .ok entry := record.getObjVal? "letE" then
          pure (Expr.letE tables.names[(← jFieldNat entry "name")]!
            tables.exprs[(← jFieldNat entry "type")]!
            tables.exprs[(← jFieldNat entry "value")]!
            tables.exprs[(← jFieldNat entry "body")]!
            (← jBool (← jField entry "nondep")))
        else if let .ok entry := record.getObjVal? "proj" then
          pure (Expr.proj tables.names[(← jFieldNat entry "typeName")]!
            (← jFieldNat entry "idx") tables.exprs[(← jFieldNat entry "struct")]!)
        else if let .ok entry := record.getObjVal? "natVal" then
          pure (Expr.lit (.natVal (← jStr entry).toNat!))
        else
          throw (IO.userError s!"line {lineNumber}: unsupported expression record")
      tables := { tables with exprs := tables.exprs.push expr }
      continue
    -- Declaration records.
    let declaration : Option Declaration ←
      if let .ok entry := record.getObjVal? "axiom" then
        pure (some (.axiomDecl {
          name := tables.names[(← jFieldNat entry "name")]!
          levelParams := (← levelParams tables (← jField entry "levelParams"))
          type := tables.exprs[(← jFieldNat entry "type")]!
          isUnsafe := false }))
      else if let .ok entry := record.getObjVal? "def" then
        let name := tables.names[(← jFieldNat entry "name")]!
        pure (some (.defnDecl {
          name := name
          levelParams := (← levelParams tables (← jField entry "levelParams"))
          type := tables.exprs[(← jFieldNat entry "type")]!
          value := tables.exprs[(← jFieldNat entry "value")]!
          hints := (← hints (← jField entry "hints"))
          safety := .safe
          all := [name] }))
      else if let .ok entry := record.getObjVal? "thm" then
        let name := tables.names[(← jFieldNat entry "name")]!
        pure (some (.thmDecl {
          name := name
          levelParams := (← levelParams tables (← jField entry "levelParams"))
          type := tables.exprs[(← jFieldNat entry "type")]!
          value := tables.exprs[(← jFieldNat entry "value")]!
          all := [name] }))
      else if let .ok entry := record.getObjVal? "opaque" then
        let name := tables.names[(← jFieldNat entry "name")]!
        pure (some (.opaqueDecl {
          name := name
          levelParams := (← levelParams tables (← jField entry "levelParams"))
          type := tables.exprs[(← jFieldNat entry "type")]!
          value := tables.exprs[(← jFieldNat entry "value")]!
          isUnsafe := false
          all := [name] }))
      else if let .ok _ := record.getObjVal? "quot" then
        pendingQuot := pendingQuot + 1
        if pendingQuot == 4 then pure (some .quotDecl) else pure none
      else if let .ok entry := record.getObjVal? "inductive" then
        let types ← jArr (← jField entry "types")
        let ctors ← jArr (← jField entry "ctors")
        let numParams ← jFieldNat types[0]! "numParams"
        let uparams ← levelParams tables (← jField types[0]! "levelParams")
        let mut families := #[]
        for family in types do
          let familyName := tables.names[(← jFieldNat family "name")]!
          let mut constructors := #[]
          for ctor in ctors do
            if tables.names[(← jFieldNat ctor "induct")]! == familyName then
              constructors := constructors.push {
                name := tables.names[(← jFieldNat ctor "name")]!
                type := tables.exprs[(← jFieldNat ctor "type")]! : Constructor }
          families := families.push {
            name := familyName
            type := tables.exprs[(← jFieldNat family "type")]!
            ctors := constructors.toList : InductiveType }
        inductives := inductives + 1
        regenerationCheck := some entry
        pure (some (.inductDecl uparams numParams families.toList false))
      else
        throw (IO.userError s!"line {lineNumber}: unknown declaration record")
    if let some declaration := declaration then
      match addDeclKernelChecked env declaration with
      | .ok next =>
        env := next
        declarations := declarations + 1
        -- `addDeclCore` accepting an `inductDecl` says nothing about the
        -- constructors and recursors the record CARRIES: Lean derived its own
        -- and never looked at ours. Compare them, or those bytes are unread.
        if let some entry := regenerationCheck then
          regenerationCheck := none
          let (found, compared) ← inductiveAgreesWithLean env tables entry
          constantsCompared := constantsCompared + compared
          unless found.isEmpty do
            IO.eprintln s!"line {lineNumber}: LEAN KERNEL REGENERATION MISMATCH: the \
exported inductive record disagrees with the {found.length} field(s) Lean's own kernel \
generated for it:"
            for disagreement in found do
              IO.eprintln s!"  {disagreement.what}: exported {disagreement.ours} \
but Lean's kernel generated {disagreement.theirs}"
            return 1
          regenerationsChecked := regenerationsChecked + 1
      | .error exception =>
        let message ← (exception.toMessageData {}).toString
        IO.eprintln s!"line {lineNumber}: REAL LEAN KERNEL REJECTED the declaration: {message}"
        return 1
  if let some out := namesOut then
    let names := (env.constants.toList.map (fun entry => toString entry.fst)).toArray
    let sorted := names.qsort (fun a b => decide (a < b))
    IO.FS.writeFile out (String.intercalate "\n" sorted.toList ++ "\n")
    IO.println s!"lean4export replay: wrote {sorted.size} kernel constant names to {out}"
  IO.println s!"lean4export replay: the real Lean kernel accepted {declarations} declaration records \
({inductives} inductive groups, {regenerationsChecked} of them also compared field-by-field \
against Lean's own regeneration over {constantsCompared} constants), environment now holds \
{env.constants.toList.length} constants"
  return 0
