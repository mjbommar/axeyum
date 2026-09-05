import Lean
/-!
# `Axeyum.Protocol` — the wire between Lean and the Axeyum sidecar

This is the *entire* vocabulary the Lean side understands, and it is
deliberately small. The shape follows C3's thin adapter
(`crates/axeyum-lean-import/src/thin_adapter.rs`, ADR-0935): a request naming
an already-elaborated goal plus an **environment identity**, and a response
that is either `accepted` (carrying the sidecar's claimed environment identity
and a proof term) or `declined` (carrying a typed reason). Anything that does
not parse into one of those two shapes is `malformed-response` — never a
crash, and never a silent accept.

What C3 could not do, and this can: the response's payload is a **term**, and
the term is elaborated by Lean and checked by Lean's kernel. So the trust
argument is one sentence — *nothing the sidecar says is believed; the only
thing that closes a goal is a term Lean's own kernel accepted.* The
environment-identity check is not a soundness mechanism (it cannot be: a
sidecar can echo any string back). It is a staleness check, and it is stated
that way in ADR-1666, exactly as ADR-0935 stated it for C3.

## The goal encoding

Lean serializes the **already-elaborated** `Expr`, not surface syntax. There
is no Lean parser on the Rust side (`docs/math-department/14-lean-lang.md`
item 9 is exactly that gap), so shipping source text would need one. An
elaborated `Expr` needs none: it is a tree of `const` / `app` / `fvar` /
`lit`, and the sidecar's translator either recognizes a node or declines
`unsupported`.
-/
open Lean

namespace Axeyum.Protocol

/-- The protocol tag carried by every request and required on every response.
A response that does not carry it is malformed. -/
def protocolId : String := "axeyum-tactic-v1"

/-- The environment identity the tactic sends and requires back.

It binds the response to *this* Lean and *this* protocol version. It is a
plain string comparison and not a cryptographic binding — the same limit
ADR-0935 recorded for C3. It catches a stale or substituted response; it does
not defend against a sidecar that fabricates a matching string, and it does
not need to, because the term still has to pass Lean's kernel. -/
def environmentId : String :=
  s!"lean-{Lean.versionString}:{protocolId}"

/-- Why the tactic did not close the goal. Every constructor is a *typed*
reason, and `by axeyum` fails with it rather than admitting anything. -/
inductive Failure where
  /-- The sidecar could not be run at all (not configured, not executable). -/
  | sidecarUnavailable (detail : String)
  /-- The response bytes are not JSON, are not an object, carry no recognized
  `status`, are missing a field the status requires, or carry a `declined`
  reason outside `knownDeclineReasons`. -/
  | malformedResponse (detail : String)
  /-- The sidecar declined, with one of `knownDeclineReasons`. -/
  | declined (reason : String)
  /-- The response's `environment_id` is not the one the request carried. -/
  | wrongEnvironment (got expected : String)
  /-- The term did not parse as a Lean term. -/
  | termDidNotParse (detail : String)
  /-- Lean refused the term: it did not elaborate, did not have the goal's
  type, left metavariables, or mentioned `sorryAx`. -/
  | termRejectedByLean (detail : String)
  deriving Inhabited

/-- The message `by axeyum` fails with. Every one names which side rejected —
the protocol check or Lean — because that distinction is the whole point of
the mutation battery in `Tests/Mutations.lean`. -/
def Failure.message : Failure → String
  | .sidecarUnavailable d => s!"axeyum: sidecar unavailable: {d}"
  | .malformedResponse d => s!"axeyum: malformed-response: {d}"
  | .declined r => s!"axeyum: declined: {r}"
  | .wrongEnvironment got expected =>
      s!"axeyum: wrong-environment: response claims {got}, request carried {expected}"
  | .termDidNotParse d => s!"axeyum: term-did-not-parse: {d}"
  | .termRejectedByLean d => s!"axeyum: term-rejected-by-lean: {d}"

/-- The only decline reasons treated as genuine. A `declined` response
carrying anything else is `malformed-response`: the tactic must not invent a
category the sidecar did not name. Mirrors
`axeyum_lean_import::thin_adapter::KNOWN_DECLINE_REASONS`. -/
def knownDeclineReasons : List String := ["unknown", "timeout", "unsupported"]

/-- A parsed response. Exactly two shapes; see the module docs. -/
inductive Response where
  | accepted (environmentId : String) (term : String)
  | declined (reason : String)

/-- Parse the response envelope. Returns `Failure.malformedResponse` for
anything outside the two shapes, so an unrecognized response can never read as
a decision. -/
def parseResponse (raw : String) : Except Failure Response :=
  match Json.parse raw with
  | .error e => .error (.malformedResponse s!"not JSON: {e}")
  | .ok json =>
    match json.getObjVal? "protocol" with
    | .error _ => .error (.malformedResponse "no \"protocol\" field")
    | .ok p =>
      match p.getStr? with
      | .error _ => .error (.malformedResponse "\"protocol\" is not a string")
      | .ok ps =>
        if ps != protocolId then
          .error (.malformedResponse s!"protocol is {ps}, expected {protocolId}")
        else
          match json.getObjValAs? String "status" with
          | .error _ => .error (.malformedResponse "no string \"status\" field")
          | .ok "accepted" =>
            match json.getObjValAs? String "environment_id",
                  json.getObjValAs? String "term" with
            | .ok env, .ok term => .ok (.accepted env term)
            | .error _, _ => .error (.malformedResponse "accepted without \"environment_id\"")
            | _, .error _ => .error (.malformedResponse "accepted without \"term\"")
          | .ok "declined" =>
            match json.getObjValAs? String "reason" with
            | .error _ => .error (.malformedResponse "declined without \"reason\"")
            | .ok r =>
              if knownDeclineReasons.contains r then .ok (.declined r)
              else .error (.malformedResponse s!"unrecognized decline reason {r}")
          | .ok other => .error (.malformedResponse s!"unrecognized status {other}")

end Axeyum.Protocol
