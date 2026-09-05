# ADR-0935: The thin Lean adapter composes C2's two already-checked paths and adds nothing else

Status: accepted
Date: 2026-08-30
Index-summary: L4 phase C3 builds the thin Lean adapter as a small grading
module (`axeyum_lean_import::thin_adapter`, ~150 lines of logic) that decides
a sidecar response's fate using only two facts ADR-0915 already established
-- pinned Lean's own by-name admission and an independently-reimported
byte-identical type -- plus two facts C2 never needed (a typed decline
protocol and an environment-identity check), against a preregistered
eight-category goal pack run live against real pinned Lean.

## Context

`docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md` section C3
asks for "a small Lean command/tactic adapter that receives an already
elaborated goal plus environment identity, calls Axeyum as a
sidecar/library, and returns a proof/certificate that Lean itself checks. It
must not trust Axeyum's verdict or add an axiom." Its exit criterion: a
preregistered representative goal pack covers success, unknown, timeout,
unsupported, malformed response, wrong goal, wrong environment, and mutated
proof; all successes are accepted by Lean and every mutation rejects.

ADR-0800 (C0) froze the library-artifact record and its type/proof
separation. ADR-0915 (C2) built the universal checked-interchange pipeline
over 9 credited roots (declarations with an exact-title Mathlib mirror fact,
a resolved kernel theorem, and an empty axiom footprint), establishing that
credit for a name requires BOTH pinned Lean's own `env.constants` membership
by name AND an independently-reimported byte-identical rendered type --
never either alone. The roadmap's ordering constraint for L4 is explicit:
artifact replay comes first (C2), then an elaborated-goal adapter whose
result Lean checks (C3); C4's source/elaboration features stay blocked until
demand is measured.

C3's own phrasing -- "thin" -- is a constraint, not a hedge: every line of
new translation logic is a line that could silently change a goal without
Lean or this kernel ever disagreeing about it. The lane brief for this work
put it plainly: "If you find yourself building a translator, stop and ask
whether the artifact contract can carry the thing instead."

## Decision

1. **The adapter reuses C2's two independent paths verbatim; it does not
   reimplement export, reimport, or replay.** `axeyum_lean_import::
   thin_adapter` calls `Kernel::render_lean4export_ndjson_roots` for export
   (unchanged), `axeyum_lean_import::import_ndjson` for the fresh
   independent reimport (unchanged), and `scripts/lean/replay-lean4export.lean`
   for submission to pinned Lean's own kernel (unchanged, same script C2 and
   `real_lean_replay_census.rs` use). The only new code is the grading logic
   around a goal request and a sidecar response -- protocol parsing,
   environment-identity comparison, and the two-stage verdict decision.

2. **Grading is staged so nothing before a real Lean invocation can be
   confused with something after one.** `pre_lean_verdict` decides
   everything answerable from the response bytes and the goal alone: a
   malformed envelope (unparseable JSON, an unrecognized `status`, or a
   `declined` `reason` outside the three known values), or an `accepted`
   response whose `environment_id` does not match the goal's. Only a
   syntactically well-formed, environment-matching `accepted` response
   reaches `PreLeanStage::NeedsLeanCheck`, the caller's signal to actually
   run the two independent paths. `decide_after_lean` then asks exactly the
   two ADR-0915 questions: did pinned Lean's kernel accept the stream at
   all (`false` -> `mutated-proof`), and does pinned Lean's own
   `env.constants` hold a constant of the goal's exact name whose
   independently-reimported type renders identically to the goal's expected
   type (either failing -> `wrong-goal`)? Neither stage ever reads the
   sidecar's own claim of success.

3. **The response protocol is deliberately the entire vocabulary the
   adapter understands.** `SidecarResponse` has exactly two shapes,
   `Accepted { environment_id, stream_path }` and `Declined { reason }`,
   parsed by hand from a `serde_json::Value` (this crate's existing
   dependency; no new `serde` derive dependency was added). Anything that
   does not parse into one of these two shapes -- including a `declined`
   reason outside `KNOWN_DECLINE_REASONS = ["unknown", "timeout",
   "unsupported"]` -- is folded into a single `malformed-response` decline,
   never a panic and never a default "success".

4. **A preregistered eight-category goal pack
   (`artifacts/lean-adapter/goal-pack/thin-adapter-v1.json`) is run live
   against real pinned Lean 4.30.0**
   (`crates/axeyum-lean-import/tests/thin_lean_adapter_goal_pack.rs`), one
   goal (`Nat.add_comm`, one of C2's own 9 credited roots -- reused, not
   reinvented) and eight synthetic sidecar responses:

   | category | mechanism | Lean invoked |
   |---|---|---|
   | success | the real, honest closure for `Nat.add_comm` alone | yes |
   | unknown / timeout / unsupported | typed decline reasons | no |
   | malformed_response | literal non-JSON bytes | no |
   | wrong_goal | a real, Lean-acceptable closure for a DIFFERENT credited root (`Nat.le_refl`) that never names `Nat.add_comm` at all | yes |
   | wrong_environment | the correct stream, wrong `environment_id` | no |
   | mutated_proof | the correct closure with `Nat.add_comm`'s proof value swapped for a different theorem's, the same mutation technique ADR-0915's adversarial fixtures use | yes |

   All eight are graded correctly against real Lean 4.30.0
   (`d024af099ca4bf2c86f649261ebf59565dc8c622`): 1 accepted, 4 declined, 3
   rejected. The suite asserts every category's observed verdict against a
   hardcoded expectation (never merely against its own `expected_verdict`
   field) and asserts that `success`, `wrong_goal`, and `mutated_proof` each
   actually recorded a real Lean invocation -- a decline or rejection path
   that was never exercised is not evidence of a decline or rejection path.

5. **A generated result artifact is validated by a gate needing no Lean
   toolchain**, matching C2's gen/check split. `crates/axeyum-lean-import/
   tests/thin_lean_adapter_goal_pack.rs` is the only writer of
   `artifacts/lean-adapter/results/thin-adapter-v1.result.json`;
   `scripts/check-lean-adapter.py` validates the committed artifact with
   seven guards, mutation-verified 1:1 in
   `scripts/tests/test-lean-adapter-mutations.sh`:

   | Mutation | Guard | What only that guard checks |
   |---|---|---|
   | dropped category | `ABSENCE` | every goal-pack-required category has an outcome |
   | no real Lean invocation recorded | `LEAN_ACTUALLY_RAN` | at least one of success/wrong_goal/mutated_proof actually invoked Lean |
   | success graded as a decline | `SUCCESS_ACCEPTED` | success's own observed_verdict is hardcoded "accepted" |
   | a mutation graded as accepted | `MUTATIONS_REJECTED` | wrong_goal/wrong_environment/mutated_proof are hardcoded "rejected" |
   | wrong typed reason | `DECLINES_TYPED_NONVACUOUS` | each decline category's reason matches the exit-criterion's own string |
   | internally inconsistent artifact | `EXPECTED_MATCHES_OBSERVED` | an outcome's own expected/observed fields agree |
   | stale toolchain claim | `ENVIRONMENT_TOOLCHAIN_STALE` | the result's lean_version/lean_commit match a FRESH read of the live checked-interchange census, external authority the result does not control |

   `ABSENCE` also fires the gate's absence requirement directly: an empty
   `--results-dir` exits 1 with a named reason rather than a silent pass.

6. **Bounded and stated as such.** This adapter covers 8 representative
   goal-pack categories over 1 subject drawn from C2's 9-credited-root
   population, not all 9 individually re-verified under the adapter (C2's
   own suite already does that per-root check) and not a general goal
   population. If the population grows, it grows by adding rows to the same
   goal pack and result artifact; nothing about the grading logic changes.

## What this format cannot express (a finding, not a gap)

The adapter's "environment identity" is a plain string comparison
(`lean_version@lean_commit:population_id`), not a cryptographic binding of
the goal to a specific kernel build or a specific machine. It is exactly
strong enough to catch a sidecar answering a stale or substituted
environment, which is what the roadmap's "wrong environment" category asks
for; it is not a defense against a sidecar that fabricates a matching
`environment_id` string while actually having run somewhere else. Nothing in
this ADR relies on the string being unforgeable -- the actual soundness rests
entirely on stage 2 (`decide_after_lean`), which never reads any field the
sidecar controls.

## Alternatives

**A real in-Lean `#lean_adapter_check` command/tactic that shells out to a
sidecar process from inside Lean's elaborator.** Rejected for this
increment: it would add a second, Lean-side integration surface (process
invocation, IO, a Lake project) as new trusted-adjacent code before C5's
native-workflow question is even in scope, and would not change what gets
checked -- the checking step is still "hand pinned Lean's own kernel a
stream via `addDeclCore`", which this ADR's orchestration already does from
the Rust side using the exact mechanism C2 validated. If C5 measures
repeated adapter friction that specifically needs an in-Lean entrypoint,
that is a new, separately-scoped decision.

**A second closure-computation or a second parser tailored to "goal
adaptation."** Rejected per the lane brief's own framing and per ADR-0800's
and ADR-0915's shared principle: a second mechanism for one question is how
two answers start disagreeing. Every check this adapter performs was
already checked, for the credited-root population, by C2.

**Recompute content digests for goal identity instead of the ADR-0915
rendered-type comparison.** Rejected for the same reason ADR-0915 rejected
it: `Kernel::render_lean` is what every other identity claim in this
repository reads from, and this ADR introduces no second identity mechanism.

## Consequences

C4 (demand-gated elaboration features) can extend the goal pack's
population and category set without touching `thin_adapter`'s grading logic,
which is already general over any goal name / expected type / environment
identity triple. Extending "environment identity" into something
cryptographically bound to a specific kernel build, if ever needed, is a
separate, explicitly scoped decision -- this ADR's environment check is
sized to exactly the roadmap's stated "wrong environment" category and no
further.

## Cross-reference, 2026-09-05

This ADR's alternatives section recorded that no in-Lean `#tactic`/command was
built, as a deliberate C5-adjacent scope call. That call is now closed:
[ADR-1666](adr-1666-by-axeyum-is-a-lean-tactic-and-lean-checks-the-term.md)
builds `lean/axeyum-tactic`, a Lake package exposing `by axeyum`, which reuses
this ADR's protocol shape — the `accepted`/`declined` envelope, the three
decline reasons, and the environment-identity discipline — and replaces the
NDJSON closure payload with a proof **term** Lean's own elaborator and kernel
check. Two of this ADR's statements carry over unchanged and are restated
there: the environment identity is a plain string comparison and a staleness
check rather than a soundness mechanism, and the soundness rests entirely on
the checking step and never on a sidecar-controlled field.

Nothing in this ADR is superseded or amended. C3 remains the Rust-side
protocol over C2's two checked paths.
