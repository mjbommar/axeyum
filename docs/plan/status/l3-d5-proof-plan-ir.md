# Lane: l3-d5-proof-plan-ir — L3 phase D5, the bounded proof-plan IR

<!-- plan-section: lane-status -->

**Landed (l3-d5-proof-plan-ir, 2026-08-31).** D5's IR and compiler are in
`crates/axeyum-lean-kernel/src/proof_plan.rs`: a `Plan` enum with the ten
node shapes the phase names (Exact, Apply, Rewrite, Symmetry, Transitivity,
Constructor, Transport, Eliminate, Induction, Witness, Compute), compiled to
ordinary kernel terms via the existing `NatOps` builder methods — the kernel
never sees a `Plan`. Three real families shortened by routing their `Eq ->
Iff` lift and `Iff` chain/flip through `proof_plan::iff_lift`/`iff_chain`/
`iff_flip` instead of a hand-copied local `pred_iff_of_eq`/`iff_trans`/
`iff_symm`:

| file | before | after |
|---|---|---|
| `nat_prelude/dvd_add_iff_left.rs` | 116 | 71 |
| `nat_prelude/gcd_dvd_mirrors.rs` | 476 | 423 |
| `nat_prelude/gcd_mul_right_mirrors.rs` | 273 | 217 |

Identity/footprint preserved: `examples/proof_plan_digest_probe.rs` hashes
each affected theorem's `Kernel::render_lean(type)|render_lean(value)` with
SHA-256. Run against this working tree and against a
`scripts/lane-snapshot.sh HEAD` build of the pre-refactor commit
(`246970caa`), all six digests are byte-identical and `axiom_footprint` is 0
in both. `cargo test -p axeyum-lean-kernel --lib nat_prelude::` is 240
passed (nonzero) after the rewrite.

Five malformed-plan declines, each mutation-verified (guard deleted, exactly
one test observed to fail, then reverted):

| guard | location | test killed |
|---|---|---|
| `Compute` non-defeq | `compile`, `Plan::Compute` | `compute_on_non_defeq_terms_declines` |
| `Transitivity` empty chain | `compile`, `Plan::Transitivity` | `empty_transitivity_chain_declines` |
| `Eliminate` zero cases | `compile`, `Plan::Eliminate` | `eliminate_with_no_cases_declines` |
| `theorem_plan` type leak | `theorem_plan` | `theorem_plan_declines_a_leaked_free_variable_in_the_type` |
| `theorem_plan` value leak | `theorem_plan` | `theorem_plan_declines_a_leaked_free_variable` |

Reverting the type-leak and value-leak guards each fell back to the
kernel's own opaque `KernelError::UnboundFVar { id }` — direct evidence the
guard converts an unnamed kernel rejection into a typed, localized decline,
which is the concrete form of "a plan language that gets binder scope right
automatically" the phase brief asks for.

Gate: `just proof-plan` / `python3 scripts/check-proof-plan.py` (three
guards: unit tests nonzero, digest probe runs and names all six subjects,
footprint unchanged at 0), plus `scripts/tests/test-proof-plan-check.py`
(in-process positive/negative controls on the checker script's own three
guards, no cargo invocation, <1s). Registered in `justfile`'s `check:` list
and at the end of `scripts/check.sh` (append-only, matching the existing —
imperfect — convention there; did not restructure either file). ADR-0980
records the trust-boundary argument, reusing ADR-0965's shape.

Deliberately out of scope this session: `Induction`/`Eliminate`/`Witness`
nodes exist and compile (each has a decline path exercised in tests where
applicable — `Eliminate`'s zero-case guard), but none of the three
rewritten families uses them; they were not exercised against a REAL
family, only structurally. No `gen-proof-plan.py` — see the module doc for
why D5 needed no code generation, unlike D1's spec pilot.

`python3 scripts/check-autogenesis-holdout-isolation.py` — measured before
touching anything and again at the end of this session — PASS both times
(held_out unchanged; this lane never touched `artifacts/autogenesis/`).

<!-- plan-section: landed-changes -->

| 2026-08-31 | `74ca7790b` | `proof_plan.rs` + compiler; three families rewritten; digest probe |
| 2026-08-31 | `ba2b22bbb` | add missing type-leak decline test; mutation-verify all 5 guards |
