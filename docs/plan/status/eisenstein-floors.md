# Lane: eisenstein-floors

<!-- plan-section: lane-status -->

**Status:** landed (2026-08-31). ADR-1260's residue 1 is closed, in general
form. Decision, mutation table and the honest limit on the controls:
[ADR-1290](../../research/09-decisions/adr-1290-the-floor-family-emits-because-the-relational-divmod-already-does.md).

## The question this lane was opened on

Can the floor-counting family be made to EMIT constructor shapes, or does it
genuinely fight `Nat.div`/`Nat.mod` being stuck at symbolic arguments?

**It emits, and nothing new had to be built to make it.** The deciding step is
`Nat.div_mod_mul_le_iff : ∀ d n q r s, divMod d n q r → (d*s ≤ n ↔ s ≤ q)`,
already in `nat_prelude/division.rs`. `Nat.divMod` is a RELATION whose quotient
is an ordinary bound variable, so there is nothing in it that could be stuck --
the same structural move as `Nat.even_or_odd`. `Nat.div_mod_exec` closes the loop
once, at the very end, when an executable form is wanted.

## Landed

| change | what |
| --- | --- |
| `crates/axeyum-lean-kernel/src/nat_prelude/floor_count.rs` | three declarations, all admitted FIRST attempt, all axiom-free |
| `crates/axeyum-lean-kernel/src/nat_prelude/floor_count_tests.rs` | evaluation probes, footprint, and the three declared types pinned character for character |
| `docs/research/09-decisions/adr-1290-the-floor-family-emits-because-the-relational-divmod-already-does.md` | the decision, the mutation table, and what the controls cannot catch |
| `docs/research/09-decisions/adr-1290-floor-count-checks.py` | 5 claims, 8 controls, 2 recorded survivors; exit status depends on the finding |
| `artifacts/facts/F-nat-countrange-succ-le-eq-min.json` | the counting core |
| `artifacts/facts/F-nat-countrange-mul-succ-le-eq-min.json` | the relational bridge |
| `artifacts/facts/F-nat-countrange-mul-succ-le-eq-floor.json` | the executable corollary |

Declarations:

- `Nat.countRange_succ_le_eq_min : countRange (fun y => ble (succ y) c) n = Min.min n c`
- `Nat.countRange_mul_succ_le_eq_min : divMod a B q r → countRange (fun j => ble (mul a (succ j)) B) n = Min.min n q`
- `Nat.countRange_mul_succ_le_eq_floor : countRange (fun j => ble (mul (succ ap) (succ j)) B) n = Min.min n (div B (succ ap))`

## Checks run

- `python3 docs/research/09-decisions/adr-1290-floor-count-checks.py` -- PASS
- `python3 docs/research/09-decisions/adr-1260-eisenstein-checks.py` -- PASS (re-run, not inherited)
- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` -- 320 passed / 0 failed
- `cargo clippy -p axeyum-lean-kernel --lib --all-targets -- -D warnings` -- clean
- `python3 scripts/validate-facts.py` -- 2514 facts, 0 errors
- `python3 scripts/check-shape-duplicates.py` -- OK, no new duplicate group
- Six mutants, five REJECTED by the trusted gate, one ADMITTED-TRUE-NOT-THE-THEOREM caught only by the type pin

## Not proved

Eisenstein's lemma and quadratic reciprocity remain open. Residue 2 (the side
condition `p·y ≠ q·x`, Euclid's lemma) and residue 3 (the mod-2 bookkeeping over
`Int.sumRange`, ADR-1275) are unchanged.
