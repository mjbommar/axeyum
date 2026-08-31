# Lane: determinant-laws

<!-- plan-section: lane-status -->

**Landed.** One of the four laws ADR-1120 left open over `Rat.det` (the
determinant at general `n`) is proved at a symbolic dimension, together with
the congruence that unblocked it and will be reused by the next two.

The blocker ADR-1120 named — "an induction relating minor structure across
dimensions" — is narrower than that and it is one lemma. `Rat.det`'s recursive
call is at the MINOR, so an induction over the dimension arrives at a matrix
that is only POINTWISE the one the induction hypothesis is about, and this
kernel has no `funext`. Reasoning recorded in
[ADR-1135](../../research/09-decisions/adr-1135-a-determinant-congruence-is-what-the-absence-of-funext-costs.md).

## Landed changes

| what | where |
| --- | --- |
| `Rat.sumRange_head_of_tail_zero`, `Rat.det_congr`, `Rat.matMinor_matId`, `Rat.det_matId` — four checked theorems, empty axiom footprint, admitted first attempt | `crates/axeyum-lean-kernel/src/rat_prelude/matrix_det.rs` |
| Statement-shape pin and the three ingredient controls | `crates/axeyum-lean-kernel/src/rat_prelude/rat_prelude_tests.rs` |
| `F:rat-det-mat-id-general-n`, `F:rat-det-congr-pointwise`, `F:rat-sum-range-head-of-tail-zero` | `artifacts/facts/` |
| ADR-1135 | `docs/research/09-decisions/` |

## Checks run

- `cargo test -p axeyum-lean-kernel --lib rat_prelude::` — **151 passed, 0
  failed** (237 s). The full prelude sweep, not a filtered subset: one bad
  declaration poisons the shared prelude build, so a narrow filter is not a
  gate here.
- `python3 scripts/validate-facts.py` — 2,392 facts, 0 errors.
  `check-fact-depends-derived.py --fix` added three edges the proof terms
  carry (`Rat.sumRange_congr`, `Rat.mul_zero`, `Rat.add_zero`).
- `python3 scripts/check-settled-fact-statements.py` — PASS, 2,206 pinned,
  0 unpinned, 0 drifted.
- `python3 scripts/gen-adr-index.py --check` — 704 rows, no new duplicate
  numbers.
- Kernel checker command verified in BOTH directions: present name prints 1
  and exits 0, absent name prints 0 and exits 1.

## What is NOT established

- `Rat.det_matId` is **not** a stronger check on the index shift or the sign
  than `det_eq_det2` already is. Measured by mutation in this lane's worktree:
  swapping `Rat.matSkip`'s branches breaks the prelude build at `det_eq_det2`,
  and `Rat.matMinor_matId` survives that same mutation because `matSkip 0 x`
  is `x` under both readings. The agreement theorem is still the discriminator.
- None of the three new controls separates a sign flip
  (`det (matMinor matId 0 1) 2` is `0`, and `neg 0 = 0`). That is
  `det_eval_example`'s job, at value 13.
- Transpose invariance and general-row expansion were **not attempted** and
  are not sized. Take general-row expansion first — transpose invariance
  needs it.
- Multiplicativity is blocked on a missing aggregate type, not on effort:
  Leibniz sums over permutations, Cauchy-Binet sums over functions
  `[0,n) -> [0,n)`, and the elementary-matrix route needs a factorization
  length as data. All three need an aggregate this kernel does not have.

## Next

`Rat.det`'s expansion along a general row (ADR-1120's law 3), reusing
`Rat.det_congr`.
