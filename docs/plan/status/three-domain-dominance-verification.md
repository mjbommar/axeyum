# Lane: three-domain-dominance-verification — the Pareto claim, checked

<!-- plan-section: lane-status -->

Status: LANDED — one referee-checkable verification document across real
analysis, number theory and linear algebra, plus ADR-1030 and three corrections
to existing documents. Every number re-measured in this worktree; none quoted.

Deliverable:
[`docs/formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md`](../../formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md).

## Measurement base, and why it matters

Local `main` at `f7adaf7c3`, merged into this worktree. `origin/main` was
`878c285d9`, **22 commits behind**. My first sweep therefore reported
`CReal.lub_decides_em` and ADR-1010 ABSENT, each with a convincing positive
control beside it. Both exist. A stale base manufactures a confident wrong
absence verdict — the failure ADR-0603 Am. 4 exists to catch, arriving through
the door marked "I checked".

`check-autogenesis-holdout-isolation.py`, identical before and after all work:
`held_out=146|files_scanned=1110|settled=0|references=0|verdict=PASS`, exit 0.

## What was measured

`kernel_declaration_projection --include-constructed`, release: `rows=12049`,
`distinct_names=2558`; theorem 2100, definition 349, constructor 31, **axiom
30**, recursor 24, inductive 24. **All 30 axiom-bearing names are in `axreal`**;
every other prelude reads 0.

46 headline declarations across the three domains: footprint **0** for every
one. 12 expected-absent controls in the same command; 11 absent as documented.

Mathlib at pinned `c5ea00351c28e24afc9f0f84379aa41082b1188f`, Lean 4.30.0,
cached oleans: ten substantive theorems all on
`[propext, Classical.choice, Quot.sound]`. Controls split **three ways** —
`IsMaxOn`/`Nat.find`/`Nat.le_total` axiom-free, `Int.le_total` `[propext]`,
`Rat.le_total` all three — which is what makes the measurement evidence rather
than a constant.

## Findings

1. **EVT conceded** as a per-statement dominance example. Not on trusted base
   (we win 0 vs 3) and not on the bookkeeping ADR-0875 named, but because our
   statement assumes strictly more (`UniformlyContinuousOn : Sort (1)`, data,
   against Mathlib's `ContinuousOn : Prop`) *and* concludes strictly less (a
   bound plus approximation, witness under the `∀ n`, against an attained
   argmax). The two-axis test needs comparable statements; these are not.
2. **Number theory HAS a row 2**, contra the brief's framing and two places in
   the curriculum note. `Nat.lnp_unrestricted_implies_em` (nat, theorem, 0) with
   converse `Nat.em_implies_lnp` (nat, theorem, 0). It reaches unrestricted EM,
   not the analytic LLPO the analysis rows reach, and it is **the only row 2 in
   the tree pinned as an exact equivalence**. ADR-0716's empty-by-proof result
   is about the *analysis* mechanism only.
3. **Row 3 is unciteable in all three domains.** `ntheory_certify.rs` now ships
   Pratt/composite/factorization/CRT certificate checkers sharing no code with
   their producers — and **0 facts name them**, against a 3-fact positive
   control for `verify_extremum_certificate` and 2,366 facts total. The exact
   defect ADR-0875 found for EVT, recurring undetected.
4. **`Nat.le_total` is a TIE** — Mathlib's is genuinely axiom-free. "0 against
   3" is not uniform and should stop being quoted as though it were.
5. Linear algebra is understated in the received picture: `matMul` (assoc, id,
   distrib) and `matTranspose_mul` are at **symbolic dimension**, all 0. It is
   the determinant that is fixed-size and `rank` that does not exist.

## Landed changes

| when | what |
| --- | --- |
| 2026-08-31 | lane opened; kernel examples built `--release`; holdout PASS before work |
| 2026-08-31 | merged local `main`; re-measured everything after |
| 2026-08-31 | full kernel projection; 46 per-statement footprints; Mathlib probe at the pinned commit |
| 2026-08-31 | `09-the-dominance-claim-verified-across-three-domains.md` written |
| 2026-08-31 | ADR-1030 |
| 2026-08-31 | corrected `08-ivt-and-evt-measured-against-mathlib.md` (EVT verdict made) |
| 2026-08-31 | corrected the NT/LA curriculum note in three places (LNP row 2, §5 target 1, the verifier census) |

## Gates run

`gen-adr-index.py` exit 0 (`rows=689`). `check-links.sh` "all links ok".
`gen-plan.py` exit 0. `check-autogenesis-holdout-isolation.py` exit 0, PASS,
identical before and after.

`scripts/check-trust-closure.py` **did not run** — it needs a `cargo run
--release` kernel build, out of scope here. Its contamination figures are read
from its committed pin and labelled as floors, not as a live measurement.

## For the next lane

Register the number-theory certificate checkers as facts. That is the binding
item — more verifiers do not help while no fact names the ones that exist.
The ledger was deliberately out of scope for a verification lane.
