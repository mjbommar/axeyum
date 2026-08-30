# Lane: ledger-uc — register the fourth batch (uniform convergence, alternating series, polynomials, crossing)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, ledger-uc, 2026-08-27).** Registered 26 new
facts in `artifacts/facts/`. `python3 scripts/validate-facts.py` is green:
**776 facts checked, 0 errors** (750 pre-existing + 26 new).

**Ch.24 (uniform convergence, new chapter):** `F:creal-uniformconvergeson`
(the CARRIER — a one-constructor `Type` in `Sort (1)`, not `Prop`: its
`--require-kind` is `inductive`, not `definition`), `F:creal-uniform-converges-id`,
`F:creal-uniform-converges-geom-half` (the two concrete instances),
`F:creal-uniform-limit-uniformly-continuous` (the headline theorem). Every
fact's `statement` records that `UniformConvergesOn` must be `Type`-valued
because the headline theorem *constructs* a `UniformlyContinuousOn` witness
from the rate as literal `Nat` data, and `Exists.rec` is `Prop`-only. No
pointwise-not-uniform counterexample is claimed or checked; the guarantee is
recorded as a type-level argument (`rate : Nat`, not `CReal -> Nat`).

**Ch.22-23 (alternating series):** `F:creal-negonepowdouble`,
`F:creal-alternatingeleo`, `F:creal-alternatingbracket`. **NOT registered**
(do not exist in the merged tree): `CReal.alternatingBracketUpper`,
`CReal.alternatingLowerBound`, `CReal.alternatingUpperBound` — see Findings
below. *(Since landed — all three now exist in the kernel; historical record.)*
<!-- was-absent: CReal.alternatingBracketUpper, CReal.alternatingLowerBound, CReal.alternatingUpperBound -- this status note's snapshot of the merged tree; all three since landed -->

**Ch.20 (`CReal` polynomials):** `F:creal-polyeval` (+`-zero`/`-succ`),
`F:creal-polyadd`, `F:creal-polyeval-polyadd`, `F:creal-polyscale`,
`F:creal-polyeval-polyscale`, `F:creal-polydegreelt` (recorded as a
PROPOSITION, not a computed degree — `CReal.Equiv`/`CReal.le` are
undecidable) (+`-polyadd`/`-polyscale`).

**Ch.25-27 (`Complex` polynomials, factor theorem):**
`F:complex-polydegreelt-polymul`, `F:complex-hornerfromtop`
(+`-zero`/`-succzero`/`-succsucc`), `F:complex-factorquotient` (a COMPUTED
quotient via a nested `Nat.rec`, never `Exists`-elimination — its own notes
record the forced-`zero`-prepend boundary bug the natural reindexing hits),
`F:complex-factorquotient-degreelt`.

**Ch.14 (integral machinery):** `F:creal-meshscaledleofge`,
`F:creal-crossingclose` — registered as what the theorem STATES, with its
`statement` and `notes` explicit that `hap`/`hpb` (`samplePt`'s domain
membership) are UNDISCHARGED hypotheses of the theorem itself, not a proof
gap; the theorem the kernel admitted is fully and soundly proved but not
usable as a closed result until those two hypotheses are separately
discharged.

Detail moved to [`../notes/133-ledger-uc.md`](../notes/133-ledger-uc.md).

