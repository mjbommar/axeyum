# ADR-1030: EVT is conceded, number theory has a row 2, and row 3 is unciteable in all three domains

Status: accepted
Date: 2026-08-31
Index-summary: A single referee-checkable verification of the Pareto claim across real analysis, number theory and linear algebra, with both trusted bases re-measured rather than quoted. Three decisions follow. EVT is CONCEDED as a per-statement dominance example — not on trusted base or bookkeeping, but because our statement assumes strictly more and concludes strictly less than Mathlib's, so the two are not comparable and the axiom-count win is a category error. Number theory DOES have a row 2 (`Nat.lnp_unrestricted_implies_em`, landed, footprint 0, and the only row 2 in the tree pinned as an exact equivalence), so the "rows 1 and 3 only" framing for the decidable subjects is wrong. And row 3 — the row the decidable-subject argument rests on — is unciteable in all three domains: number theory's certificate layer now exists in code with ZERO facts naming it, the same defect ADR-0875 found for EVT, recurring undetected.
Index-status: accepted

## Context

The project's central claim is that results like IVT and EVT are
Pareto-dominant over Mathlib on two axes — trusted base and computational
content — with breadth explicitly conceded. That claim and the graded-family
method carrying it are spread across a dozen ADRs (0603, 0692, 0699, 0716,
0717, 0725, 0825, 0875, 0895, 0930, 1000, 1010) and three curriculum notes. No
single artifact stated it so a referee could check it in one sitting.

This ADR records what a verification pass found. The document is
[`docs/formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md`](../../formalized-math-2026-08/09-the-dominance-claim-verified-across-three-domains.md).
Every number in it was measured in the lane's own worktree; none was quoted
from an ADR, because several ADR figures had already moved.

One methodological note that shaped everything else. The lane's first sweep ran
against `origin/main`, which was **22 commits behind local `main`**, and
reported `CReal.lub_decides_em` and ADR-1010 ABSENT — with a correct-looking
positive control beside each. Both exist. A stale base manufactures a confident
wrong absence verdict, which is the exact failure ADR-0603 Amendment 4 exists to
catch, arriving through the door marked "I checked". Merge local `main` before
measuring, and say which commit you measured at.

## Decision

### 1. EVT is conceded as a per-statement dominance example

`08-ivt-and-evt-measured-against-mathlib.md` has carried, since ADR-0895, an
explicit deferral: a "fresh two-axis pass is needed" to say whether
`CReal.evt_approx_max` against `IsCompact.exists_isMaxOn` counts as dominance.
**Make the call: it does not.**

The reason is not the trusted base, which we win, nor the bookkeeping ADR-0875
named. Both were re-measured. Ours reads `0`; Mathlib's reads
`[propext, Classical.choice, Quot.sound]` at pinned commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f` under Lean 4.30.0, with `IsMaxOn`,
`Nat.find` and `Nat.le_total` returning "does not depend on any axioms" in the
same run as discriminating controls.

The reason is that **two asymmetries point the same way**, and the repository
records them in separate sections but never together:

- **We assume strictly more.** `CReal.UniformlyContinuousOn` is `Sort (1)`,
  read from the kernel against `CReal.le : ... -> Prop` as control. The modulus
  is *data*. Mathlib assumes `ContinuousOn`, a `Prop`. Stronger in two
  independent ways: uniform rather than pointwise, and data rather than a
  proposition. And this kernel has no pointwise-continuity predicate at all
  (`CReal.ContinuousOn` ABSENT, controls FOUND), so the gap cannot be stated
  here, let alone bridged.
- **We conclude strictly less.** `evt_approx_max` gives, for each `n`, a point
  within `1/(n+1)` of maximising; the witness sits under the `∀ n` and is never
  claimed to converge. Mathlib gives a point where the maximum is achieved.

The two-axis test (ADR-0692) is defined to run on a statement "comparable in
content to Mathlib's". This one differs in the hypothesis *and* the conclusion,
in the same direction, and the axis we win is a third thing. The strongest
objection a Mathlib maintainer would raise — that a per-statement Pareto claim
across two different statements is a category error — is correct here, and the
honest move is to say so in print rather than to answer it.

What survives is stronger than the overclaim it replaces: EVT's classical
conclusion is not merely unbuilt, it is a **boundary**.
`CReal.evt_attained_max_decides_sign` (footprint 0) shows that an attained
maximum yields analytic LLPO. That is the claim EVT should carry.

**IVT is unaffected.** `CReal.ivt_approx` and `intermediate_value_Icc` are the
same *kind* of statement, and their exactness difference is exactly the
computational-content trade the axis measures rather than a third, uncounted
one. IVT remains citable with its caveats attached, as ADR-0692 and ADR-0875
already require.

### 2. Number theory has a row 2, and it is the strongest one in the tree

ADR-0716 measured that row 2 **of the analysis kind** is provably empty over ℕ,
ℤ and ℚ, because the principle every analysis row 2 extracts — order totality —
is a landed axiom-free theorem here (`Nat.le_total`, `Int.le_total`,
`Rat.le_total`, all re-confirmed FOUND at 0, against `CReal.le_total` and
`CReal.lt_total` ABSENT). That result stands and is a positive measurement.

It has been read one step too far, including in the brief that commissioned this
lane: as *"dominance in number theory and linear algebra must come from rows 1
and 3, not from row 2."* **For linear algebra that is right. For number theory
it is wrong.** ADR-0716 §2 itself named unbounded search as the boundary that
survives, and ADR-0725 built it:

- `Nat.lnp_unrestricted_implies_em` — `nat`, theorem, footprint **0**
- `Nat.em_implies_lnp` — `nat`, theorem, footprint **0**

Two consequences. The reduction reaches **unrestricted excluded middle**, not
the analytic LLPO the IVT and EVT rows reach — a strictly stronger boundary,
since LLPO is consistent with Bishop's mathematics and `em` is not. And because
the converse is also landed, it is **the only row 2 in the repository that pins
the price exactly** rather than bounding it from below; the three `CReal` rows
are one-directional implications.

So the ordering the curriculum documents imply is inverted: number theory's row
2 is stronger than real analysis's, and the decidable subjects are graded, not
flat.

`graded-statement-families-number-theory-and-linear-algebra.md` still said the
row was "the highest-value unbuilt row in this note" and still listed it as a
next target. Both corrected in place, citing the measurement.

### 3. Row 3 is unciteable in all three domains, and that is the weakest point

The dominance argument for the decidable subjects (ADR-0716 §4) is "one
statement, one trust anchor, three artifacts": the theorem, an executable
settling any concrete instance, and a certificate a third party re-derives.
Row 3 is where that argument lives.

Two documents record that `axeyum-cas` has 19 `verify_*`/`check_*` functions
and that **not one is number-theoretic**. Their method was sound; the tree moved
under it. Re-running their exact pattern gives **22 distinct** today, and **six
are number-theoretic**: `check_primality_certificate`,
`check_composite_certificate`, `check_factorization_certificate`,
`check_crt_certificate`, `check_irreducible_certificate`,
`check_irreducible_certificate_independent`, all in
`crates/axeyum-cas/src/ntheory_certify.rs`. That module exports
`PrattCertificate`, `CompositeCertificate`, `FactorizationCertificate` and
`CrtCertificate`, and its primality checker's doc records that it "shares no
code with `certify_prime` or with `ntheory::is_prime`" — the producer/verifier
separation ADR-0716's gap list asked for. Three of that list's four items are
closed. The fourth is not: `legendre` matches 0 times in that file, against a
17-match `Pratt` positive control in the same command.

**And no fact names any of them.** Count: `0`, against a positive control of 3
facts naming `verify_extremum_certificate` and 2,366 facts in the ledger.

This is exactly the defect ADR-0875 diagnosed for EVT — *the content exists and
the bookkeeping that would let anyone verify it does not* — recurring in a
different domain, weeks later, with no gate noticing. It is why two ADRs and a
curriculum note all report number-theoretic verification as absent: they looked
where the repository tells a referee to look, and it was not there.

Meanwhile the analysis families' row 3 is `cas-internal`, so it does not reach
the trust anchor the argument invokes.

**Therefore: a row-3 dominance claim requires a fact, not a function.** A
producer/verifier pair that no fact names is not row 3 in ADR-0603's sense,
because a referee has nothing to check. This ADR does not repair the ledger —
the lane was a verification and the ledger was out of scope — but it records
that the repair, not more verifiers, is the binding item.

## Consequences

- `07-the-cost-model-and-pareto-position.md`'s Pareto claim should cite IVT and
  should not cite EVT, and the reason to record is non-comparability rather
  than the bookkeeping ADR-0875 named. ADR-0675's original decision to cite IVT
  rather than EVT is vindicated by a third, independent route.
- "0 against 3" is **not uniform** and should stop being quoted as though it
  were. Measured per statement: 0 against 3 for the classical analysis and
  number theory, 0 against 1 for `Int.le_total`, and **0 against 0 for
  `Nat.le_total`**, which is a genuine tie. Mathlib's three axioms are the price
  of a classical quotient-backed ambient structure and it does not pay them
  everywhere.
- Any future claim that a subject is flat because row 2 is empty must say
  **which kind of empty**: empty by proof (the reduction target is landed here),
  empty by shape (argued from the classical proof, naming the principle that
  would have been extracted), or empty by omission. ADR-0716's result is the
  first kind and only for the *analysis* mechanism.
- Three of the thirteen per-statement comparisons are between statements that
  are **not comparable** (existence vs uniqueness of factorization; 2×2 vs
  general-`n` determinant; ℚ at arbitrary `n` vs a normed inner-product space).
  They are marked rather than counted. A dominance table that does not mark
  them is inflating itself.
- Linear algebra's received picture is too pessimistic in one specific way:
  `Rat.matMul` with associativity, identity, distributivity and
  `Rat.matTranspose_mul` are already at **symbolic dimension** over
  `Nat -> Nat -> Rat`, all axiom-free. It is the **determinant** that is
  fixed-size (`det2`, `det3`) and `rank` that does not exist (0 matches in
  `matrix.rs`, against an 11-match `rref` control).
- **Deliberately no score.** A weighted number would hide the per-statement
  detail that is the entire content of this verification.

## Alternatives considered

**Answer the EVT category-error objection instead of conceding it.** The
available answer is that `evt_approx_max` is the constructive substitute for a
statement that provably costs LLPO here, so comparing it to Mathlib's is
comparing the best available constructive content against the classical
content. That is a good argument for *why the gap exists*; it is not an argument
that the two statements are comparable, which is what the two-axis test
requires. Conceding costs one headline example and buys a claim that survives an
adversarial reading.

**Repair the ledger for the number-theory certificates in this lane.** Rejected:
a verification lane that also repairs what it measures cannot be checked
independently, and the ledger was explicitly out of scope. Recorded as the next
lane's item instead.

**Treat the 19-verifier claim as a method failure.** Rejected on measurement:
re-running the documents' exact pattern reproduces their approach faithfully and
returns a larger number, so the probe was fine and the claim went stale. Blaming
the probe would have taught the wrong lesson and would have obscured the real
one, which is that an absence claim about a moving tree needs a date and a
commit.
