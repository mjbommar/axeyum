# ADR-0603: A classical theorem lands as a graded statement family, not a single row

Status: accepted
Date: 2026-08-27
Index-summary: Each classical theorem is represented by the strongest statement true of each function class — constructive general form, refutation certificate for the boundary, exact form on the decidable fragment, labeled import — one fact per statement, multiple evidence rows where routes overlap.
Index-status: accepted

## Context

Constructive strength varies by function class, and the boundary is itself a
theorem. IVT, worked: for arbitrary uniformly continuous `F`, the exact root
is REFUTED (`creal/ivt.rs`, two kernel-computed counterexamples) and
`ivt_approx` (an ε-root at every accuracy) is provably optimal; for
polynomial/algebraic `F`, zero-testing is decidable and the full
classical-strength statement — a root, named, as a real algebraic number — is
reachable, axiom-free, executable (Sturm isolation shipped; arithmetic layer
in flight). EVT stratifies three ways: attainment refuted in general; the
supremum constructively buildable for uniformly continuous `F`; the polynomial
case fully exact via certified differentiation + Sturm on `F'`. Pretending
these are one theorem proved twice would misstate all of them.

## Decision

A classical theorem's library entry is a FAMILY:

1. **The constructive general form** — the strongest statement for the widest
   class (`kernel-lean`), executable.
2. **The boundary certificate** — where the classical form is constructively
   unavailable, that unavailability is recorded as a refuted fact with its
   counterexample, not as an apology. The refutation is what proves row 1
   optimal.
3. **The exact form on the decidable fragment** — full classical strength via
   the CAS route, kernel-reconstructed per ADR-0601 §2, still axiom-free,
   still executable.
4. **The labeled import** — the classical statement in full generality,
   `imported-kernel-lean`, axiom footprint visible, excluded from headline
   counts (ADR-0601 §3).

One fact per DISTINCT statement. Where classes overlap and two routes prove
the SAME statement, that is one fact with multiple evidence rows (the
existing 2+-checker pattern), never duplicate facts.

## Consequences

- The curriculum map and ledger stop forcing a false choice between "weaker
  theorem" and "classical theorem"; both exist, labeled, with the boundary
  proved.
- Row 2 makes the family self-justifying to a referee: the entry explains WHY
  row 1 is the general ceiling, with a machine-checked certificate.
- Row 3 is the Pareto showpiece per topic and inherits ADR-0601's
  reconstruction requirement — a CAS-internal-only row 3 must read as such.

## Postscript: the four rows stated for MVT, LUB, Taylor remainder, FTA

IVT and EVT had their families stated at acceptance. The 2026-08-27
architecture review §4 named four more theorems still owed this treatment;
[`docs/curriculum/graded-statement-families.md`](../../curriculum/graded-statement-families.md)
states all four rows for each, as measured status rather than aspiration —
including that EVT's own row 2 is itself only "in progress"
(`crates/axeyum-cas/src/extremum.rs`), and that MVT's and LUB's row 2 are
currently asserted unavailability rather than proved refutations.

## Amendment, 2026-08-27: row 2 is PROVED for exactly one theorem

Measured against the kernel and the CAS source, not against prose:

- **IVT row 2 is genuine.** `creal/ivt.rs` carries two independent,
  kernel-verified counterexamples on `F := id` over `[-1,2]`, plus a concrete
  reduction test recording one at the kernel level.
- **EVT row 2 is NOT landed.** No declaration exists, and
  `crates/axeyum-cas/src/extremum.rs` says so itself: *"Row 2 (kernel side,
  **in progress**)"*. The coordinator repeatedly described EVT's boundary as
  "refuted rather than merely unbuilt" — that was an assertion inherited from
  the curriculum map, not a proved refutation.
- **MVT row 2** is an inherited assertion (`creal/monotone.rs:5029-5032`)
  which leans on the EVT one above, so it inherits its unprovenness.
- **LUB row 2** is a clean absence — no constructive-LUB counterexample exists
  anywhere in the repository.
- **Taylor row 2** is undecided: which statement (Lagrange vs integral-form
  remainder) would even be the refutation target has not been settled.
- **FTA row 2** is unassessed, and may not belong in this failure class at
  all: Bishop-style constructive analysis proves an APPROXIMATE FTA via
  infimum-of-modulus over a compact disk. Neither attempted nor refuted here.

**Consequence for the Pareto argument.** "The entry proves WHERE the boundary
is, with a machine-checked certificate" is the strongest thing this design
claims over a classical library — and it currently holds for **one theorem of
five**. An asserted unavailability is exactly the shape of claim this project
audits against everywhere else: it cannot fail, so it is not evidence. Row 2
must be either proved or labeled "asserted, not proved" wherever it appears;
`docs/curriculum/graded-statement-families.md` now labels each one.

**Cheapest closures, measured**: `polynomial_mvt` (row 3 for MVT) has every
ingredient shipped today — `rat_derivative`, `polynomial_ivt`,
`polynomial_extremum` — and is assembly, not new mathematics. The row-2
refutations are genuine research: each needs a kernel-computed counterexample
of the kind `creal/ivt.rs` already demonstrates is achievable.

## Amendment 2, 2026-08-27: EVT row 2 closed — and "refuted" was the wrong word

`CReal.evt_attained_max_decides_sign` (`creal/extreme_value.rs`) is landed and
kernel-accepted on first attempt:

    ∀ v c, le zero c → le c one →
      (∀ t, le zero t → le t one → le (mul t v) (mul c v)) →
      Or (le v zero) (le zero v)

An attained maximum on `[0,1]` for `evtLinear v := fun t => mul t v` yields a
sign decision for arbitrary `v`. An `argmax : CReal → CReal` operator would
discharge that hypothesis at every `v` at once, handing back exactly the
comparison `creal/cotransitivity.rs` states verbatim is "not assumed or
provable" here — the absence that cotransitivity exists to work around. So
`bounded_of_uniformly_continuous`'s **computed** bound with no attaining point
is OPTIMAL, not merely unimproved. **Row 2 now holds for two theorems of five**,
and MVT's row 2, which this amendment previously recorded as inheriting an
unproven assertion, now inherits a landed foundation.

**This form is stronger than IVT's.** `ivt.rs` closes off two specific
CONSTRUCTIONS by computed counterexample and argues the general case in prose
("as hard as deciding the sign of an arbitrary real"). EVT's row 2 makes that
argument itself the theorem.

**And it corrects this ADR's vocabulary.** Neither row 2 derives `False`.
Analytic LLPO is consistent with BISH, so what both establish is that the
classical conclusion is **at least as strong as a decision principle this
kernel demonstrably lacks** — i.e. *unprovable here*, not *refutable*. That is
the honest claim, and it is falsifiable in a way "refuted" is not: **land
`lt_total` over `CReal` and EVT's row 2 stops being a boundary result.** Row 2
should be described as an UNPROVABILITY WITNESS, and any row 2 that cannot name
the decision principle it reduces to is not yet one.

**The non-vacuity control is mandatory for this shape.** A row 2 stated as an
implication is unfalsifiable if its hypothesis has no models. The EVT lane
DISCHARGED its maximality hypothesis twice — at `v=c=1` (true argmax at the
right endpoint) and `v=c=0` (every point a maximiser) — with `Kernel::infer`
accepting both, plus computed endpoint instances whose strict comparison flips
with the sign of `v`. Future row 2s must carry the same control.

## Amendment 3, 2026-08-27: the family is UP TO four rows, not always four

This ADR's decision reads as though every classical theorem has all four rows.
Two independent lines of evidence now say that is a template, not a law, and
**FTA is the first candidate for a THREE-row theorem (1, 3, 4) with no row 2.**

1. **Shape argument** (FTA assessment lane). FTA's classical proof is a
   compactness argument over a **bounded closed disk**. Row 2 arises for IVT,
   EVT, MVT and LUB because their classical statements require deciding a
   comparison over an unbounded or open search — that is what
   `evt_attained_max_decides_sign` extracts. A compactness argument over a
   bounded region has no such step to extract.
2. **Construction evidence** (approximate-FTA lane). Building the shared
   prerequisite both FTA routes need — `Complex.abs_neg` and
   `Complex.abs_le_add_abs_sub`, the directional reverse triangle inequality —
   **encountered no undecidable comparison at any point**, and every
   construction type-checked on the first `add_declaration` attempt. That is a
   second, independent data point.

**It is NOT settled**, and the hedge matters: row 1 (approximate FTA) has not
closed. Its final assembly step still faces a real question the assessment doc
raised — distinguishing "the infimum is exactly 0" from "arbitrarily small" —
and that is precisely where an undecidable comparison could still appear. What
is established is that the *prerequisites* are clean and the *shape* differs
from the row-2 family.

**Decision**: a graded family has **up to** four rows. Row 2 is required
wherever the classical statement demands a decision the kernel lacks, and its
absence must be **argued from the shape of the classical proof**, never assumed
from a failure to find one. An entry claiming "no row 2 needed" must say which
decision principle would have been extracted and why the classical argument
never reaches it.

**Why this is not a weakening.** A theorem with no row 2 is one where axeyum's
row 1 and row 3 simply *dominate* the classical entry with nothing conceded —
strictly better for the Pareto argument than a theorem whose boundary must be
mapped. The four-row template was a worst case mistaken for a law.


## Amendment 4 (2026-08-27) — prose describing an absence is NOT a row 2

**A design-level remark that a principle is unavailable does not constitute an
unprovability witness, and mistaking one for the other silently converts this
ADR's hardest row into a freebie.**

Measured while sizing π. `creal/trig_fn.rs`'s module doc refers to
"`creal/ivt.rs`'s **refutation** of exact-root construction", and
`creal/cotransitivity.rs` states that "`CReal.lt` is not decidable and no
`lt_total` is assumed or provable over `CReal`". The coordinator read those and
concluded that π's row 2 already existed and was proved — that π would land as
a graded family whose hardest row was finished.

It does not exist. Checked by the lane, three ways:

- `shape_search --name-like lt_total` → **ABSENT** (no declaration of that name
  or shape, positive or negative).
- `shape_search --name-like ivt` → 12 hits (`ivt_approx`, `ivt_step`,
  `ivt_iter`, `ivt_bisect*`), **all constructive**, none concluding `False` or
  `Not (...)`.
- `grep -n "refut"` across `ivt.rs` and `cotransitivity.rs` → **zero hits**.

Both statements are meta-theoretic prose about what this development supports.
Neither is a `Kernel::add_declaration`-checked term. What `ivt.rs` actually
provides is

    CReal.ivt_approx : ∀ F a b, UniformlyContinuousOn F a b → le a b →
      le (F a) zero → le zero (F b) →
      ∀ e : Nat, ∃ x, le a x ∧ le x b ∧ le (abs (F x)) (ofRat (natDivSucc 1 e))

an approximate-root family — never `F c ≡ zero`.

**This is the same failure Amendments 1 and 2 already corrected, arriving by a
new route.** Amendment 1 found EVT's row 2 was an assertion inherited from a
curriculum map. Amendment 2 fixed the word "refuted", because a row 2 is a
falsifiable unprovability witness rather than a refutation. Amendment 4 is the
third form: a row 2 inferred from *someone else's prose* about an absence.

**Rule.** A row 2 exists only when a kernel-checked declaration exhibits the
reduction — classical statement ⟹ decision principle the kernel lacks. Until
then the row is **unassessed**, which is a legitimate and honest state (Rolle's
and MVT's row 2 are both recorded that way today). Specifically:

- **Never cite a module doc, a status note, or this ADR's own prose as evidence
  that a row 2 is proved.** Cite the declaration, by name, and confirm it is
  present with `shape_search` or `kernel.environment()`.
- **"No `lt_total` exists" and "`lt_total` is unprovable" are different
  claims.** The first is a measurement. The second is a theorem nobody has
  written, and it is exactly what a row 2 would be.
- The asymmetry is what makes this expensive: prose asserting an absence reads
  as more authoritative than an unassessed row, so it *removes* the pressure to
  build the row while conceding the same ground.
