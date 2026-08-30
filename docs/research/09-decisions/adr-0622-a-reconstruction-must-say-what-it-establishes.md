# ADR-0622: a CAS reconstruction must say what its kernel obligation establishes

Status: accepted
Date: 2026-08-30
Lane: `cas-substance-gate`
Index-summary: `kernel-reconstructed` counted reconstructions whose obligation was `X = 1*X`; every such fact now carries a `cas_substance` block whose shape is DERIVED from the certificate, and a non-discriminating shape must be disclosed rather than excluded.

## Context

ADR-0601 §2 split the `cas-certificate` proof route in two, so that evidence
reconstructing through `Kernel::add_declaration` could not read the same as
evidence terminating in the CAS's own normal form. `scripts/validate-facts.py`
implements the split in `classify_cas_certificate_checker`: a fact is
`kernel-reconstructed` when some executed `cargo test` / `cargo run` segment
names the `axeyum-lean-kernel` package.

That is a correct answer to *which trust anchor ran*. It is not an answer to
*what the anchor was asked to check*, and the headline

    cas-certificate: 42 total -- kernel-reconstructed 14, cas-internal 28

is read as the second. Nothing in the ledger inspected the obligation, so

    poly_expr(X) = Rat.ofInt 1 * poly_expr(X)

— a `mul_one`-shaped ring fact true of **every** polynomial — moved the counter
by exactly as much as a six-variable identity in which sixteen monomials from
two independently-derived geometric predicates cancel to eight. Both run
`add_declaration`, both are admitted axiom-free, both are honest, and only one
of them establishes anything about the theorem it is filed under.

This is the repository's standing "a checker that cannot fail is worse than no
checker" defect moved one level up. The checker here *can* fail — it just
cannot fail on the axis a reader cares about, and at N lanes the ledger is the
product.

It is not hypothetical. One lane hit both edges of it in a single session and
handled both correctly by judgement:

- **Thales.** `cert.generators[0]` is byte-identical to `cert.conclusions[0].poly`
  (the same 8-term `IntPoly` over six coordinates) and the single cofactor is
  the constant 1. The lane registered
  `F:geometry-thales-cofactor-identity-kernel-checked` anyway — the translator
  really does transcribe a real six-variable, eight-term polynomial and the
  kernel really does re-derive a well-typed `Rat` identity from it — and
  disclosed the refl shape in the fact's `axiom_footprint`.
- **Varignon.** Its certificate has `coordinates: []`, `generators: []`, and
  both conclusion polynomials already `{"terms": []}`: the CAS's own ring
  arithmetic cancelled everything before the certificate existed, so the only
  reconstructible statement is `Rat.zero = Rat.zero` over zero variables. The
  lane declined to register it, and said plainly that it would have passed the
  classifier and moved the counter with zero geometric content.

The orthocentre sibling's `notes` had already flagged the same refl shape
before either of those. Three correct calls in a row, all by judgement, none of
them checkable by anything.

## Decision

**1. A `kernel-reconstructed` `cas-certificate` fact must carry a
`cas_substance` block.** Schema in `artifacts/ontology/fact.schema.json`, gated
by `scripts/check-cas-substance.py`, registered in both aggregate gates.

**2. The block's `shape` is DERIVED from the certificate wherever a certificate
exists, and a declaration that disagrees is refused.** `scripts/cas_substance.py`
reads the artifact the CAS actually emitted, not the fact's prose. Per
conclusion, the obligation is `conclusion = Σ cofactor_i · generator_i`, and the
shape follows from how many generators carry a **nonzero** cofactor:

| shape | condition | what it establishes |
| --- | --- | --- |
| `empty` | no coordinates, no generators, empty conclusion polynomial | nothing |
| `refl` | one active generator, cofactor the constant 1, generator identical to the conclusion | `X = 1·X`, true of every polynomial |
| `scale` | one active generator whose cofactor must be distributed | a law about one polynomial and a multiplier |
| `combination` | two or more active generators | monomials from distinct generators must cancel — specific to the configuration |

Two further shapes are **declared, not derived**, because their producers emit
no certificate: `identity` (a symbolic ring identity at a free variable) and
`evaluation` (a closed obligation at concrete rationals).

A certificate's shape is the **weakest** of its conclusions'. That is the
opposite of `classify_cas_certificate_fact`'s stronger-wins rule across evidence
rows, and deliberately so: there the question is whether an independent
re-derivation exists at all, here it is what a reader may conclude.

**3. A non-discriminating shape is DISCLOSED, not excluded.** `refl` and `empty`
require a `disclosure` string and a `disclosure_axiom_key` naming an
`axiom_footprint` entry that carries the same disclosure, so a reader meets it
where the assumptions are listed rather than only in a validator's summary.
Thales is the model and the design target: registration plus disclosure.
Excluding it would drop real work; silence would let it read as orthocentre
does. `empty` alone is refused outright, because there is nothing to
reconstruct.

**4. A second, independent detector runs on the fact's own `formal.statement`.**
Parse it, erase multiplication by the literal 1, and refuse any fact whose
declared shape is not `refl` when some equation's two sides are then identical.
Over the 14 committed facts it fires on Thales and nothing else. It is
secondary — three of the fourteen statements carry placeholder names no parser
can expand, and it returns `None` (no signal, never "clean") for those — but it
gives the eight facts with no certificate one genuine failure mode instead of
pure self-report.

**5. The headline publishes the split.** `validate-facts.py` keeps its existing
line and adds a sub-line derived from the same blocks the gate checks, so the
two cannot drift without the gate going red.

## Consequences

The measured state of the ledger on 2026-08-30, all 14:

| shape | count | provenance | facts |
| --- | --- | --- | --- |
| `combination` | 5 | derived | centroid, medians, orthocentre, parallelogram, rhombus |
| `evaluation` | 6 | declared | evt, extremum, ivt-degree4, ivt-cbrt2, mvt, taylor |
| `identity` | 2 | declared | difference-of-squares, partial-fractions |
| `refl` | 1 | derived | **thales** — establishes nothing specific |

The five `combination` facts carry real cancellation: orthocentre 16 monomials
in and 8 out, centroid and parallelogram 88 → 4 per conclusion, rhombus
264 → 8. Thales is 8 in, 8 out, zero cancellation, because the input and the
output are the same polynomial.

**What this does NOT establish, stated because a gate implying coverage it
lacks is the defect it was built to fix.** Rule 2 is only available for the six
facts that name a certificate artifact. The other eight reconstruct sign
brackets and coefficient-matching identities built inside a Rust test, with no
JSON certificate to derive from; their shape is checked for validity, for the
absence of a refl-shaped statement, and for disclosure, and is otherwise
**self-reported**. The gate prints that 6-of-14 coverage as a number. Closing it
means having the real-algebraic and partial-fractions producers emit
certificates of the shape `artifacts/geometry-certificates/*.json` carries; that
is the follow-on work this ADR names and does not do.

The controls are `scripts/tests/test_check_cas_substance.py`, 21 tests
registered as two mutation suites. Measured: 12 gate mutants and 5 derivation
mutants, **each killing exactly one test, none surviving, none killing more
than one**. Three of the 21 are positive controls asserting that an honest
`combination`, a disclosed `refl`, and an ordinary `cas-internal` fact are all
accepted — without them every refusal test would be satisfied by a gate that
refused everything.

One control has no counterpart in the real data and is the more important for
it: no committed certificate carries a zero cofactor (0 of 45 across all ten),
so nothing but `D1` exercises the rule that a zero cofactor is not an active
generator. Deleting that rule is exactly how a `refl` certificate gets promoted
to `combination` by padding it with zeros, and the whole tree would stay green.

## Alternatives considered

**Refuse `refl` outright.** Rejected: it would have forced the Thales lane to
either drop a real, correctly-disclosed reconstruction or misdescribe it. A
binary pass/fail on a ledger whose entries are judgement calls produces lying,
not rigour.

**Key the gate on `formal.statement` alone.** Rejected as primary: three of the
fourteen statements carry placeholder identifiers, so a lane could defeat the
check by rewording. Kept as a secondary detector where it is sound.

**Fold the split into `classify_cas_certificate_checker`.** Rejected: that
function answers a different and still necessary question, and merging the two
would make "an independent re-derivation exists" and "the re-derivation has
content" indistinguishable — which is the failure being fixed.

## Related

- ADR-0601 — three producers, one trust anchor; §2 is the split this refines.
- `docs/plan/status/332-cas-thales-varignon.md` — the session that found both edges.
- `docs/plan/status/333-cas-substance-gate.md` — the measurement and this gate.
