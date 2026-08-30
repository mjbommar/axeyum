# Notes: 333-cas-substance-gate

Detail moved out of [`../status/333-cas-substance-gate.md`](../status/333-cas-substance-gate.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**Exactly one of the 14 is refl-shaped: Thales.** The independent
s-expression detector agrees — over all 14 `formal.statement` strings it
returns True for Thales and for nothing else — and the two signals were built
from different inputs, so their agreement is a real cross-check.

The certificate derivation also reproduces, mechanically, the two calls the
`332-cas-thales-varignon` lane made by judgement: `thales` is `refl` and
`varignon` is `empty` (0 coordinates, 0 generators, both conclusion polynomials
`{"terms": []}`), while the other eight committed certificates are
`combination` — euler-line 2150 → 14, simson-line 14008 → 6, pappus 462 → 6.

## What the gate refuses

Twelve conditions, each with its own control (`scripts/tests/test_check_cas_substance.py`):

1. a kernel-reconstructed fact with no `cas_substance` block;
2. a `shape` outside the enumeration;
3. no `certificate` key at all;
4. a certificate path that does not resolve;
5. **a declared shape disagreeing with the certificate's derived one** — the
   half a lane cannot talk around, because the number comes from the CAS's own
   output;
6. a null certificate with no `derivation_declined_reason`;
7. a non-discriminating shape with no `disclosure`;
8. …with no `disclosure_axiom_key`;
9. …whose key names no `axiom_footprint` entry;
10. shape `empty` registered at all;
11. a `formal.statement` that is `X = X` after erasing `*1`, declared as
    anything but `refl`;
12. a `cas_substance` block on a fact that is not kernel-reconstructed.

**Nothing here excludes `refl`.** Thales' outcome — register, and disclose in
the `axiom_footprint` — is what this is designed to produce; a binary
pass/fail would have forced that lane to either drop real work or misdescribe
it. What is forbidden is `refl` reading the same as `combination`.

## Mutation kill sets, as measured

Both suites exit 0. `--check-anchors`: `suites=40 anchors=455 stale=0`.

    cas-substance             12 mutants, each killed exactly 1 test
    cas-substance-derivation   5 mutants, each killed exactly 1 test

**No mutant killed more than one, and none survived.** Per-mutant kill sets are
in the run output; each guard's control names the guard it measures.

Three of the 21 tests are positive controls — an honest `combination`, a
disclosed `refl`, and an ordinary `cas-internal` fact must all be ACCEPTED —
because every refusal test above would be satisfied by a gate that refused
everything.

`D1` is worth naming: no committed certificate carries a zero cofactor (0 of 45
across all ten), so the real ledger cannot exercise the rule that a zero
cofactor is not an active generator. Without that control the rule would be
deletable with the whole tree green — and deleting it is exactly how a `refl`
certificate gets promoted to `combination` by padding it with zeros.

## What the honest headline should be

The existing line is **not wrong** and this lane did not rewrite it: 14 *is* the
number of reconstructions. What was missing is what they establish.
`validate-facts.py` now prints, under the unchanged line:

    cas-certificate: 42 total -- kernel-reconstructed 14, cas-internal 28
      of those 14 kernel-reconstructed, by what the kernel obligation
      establishes: combination 5, evaluation 6, identity 2, refl 1
      1 of the 14 are NON-DISCRIMINATING (the obligation holds of every
      polynomial in place of the certificate's) and are disclosed as such --
      do not quote 14 as reconstructions with geometric content

**The proposal, for whoever owns the prose: quote the pair, never `14` alone.**
The defensible sentence is *"14 CAS results reconstruct through the kernel; 13
of those obligations discriminate the result they are filed under, and the
fourteenth (Thales) is refl-shaped and says so."* For geometry specifically the
honest number is **5 of 6**, not 6.

**Where `kernel-reconstructed` is quoted today** (found by grep; each needs a
human read, none were edited by this lane):

- `PLAN.md` (generated — fix the lane status it is generated from)
- `docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md`
- `docs/curriculum/graded-statement-families.md`, `BACKLOG.md`,
  `foundational-books/spivak.md`
- `docs/research/09-decisions/adr-0603`, `adr-0047`
- `docs/research/11-design-review/2026-08-29-row-three-is-blocked-on-multivariate.md`,
  `2026-08-28-ivt-evt-pareto-position-measured.md`
- lane statuses `145`, `223`, `224`, `274`, `277`, `314`, `317`, `322`, `327`,
  `332`, `135`, `138`, `adr601-impl`

## Coverage this gate does NOT have

Rule 5 — the derivation — is only available for the **6 of 14** facts that name
a certificate artifact. The other **8** reconstruct sign brackets and
coefficient-matching identities built inside a Rust test; their producers return
a decision and a witness rather than a JSON certificate, so their shape is
checked for validity, for the absence of a refl-shaped statement, and for
disclosure, and is otherwise **self-reported**. The gate prints that as a
number rather than implying it checks all fourteen equally.

**Follow-on work, not done here:** have `axeyum_cas`'s real-algebraic
sign-bracket route and `partial_fractions` emit certificates of the shape
`artifacts/geometry-certificates/*.json` carries. That would move 8 facts from
`declared` to `derived` and close the gap.

## Ledger changes, stated explicitly

No fact was reclassified, reopened, or had a status, evidence row,
`checker_command` or `axiom_footprint` entry changed. The only edit to the 14
facts is an additive `cas_substance` block. Blocks were spliced textually rather
than through a JSON round-trip, because seven of the files write
`"free_symbols": ["x"]` on one line and `json.dumps` re-wraps it — reformatting
a file this lane did not author is how a one-key addition becomes a 200-line
diff and someone else's merge conflict.

One observation for whoever owns that fact, NOT changed here:
`F:geometry-medians-cofactor-identity-kernel-checked`'s `formal.statement` has
**unbalanced parentheses** (one `)` too many). It parses as no-signal for the
text detector, so the gate falls back to the certificate derivation and still
has authority over that fact — but the statement should be corrected.

## Files

- `scripts/cas_substance.py` — the derivation core and the text detector
- `scripts/check-cas-substance.py` — the gate (`--report` prints the table)
- `scripts/tests/test_check_cas_substance.py` — 21 controls
- `scripts/tests/mutation_controls.py` — suites `cas-substance`,
  `cas-substance-derivation`
- `artifacts/ontology/fact.schema.json` — the `cas_substance` schema
- 14 facts under `artifacts/facts/` — one additive block each
