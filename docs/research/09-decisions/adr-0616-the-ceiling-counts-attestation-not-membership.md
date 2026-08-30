# ADR-0616: The ceiling counts attestation, not membership

Status: accepted
Date: 2026-08-30
Index-summary: Amend ADR-0615's R3 to compare the UNATTESTED cohort against the attested one rather than the extension's flat row count, so re-attestation is the exit the ADR said it was; keep the dependency-component gap as a separate, unpromoted limitation

## Context

[ADR-0615](adr-0615-the-evaluation-envelope-is-per-cohort-and-a-draw-is-incremental.md)
replaced a cross-manifest sum bound with `EXTENSION_CEILING =
V1_EVALUATION_ENTRIES`, on a stated rule rather than a chosen number:

> **the unattested cohort may never outweigh the attested one**, which is
> ADR-0601's "imports are labeled scaffolding, never headline" applied to the
> same distinction.

and it named its own exit, twice:

> The v2 cohort exists at a weaker grade only because re-attestation needed a
> built Mathlib […] **When the ceiling binds, re-attest.**

**The exit does not work as implemented**, and the code says so plainly. R3
compares `len(entries) > EXTENSION_CEILING` — a flat count of the extension
manifest. Nothing in that expression reads the attestation record, so
re-attesting a row moves nothing.

That became live the same day the ADR landed. Lane `305-lean-attestation-s5`
built `scripts/attest-nursery-surface.py` and attested 159 of 160 rows on s5 in
3.6 s; lane `309-nursery-draw-four` drew 40 more and attested the full 200-row
manifest in 3.9 s, recording **197 attested, 3 not-elaborable, 0 unattested**
in `surface_validation`. The ceiling still counted all 200 as scaffolding, at
200 of 214, leaving 14 rows of headroom against a smallest rule-compliant draw
of 40 — so the only route past it was the raise ADR-0615 rejected with reasons.

The manifest also contradicted itself. It carried a populated
`surface_validation.attested` list of 197 ids **and** a `limitations` entry
reading *"These statements carry the quotation grade, not v1's real-Lean
round-trip attestation; the two must not be reported together as one attested
population."* Both sentences cannot be current, and nothing in the file said
which was.

## Decision

**Three changes. Raising a number is still not one of them.**

1. **R3 compares by ATTESTATION.** `attested_cohort` is every row that went
   through the real-Lean round trip and was accepted — nursery-v1's 214 plus the
   extension's accepted rows. `unattested_cohort` is every extension row that
   did not. R3 refuses when `unattested > attested`, which is the rule ADR-0615
   wrote. `EXTENSION_CEILING` is deleted rather than re-pointed: a constant that
   no longer names what it bounds is the next lane's wrong assumption.
2. **A `not_elaborable` row counts as UNATTESTED.** It has been through the
   round trip and Lean refused it, so it is a preregistered string that is not a
   proposition — strictly worse than a row nobody has checked, and it must never
   buy headroom. The three such rows
   (`F:ml430-nat-le-induction-2f088ac3` and the two
   `integer-absolute-value` coercion failures) stay counted against.
3. **`limitations` is derived from the run, not asserted.** The attestation
   clause is computed from `surface_validation`; the clause that survives full
   attestation is the one attestation does not repair (below).

Plus one guard the change makes necessary: **an ingested attestation record must
name the pinned Mathlib commit.** Recording `mathlib_commit` was descriptive
before; now that an accepted row buys ceiling headroom, a run against another
commit would grade statements against a library they were not quoted from.

## Evidence

### Is an attested extension row the same grade as a v1 row?

**On the statement, yes — and it is better-evidenced.** Measured rather than
inferred, because `nursery-v1.json` itself carries **no `surface_validation`
key at all**; the record lives in its source catalog.

`artifacts/autogenesis/mathlib-nat-int-fact-catalog-v1.json`:

```json
"surface_validation": {
  "method": "declare every formal.statement as an axiom after import Mathlib;
             no theorem value or proof is read",
  "observed_result": "accepted-214-proof-free-axiom-types",
  "statement_count": 214,
  "expected_sha256": "a4f51828c0b70709aeef3429400d8fac90f80d5d3164bd8259b1b5fd1fd5995d",
  "external_file": ".../mathlib-v4.30.0-nat-int-nursery-surface-v1.lean"
}
```

That file is still on disk and still intact:

| check | result |
| --- | --- |
| `sha256sum` of the pinned module | `a4f51828…` — **matches** `expected_sha256` |
| `/usr/bin/grep -c '^axiom '` | **214**, one per evaluation entry |
| `/usr/bin/grep -c 'negative_control\|DoesNotExist'` | **0** |

`scripts/attest-nursery-surface.py` runs the same method verbatim — `import
Mathlib`, one `axiom <name> : <statement>` per row, no proof read. So on the
question the grade answers (*is this string a well-formed Mathlib proposition?*)
the two cohorts are graded identically.

**The third row is the one that decides "at least as good".** v1's run carries
**no negative control**, so its `accepted-214` cannot distinguish *Lean accepted
214 statements* from *the harness could not see errors*. That is not a
hypothetical: lane 305's first run of the new harness reported a clean 4 of 4
because its diagnostic regex demanded a bare `error:` while Lean 4.30 emits
`error(lean.unknownIdentifier):`, and only the deliberately-unelaborable
negative control caught it. The extension's attestation therefore carries
strictly more evidence than v1's — per row rather than as a block, with a
control that must be REJECTED or the run fails.

### What is NOT the same, and is therefore not promoted

**The row, as a member of a blind evaluation population.** `nursery-v1.json`'s
`policy` states:

```json
"split_component_authority": "declared-dependency-weak-component",
"split_leakage": "no-declared-component-may-cross-evaluation-partitions",
"minimum_declared_dependency_depth": 2
```

and its entries' `source_group` values are hashed components
(`mathlib-v4.30.0-b064fa21f15a772b`, …). The extension's `source_group` values
are Mathlib module paths (`Init.Data.Nat.Mod`, `Mathlib.Data.Nat.Totient`, …),
and no dependency-component analysis was run. Two theorems in different modules
can sit in one dependency component, so a held-out row here can be entailed by a
train row here and nothing in the manifest sees it.

**So "same grade" is true of the STATEMENT and false of the ROW**, and the
ceiling is the wrong instrument for the second. R3 is a statement-provenance
rule — ADR-0601's scaffolding/headline distinction. Split integrity is governed
by R1, R8, R9 and `check-autogenesis-holdout-isolation.py`, per row and per
family. Promoting on the attestation axis must not launder the other, so the
gap is stated as its own limitation and is asserted by a control that runs
against a **fully attested** cohort.

Note in passing that the old limitations text was stale in a second way: it said
*"depends_on is empty"*, and 96 of 200 extension facts now carry edges (as do
125 of v1's 214). Those are ledger-owned and accrued after the fact — ADR-0615
item 3 makes `depends_on` mutable — never the preregistration-time analysis the
sentence was about. The replacement says so.

### What the change does to the numbers

```
python3 scripts/gen-autogenesis-nursery-refill.py --check
AUTOGENESIS_NURSERY_REFILL_OK|entries=200|…|combined=414|attested=411|unattested=3
```

Headroom goes from **14 rows to 408** — the attested cohort is 214 + 197, the
unattested one is the 3 Lean refused. The manifest regenerated with 8 insertions
and 6 deletions: no entry moved, no partition moved, no fact file touched.

**That is looser than the old bound and it is not a bound removal.** A draw's
rows land in `unattested` by construction (`surface_validation` puts any id no
run has covered there, verified byte-stable across a re-run with no ingest), so
the guard still binds on a draw and is still cleared only by running Lean
against the pinned Mathlib — which is exactly the cadence ADR-0615 asked for,
at 4 seconds a run.

It is also not the binding constraint on drawing. Draw 4 measured
held-out-safe **family** supply as essentially exhausted at the 10-candidate
module granularity, and had to combine four below-floor modules to fill two
held-out slots. R5 and R9 are what actually gate a draw; the row ceiling
binding at 200 was an artifact of counting the wrong thing.

## Alternatives

**Raise `EXTENSION_CEILING` to 400.** Rejected for the reason ADR-0615 rejected
it: it is a dial, not a rule, and it leaves the misattribution in place. The
whole point of `EXTENSION_CEILING = V1_EVALUATION_ENTRIES` was that it was
derived; the defect was the *comparison*, not the value.

**Compare `unattested` against `V1_EVALUATION_ENTRIES` alone** — "at most 214
rows may be unattested at any time" — which is tighter (214 instead of 408) and
coincides with today's constant. Rejected: it reintroduces a frozen literal that
tracks nothing, and it is not what the rule says. "May never outweigh the
attested one" means the attested population, which grows as rows are attested.

**Require every row to be attested before a draw may land.** Attractive as
cadence and unimplementable as stated: a draw's own rows are unattested at
emission, so the rule would refuse every draw. The weaker "no draw while a
PRIOR row is unattested" would make drawing hard-depend on one host being
reachable, and as of 2026-08-29 only s5 has a built Mathlib.

**Count `not_elaborable` as attested** (it *has* been through a run). Rejected —
this is the direction where being wrong is expensive. Lean refusing a string
means we preregistered something that is not a proposition; treating that as
evidence of statement quality inverts the finding.

**Leave `limitations` a literal and just fix the sentence.** Rejected for the
reason the grade itself was made derived one ADR earlier: a literal cannot
degrade. The next draw's rows would inherit whatever the string claimed, which
is precisely how this contradiction arose.

## Consequences

- **Easier**: the exit ADR-0615 named now works. Attesting a draw is a 4-second
  s5 run and it moves the ceiling; nobody has to choose between a raise and a
  stalled queue.
- **Harder**: an attestation record is now evidence with consequences, so it is
  checked harder — pinned commit, negative control rejected, per-row ids. A run
  against an unpinned Mathlib is refused rather than recorded.
- **Newly visible**: `gen-autogenesis-nursery-refill.py --check` is registered
  in `scripts/check.sh` and the `justfile`, the debt ADR-0615 recorded as owed
  once the `F:ml430-nat-totient-eq-zero-3be161d6` drift was resolved. It is
  green, and R3 now depends on `surface_validation`, so a hand-edit there
  changes what the ceiling permits and this is what re-derives it.
- **Watch**: the ceiling is now loose enough that it will not fire for roughly
  ten draws. If row count ever becomes the binding constraint again — rather
  than held-out family adjacency, which is what binds today — revisit whether
  the rule needs a cadence term as well as a ratio.
- **Unchanged and deliberately so**: the two cohorts are still not
  interchangeable as an evaluation population, and nothing here makes them so.

## Related

- ADR-0615 — the per-cohort envelope this amends; everything else in it stands.
- ADR-0601 — "scaffolding, never headline", the rule R3 encodes.
- ADR-0542 — the amendment ledger, why a `not_elaborable` row is recorded rather
  than repaired or deleted.
- `docs/plan/status/294-nursery-ceiling-adr.md`,
  `305-lean-attestation-s5.md`, `309-nursery-draw-four.md` — the three lanes
  whose measurements this rests on.
- `docs/contributor-guide/lean-surface-attestation.md` — how to run the
  attestation and what its output means.
