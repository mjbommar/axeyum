# Notes: 362-ivt-evt-ledger-hygiene

Detail moved out of [`../status/362-ivt-evt-ledger-hygiene.md`](../status/362-ivt-evt-ledger-hygiene.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

All ten flipped `provenance.curation` to `curated` per
`scripts/gen-kernel-facts.py`'s own contract. No `epistemic_status`,
`proof_route`, `axiom_footprint`, or `formal.statement` touched.

Commit: `6a78868f7`.

## 2. `exhaustive-enumeration` label on IVT row 2's non-vacuity check

Determination: **the label was wrong, the check was right.** The check
(`creal_tests::ivt_row_two_derives_a_principle_absent_from_the_environment`)
enumerates `kernel.environment()`, requires a same-kind positive control
(`CReal.lt_cotrans`) to be found by the identical lookup, and asserts absence
of four specific names (`CReal.le_total`/`lt_total` and both camelCase
spellings). That is real, falsifiable work — but it is not exhaustive over
every way a total-order principle could be expressed (a declaration landed as
`CReal.le_or_le` would not trip it), so `"kind": "exhaustive-enumeration"`
overstated it. Relabeled `"instance-pin"` (already used elsewhere in this
ledger for a check pinning a specific, named, finite set of instances) and
rewrote `supports` to say exactly what is and is not covered.
`checker_command` unchanged.

Verified both directions:
- Ran the checker: `cargo test -p axeyum-lean-kernel --lib
  creal::creal_tests::ivt_row_two_derives_a_principle_absent_from_the_environment
  -- --exact` → **1 passed; 0 failed; finished in 121.73s** (measured this
  session).
- Did not land a fabricated declaration to confirm the fail-direction by
  execution (`creal/` is another lane's working area this session, per this
  lane's own working rules). Confirmed by reading
  `crates/axeyum-lean-kernel/src/creal/creal_tests.rs`: the test asserts
  `!present(name)` for each of the four forbidden spellings inside a loop, so
  landing any one as a real declaration fails that assertion and the test.

Commit: `68e5d2372`.

## 3. Why every survey (including the audit's own) missed `F:cas-extremum-irrational-argmax`

Both a naming problem and a metadata problem; **not** a real classification
gap — the fact is correctly tagged where it matters.

- **Naming**: `extremum` does not contain `extreme` as a substring (they
  diverge at the 7th character: `extremu` vs `extreme`), and neither the id
  nor the prose contains `evt` or `ivt`. Any survey built on `grep -i
  'evt|extreme'` over ids or prose structurally cannot find it, independent of
  care taken.
- **It is not a classification gap**: `formal.fragment` for this fact is
  `"real-algebraic-evt"`, and all five other CAS IVT/EVT facts carry an
  equally unambiguous `real-algebraic-ivt*`/`real-algebraic-evt*` fragment.
  Measured — `formal.fragment` matched against `ivt|evt` case-insensitively
  across the whole ledger returns exactly these 6 CAS facts and nothing else.
  The fact is tagged correctly; nobody's survey queried that field.
- **The deeper metadata problem**: `formal.fragment` means something
  different per family. For CAS facts it is a topic tag
  (`real-algebraic-evt`); for the 11 `CReal` facts it is the carrier
  (`"CReal"`, the same for every `CReal` fact regardless of topic). No single
  query against `formal.fragment` spans both families — a correct survey has
  to know to combine a `formal.fragment` match for CAS facts with an
  id/`formal.kernel_theorem` name match (`ivt_`/`evt_`) for `CReal` facts.
  `concept_refs`, the schema's field for exactly this kind of cross-cutting
  classification, is unused (`None`) on all 17 IVT/EVT facts in the ledger,
  in both families — so no facts-side mechanism currently closes this gap.

Not fixed here: restructuring `formal.fragment`'s semantics or populating
`concept_refs` ledger-wide is a schema/taxonomy decision, out of this lane's
scope (diagnosis only, per brief) and arguably ADR-worthy given
`docs/research/11-design-review/2026-08-27-retrieval-is-the-bottleneck.md`'s
existing finding that retrieval is the binding cost gate.

## formal.statement misdescription

None found. Every `formal.statement` checked against its fact's new prose was
first read from `creal.rs`'s own field-doc comments (which independently
transcribe the same rendered Lean type) or directly from the JSON's
`formal.statement`, and both agreed in every case.

## Verification run this session

- `scripts/validate-facts.py` → 2265 facts checked, 0 errors (run twice, once
  after each commit's edits).
- `scripts/gen-kernel-facts.py --audit` → 1035 generated-unreviewed, 10
  generated-then-curated, 0 problem(s).
- `scripts/check-mirror-statement-fidelity.py` → `facts=2265 mirrors=514
  hash_verified=502 unpinned=12 violations=0 verdict=PASS`.
- `cargo test -p axeyum-lean-kernel --lib
  creal::creal_tests::ivt_row_two_derives_a_principle_absent_from_the_environment
  -- --exact` → 1 passed, 121.73s.
- Did not run: `cargo test --workspace`, `./scripts/check.sh`, or any other
  broad gate — out of scope per this lane's working rules (targeted checks
  only; `creal/` source is another lane's area this session).
