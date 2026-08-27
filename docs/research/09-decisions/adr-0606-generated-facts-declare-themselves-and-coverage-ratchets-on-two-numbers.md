# ADR-0606: Generated facts declare themselves, and ledger coverage ratchets on two numbers

Status: accepted
Date: 2026-08-27
Index-summary: A mechanically written fact carries `provenance.generated_by` + `provenance.curation`, is held to a transcription-only prose vocabulary, never guesses `external_status`, and must carry a checker demonstrated able to fail; ledger coverage should ratchet on registered AND curated counts separately so bulk generation cannot masquerade as curation.
Index-status: accepted

## Context

`scripts/gen-ledger-coverage.py` measured the gap on 2026-08-27: **1,397 kernel
theorems, 474 registered, 923 unregistered — 34%.** Six ledger batches before it
each hand-picked and hand-wrote 12–30 facts. At that rate the backlog is thirty
more batches and it grows every time a lane lands a theorem. That is a defect in
the registration *process*, not a queue that needs draining harder.

Nearly every field of a `kernel-lean` fact about an already-proved theorem is a
transcription of something a tool already prints — the rendered type, the direct
theorem-dependency edges, the axiom-footprint size, and two settled
`checker_command` shapes. Automating that is straightforward.

The reason it had not been automated is the part that is not formulaic, and the
reason it is dangerous is stated in CLAUDE.md: **at N lanes the ledger IS the
product, so a checker that cannot fail is worse than no checker.** The 2026-08-15
audit found 40 of 162 checker runs exiting 0 on completion alone. Bulk-generating
923 facts with formulaic checkers is precisely how that finding gets reproduced
at scale, in one commit, with every file looking correct.

Three things a generator must not fake:

* **The mathematical characterisation.** Hand-written facts in this ledger carry
  observations a generator cannot invent — "this bound is loose and does not pin
  the sign", "the global version is FALSE for an arbitrary witness",
  "domain-restricted", "the ninth slice, and the one that closed it". Generated
  prose that reads like those is a fabrication.
* **The absence of commentary.** Silence is the failure mode: a fact with no
  caveats reads as a fact with no caveats to record.
* **`external_status`.** Whether mathematics-at-large knows a statement is a
  judgement about the literature, and this project has already cited Zenodo
  self-deposits as though they were refereed results.

## Decision

### 1. A generated fact declares itself, in `provenance`, with two keys

`artifacts/ontology/fact.schema.json` is `additionalProperties: false` at the top
level and `additionalProperties: true` inside `provenance`, which is also where
the marker semantically belongs. So:

```json
"provenance": {
  "date": "2026-08-27",
  "curation": "generated-unreviewed",
  "generated_by": "scripts/gen-kernel-facts.py",
  ...
}
```

**Two keys, not one, because they answer different questions and they
decouple.** `generated_by` records what wrote the skeleton and stays true
forever. `curation` records whether a human or lane has vouched for the prose
and the notes. A later lane that enriches a generated fact flips `curation` to
`curated` while `generated_by` remains accurate.

Collapsing them into one key forces that lane to choose between deleting a true
provenance statement and leaving an enriched fact indistinguishable from an
unreviewed one. Both are worse, and the second is the exact confusion the marker
exists to prevent.

No schema change is required, and none should be made to accommodate this: the
marker is provenance, and provenance is open by design.

### 2. Generated prose is held to a transcription vocabulary, enforced

Generated `title` and `statement` may name the theorem, its prelude, its
admission gate and its measured footprint, and may point at `formal.statement`.
They may **not** characterise what the theorem says. The generated `statement`
opens by saying so in its own text, so a reader who never sees this ADR still
learns that no characterisation was attempted. Generated `notes` state that no
curated commentary exists and that its absence means nobody has looked.

This is enforced, not merely intended. `gen-kernel-facts.py --audit` re-derives
the prose the generator would emit for every fact marked `generated-unreviewed`
and requires a byte-identical match. Hand-edited prose therefore **cannot** sit
under a generated marker: enrichment must declare itself.

### 3. `external_status` is omitted from generated facts, never guessed

The schema already reads an absent `external_status` as "nobody has looked",
which is exactly the case. `--audit` rejects a generated fact that carries one.

### 4. Every generated fact's checker must be able to fail, demonstrated

Two shapes, both with an exit status that depends on the finding:

* `theorem_dependency_inventory -- <Name> | grep -cE '^<Name>[[:space:]]'` — the
  example exits non-zero when a named filter matches nothing, and `grep -c`
  exits 1 printing `0` when the anchored line is absent. `grep -c` rather than
  `grep -q` (which SIGPIPEs the producer and reads as "not found" under
  `pipefail`); `[[:space:]]` rather than `\t` (a literal `t` in scripted GNU
  grep, which once made 54 facts' checkers wrong).
* `nat_axiom_inventory --require-axiom-free <prelude>` — non-zero when the
  trusted surface is not empty, and an error rather than a silent pass for a
  prelude the run never built.

`--audit` rejects any generated `checker_command` outside those shapes.

**And "can fail" is demonstrated per class, not asserted.** For the string
pilot, in an isolated snapshot: renaming `append_assoc`'s interned name and
rebuilding made its generated checker exit 1 with `count=0`, while `append_nil`'s
passed in the same run against the same binary and the renamed declaration still
resolved under its new name — so the failure was the *name*, not a broken build
or a lost proof. Footprint side: `--require-axiom-free string` exits 0, `axreal`
(30 axioms) exits 1, and a prelude the run never built exits 1.

### 5. The generator refuses rather than guesses

Declines, each with a printed reason: a non-zero axiom footprint (the projection
prints the *size*, not the axiom names, so the field could only be guessed); a
prelude with no falsifiable whole-prelude footprint checker; a slug colliding
with an existing or in-batch fact; a name whose `lean_pp` `_`-form namespace
cannot be confirmed against its own rendered type. **A smaller honest batch beats
a large unfalsifiable one**, and a declined theorem never enters the batch's id
map, so it cannot become a dangling `depends_on` edge.

### 6. Coverage should ratchet — on TWO numbers

**Recommendation, and the reasoning matters more than the verdict.** A static
`--check` says "regenerate the artifact"; it does not say "do not let coverage
fall". A ratchet turns "register what you land" from an aspiration into a gate.

But a single coverage ratchet creates exactly the incentive it should not:
generate junk to clear it. So ratchet **two** numbers from
`artifacts/ledger-coverage.json`:

* `registered` — total, any provenance. Unregistered count must never increase.
* `curated` — facts whose provenance is not `generated-unreviewed`. Reported and
  separately never-decreasing.

Generating facts moves the first and not the second. Bulk generation therefore
cannot masquerade as curation; it is *permitted*, and *visible*. Combined with
§4, junk cannot clear the ratchet at all, because a generated fact without a
checker that fails on absence does not pass `--audit`.

The `curated` counter requires a small addition to `gen-ledger-coverage.py`,
which this ADR's implementing lane deliberately did not make (that file was out
of its scope). Recorded here as the follow-up, not as done.

## Consequences

* The string prelude went from **0/64 to 64/64** and overall ledger coverage from
  **474/1,397 (34%) to 538/1,397 (38.5%)** in one mechanical batch, 0 declined,
  with all 128 emitted checker commands executed and 0 failing.
* Registering the string prelude required one narrow addition to
  `validate-facts.py`'s `KERNEL_THEOREM_RE`: the allowlist never admitted
  `axeyum.string.<N>`, the prelude's *actual* namespace. `Str` in that list is
  the carrier type's short name and matches no declaration the kernel admits, so
  the allowlist rejected all 64 string theorems. It went unnoticed for as long as
  the ledger registered zero of them — **an allowlist is only tested by the names
  someone tries**, which is the coverage trap one level down.
* A generated fact is a weaker artifact than a curated one and the ledger now
  says which is which. Nobody should quote a generated count as though it were a
  reviewed count, and §6's two-number ratchet is what keeps that distinction
  legible over time.
* Two theorem classes were deliberately **not** generated: anything with a
  non-zero axiom footprint (§5), and every prelude outside `PRELUDE_CONTRACT`.
  Adding a prelude to that table is a deliberate act that asserts a falsifiable
  whole-prelude footprint checker exists for it.

## Alternatives considered

**A top-level `generated: true` field.** Rejected: the schema is
`additionalProperties: false`, so it needs a schema change for information that
is already provenance, and one boolean cannot express the
generated-then-curated state.

**Marking generated facts only in a side file.** Rejected: the fact must stand
alone (`SELF-CONTAINMENT IS A REQUIREMENT` in the schema's own description), and
a side file is the shared append point this repository has been bitten by
repeatedly.

**Generating richer prose from the rendered type** (e.g. "states an equality
between `append (append a b) c` and `append a (append b c)`). Rejected: that is
a re-rendering of `formal.statement` wearing prose clothes, and the moment it is
readable it is also *interpretable* — a reader cannot tell where transcription
ends and characterisation begins. A generator that says nothing is honest; a
generator that says something almost-mathematical is the failure this ADR is
about.

**Not generating at all, and hand-writing thirty more batches.** Rejected on the
measurement: the backlog grows faster than hand-registration retires it, so this
is not a slower path to the same place — it is a path to a permanently widening
gap between what the kernel proves and what the ledger can show a referee.
