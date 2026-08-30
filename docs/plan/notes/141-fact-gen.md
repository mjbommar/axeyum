# Notes: 141-fact-gen

Detail moved out of [`../status/141-fact-gen.md`](../status/141-fact-gen.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**The honesty design, and what it refuses (ADR-0607).** Generated prose is held
to a transcription vocabulary — it may name the theorem, its prelude, its
admission gate and its measured footprint, and may not characterise what the
theorem says; the emitted `statement` says so in its own text. Generated `notes`
state that no curated commentary exists and that its absence means nobody has
looked. `external_status` is omitted, never guessed. Provenance carries **two**
keys, `generated_by` (what wrote the skeleton, true forever) and `curation`
(whether anyone vouched for the prose), because they decouple: enrichment flips
`curation` to `curated` while `generated_by` stays accurate. `--audit` makes the
marker load-bearing by re-deriving the generated prose and requiring a
byte-identical match, so hand-edited prose cannot sit under a generated marker.

**Refusals, each with a printed reason:** non-zero axiom footprint (the
projection prints the size, not the axiom names — the field could only be
guessed); a prelude outside `PRELUDE_CONTRACT` (no falsifiable whole-prelude
footprint checker known for it); a slug colliding with an existing or in-batch
fact; a name whose `lean_pp` `_`-form namespace cannot be confirmed against its
own rendered type. A declined theorem never enters the batch id map, so it
cannot become a dangling `depends_on` edge.

**One real defect found by registering them.** `validate-facts.py`'s
`KERNEL_THEOREM_RE` rejected all 64: its allowlist contains `Str` (the carrier
type's short name, matching no declaration this kernel admits) and never
contained `axeyum.string.<N>`, the prelude's actual namespace. One narrow
alternative added and nothing else — `theorem_of` returns
`formal.kernel_theorem` verbatim when present, so no consumer changed. It
survived because the ledger registered zero string theorems: an allowlist is
only tested by the names someone tries.

**Mutation controls:** `mutation_controls.py kernel-facts`, 13 guards over 32
tests, baseline green, 13 killed. Eleven kill exactly one; two (`[[:space:]]`
anchor, `grep -c`) kill four because `ALLOWED_CHECKER_SHAPES` is the audit half
of the same contract the emitter implements — recorded in the registration
comments rather than papered over. Two tests run `/usr/bin/grep` against the
emitted pattern rather than asserting its text.

**Recommendation on the ratchet: yes, on TWO numbers.** A single coverage
ratchet creates exactly the incentive to generate junk to clear it. Ratchet
`registered` (any provenance) and `curated` (provenance not
`generated-unreviewed`) separately, so generating moves the first and not the
second and bulk generation cannot masquerade as curation. The `curated` counter
needs a small addition to `gen-ledger-coverage.py` — out of this lane's scope,
recorded in ADR-0607 as the follow-up.

**Next.** Run the generator on `nat` (243 unregistered) and `creal` (237) once
the ratchet decision lands; enrich the 64 generated string facts and flip their
`curation` markers; add the `curated` counter to `gen-ledger-coverage.py`.

Full write-up: [`docs/autogenesis/298-mechanical-fact-registration.md`](../../autogenesis/298-mechanical-fact-registration.md).
Decision: [ADR-0607](../../research/09-decisions/adr-0607-generated-facts-declare-themselves-and-coverage-ratchets-on-two-numbers.md).
