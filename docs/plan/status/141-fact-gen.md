# Lane: fact-gen — making mechanical fact registration mechanical

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, fact-gen, 2026-08-27).** Built
`scripts/gen-kernel-facts.py`: ledger-schema facts emitted for already-proved
`kernel-lean` theorems, deriving every formulaic field from
`kernel_declaration_projection`'s unfiltered eight-field emit and **refusing**
the rest. The join ("which theorem is this fact about") is imported from
`gen-ledger-coverage.py`, which imports `theorem_of` from
`check-fact-depends-derived.py` — three consumers, one definition, no fourth
copy to diverge. Registered `--audit` in `scripts/check.sh` and `justfile`
beside the existing `gen-ledger-coverage --check` step.

**Headline: the string prelude, 0/64 → 64/64, and overall coverage
474/1,397 (34%) → 538/1,397 (38.5%).** 64 planned, **0 declined**;
`validate-facts.py` green at 882 facts / 0 errors. `string` was
[297](../../autogenesis/297-ledger-coverage-gate.md)'s only genuine zero and
is now the only prelude at full coverage.

**Every emitted checker was executed, not assumed: 128 commands, 0 failed** —
all 64 facts × 2 evidence rows, not a sample. And shown able to FAIL, which is
the part that matters for a bulk generator. In an isolated snapshot
(`scripts/lane-snapshot.sh`, never the shared checkout), renaming
`append_assoc`'s interned name and rebuilding gave `count=0 exit=1` for its
generated checker, `count=1 exit=0` for `append_nil` in the **same run against
the same binary**, and `count=1 exit=0` for `append_assoc_MUTANT` — so the
failure is the *name*, not a broken build or a lost proof. Footprint side:
`--require-axiom-free string` exits 0, `axreal` (30 axioms) exits 1, a prelude
the run never built exits 1.

**The honesty design, and what it refuses (ADR-0606).** Generated prose is held
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
recorded in ADR-0606 as the follow-up.

**Next.** Run the generator on `nat` (243 unregistered) and `creal` (237) once
the ratchet decision lands; enrich the 64 generated string facts and flip their
`curation` markers; add the `curated` counter to `gen-ledger-coverage.py`.

Full write-up: [`docs/autogenesis/298-mechanical-fact-registration.md`](../../autogenesis/298-mechanical-fact-registration.md).
Decision: [ADR-0606](../../research/09-decisions/adr-0606-generated-facts-declare-themselves-and-coverage-ratchets-on-two-numbers.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | fact-gen | `scripts/gen-kernel-facts.py` + 32-test suite + `mutation_controls.py kernel-facts` (13 guards); 64 generated `string` facts (0/64 → 64/64); ledger coverage 34% → 38.5%; ADR-0606; one `KERNEL_THEOREM_RE` alternative in `validate-facts.py` |
