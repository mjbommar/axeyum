# ADR-0652: one producer per key — a generated artifact has exactly one writer

Status: accepted
Date: 2026-08-30
Index-summary: The statable vocabulary had two writers and the poorer one deleted `bridge_provenance` and `row_digest` at exit 0 while its own `--check` advised exactly that; the refill generator now READS the artifact and cross-checks it, and `check-generated-artifact-ownership.py` runs every non-owner producer in a sandbox and requires byte-identity, with a planted second writer as its own positive control

Related: ADR-0624 (the vocabulary is generated, not maintained), ADR-0631
(bridge provenance is the published per-constant classification), ADR-0645
(draw 6 declined; the lane that found this), ADR-0542 (held-out isolation)

Lane: vocab-two-writers

## Context

`artifacts/autogenesis/mathlib-statable-vocabulary-v1.json` had **two**
writers.

- `scripts/gen-autogenesis-statable-vocabulary.py` — the generator ADR-0624
  introduced. It emits `bridge_provenance` (the per-constant
  `elaboration`/`expressed`/`elided`/`unrendered` classification of ADR-0631)
  and `row_digest`, plus the four `bridge_*` tier counts inside `coverage`.
- `scripts/gen-autogenesis-nursery-refill.py` — which built its own copy of
  the same document from a different source and wrote it over the top.

Reproduced at `main` in a scratch tree extracted with `git archive`:

    BEFORE  sha 096d8c85…  keys [bridge, bridge_provenance, coverage,
                                 derivation, environment_snapshot, keyed_by,
                                 kind, row_digest, schema_version, settled,
                                 source]
    $ python3 scripts/gen-autogenesis-nursery-refill.py     -> exit 0
    AFTER   sha 27205641…  keys [bridge, coverage, derivation,
                                 environment_snapshot, keyed_by, kind,
                                 schema_version, settled, source]
    LOST    bridge_provenance, row_digest

Exit 0. No warning. And `gen-autogenesis-nursery-refill.py --check` had been
**RED on `main` since 04:23 that day** with

    autogenesis-nursery-refill: 1 generated file(s) are stale, first
    artifacts/autogenesis/mathlib-statable-vocabulary-v1.json;
    regenerate without --check

whose only effect on that file is the deletion. So the failing gate's advice
was the defect. A lane authoring a nursery draw — which runs that generator by
design — would have reverted `edd775b19` inside a commit that looks like a
draw, and the routine repair does not help: the owning generator then reports
`UNCHANGED`, because from its own point of view nothing needs writing.

The `nursery-draw-6` lane found this and correctly declined to run the
generator (ADR-0645).

**Why `--check` was red is worth stating plainly, because "the staleness might
be benign" was a live possibility and it is not the answer.** The staleness is
real and it is *entirely* the second writer: measured, the two producers agree
**element for element** on `bridge` (72 entries) and `settled` (174 rows) — the
whole substantive derivation. The refill generator's document is a strict
SUBSET, missing `bridge_provenance`, `row_digest`, the four `bridge_*` coverage
counts, and carrying a shorter `derivation` string. The two never disagreed
about the mathematics; one of them simply knew less.

This is the repository's shared-append-point failure — the one CLAUDE.md
records for `PLAN.md` and the ADR index, where the remedy was one owner and a
generated view — arriving in an artifact instead of a document.

## Decision

**1. The vocabulary generator owns the file. The refill generator reads it.**

`build_vocabulary` becomes `derive_vocabulary_content`, returning only the two
fields the refill script genuinely derives (`bridge`, `settled`) and none of
the metadata it used to fabricate. `read_vocabulary` loads the owned artifact
and **cross-checks** it against that derivation, raising rather than
overwriting when they disagree. `VOCABULARY` is gone from the script's
`outputs` map.

The cross-check is deliberate rather than incidental. What two writers bought
by accident was two independent derivations of the same content — the refill
script takes constants from the pinned inventory's `type_repr`, the owner from
`mathlib-statement-constants-v1.json`. That is worth keeping. What it must not
do is resolve a disagreement by writing.

Measured, both directions, in a scratch tree:

    fixed, real draw run (no --check)  -> sha 096d8c85… unchanged, 11 keys
    vocabulary perturbed by one entry  -> exit 1, names the owning generator
    refill --check                     -> exit 0, the red is cleared

**2. `scripts/check-generated-artifact-ownership.py` makes the shape
impossible to repeat silently.**

The specific collision is one instance. The gate is the durable part.

| arm | what it refuses |
| --- | --- |
| `KEYS` | the committed artifact missing any key its owner derives, top level or nested. Goes red the moment `bridge_provenance` disappears, whoever removed it. |
| `KNOWN` | a script whose text names a guarded artifact and is not classified — and a classification that no longer matches the tree. |
| `READS` | a script declared read-only that contains any write call (AST). |
| `RUNS` | a non-owner producer, **executed** in a sandboxed copy, that leaves the artifact anything but byte-identical. |
| `CTRL` | a RUNS arm that accepts a planted second writer. |
| `OWNER` | an owner that cannot restore a perturbed copy byte for byte. |

Three design points, each forced by something measured:

- **RUNS is empirical, not static, because the destroying write was**

      outputs = {VOCABULARY: render(vocabulary), EXTENSION: render(extension)}
      for path, text in outputs.items():
          path.write_text(text)

  The path constant reaches the write through a dict value. A receiver
  analysis for `VOCABULARY.write_text(...)` — the analysis anybody would
  actually write — sees nothing. Static analysis appears only in `READS`,
  where the question is decidable: a module containing no write call at all
  cannot write this one.

- **`KNOWN` derives its script set from the tree**, so a new writer turns the
  gate red instead of being unmeasured. This is the "any test named *every X*
  must derive its X from the authority" rule; a hand-maintained producer list
  would measure the maintainer's memory.

- **`CTRL` and `OWNER` run on every invocation and are not opt-in.** Four
  `RUNS ok` lines are equally consistent with a comparison that can no longer
  fail, and with a sandbox no script ever reached. Those two arms separate the
  three.

The gate classifies **itself** as a producer: it writes (a sandbox tree, a
perturbed copy, a planted control), so it cannot claim read-only, and "running
this does not rewrite the artifact" is worth measuring. A nested invocation
inherits `AXEYUM_ARTIFACT_OWNERSHIP_NESTED` and skips only itself, so it cannot
recurse.

## Consequences

Registered in **both** aggregate gates; `check-aggregate-scope.sh` is green
(410 / 466 steps, 66 recorded differences, no new one). Runs in ~10 s on this
host, 5 producers executed.

Controls: `scripts/tests/test_check_generated_artifact_ownership.py`, 18
cases, registered with the mutation harness as `artifact-ownership`. The
sweep is clean with **no survivors**:

    KEYS dropped top-level key         killed 1
    KEYS dropped nested tier count     killed 1
    KEYS non-object top level          killed 1
    KNOWN unclassified script          killed 1
    KNOWN stale classification         killed 1
    READS declared reader that writes  killed 1
    RUNS before/after comparison       killed 4
    RUNS producer DELETES artifact     killed 1
    CTRL inert RUNS arm                killed 1
    OWNER byte-for-byte restoration    killed 2

The two multi-kills are structure rather than weakness, and are recorded at
the registration site: `CTRL` is *defined* as "the RUNS machinery must reject
a planted second writer", so blinding the RUNS comparison necessarily blinds
`CTRL`; the same mutant also stops `compare_after_run` restoring the artifact
after a finding, which two further cases assert. A suite in which those died
separately would be testing two comparisons, and there is only one.

**The control suite found a real defect in the gate on its first run**, which
is the strongest thing this ADR can say for it. `SECOND_WRITER` — the planted
writer whose whole job is to prove `RUNS` can fail — dropped
`bridge_provenance` and `row_digest` **by name**. Against any artifact not
carrying those two keys it writes the file back byte-identical and is
accepted, so the control designed to prove the arm can fail would itself have
been a check that cannot. Harmless today with one guarded artifact; latent the
moment a second is registered, which is exactly when nobody would be looking.
It now drops `artifact.required_keys[-1]`, the artifact's own.

`KNOWN` also, correctly, flagged the control file itself, which named the
guarded artifact in a fixture string. The literal is built from parts there
now, with a comment saying why.

Gates run: holdout isolation
`held_out=116|files_scanned=1107|settled=0|references=0|PASS`, exit 0,
unchanged. No held-out row was read or written by any of this.

### What this does not do

The registry holds **one** artifact. Every other generated file under
`artifacts/` is unguarded, and adding one is a few lines — but each addition
must run its producers, so the cost is real and the list should grow by
demand rather than by sweep. `nursery-v2-extension.json` is the obvious next
candidate: it has one writer today, and nothing structural says so.
