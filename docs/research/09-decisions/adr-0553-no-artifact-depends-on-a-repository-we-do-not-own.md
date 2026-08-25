# ADR-0553: No artifact depends on a repository we do not own

Status: accepted
Date: 2026-08-24
Index-summary: `../math-education` is reference-only; the data coupling to it is removed and gated

> **On the number.** `gen-adr-index.py --check-remote` reported `next_free=0546`
> against a remote-tracking ref of unknown age, and 0546 was being written by a
> concurrent lane at the time. 0546–0552 are left for lanes in flight rather
> than risking the collision this gate exists to catch. The gap is deliberate.

## Context

The project owner's constraint on the sibling repository `../math-education` is
that it is **reference only**: something to read for calibration, never
something this project depends on, integrates with, or points at in its data.

The constraint was stated and never gated. Measured 2026-08-24, it had been
violated in five places at once, and **no existing gate could see any of them**.
Every validator involved exited 0.

| where | what |
|---|---|
| `knowledge-overlay-v1.json` | a source of `kind: external-repository`, `path_hint: ../math-education`, pinned to `ce3e2a52e7`; a namespace with `resolution: external-pinned`; **24 of 33 links** with an endpoint in it, each carrying that SHA as `source_revision`, several naming `../math-education/graph/...` files in `provenance.sources` |
| `family-concept-crosswalk-v1.json` | `path_hint: ../math-education/graph/concepts` and the same pin — which its validator hardcoded as a constant and **required** the file to match |
| `tactic-catalog.schema.json` | `uses_technique` is **required on every tactic** and required `source: {const: "math-education"}` plus a 40-hex `revision` |
| `artifacts/claims/**` | **all 104** carried `provenance.graph_pin` (the same SHA), 438 `concept_refs[].resolved: true` asserting resolution against it, and 60 notes saying so in prose. `claim.schema.json` made `concept_refs` required and `graph` a one-value enum |
| `python/axeyum/knowledge/math_education.py` | 777 lines opening `DEFAULT_PATH_HINT = Path("..") / "math-education"`; resolved that path, ran `git rev-parse HEAD` against it, parsed its YAML, and `agent/web.py` put the resulting `file://` prefix **into the agent's fetch allowlist** |

Four validators reached outside the checkout in code —
`validate-autogenesis-knowledge.py`, `validate-tactic-catalog.py`,
`validate-claims.py`, and `check-reachability-census.py`, the last defaulting to
`~/projects/personal/math-education/graph`, an absolute path into one machine's
home directory in a tracked file.

## Decision

**No artifact in this repository may declare a dependency on a repository this
project does not own, and `scripts/check-external-coupling.py` refuses one.**

The distinction the whole change turns on:

> A **citation** names a source. A **dependency** tells you where to find it and
> which version to use.

Only the second is a coupling. A `C:factorial` label, a `TQ:` id, a prose
paragraph discussing the sibling — all fine, all kept. A `path_hint`, a
`resolution: external-pinned`, a pinned foreign revision, a `resolved: true`
that can only be evaluated against a checkout — all removed.

### What was removed

- The overlay's `math-education` source, namespace, and 24 links (19
  `formalizes`, 3 `exemplifies`, 2 `uses-technique`), plus the three relation
  types left with no reachable target. Nine links survive.
- The crosswalk's `path_hint` and `revision`.
- `uses_technique.source` and `.revision` from the tactic schema and its 9 rows.
- `provenance.graph_pin` and `concept_refs[].resolved` from all 104 claims and
  from `claim.schema.json`; the `graph` enum is now a free label.
- The 777-line Python module, its 279-line test suite, `sibling_prefix()`, and
  the `file://` branch of the agent's URL classifier.
- Every outward-reaching path expression in `scripts/`.

The **schemas** were tightened too, not just the data. The overlay schema still
offered `external-repository`, `external-artifact`, `external-pinned` and
endpoint `source_revision` after its data was clean; `path_hint` now refuses `..`
and absolute paths by pattern. A schema that offers the vocabulary is an
invitation, and the next lane takes it.

## Alternatives

**Internalize the 24 edges** — declare local `C:factorial`-style concept
entities and repoint. Rejected. It keeps the edges' shape and moves their
semantics nowhere: an axeyum-local `C:factorial` would mean "whatever the
sibling means", with nobody here to adjudicate it. That is the coupling
laundered through a rename — it would pass the new gate while the authority
still lived elsewhere. This repository's documented failure mode is building
projection artifacts that grant no authority and move no metric
(`docs/autogenesis/228-capsule-lane-retrospective.md`), and minting 16 concept
entities to save 24 edges is precisely that.

**Drop the edges and say nothing more.** Rejected as incomplete: it leaves the
next lane free to re-add them, which is how this happened.

**Drop the edges and record the prerequisite** — taken. **A concept vocabulary
this repository owns and can adjudicate is a prerequisite for ever re-adding a
`formalizes` edge.** Not a nice-to-have and not a follow-up ticket: without it
there is nothing here for a fact to formalize, and the relation cannot mean
anything. Three guards went with `formalizes` (single-edge partial coverage, the
kernel source must be a theorem, its axiom footprint must be empty); **they must
return with it.**

## Evidence

### The gate

Four rules, each naming a *mechanism* rather than a repository, so a different
sibling is caught too:

- **R1** — the external-declaration vocabulary as a value anywhere, including
  inside a schema `enum` or `const`.
- **R2** — any `..` path **segment** in any string value. The overlay hid 24 of
  these in `provenance.sources`, a list of free-form strings; a rule inspecting
  only path-shaped *keys* would have missed every one.
- **R3** — a 40-hex revision under a key not in `REVISION_KEYS`, which names the
  repository each of the 36 keys pins. This does **not** forbid a foreign pin:
  Mathlib, the Lean toolchain and lean4export are pinned on purpose and the
  `imported-kernel-lean` route depends on it. It forbids an **undeclared** one.
- **R4** — source that builds a path out of the checkout, over `scripts/*.py`,
  `python/**/*.py` and `tools/**/*.py`.

Measured over 1,885 artifacts and 159,474 strings: `findings=0` on this tree.

**Positive control.** Pointed at the four real pre-change artifacts read from
`56eaab2cc`, the gate produces **64 findings** — R1 2, R2 26, R3 36 — naming
`graph_pin`, `path_hint`, `external-repository` and `external-pinned`
individually. R4 restored the deleted 777-line module and fired on its first
constant. Both are permanent controls.

**`--self-test`** drives every rule over a synthetic violation and fails if any
rule does *not* fire; it runs **before** the scan in both aggregates, so the
zero the scan prints is a measurement rather than a no-op.

**Vacuity.** Zero artifacts scanned, zero strings examined, or zero source files
scanned each FAIL. They are three separate guards because they fail for three
different reasons.

**Mutation.** 8 guards, 25 tests, **each guard killed by exactly one test**
(`scripts/tests/mutation_controls.py external-coupling`).

### What R3's registry does not do

It does **not** verify attribution with `git cat-file`. Measured the same day,
`detached_transition_commit`, `reconstructed_replay_commit`,
`pre_a_state_commit` and `reconstructed_prestate_commit` all report "not a
commit" in this checkout while being ordinary commits of *this* repository, made
in detached scratch worktrees and never pushed. A verifier calling those foreign
would be wrong in the direction that matters, and it would have looked
authoritative doing it.

### Deliberately not covered, measured rather than assumed

- **Absolute paths.** There are **1,174** in `artifacts/**` —
  `/nas3/data/axeyum/autogenesis/reference-packs/...`,
  `/home/mjbommar/lean-import-scale/mathlib4`, `/home/mjbommar/.elan/...`. Each
  records *where a measurement physically ran*: provenance, not a dependency
  declaration, and the artifact stays checkable when the path is gone.
  Forbidding them is a real and separate policy question with a 1,174-row blast
  radius; conflating it with this one would have made the gate unlandable. The
  single `~`-rooted value (`lean_binary`) is the same category. **This is the
  largest gap.**
- **A bare `"../"` string in source.** `scripts/` alone has 13, every one a
  relative markdown link or an upstream Lean case id. Likewise `.parent.parent`,
  which is how a dozen scripts compute the repository root. Both would bury real
  findings in noise, and a rule nobody can keep green gets deleted.
- **Prose.** A document may name, cite and discuss the sibling. That is the
  behaviour the owner asked for.
- **`scripts/tests/` and `python/tests/`.** A control that pins this removal has
  to *name* what it forbids, and a hermetic fixture legitimately builds a
  stand-in external root under `tempfile`. Both trip R4. The cost is that a test
  helper could reintroduce an escape unseen; the benefit is that the controls
  enforcing this rule can exist at all.

## Consequences

**Two downstream artifacts went structurally empty, and were reduced rather than
left reporting zero.** `concept-coverage-projection-v1.json` and the generated
knowledge-coverage census both derived their headline numbers from `formalizes`
links. With those gone the numbers could not be anything but zero, and the
projection validator's strongest check had degenerated to comparing two empty
sets — a check that cannot fail, shipped while removing a coupling. So:

- the projection keeps only `family_topic_*` (9 concepts, 157 facts, checked
  against the crosswalk) and **refuses the removed fields by name**;
- the census keeps only the operation population (2 operations, 9 applicable, 7
  credited) and **names** the ten removed rows instead of printing them as zero.
  A row pinned at zero reads as a measurement and is not one.

**Two suites were skipping their strongest controls.** `test_validate_tactic_catalog.py`
and `test_check_reachability_census.py` both `skipTest`-ed whenever the sibling
was absent — which, after this change, is always. Both are now hermetic.

**The historical controls do not run under the mutation harness.**
`mutation_controls.py` copies the tree with `ignore_patterns(".git", ...)`, so
the `git show`-based positive controls skip there. This is stated in the suite
rather than left to be discovered, and it is safe *only* because every guard has
its own hermetic control — the skip costs evidence, not coverage. A meta-test
fails if the base commit ever leaves history, so "skipped everywhere" cannot
quietly become the steady state.

**Citation stays legal, and a later reader must not mistake it for a
dependency.** Facts and claims still carry `{graph, ref, relation}` labels
naming that corpus; documents still cite its measurements. Any ADR that cites a
math-education measurement as justification should say explicitly that it is a
citation and creates no dependency — the citation is welcome, the ambiguity is
not.

**Wired into both aggregates.** `scripts/check.sh` 276 → 279 steps, `just check`
327 → 330; one-sided steps unchanged at 121, so `check-aggregate-scope.sh` sees
no new divergence.
