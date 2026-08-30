# Lane 365 — gate survivors

<!-- plan-section: lane-status -->

## Status

**LANDED.** All five gates named in
[the 2026-08-30 session audit](../../research/11-design-review/2026-08-30-session-audit.md)
§5b now have controls that die when the guard dies. Every kill set below is as
measured by `scripts/tests/mutation_controls.py`, survivors included.

The standing rule this lane worked to: **a gate is not made green by making it
blind.** Two gates gained new failure modes (a ratchet, a scope assertion) and
both were driven to red on purpose before being recorded green.

### 1. `check-merge-hygiene.sh` — zero controls, and its exemption covered every control suite

It landed the same day with **no registered controls**, so every guard in it was
a survivor by definition. Ten scenarios now drive the shipped script against a
throwaway git tree (`AXEYUM_MERGE_HYGIENE_ROOT`, the `AXEYUM_KERNEL_SUITES_ROOT`
device); nothing is re-implemented.

Two defects fixed alongside, both reported by the audit:

- the conflict-marker pathspec excluded `scripts/tests/*` — **every control
  suite in the repository** — from the marker guard. Narrowed to
  `scripts/tests/fixtures/*`. Measured before narrowing: zero tracked files
  under `scripts/tests/` contain a marker, so it cost nothing. The new suite
  therefore *builds* its marker text from repeated characters rather than
  writing it literally, so it is scanned by the guard it tests.
- the header said "the four things" while the body gives a reasoned explanation
  for enforcing three.

| mutant | killed |
| --- | --- |
| M1 conflict-marker branch | 4 |
| M2 bare `=======` alternative | 1 |
| M3 `fixtures/` exemption, not the whole directory | 1 |
| M4 ADR-index branch | 3 |
| M5 the ADR checker's own output is reported | 1 |
| M6 `gen-plan` branch | 2 |

No survivors. M1/M4/M6 kill more than one because each is **one** `if` reached
by several scenarios; a suite in which they died separately would be testing
branches that do not exist.

### 2. `check-aggregate-scope.sh` — an untested failure path and a live phantom class

`if [ -s "$new" ]; then` → `if false; then` left the registered suite green
(`AGGREGATE_SCOPE_CONTROLS|guards=5|negative_controls=2|PASS`, exit 0), because
all five registered controls test the **normalizer**.

`test-check-aggregate-scope.sh` keeps that job. The new suite drives the gate
end to end on a synthetic tree via `AXEYUM_AGGREGATE_SCOPE_ROOT` — hermetic,
because the real tree costs 413 + 469 steps to enumerate and because the
zero-side refusal cannot be reached on it at all.

The phantom: `strip_wrappers` *tested* for a leading environment assignment with
a quote-aware regex and *stripped* it with `line.split(" ", 1)`, which cuts at
the first space — inside the quotes.

```
RUSTDOCFLAGS="-D warnings" cargo doc …   ->   warnings" cargo doc …
```

**Measured against every subject**, which is what separates a surgical fix from
a silent weakening: both step counts unchanged, divergence 66 → 64, and the diff
of the recorded sets is exactly that pair and nothing else.

| mutant | killed |
| --- | --- |
| A1 an unrecorded divergence fails | 3 |
| A2 zero-side refusal (exit 2) | 1 |
| A3 a missing expectation file | 1 |
| A4 the just-only `comm` arm | 2 |
| A5 a quoted assignment is matched | 3 |
| A6 the strip consumes what matched | 3 |

No survivors. Five of the thirteen tests are killed by no mutant and that is
their job — they are the positive controls, without which every scenario above
is satisfied by a gate that always fails.

### 3. `check-cas-substance.py` — derived is not defended ([ADR-0699](../../research/09-decisions/adr-0699-a-derived-count-is-not-a-defended-one.md))

The count *was* derived — all 12 mutants died and the number moved under
mutation — and a fact could still lose its kernel reconstruction, or vanish, with
the gate green and a quietly smaller headline.

The honest floor is the **set**, not the number: one ratchet row per fact that
reached kernel reconstruction, carrying the two properties this gate can verify
(shape **derived** from a committed certificate; shape **discriminating**).
Three refusals, all losses of established ground; growth is free and
strengthening is accepted. Plus `MIN_KERNEL_RECONSTRUCTED = 14`, because
deleting a fact *and* its row in one commit satisfies all three per-fact rules.

| mutant | killed |
| --- | --- |
| R0 a missing ratchet file | 1 |
| R0b a trimmed ratchet vs the floor | 1 |
| R0c a fallen ledger vs the floor | 1 |
| R1 a fact no longer reconstructed | 2 |
| R2 a derived shape gone self-reported | 1 |
| R3 a discriminating shape gone weak | 1 |
| R4 the ratchet is consulted at all | 4 |

R0 and R0c **survived the first run** and were closed by building the scenario
that isolates each, not by excusing them. The audit's own scenario now exits 1.

### 4. `check-generated-artifact-ownership.py` — correct as designed, with no denominator

The audit did not say this gate is wrong, and it is not. Every arm derives what
it needs from the tree. What it could not answer is one level up: `GUARDED` was a
literal of length one reported as `artifacts=1`.

New COVER arm: an artifact named by ≥2 `scripts/gen-*.py` producers must be
GUARDED or recorded in `check-generated-artifact-ownership.candidates`. The
summary now reads `guarded=1|multi_writer_candidates=33`.

**This does not guard 33 artifacts, and does not claim to.** The RUNS guarantee
comes from executing each writer in a sandbox; a static write-call scan cannot
say which file a script writes, and `nursery-v1.json` alone is named by 45
scripts.

**What would make the one-owner guarantee real** (the audit asked, and this is
the open item): a **second** artifact in `GUARDED` whose producers run in the
sandbox. With one entry, CTRL tests one comparison against one file — the
registering lane already found its planted writer vacuous against any other
artifact. It needs a candidate whose producers are sandbox-runnable without the
kernel, and that selection is the work.

Six new mutants, killed 1/1/1/2/2/2. One **survived** in its first form — it gave
a parameter a default, which is behaviour-neutral — and was replaced with a real
guard deletion rather than excused.

### 5. `check-shell-antipatterns.sh` — correct and under-scoped, and both hooks violated

The scan set was `git ls-files '*.sh'`, so the two tracked shell scripts without
that extension were never read, and **both violated** — including
`hooks/pre-push:249`, the nonzero-test-count guard this repository leans on
hardest, built from the exact idiom that reads a SIGPIPE as "no match". Both are
fail-closed and both are fixed to `grep -c` plus a count test. `hooks/` gates
every push, so "out of scope" was a defect in the scope.

The scan set is now derived from the index mode plus a shebang probe: 116 → 118
files, with **every other number byte-identical**
(`files=7|grep_q_in_pipeline=14|pipeline_status_reads=0`). Seven mutants, all
killed; two were added after the first run showed two tests no mutant could
reach.

**Deliberately not added:** a detector for `cmd 2>&1 > file`, which the audit
named as undetected. The tree's only occurrence is the *correct* idiom for "pipe
stderr only", so a blanket pattern would report it as a bug. The distinction is
authorial intent; a detector would be a false-positive generator, and this gate
has already sat red on one.

## Landed changes

| commit | what |
| --- | --- |
| `gate(merge-hygiene)` | 10 controls, 6 mutants; `scripts/tests/` no longer exempt |
| `gate(shell-antipatterns)` | `hooks/` scanned; both hook violations fixed; 9 controls, 7 mutants |
| `gate(aggregate-scope)` | failure-path controls; quote-blind normalizer fixed, 66 → 64 |
| `gate(cas-substance)` | per-fact ratchet + absolute floor; ADR-0699; 7 new mutants |
| `gate(artifact-ownership)` | COVER arm derives the denominator; 6 new mutants |

## Next

- Guard a **second** artifact in `check-generated-artifact-ownership.py`, which
  is what turns the one-owner guarantee from "this comparison works" into "this
  comparison works for artifacts in general". Pick from
  `scripts/check-generated-artifact-ownership.candidates`; the constraint is
  producers that run in a sandbox without the kernel.
- Have the 8 self-reported `cas_substance` shapes emit certificates, so ADR-0622
  rule 3 covers them. The ratchet pins that 6 of 14 are derived today and
  refuses that number falling; it cannot raise it.
