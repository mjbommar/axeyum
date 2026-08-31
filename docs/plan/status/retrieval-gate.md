# retrieval-gate — give retrieval a harness and a gate that can fail

<!-- plan-section: lane-status -->

**Status: DONE.** The gap was an **unadopted tool, not a missing one** — twice
over. No new script was written. Full reasoning, method and verification:
[ADR-1170](../../research/09-decisions/adr-1170-the-retrieval-gate-existed-and-ran-nowhere.md).

## The re-measurement, with its method

`/usr/bin/grep -l` (GNU grep, not the interactive `ugrep` wrapper) over the
**429** files in `docs/plan/status/*.md`, with a positive control in the same
sweep so an empty answer could not read as a negative result:

| pattern | files | share |
| --- | --- | --- |
| `shape_search` (`grep -lF`) | 30 | **7.0%** |
| `mutation`/`mutant` (`grep -lE`) | 180 | **42.0%** |
| `brief-step0` (`grep -lF`) | 10 | **2.3%** |
| `cargo` — control (`grep -lF`) | 238 | 55.5% |

Reproduces the brief exactly, and ADR-1165's 4.8% / 46% over its 272-document
subset: different denominator, same ratio. Case-insensitive `mutation|mutant`
gives 196, not 180 — the brief's figure is the case-sensitive one.

## Missing tool, or unadopted tool?

**Unadopted, both halves.**

- **Harness:** `scripts/brief-step0.py` / `just brief` (1,181 lines, landed
  2026-08-29). It runs the `shape_search` query for you and adds what the raw
  query cannot — an environment check by rendered *type*, both prelude paths
  for a shared module basename, held-out/mutation-control/divergence screens —
  and self-reports its two failure modes (exit 3 control probe failed, exit 4
  stale snapshot). Verified running: `--self-check` reports `control probe OK`,
  320 module basenames, 65 shared across directories. It is named in the
  `justfile` and in `check.sh`'s controls step, and **nowhere in CLAUDE.md's
  retrieval section** — the passage every lane and brief-writer reads about
  precisely this problem.
- **Gate:** `scripts/check-shape-duplicates.py` (282 lines, 2026-08-27).
  Complete, bidirectional, unit-tested — and **named by no gate at all.**
  `check.sh:347` registered `scripts.tests.test_check_shape_duplicates`, its
  unit tests. Zero references to the checker in `local-ci.sh`, `ci.yml`,
  `hooks/pre-push` or the `justfile`. Guards tested every run, subject never
  examined.

## What the gate found the first time it was ever run

Against a **freshly built** index (2,623 declarations; the shared checkout's
prebuilt binary was four hours stale at 2,577 and was not used):
**five unadjudicated duplicate groups** accumulated in the four days since the
last hand run. Read at their declaration sites:

- Four are deliberate Mathlib-name aliases whose bodies already forward —
  `Nat.dvd_of_dvd_mul_left`→`gauss_lemma`,
  `Nat.coprime_dvd_left`→`coprime_of_dvd_left`, and both
  `log`/`clog` `_monotone`→`_mono_right` (Mathlib states these as
  `Monotone (log b)`, and `Monotone f` is Mathlib's own name for the pointwise
  form). Allowlisted with that reason.
- **One is a real independent re-derivation.** `Rat.int_right_distrib`
  (`rat_prelude/laws.rs`) and `Int.add_mul` (`int_prelude/add_basics.rs`) state
  right-distributivity over `Int` and ran the *same* `mul_comm`-thrice-plus-
  `left_distrib` chain in two preludes under two names. Fixed: the Rat-side
  name stays (20 call sites) and its body is now `d.lemma(int.add_mul, …)`.
  One proof term, two names.

## What landed

- `crates/axeyum-lean-kernel/src/rat_prelude/laws.rs` — the dedup fix.
  Verified `cargo test -p axeyum-lean-kernel --lib rat_prelude::`, **151
  passed, 0 failed**, 376 s. Statement unchanged, so no downstream prelude is
  affected.
- `scripts/shape-duplicates-allowlist.json` — five adjudications, each with a
  reason, a date and a source.
- `scripts/local-ci.sh`, `.github/workflows/ci.yml` (in `l0-trust-closure`,
  the only job already doing a `--release` kernel build), `scripts/check.sh` —
  the checker wired, matching each file's own idiom.
- `scripts/check-l0-gate-enforcement.py` — `check-shape-duplicates` added to
  `L0_GATES`, seven → eight, so the wiring cannot drift back out.
  `verdict=PASS | gates=8 | local_ci_gates=8`; `--self-test` 9 cases 0
  failures; `test_l0_gate_enforcement` 15/15.
- `scripts/tests/test_check_shape_duplicates.py` — the exact-length pin (10)
  replaced by a floor plus per-entry `reason`/`source`/`adjudicated` structure.
  The pin measured nothing the gate does not, and broke on the first
  legitimate adjudication.
- `CLAUDE.md` — the retrieval section now names `just brief`, says the step
  belongs to the brief-writer rather than the lane, carries the re-measured
  numbers, and states the coverage limit below.

## Break/restore proof

Through the **real** `cargo run --release --example shape_search --duplicates`
path against the real environment, via `--allowlist` so no tracked file was
mutated:

| subject | result |
| --- | --- |
| committed allowlist | exit **0**, `OK: 15 duplicate group(s), all allowlisted with a reason.` |
| one adjudicated entry dropped | exit **1**, `NEW/UNADJUDICATED … Int.add_mul Rat.int_right_distrib` |
| entry added naming a group nothing reports | exit **1**, `STALE Nat.no_such_lemma_a Nat.no_such_lemma_b` |

Stronger than any of those: the gate's first run on its true subject exited 1
and named five real groups, one a real defect.

## What the gate does NOT cover

Stated because a gate implying coverage it lacks is worse than no gate.

- **Hiding place 2 is structurally out of reach.** A reusable step built
  *inline* inside a bigger declaration has no declaration, therefore no type,
  therefore cannot appear in a duplicate group. No name- or type-based tool can
  ever see one re-derived.
- **It is a lagging indicator.** A lane that spends four hours re-deriving a
  lemma and then finds it has cost the four hours and left no duplicate to
  catch. The harness half addresses that; its effect is not yet measurable.
- **It says nothing about the 7.0%.** Deliberately — a gate asserting that lane
  documents *mention* `shape_search` is satisfied by typing the word.

## Corrections to the brief

- The brief said `shape_search` appears "once in `check.sh`, twice in the
  `justfile`". Accurate, and the once is the **unit tests**, not the checker —
  which is the finding, and the brief's own framing ("retrieval has neither
  [a harness nor a gate]") understates it: it has both, unreached.
- The brief's mutation figure of 180 is case-sensitive; case-insensitive is
  196. Neither changes the conclusion.
