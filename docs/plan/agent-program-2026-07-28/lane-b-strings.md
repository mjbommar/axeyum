# Lane B — Strings (the volume gap)

**Ranked-program anchor:** Rank 2 — *the largest single decide-rate lever by
benchmark volume.*
**Phases:** [P2.7 Strings](../track-2-theories/P2.7-strings.md) +
[`P2.7-strings/`](../track-2-theories/P2.7-strings/), P2.7a.
**Worktree / branch:** `~/projects/personal/axeyum-strings` / `agent/strings/qf-slia-breadth`.
**Owns:** `crates/axeyum-strings/`, string tests, the **string regions** of
`crates/axeyum-smtlib/src/parse.rs`.
**Blocks on:** Phase 0 (T0.1 lands 1,845 lines into `parse.rs`).

---

## The situation: strings are *not* done, they are *unmeasured*

QF_SLIA (84,395) + QF_S (18,940) ≈ **103k benchmarks, ~24 % of the library.**

Two different pictures exist right now, and reconciling them is task B1:

| Population | Decided | Source |
|---|---|---|
| Noetzli fixed, 1,880 files | **1,880 / 1,880 = 100 %** | lane report, lands via Phase 0 T0.1 |
| PyEx fixed selection, 2,535 files | **1,730 / 2,535 ≈ 68 %** | STATUS 2026-07-26 |
| PyEx paired residual, 956 files | 109 / 956 | STATUS 2026-07-26 |
| **QF_SLIA cvc5-regress (SCOREBOARD, authoritative)** | **18 / 50 = 36 %** | SCOREBOARD |
| **QF_S cvc5-regress (SCOREBOARD, authoritative)** | **87 / 134 = 65 %** | SCOREBOARD |
| QF_SEQ cvc5-regress | 26 / 33 = 79 % | SCOREBOARD |

The SCOREBOARD rows have **not been re-measured since the Noetzli and PyEx
mechanisms landed.** They may be badly stale — or the mechanisms may be
population-specific and not generalize. Both outcomes are important and neither
is currently known. Everything else in this lane is downstream of finding out.

Known deferred capability gaps (from the SCOREBOARD attribution notes and P2.7):
- **Concat emptiness (`unsat`)** is deferred — the `str.in_re`-over-`str.++`
  work is a **sat-side** slice; unsat concat rows stay `unknown`.
- **Unbounded `str.len` unsat** — the bounded-unsat gate (ADR-0052) does not
  cover the unbounded case.
- **Extended `str.*` / sequence coupling** and the **Nielsen transform**
  (ADR-0025/0029/0052/0053/0054/0061).

---

## B1 — Re-measure the authoritative rows (W1, do this first)

**Goal.** Regenerate the QF_SLIA, QF_S, and QF_SEQ SCOREBOARD rows from a
release build off the post-Phase-0 `main`, and publish the delta.

**Steps**
1. Build release off `main` after T0.1 lands.
2. Re-run the three curated cvc5-regress slices with the same command and
   budgets the committed baselines used (read the baseline JSON headers under
   `bench-results/baselines/` — do **not** invent new budgets, or the row is not
   comparable).
3. `python3 scripts/gen-scoreboard.py` and commit the regenerated SCOREBOARD.
4. `python3 scripts/check-parity-docs.py` — this gate rejects stale prose
   claims; fix any it flags in `PLAN.md`/`STATUS.md`.
5. Write the delta up: which rows moved, which mechanisms carried, which did
   not, and — critically — **which Noetzli/PyEx mechanisms failed to generalize**.

**Exit criteria**
- SCOREBOARD regenerated and committed, DISAGREE still 0 on all three rows.
- `check-parity-docs.py` green.
- A committed note naming the residual shapes in each row's non-decisions
  (the input to B2/B3).

**Size:** S–M. **This is the highest-value single task in the lane** — it either
banks a large measured gain or tells us the mechanisms are overfit to Noetzli.

---

## B2 — Concat emptiness: the UNSAT direction

**Goal.** Certify emptiness for membership-over-concatenation, closing the
explicitly deferred unsat side.

**Current state.** The parser rewrites `(str.in_re (str.++ p…) R)` into
`w ∈ R ∧ w = p…` with a fresh operand, and the sat branch witnesses each
membership class, pins the witness as a word equation, and re-solves the
augmented word system. `sat` is gated on mandatory `Seq`-level model replay
against the skeleton, so no wrong `sat` is possible even when the shape
heuristic is imprecise. **The unsat direction has no such route** — an
undecomposable shape stays `unknown`.

**Approach sketch.** The refutation needs the intersection `R ∩ shape` to be
provably empty where `shape` is built from the parts' witnessed languages. That
is a regular-language emptiness check over a product construction — decidable,
but it needs (a) a deterministic size bound on the product and (b) an
independently checkable emptiness certificate, or an explicit ledgered trust
note under P3.0.

**Exit criteria**
- A named set of previously-`unknown` concat rows decides `unsat`, each
  confirmed by Z3 **and** cvc5.
- The emptiness argument is either independently rechecked in-tree or ledgered
  as a trust note with an ADR.
- The membership differential fuzz is extended with an unsat-direction seed
  class (it currently emits `str.in_re` over `str.++`-of-variables for the sat
  side); ≥700 generated scripts vs both Z3 and cvc5, DISAGREE = 0.
- Zero retained loss on the Noetzli, PyEx, and cvc5-regress populations.

**Size:** L. **ADR required.**

---

## B3 — Unbounded `str.len` UNSAT / length coupling

**Goal.** Refute length-coupled string constraints without a length bound.

**Prereq:** BV+LIA combination (P1.6, landed conjunctive) — the `len`↔LIA link
is ADR-0052. Confirm the link is live on the CDCL(T) spine before building on it.

**Exit criteria:** a measured decide-rate delta on B1's length bucket; every new
`unsat` carries a checked certificate or an explicit trust note; zero retained
loss.

**Size:** L.

---

## B4 — Nielsen transform for word equations

**Goal.** The general word-equation decision procedure (ADR-0025/0029/0053/0054/
0061), replacing shape heuristics for the cases they cannot decompose.

**Bounds:** Nielsen is exponential in the worst case. It ships with an explicit
deterministic step/size cap that degrades to `Unknown` — bound first, feature
second.

**Exit criteria:** decides a named set of previously-`unknown` word-equation
rows; deterministic; bounded; zero retained loss; cross-checked both directions.

**Size:** XL. Do not start before B1 and at least one of B2/B3 have landed.

---

## B5 — Extended `str.*` and sequence coupling breadth

**Goal.** Close the remaining unsupported operator surface driving the
`unsupported` counts (QF_SLIA has 28 unsupported of 50 files; QF_S has 41 of
134 — those are *breadth*, not *hardness*, and are usually the cheapest points
on the board).

**Steps**
1. From B1's census, list every operator/shape that produced `unsupported`
   rather than `unknown`, ranked by row count.
2. Take them cheapest-first — the "cheap encoding before proof investment"
   advice from [`decide-rate-frontier-2026-06-28.md`](../decide-rate-frontier-2026-06-28.md) §2.

**Hard rule reminder — this lane has already been burned twice.**
- Every underspecified string operator (`str.at` out-of-range, `str.to_code` of
  non-singletons, `str.substr` with negative or overlong indices, …) needs a
  fuzz seed class that *deliberately emits the degenerate case*.
- String fuzz **generators** must cover the full SMT-LIB literal grammar,
  including `\u{…}` / `\uXXXX` escapes and code points above `0xFF`. Every
  generator once omitted escapes and a wrong-verdict class hid for weeks
  (`ba0d9149`).
- `cargo test -p axeyum-solver --test corpus_regression` is a **pre-merge gate**
  for any string-route change (~6 s). It caught a vacuous-sat harness hole that
  two oracle fuzzes missed (`f5b00c72`).

**Exit criteria:** the `unsupported` count on the QF_SLIA and QF_S rows drops
with DISAGREE = 0; each new operator has its degenerate-argument fuzz class.

**Size:** M, incremental — good task to run continuously alongside B2–B4.

---

## Lane B rolling exit (the Rank 2 exit criterion)

> QF_SLIA/QF_S decide-rate on the s4 selection ≥ (measured cvc5 baseline − 10
> points), DISAGREE = 0.

Note the exit is stated against the **s4 selection**, which Lane D produces.
Until Lane D's credited run reaches strings, B1's curated-row re-measurement is
the operative proxy.

### What SMT-COMP 2025 says about this target

From [`smtcomp-2025-parity-targets-2026-07-28.md`](../smtcomp-2025-parity-targets-2026-07-28.md):

| Division | 2025 winner | Solved | % | cvc5 |
|---|---|---:|---:|---|
| QF_SLIA | Z3-Noodler-Mocha | 23,626 / 23,730 | **99.6 %** | 4th, 21,585 (91.0 %) |
| QF_S | Z3-Noodler-Mocha | 10,414 / 10,428 | **99.9 %** | 4th, 9,016 (86.5 %) |

**Strings at the top are effectively saturated.** Parity here means ~100 %, not
"competitive" — the exit criterion's "cvc5 baseline − 10 points" is a *much*
weaker bar than the state of the art, because cvc5 is only 4th in both
divisions. State which bar a result clears; do not let the cvc5-relative exit
imply we are near the frontier.

Two further notes: the QF_S population **grew 17.6 %** (8,867 → 10,428) between
2024 and 2025, so any cross-year comparison must be per-benchmark; and
SMT-COMP strips every benchmark solved by all solvers in under 1 s, so its
corpora are harder than the raw SMT-LIB logic our own runs sample.

## In-flight declarations

*(`parse.rs` region announcements go here before the first commit touching it.)*

- _(none yet)_
