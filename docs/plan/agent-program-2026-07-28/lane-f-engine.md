# Lane F — Engine keystone & QF_BV hard tail

**Ranked-program anchor:** Rank 4 (complete the CDCL(T) keystone migration) +
Rank 6 (QF_BV / QF_FP hard-tail performance).
**Phases:** [P1.5 CDCL(T) loop](../track-1-engine/P1.5-cdcl-t-loop.md),
[P1.1 SAT inprocessing](../track-1-engine/P1.1-sat-inprocessing.md),
[P1.2 preprocessing](../track-1-engine/P1.2-preprocessing.md),
[P1.3 SAT-core modernization](../track-1-engine/P1.3-sat-core-modernization.md).
**Worktree / branch:** `~/projects/personal/axeyum-engine` / `agent/engine/cdclt-dispatch`.
**Owns:** `crates/axeyum-cnf/`, `crates/axeyum-bv/`, `crates/axeyum-aig/`,
`crates/axeyum-rewrite/` preprocessing, solver dispatch.
**Blocks on:** Phase 0. **F1 unblocks Lanes A and B.**

---

## Why this lane exists

Rank 4 is *"not a decide-rate line itself, but the **enabler** under Ranks 2–3
and arrays."* Both keystones are **partially built**, not missing:

- **P1.4 e-graph: DONE.** `axeyum-egraph` (ADR-0032) — hash-cons + union-find +
  congruence + explanation + checker. Live and backtrackable (ADR-0077).
- **P1.5 CDCL(T): WIP.** A `CdclT<T>` driver with 1-UIP plus EUF and String
  adapters exists.

So the remaining work is **porting arrays/BV/datatypes onto the spine and
landing the default-dispatch ADR** — not building the driver. That is
[`gap-analysis-z3-cvc5-2026-07-07.md`](../gap-analysis-z3-cvc5-2026-07-07.md)
Gap 3.

The dependency DAG is explicit: the e-graph blocks P2.2 (lazy arrays), P2.3
(EUF-on-loop), **P2.6 (quantifiers)**, P2.9 (datatypes), and P1.6 (combination).
Lane A's MAM wants to walk the *live* e-graph; Lane B's word-equation work wants
the same spine. F1 is the gate.

---

## F1 — The CDCL(T) default-dispatch ADR (W1, first; unblocks A and B)

**Goal.** Decide and record *when* the CDCL(T) spine is the default route,
per fragment, and what the fallback contract is.

**Why an ADR and not just code.** This changes the default routing for every
supported logic — squarely "decisions are not made silently in code." It also
determines what Lanes A and B can assume, so it must be written down before they
build on it.

**Must specify**
1. Per-fragment default: which logics dispatch to CDCL(T) vs the existing eager
   routes, and the exact predicate that decides.
2. The fallback contract: what happens when the spine declines or exhausts its
   bound — and that the fallback is *sound*, never a second untrusted opinion
   promoted to a verdict (the P0-B lesson: two untrusted search paths agreeing
   is not a proof).
3. The evidence contract: what a CDCL(T) `unsat` can emit, and what it declines
   to claim. Coordinate with **Lane E** — new routes must be born with evidence,
   not added to the 58-occurrence backlog.
4. Determinism: stable literal/atom ordering, explicit seeds, no hash-map
   iteration order in output.
5. The resource bound that degrades to `Unknown`.

**Exit criteria**
- ADR accepted in `docs/research/09-decisions/`.
- `cargo test -p axeyum-solver --test progress_frontier` shows no capability
  regression under the new default.
- Lanes A and B are notified with the exact assumptions they may rely on.

**Size:** M (mostly design + measurement, small diff). **Do it first.**

---

## F2 — Port arrays onto the spine

**Goal.** Move array reasoning from eager elimination onto the CDCL(T) loop.

**Current state.** Eager elimination plus a certifying fallback remains
(ADR-0010). A large amount of canonical array machinery is already landed —
ADR-0071 through ADR-0094 cover replay-guided interfaces, candidate-guided lazy
ROW, extensionality, dynamic in-search ROW insertion, array-valued UF result
projection, structural array-class equations, and the retained-warm family.
P2.2's remaining arc is making the lazy path the *default* rather than a
candidate-guided augmentation.

**Payoff.** QF_ABV is 15,148 library benchmarks at 88 % curated (169/193) vs
Bitwuzla's 99.7 % (7,553/7,574) — the gap there is hard-tail plus budget, and
arrays also gate AUFLIRA/AUFDTLIRA for Lane A's A5.

**Exit criteria:** QF_ABV / QF_AUFBV curated rows hold or improve with
DISAGREE = 0; `progress_frontier` clean; every new `unsat` route has an evidence
story agreed with Lane E.

**Size:** L.

---

## F3 — Flip and measure the inprocessing/preprocessing levers (Rank 6)

**Goal.** The cheapest measured win available: P1.1 and P1.2 are **built but
default-off**. The next step is *measure-and-flip*, not build.

**What exists**
- **P1.1 SAT inprocessing** — subsumption + BVE landed (T1.1.1/T1.1.2), wired
  into the solve pipeline. Vivification and glue tiers remain.
- **P1.2 preprocessing** — general opt-in word-level pass; batched value
  propagation landed 2026-07-27 (4.02 s → 50.38 ms on the QF_BVFP ESBMC
  conversion alarm).
- **P4.5 the PAR-2 head-to-head gate: landed.** `582ecba8` is the first
  committed head-to-head (public QF_BV p4dfa, lazy-vs-eager at 3 s/20 s,
  DISAGREE = 0).

**What is already measured** — read before assuming a lever is free:
- Lazy weakly dominates eager (7 > 4 decided at 20 s), but `lazy_ops_total = 0`
  everywhere — the lazy path is not actually doing lazy work.
- `bench-public-qfbv-preprocess-fair-20s` decides **7/113 vs eager's 3**.
- The paired control: axeyum **8/113** and the Z3 crate **8/113** at 20 s, exact
  overlap **6 jointly decided / 2 axeyum-only / 2 Z3-only** (Z3 CLI 9/113). That
  is *bounded corpus parity*, not a general performance claim, and it must not
  be restated as one.

**Steps**
1. Run the existing fair-comparison recipes across the tiers
   (`bench-public-qfbv-preprocess-fair-3s`/`-20s`,
   `-preprocess-inprocess-fair-3s`/`-20s`, `bench-public-qfbv-lazy-fair-*`).
2. Flip defaults only where the PAR-2 delta is positive **and** DISAGREE stays 0
   **and** no decided instance is lost.
3. Investigate `lazy_ops_total = 0` — either the lazy path is mis-instrumented
   or it never triggers. Both are worth knowing.
4. Take **Lane C's C2 hard third ordering obligation** as a named target: the
   binary79 residual is a pure-BV search problem after lowering, so it belongs
   here, not in an FP-private path.

**Exit criteria:** committed PAR-2 artifacts per tier; each flipped default has
its measurement cited in the ADR or result note; the QF_BV hard-tail delta is
stated on a named slice with its budget.

**Size:** M–L (mostly measurement).

### Pick the right peer: `bv_decide`, not Bitwuzla

SMT-COMP 2025 QF_BV (10,703 benchmarks, 1,200 s) — see
[`smtcomp-2025-parity-targets-2026-07-28.md`](../smtcomp-2025-parity-targets-2026-07-28.md):

| Entry | Solved | % |
|---|---:|---:|
| Bitwuzla-MachBV (winner) | 10,523 | 98.3 % |
| Bitwuzla | 10,498 | 98.1 % |
| Yices2 | 10,491 | 98.0 % |
| **`bv_decide-nokernel`** (Lean) | 8,862 | 82.8 % |
| **`bv_decide`** (Lean, kernel-checked) | 8,638 | 80.7 % |
| Z3-alpha-base *(non-competing)* | 8,945 | 83.6 % |

`bv_decide` is the Lean 4 bitblasting tactic — bit-blast to SAT, check through a
small trusted kernel. **That is our thesis, built by someone else, measured on
the competition corpus.** It is the honest peer comparison for a QF_BV claim;
Bitwuzla is the ceiling, and the top three are within 32 benchmarks of each
other, so QF_BV is saturated at the top.

The single most useful number here: **the kernel-checked variant scores 224
lower than the unchecked one** — roughly 2.1 points of decide-rate. That is
published third-party evidence of what proof checking costs, and it is the right
anchor for any "untrusted fast search, trusted small checking" tradeoff argument
in [`benchmarking-and-performance-methodology.md`](../../research/08-planning/benchmarking-and-performance-methodology.md).

Note also that plain **Z3 did not compete in 2025** — it appears only as
non-competing base entries. Our Z3 comparison must stay our own head-to-head on
committed slices; there is no 2025 ranking to cite.

---

## F4 — SAT-core modernization (P1.3), demand-pulled

**Goal.** VSIDS/VMTF modes, EMA/Luby restarts, arena + packed watches, chrono
backtracking.

**Priority gate — read this before starting.** The custom CDCL core is settled
identity (ADR-0002) but its *priority* is gated by
[`benchmarking-and-performance-methodology.md`](../../research/08-planning/benchmarking-and-performance-methodology.md):
**encodings come first until SAT time dominates on real corpora.** F3's
measurements are what license F4. If F3 shows encoding size dominating, do
encodings; if it shows CDCL time dominating on the hard tail, do F4.

**What exists:** the proof-producing CDCL core `solve_with_drat_proof` (1-UIP
conflict analysis, two-watched-literal propagation, DRAT emission, ADR-0012).

**Reference reading:** CaDiCaL for clause arenas, varisat for Rust CDCL + proof
output, Kissat — all under `references/`. varisat is unmaintained (last release
2019); treat it as a design reference, not a dependency.

**Exit criteria:** a PAR-2 improvement on a named hard slice with DRAT proof
output preserved and `check_drat` still accepting every emitted proof.

**Size:** L. **Do not start before F3 licenses it.**

---

## F5 — Strategy & tactics (P1.8), risk control

**Goal.** Combinators + probes + per-logic scripts. The Codex review recommends
promoting this from cleanup to **risk control** — with more routes (lazy/eager,
CDCL(T)/eager, preprocessing on/off, portfolio members), route selection becomes
the dominant correctness and performance surface.

**Relationship to F1:** F1 decides the *default* dispatch; F5 makes dispatch
*configurable and inspectable*. F1 first.

**Exit criteria:** per-logic strategy scripts are declarative and committed; the
selected route is recorded in the evidence artifact (coordinate with Lane E's
route provenance, E1 — same field, do not build two).

**Size:** M. **Gated on:** F1 and E1.

---

## Lane F rolling exit

> The CDCL(T) default-dispatch ADR is accepted and arrays are on the spine
> (unblocking Ranks 2–3); the built-but-off preprocessing/inprocessing levers
> are measured and flipped where they win; the QF_BV hard-tail delta vs
> Bitwuzla is stated on a named slice at a named budget.

## In-flight declarations

- _(none yet)_
