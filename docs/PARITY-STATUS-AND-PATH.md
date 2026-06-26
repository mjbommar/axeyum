# Parity Status & Path — top-down (2026-06-24)

A from-scratch reader's map: **what axeyum is, where it actually stands against
Z3/cvc5/Lean (measured, not asserted), and the exact remaining path to parity.**
This complements — does not replace — [`PLAN.md`](../PLAN.md) (the engineering
roadmap + standing rules), [`STATUS.md`](../STATUS.md) (the live tracker), and the
auto-generated [`bench-results/SCOREBOARD.md`](../bench-results/SCOREBOARD.md) (the
measured numbers). When those disagree with prose, **the scoreboard is the truth.**

---

## 1. What axeyum is (one paragraph)

A pure-Rust automated-reasoning stack — typed term IR → rewriting → bit-blast/theory
solving → models, proofs, checkable evidence. Identity: **untrusted fast search,
trusted small checking.** Default build has **no C/C++ dependency**; native solvers
(Z3) are feature-gated oracle/cross-check scaffolding only. Two goals, both required
for "done": **Z3 parity** = feature coverage + competitive *measured* performance on
the decidable fragments, honest `unknown` elsewhere; **Lean parity** = every
`unsat`/`valid` carries a machine-checkable certificate a Lean-grade kernel accepts.

## 2. Where we actually stand (the honest top-down)

**The single most important fact: across ~24 logic fragments measured head-to-head
vs Z3 4.13.3 — 992 files, 597 oracle-compared — DISAGREE = 0. Zero wrong sat/unsat,
anywhere.** Soundness is the settled foundation. The gap to Z3/cvc5 is **decide-rate
and depth, never correctness.**

### 2a. The Z3-functionality axis — measured (see SCOREBOARD.md for live numbers)

The capability frontier (decide% per division) partitions cleanly:

- **Strong / competitive (≥80%):** QF_ABV 88%, QF_AUFBV 93%, QF_DT 100%, QF_FP 100%, QF_UFBV
  100%, QF_UFFF 100%, QF_FF 80%, QF_LIA 91%, QF_NIA-synthetic 100%,
  QF_NRA-synthetic 91%, quantified-BV 69–80%, QF_SEQ 79%, QF_BVFP 88%,
  QF_LRA 82%.
- **Mid (40–70%):** QF_UF 54–67% after the first-class carrier-sort remeasurement
  and the 2026-06-26 SMT-LIB div/mod underspecification guard, QF_ALIA 50%,
  QF_NIA 54%, QF_S 44%, QF_AUFBV-cvc5 56%,
  QF_UFLIA 50–83%.
- **Weak / open (<40%) — the real frontier:** QF_SLIA 30% (bounded-string length
  wall), QF_NRA-cvc5 24% (high-degree nonlinear), QF_AX 38%, QF_AUFLIA 14%,
  **quantified-LIA/UF over infinite domains 0%**. Int-indexed arrays are now
  split: QF_ALIA has moved to the mid band after the generic Bool/linear-Int
  array route, while broader AUFLIA remains weak.
- **QF_BV:** measured at parity with Z3 on the hard public p4dfa slice (both
  hard-capped) — see PLAN's lazy-bitblasting findings.

**Reading it:** where axeyum decides, it matches Z3. The weak rows are *coverage*
(front-end gaps, modeling caps) and *decision power* (high-degree NRA, infinite-domain
quantifiers, Int-array theory) — not soundness.

### 2b. The Lean-parity axis — the *Certifying* moat (ahead of Z3, competitive w/ cvc5)

Every `unsat` that reduces to QF_BV carries an independently re-checkable **DRAT**
proof (the in-tree `check_drat`, RUP+RAT) + the bit-blast faithfulness miter. On top:

- **Datatype field-axiom Lean chain — COMPLETE and real-Lean-validated.** is-tester,
  distinctness, injectivity, and acyclicity (single + multi-step cycles) all
  reconstruct **axiom-free** to a kernel-checked `False`, accepted by **both** the
  in-tree trusted kernel **and** the real `lean` binary (`#print axioms` clean, no
  `sorryAx`). Acyclicity via a **size argument** (`size:D→Nat`, `n≠succ^k n`) — no
  well-founded recursion needed.
- **Reduction trust holes — four narrowed by per-query witness certs** (each
  re-validated by `check_drat`, `is_certified` honestly left `false`, only the
  witnessed sub-case documented): **IntBlast** (bounded-box exact int-blast),
  **Ackermann** (eager UF-elim), **ArrayElim** (read-over-write + select-congruence),
  **Fpa2Bv** (exhaustive small-format FP8_E5M2 faithfulness vs `rustc_apfloat`).
- **Other certs:** QF_LRA Farkas, QF_UF congruence, degree-2 SOS→Lean, QF_BV Alethe→
  Carcara (mul/rem/shift are Carcara holes → DRAT route covers them), datatype ROW
  same/diff Carcara.
- **The pattern** (reusable): witness a *deterministic* reduction whose steps are
  *self-evidently valid theory consequences* → re-derive + `check_drat`. It works for
  IntBlast/Ackermann/ArrayElim; it does NOT for Fpa2Bv (a circuit's correctness isn't
  self-evident → needs an exhaustive/sampled miter vs an independent reference). See
  `~/.claude/.../memory/trust-hole-witness-pattern.md`.

### 2c. Three progress instruments (regenerable, committed or generated)

- **`bench-results/SCOREBOARD.md`** (`python3 scripts/gen-scoreboard.py`) — the
  division-level measured view vs Z3. Aggregate "are we competitive."
- **`bench-results/DOMINANCE.md`** (`python3 scripts/gen-dominance-scoreboard.py`) —
  the conservative Pareto-dominance view: measured decide/PAR-2 rows plus exact
  results for committed per-instance audits. It currently reports **35 rows,
  992 files, 648 decided, 597 oracle-compared, DISAGREE=0**, with **19 complete
  exact audit rows** and no remaining first-queue audit rows. Exact committed
  rows now include BV/bitwuzla quantified `100% (4/4)`, BV/cvc5 quantified
  `100% (37/37)`, QF_ABV/cvc5+bitwuzla
  `100% (169/169)`, QF_AUFBV/bitwuzla `100% (41/41)`, QF_BV/bvred `100% (6/6)`,
  QF_BVFP/bitwuzla `100% (7/7)`, QF_DT/cvc5 `100% (3/3)`,
  QF_FF/cvc5 `100% (24/24)`, QF_FP/bitwuzla `100% (16/16)`,
  QF_LIA/cvc5 `100% (10/10)`, QF_LRA/cvc5 `100% (9/9)`, QF_NIA synthetic
  `100% (32/32)`, QF_NRA synthetic `100% (30/30)`, QF_UF/cvc5 bounded
  declared-sort `84% (37/44)` with Lean unsat `57% (8/14)`,
  QF_UFBV/cvc5 `100% (4/4)`,
  QF_UFBV/bitwuzla `100% (2/2)`, QF_UFFF/cvc5 `100% (8/8)`, QF_UFLIA curated
  `100% (2/2)`, and QF_UFLIA bounded `100% (5/5)`. QF_ABV/QF_AUFBV no longer
  carry audit runtime failures:
  phase timing first localized all 11 old ABV/AUFBV timeouts to
  `produce-evidence`, the timed evidence export guard cut that to 3, and the
  array budget-propagation pass eliminated the remaining timeout rows by
  returning checked budget `unknown` instead of falling through to expensive
  qf-bv fallbacks. The former ABV timeout/search-frontier files (`rw34` and
  `arraycond9`) are now certified `array-axiom-unsat` rows, and the former
  AUFBV timeout row `fifo32ia04k05` is closed by a replay-checked model. The
  former bitwuzla
  AUFBV finite-array extensionality rows `smtextarrayaxiom{1..4}.smt2` are now
  certified by `UnsatFiniteArrayExtensionality` and reconstruct through the
  `FiniteArrayExtensionality` Lean fragment. The former AUFBV
  `smtaxiommccarthy`, `smtarraycond1`, and `smtarraycond3` rows are now certified
  by `UnsatArrayAxiom` and reconstruct through the `ArrayAxiom` Lean fragment.
  The structural AUFBV program-array lane now also covers `rw213`, `wchains002ue`,
  `memcpy02`, `bubsort002un`, `selsort002un`, `dubreva002ue`, `swapmem002ue`,
  `binarysearch32s016`, and `fifo32bc04k05` with checked evidence plus Lean
  fragments; the generated FIFO induction SAT row `fifo32ia04k05` is now closed
  by a replay-checked concrete model.
  The former cvc5
  `bug593` error is now a certified and Lean-reconstructed finite-domain
  pigeonhole result (`ProofFragment::FiniteDomainPigeonhole`); the bitwuzla
  `declsort1` SAT error is now a replay-checked declared-sort UFBV model; the
  LRA audit error class is gone because unsupported pure-real certificate
  declines now fall through to replayable evidence. Direct array-extensionality
  proofs now reconstruct to Lean through the EUF path, moving the ABV
  `ackermann3` row plus the AUFBV `smtextarrayaxiom*uf` rows from
  Alethe-certified-only to Lean-checked. ABV BTOR-style read-over-write rows
  now include certified `array-axiom-unsat` coverage for `write1` and `write13`;
  the read-congruence extension then added representative `read*`/`ext*` rows
  such as `read1`, `read4`, and `read10`, and the refreshed audit also reflects
  current `BvAbstraction` ABV rows. The guarded write-case extension then added
  `write2`, `write4`, `write7`, `write8`, `write9`, `write10`, and `verbose2`,
  the nonzero-offset ROW extension added `rwpropindexplusconst{1..4}`, the
  store-shadowing extension added `write22`, `write23`, and `write24`, the
  conditional-select extension added `rw30`, `rw31`, `rw32`, and `rw33`, the
  contextual BV1-false extension added `write14` and `arraycondconst`, the
  nested BV1-complement extension added `arraycondconstaig`, the finite
  extensionality-bit extension added `ext5` and `ext21`, the BV-not
  injectivity read-congruence extension added `read22`, the concat-suffix ROW
  extension added `3vl1`, the store same-cell injectivity extension added
  `extarraywrite1`, the store self-update read extension added `ext22`, and
  the equal store-chain readback extension added `ext27` and `ext28`. The BV1
  order/extensionality extension then added `ext16` and `ext26`, the
  concat-xor finite extensionality extension added `ext23`, the finite
  row-wise extensionality extension added `ext19`, `ext24`, and `ext25`, the
  symbolic-cover/implication extension added `ext13`, `read9`, `write16`, and
  `write17`, and the array-ite all-true branch-cover extension added
  `arraycond3`, `arraycond5`, `arraycond6`, `arraycond7`, and `arraycond8`.
  The contextual ITE-branch/self-update extension then added `arraycond11`,
  `arraycond12`, `arraycond13`, `arraycond14`, `arraycond18`, and `ext11`,
  and the cvc5 same-cell store/range extension added `issue9519` and
  `proj-issue321`. The cvc5 store-restore no-op extension then added
  `bug637.delta`, the same-value store-chain coverage extension added
  `bvproof2`, the signed-BV1 read-congruence extension added `issue9041`, and
  the ITE branch-exhaustion/read-congruence extension added `rw34` and
  `arraycond9`, lifting ABV exact dominance to **169/169** and Lean unsat
  coverage to **85/85** with no ABV `bare-unsat`, `unknown`, or non-dominant
  rows in the exact audit.
  The exact bitwuzla AUFBV audit row is
  now fully dominant at **41/41**; remaining array work is broader proof coverage
  and cvc5/AUFLIA decide depth, not this exact row. The exact QF_BV/bvred row is
  also fully dominant at **6/6** with Lean unsat **2/2**; the former
  `cvc5__redand-eliminate.smt2` miss now reconstructs through the checked
  structural Lean route with no trust holes, and literal `not (= t t)` cases have
  a direct `ReflexiveDisequality` fallback. QF_LRA/cvc5 is now fully dominant at
  **9/9** with Lean unsat **3/3**: `ite_arith` is certified as
  `term-identity-unsat`, and the Boolean/DPLL rows `arith__ite-lift` and
  `simple-lra` reconstruct through `ProofFragment::LraDpll`. The audit
  entry point is:
  `cargo run --release -p axeyum-bench --example audit_dominance -- <baseline.json>
  [timeout_ms] [limit] [out.json]`. Rows without a complete committed
  `bench-results/dominance/*.json` artifact remain readiness entries.
- **`crates/axeyum-solver/tests/progress_frontier.rs`** (oracle-free, CI-gated) — a
  per-roadmap-lever *frontier* (largest difficulty-knob N axeyum decides): bv_reduction
  33, lia_cuts 26, nia_unsat **40**, nra_degree 2,
  string_bound 8. Each is a single integer that *rises* when its lever improves — the
  "gradual progress" signal. Self-checking, so it's also a soundness gate.

## 3. The remaining path to 100% — partitioned by who/what, prioritized

The remaining distance is legibly partitioned. **Nothing here is vague; each item has
a named mechanism.**

### Tier A — decide-rate keystones (the biggest capability gaps). Mostly the
**deciders/IR**, actively advanced by the parallel agent's `axeyum-ir`/`axeyum-rewrite`/CAD work.

1. **Int-indexed arrays** (QF_ALIA/QF_AUFLIA/QF_AX ~0–38%). The first IR blocker is
   **partially lifted (2026-06-25):** `Sort::Array` now carries sort-valued
   index/element metadata (`ArraySortKey`) instead of BV widths only; SMT-LIB
   parses/writes free `(Array Int Int)` terms, and congruence-UNSAT over
   Int-indexed arrays is decided. **Second slice landed (2026-06-25):** generic
   non-BV array model projection (`Value::GenericArray`) plus lazy
   ROW/extensionality over the Bool/linear-Int scalar abstraction now returns
   replay-checked `sat` for free `(Array Int Int)` reads and disequality
   witnesses, and refines ROW conflicts to `unsat`. Local remeasurement on the
   fair cvc5 clean slice moved QF_ALIA to **3/5 decided, DISAGREE=0**; QF_AUFLIA
   remains **1/3 decided**. **Third prerequisite slice landed (2026-06-25):**
   SMT-LIB/IR now admit array-valued UF parameters such as
   `g : (Array Int Int) -> Int` (array-valued UF results remain rejected), and
   function models use full-`Value` keys so concrete generic arrays can appear in
   UF tables; the narrow AUFLIA congruence conflict `a=b ∧ g(a)≠g(b)` is now
   decided `unsat`. The next blocker is the broader mixed UF/array route: lazy
   ROW/extensionality needs a scalar backend that can solve UF+LIA applications
   over array arguments, followed by a committed QF_AUFLIA/QF_ALIA baseline
   refresh. **Mixed ROW+UF route landed later 2026-06-25:** lazy
   ROW/extensionality now delegates Bool/linear-Int+UF scalar abstractions to
   the existing UF+LIA combination, preserves/completes UF interpretations for
   replay, and decides replayed SAT shapes with UF-produced Int indices. Local
   QF_AUFLIA fair-slice remeasurement is **2/6 decided, DISAGREE=0**. Remaining
   blockers are concrete from per-file traces: scalar Int-array timeout
   (`bug337`), array term shapes outside the current ROW fragment (`bug330`,
   `swap...`), and missing array-equality-to-UF congruence refinement (`bug336`).
   **Store-disjunction refuter landed later 2026-06-25:** the array fast path now
   uses `store(a,i,v)=b ∧ store(a,j,w)=b ⇒ i=j ∨ a=b` with checked congruence
   refutations of both branches, closing `bug336` and moving the local QF_AUFLIA
   fair slice to **3/6 decided, DISAGREE=0**. Remaining blockers are now scalar
   Int-array timeout (`bug337`) and array-valued structural terms outside the
   current ROW fragment (`bug330`, `swap...`).
   **Structural ROW coverage widened later 2026-06-25:** array-valued UF
   arguments are now preserved through scalar applications, `select` over
   array-valued `ite` lowers to branch reads, store ROW misses can reference a
   scalar read expression, and mixed array+UF `unknown` from the UF-arithmetic
   overbound guard falls through to the array route. Local QF_AUFLIA measurement
   remains **3/6 decided, DISAGREE=0**, but `bug330` and `swap...` are now past
   structural ROW rejection. Remaining blockers are the scalar UFLIA Boolean atom
   cap (`bug330`), swap-chain replay/refinement incompleteness, and the scalar
   Int-array timeout (`bug337`).
   **Projection-completion slice landed later 2026-06-25:** the AUFLIA ROW scalar
   backend can fall back from non-budget online-UFLIA `unknown` to eager
   UF+arithmetic, and function model projection now completes non-application
   symbols before evaluating full-`Value` UF argument keys. This closes the
   concrete array-valued-UF projection failure exposed by `swap...`; local
   QF_AUFLIA measurement is still **3/6 decided, DISAGREE=0**. Remaining misses
   are scalar-engine frontiers: `bug330` has a 339-atom Boolean UFLIA abstraction
   against the current cap of 48, while `swap...` and `bug337` hit lazy-LIA
   timeouts.
   **Bounded LIA probe + clean swap-chain refuter landed later 2026-06-25:**
   the scalar arithmetic path now gives the online LIA DPLL(T) spine a bounded
   deadline-aware probe before falling back to the legacy certified route, and
   the array fast path recognizes clean symmetric store-swap chains as
   extensionally equal. Local QF_AUFLIA measurement remains **3/6 decided,
   DISAGREE=0** (`qf-auflia-after-swap-chain-refuter.json`); this does **not**
   close the current cvc5 `swap...` instance. The frontier is still scalar
   search/relevance (`bug330`), a stronger array-permutation/ROW normalizer
   (`swap...`), and the Int-array timeout (`bug337`).
   **Permutation-chain refuter landed later 2026-06-25:** the swap-chain
   recognizer is now a memoized array-permutation normalizer, and proven
   array-unsat refuters run before the expensive scalar routes. This closes the
   exact cvc5 `swap_t1_pp_nf_ai_00010_004` regression. Local QF_AUFLIA
   measurement is now **4/6 decided, DISAGREE=0**
   (`qf-auflia-after-permutation-refuter.json`); Z3 remains **6/6**. At that
   point, the two remaining misses were scalar frontiers: `bug330` (339 Boolean
   UFLIA atoms against cap 48, then lazy-LIA timeout) and `bug337` (pure Int-array
   lazy-LIA timeout).
   **UFLIA/UFLRA deadline + cap diagnostic landed later 2026-06-25:** the
   integrated combined-theory DPLL drivers now honor their configured deadline,
   and the UFLIA Boolean atom cap is raised to 384 under that guard. Local
   QF_AUFLIA measurement remains **4/6 decided, DISAGREE=0**
   (`qf-auflia-after-uflia-deadline-cap.json`). The `bug330` diagnosis is now
   sharper: it is no longer blocked by the old 48-atom admission cap; it reaches
   online UF+LIA, declines on an uncertified Boolean-layer theory model, and then
   the lazy Int-array route exhausts the budget. `bug337` remains the pure
   Int-array lazy-LIA timeout.
   **Measurement timeout + scalar-abstraction diagnostics landed later
   2026-06-25:** the corpus measurement harness now passes its timeout into
   `SolverConfig::timeout`, and lazy ROW/extensionality plus arithmetic DPLL now
   report remaining-budget-aware scalar failure details. Local QF_AUFLIA remains
   **4/6 decided, DISAGREE=0**
   (`qf-auflia-after-scalar-abstraction-diagnostics.json`). The residual misses
   are no longer mysterious refinement loops: `bug330` fails before any ROW lemma
   is added (62 select sites; scalar abstraction 832 atoms / 4 blocking lemmas),
   and `bug337` fails before any extensionality lemma is added (152 select sites;
   scalar abstraction 1374 atoms / 2 blocking lemmas).
   **Arithmetic atom canonicalization landed later 2026-06-25:** reversed and
   negated order atoms now share canonical propositions, self-comparisons fold,
   and the online LIA probe is capped at 1s before fallback. Local QF_AUFLIA is
   still **4/6 decided, DISAGREE=0**
   (`qf-auflia-after-arith-atom-canonicalization.json`), but `bug330` improves
   from 832 to 802 scalar atoms and from 4 to 7 fallback blocking lemmas before
   timeout. `bug337` is unchanged.
   **Scalar Boolean short-circuiting landed later 2026-06-25:** the arithmetic
   abstractor now folds Boolean constants and identical branches for `and`/`or`/
   `xor`/implication/Bool equality/Bool `ite`, and skips dead branches before
   allocating arithmetic atoms. This is a useful local invariant but does **not**
   move the measured frontier: local QF_AUFLIA remains **4/6 decided,
   DISAGREE=0** (`qf-auflia-after-boolean-simplification.json`), `bug330`
   remains 802 atoms / 7 blocking lemmas, and `bug337` remains 1374 atoms / 2
   blocking lemmas. The next useful move is scalar relevance / Boolean-layer
   model certification for `bug330`, or a smaller initial extensionality
   abstraction / model-construction shortcut for `bug337`.
   **Scalar snapshot preprocessing landed later 2026-06-25:** lazy
   ROW/extensionality now flattens positive top-level conjunctions before sending
   scalar snapshots through the existing replay-safe
   `propagate_values`/`solve_eqs` preprocessing wrapper. This exposes generated
   aliases and constants without weakening the normal SAT replay gate. The
   measured frontier is still **4/6 decided, DISAGREE=0**
   (`qf-auflia-after-scalar-preprocess-flatten.json`), but `bug337` moves
   materially: 1374 atoms / 2 blocking lemmas becomes 946 atoms / 7 blocking
   lemmas at 10 s, and a 30 s single-file run reaches 19 blocking lemmas before
   timeout. `bug330` remains 802 atoms and times out after 6 lemmas.
   **Online LIA/LRA Boolean-leaf model lift landed later 2026-06-25:** standalone
   online arithmetic drivers now include declared Boolean-leaf values from the
   final DPLL assignment in replayed `sat` models. This closes a scalar replay
   gap but does not move the current AUFLIA count: **4/6 decided, DISAGREE=0**
   (`qf-auflia-after-online-boolean-model-lift.json`), with `bug330` still 802
   atoms / 6 lemmas and `bug337` still 946 atoms / 7 lemmas at 10 s. A 3s online
   probe cap was tested and rejected because it did not decide either hard file.
   **Scalar LIA bound-lemma + large-core cutoff landed later 2026-06-25:** the
   legacy arithmetic DPLL fallback now records certifiable simple integer-bound
   mutex lemmas up front and stops deletion-minimizing theory cores once a scalar
   abstraction exceeds 128 atoms. This does not change the measured count:
   **4/6 decided, DISAGREE=0**
   (`qf-auflia-after-bound-lemmas-core-cutoff.json`). It does change the
   bottleneck diagnosis: `bug330` now reaches 40 scalar blocking lemmas at 10 s
   (27 upfront bound lemmas), `bug337` reaches 46 at 10 s (150 upfront bound
   lemmas), and a 30 s `bug337` run reaches 84 before the pure Boolean skeleton
   times out. The residual blocker is Boolean-skeleton scaling/relevance after
   many learned clauses, or a replay-gated SAT/model-construction shortcut for
   `bug337`, not simplex core-minimization cost.
   **Warm scalar Boolean skeleton landed later 2026-06-25:** the legacy
   arithmetic DPLL fallback now encodes the scalar Boolean skeleton once into a
   warm `IncrementalSat` and adds learned theory clauses incrementally, rather
   than rebuilding through the general SAT-BV path every round. The measured
   AUFLIA count is still **4/6 decided, DISAGREE=0**
   (`qf-auflia-after-warm-scalar-bool-skeleton.json`), but the residual
   diagnosis moved again: `bug330` reaches 608 scalar blocking clauses at 10 s,
   `bug337` reaches 788 at 10 s, and a 30 s `bug337` run reaches 1670 before
   `rustsat-batsat` times out. The remaining blocker is SAT search quality /
   relevance over a large learned-clause Boolean skeleton, or a replay-gated
   `bug337` model-construction shortcut; Boolean rebuild overhead is no longer
   the limiting factor.
   **Current-polarity integer-bound cores landed later 2026-06-25:** dynamic
   scalar LIA conflicts now scan the assigned literal polarities for a cheap
   two-literal integer-bound contradiction before using the large full-theory
   slice. This covers complement bounds from assignments such as `not (x <= 1)`
   and keeps the lemma on the existing certificate path. The measured AUFLIA
   count remains **4/6 decided, DISAGREE=0**
   (`qf-auflia-after-cheap-bound-core.json`), with diagnostics moving to
   `bug330` at 1143 scalar blocking lemmas at 10 s and `bug337` at 860. This
   confirms the residual blocker is still learned-clause search quality /
   relevance, or a replay-gated `bug337` model-construction shortcut.
   **Integer local-search scalar probe landed later 2026-06-25:** the one-sided
   local-search model finder now supports `Int` variables and is tried for 100 ms
   after preprocessing in the lazy ROW/extensionality scalar snapshot. The
   measured AUFLIA count remains **4/6 decided, DISAGREE=0**
   (`qf-auflia-after-int-local-search-scalar-probe.json`; axeyum PAR-2 6.668 s),
   but the diagnostic split is clearer: `bug330` still has UF applications
   outside this probe's scope, while `bug337` is in scope but local search times
   out before the exact scalar loop later times out after 857 rounds. Next:
   finite UF-table model search for `bug330`, or SAT relevance / replay-gated
   model construction for `bug337`.
   **Capped structural PBLS scoring landed later 2026-06-25:** compact Boolean
   assertions now get a structural local-search cost, but large generated
   assertions stay on the cheap root score. The measured AUFLIA count remains
   **4/6 decided, DISAGREE=0**
   (`qf-auflia-after-structural-pbls-score.json`; axeyum PAR-2 6.668 s).
   `bug330` remains out of this probe's scope because of UF applications; `bug337`
   remains in scope but local search times out and exact scalar search reaches
   865 blocking lemmas before SAT timeout. The useful next step is still SAT
   relevance / replay-gated model construction for `bug337`, or finite UF-table
   model search for `bug330`.
   **Capped integer-difference cores landed later 2026-06-25:** scalar arithmetic
   DPLL(T) now extracts compact IDL negative-cycle cores for small/medium
   snapshots (`x + c <= y + d` / strict variants), with a direct two-edge path
   for conflicts like `x <= y` and `y + 1 <= x`. Large generated AUFLIA snapshots
   decline this extractor to avoid core-search overhead. The measured AUFLIA
   count remains **4/6 decided, DISAGREE=0**
   (`qf-auflia-after-capped-idl-core.json`; axeyum PAR-2 6.668 s); `bug330`
   reaches 1140 blocking lemmas and `bug337` reaches 849 before SAT timeout. The
   hard slice still wants SAT relevance / model construction or a different
   array/branch abstraction shortcut.
   **Compact bound-implication lemmas landed later 2026-06-25:** scalar
   arithmetic DPLL(T) now seeds asserted simple-bound monotonicity lemmas for
   compact skeletons, e.g. `x <= 0 => x <= 1`, as normal certifiable LIA cores
   `{stronger_bound, not weaker_bound}`. A broader all-polarity version was
   measured and rejected because it inflated the hard AUFLIA upfront clause set;
   the landed pass is asserted-bound-only and gated at 256 arithmetic atoms. The
   measured AUFLIA count remains **4/6 decided, DISAGREE=0**
   (`qf-auflia-after-compact-bound-implications.json`; axeyum PAR-2 6.668 s),
   with hard diagnostics back near baseline (`bug330` 27 upfront bound lemmas /
   1137 blocking lemmas; `bug337` 150 / 854). This is a compact-query guardrail;
   it does not change the conclusion that the remaining AUFLIA misses require
   large-skeleton SAT relevance/model construction, finite UF-table model search,
   or a higher-level array/branch abstraction shortcut.
   **PBLs affine integer repair candidates landed later 2026-06-25:** the
   one-sided local-search model finder now proposes assertion-local integer
   repair moves for unit-affine equality/order atoms (`x`, `x + c`, `c + x`,
   `x - c`) from the current value of the opposite side. The move set is capped
   and remains replay-gated. The measured AUFLIA count remains **4/6 decided,
   DISAGREE=0** (`qf-auflia-after-pbls-affine-repairs.json`; axeyum PAR-2
   6.668 s, Z3 PAR-2 0.105 s). Diagnostics are unchanged: `bug330` is still
   outside this probe because the scalar snapshot contains UF applications, and
   `bug337` still times out in local search before the exact scalar loop reaches
   855 blocking lemmas. Treat this as a small-query model-search primitive, not
   an AUFLIA frontier close.
   **Focused OR branch repair for PBLs landed later 2026-06-25:** wider
   OR-shaped assertions now keep the cheap persistent root score, but when
   selected by local search they get a bounded structural tie-break plus a
   branch-repair planner that tries to satisfy one disjunct by applying simple
   literal repairs as a unit. A broad structural-cap increase and a 1 s scalar
   local-search probe were measured and rejected because they still did not
   close the two hard files. The measured AUFLIA count remains **4/6 decided,
   DISAGREE=0** (`qf-auflia-after-pbls-focused-or-repair.json`; axeyum PAR-2
   6.668 s, Z3 PAR-2 0.104 s). Diagnostics remain baseline-shaped: `bug330` is
   still UF-out-of-scope for local search and times out after 1144 scalar
   blocking lemmas; `bug337` still local-searches to timeout, then scalar LIA
   times out after 851 blocking lemmas. The next AUFLIA move should be a real
   branch-schedule/model constructor, finite UF-table reasoning for `bug330`, or
   SAT relevance in the large scalar skeleton.
   Then extend from the current Bool/linear-Int array slice to broader non-BV
   component sorts.
2. **QF_NRA high-degree** (cvc5 24%). Linear/McCormick → **CAD/nlsat**; high-degree SOS
   needs SDP. The CAD decision side + bignum algebraic path are landing (parallel agent).
3. **QF_NIA** beyond bounded-box. The bounded synthetic row is now
   Pareto-dominant: finite-box SAT uses replayed models, bounded nonlinear
   UNSAT carries `bounded-int-blast-unsat` evidence plus
   `ProofFragment::BoundedIntBlast` Lean reconstruction. The residual frontier
   is unbounded/symbolic div-mod and genuinely nonlinear integer arithmetic —
   the multiplier no-overflow guard (parallel agent, NIA Unknown 498→146) is the
   decide-rate lever.
4. **Uninterpreted-sort QF_UF** (43% modeled-as-BV vs 56% bounded). **First-class
   IR carrier sort landed 2026-06-25:** arity-0 SMT-LIB `declare-sort` now becomes
   `Sort::Uninterpreted(SortId)`, not a BitVec over-approximation; `check_auto`
   routes pure many-sorted EUF through the e-graph path and replay-checks `sat`
   models with deterministic uninterpreted tokens. Remaining work: remeasure the
   QF_UF bounded/uninterpreted-sort corpus, then address the residual front-end
   coverage (`Set`/`Seq` sorts, `sin`, `fmf.card`) rather than congruence itself.
5. **Infinite-domain quantifiers** (UF/LIA quantified 0%). MBQI/instantiation can only
   *refute* over infinite domains; sat-side needs a model-finding loop. Finite-domain BV
   quantifiers already decide (69–80%).

### Tier B — front-end coverage (parser lane, tractable, mostly mined). The clean
finite-modeling vein (Sets/Strings/Seq/FF opened this session) is largely exhausted.
Residual: symbolic `str.replace_all` (~8 files, low value), the **bounded-string length
cap** (`STRING_MAX_LEN=8` — raising it *regresses* decide-rate via packed-BV blowup; the
real lift is migrating the parser onto the solver's `BoundedString` `StrTerm` API that
`check_auto` can't currently reach), NIA operators (`int.pow2`, `iand`), `:named`.

### Tier C — Lean-parity depth (cert lane, mostly mine; the cleanly-witnessable holes done)
1. **Fpa2Bv large/non-IEEE formats.** Exhaustive small-format done; FP32/64/128 and
   non-IEEE FP8-E4M3/FP4 need a **sampled or SMT-equivalence miter vs an independent
   reference circuit** (not the re-derivation trick). Research-grade.
2. **Carcara/Lean reconstruction of mul/rem/concat** (the finite-modeled theories certify
   via DRAT but not yet Carcara — mul/rem/shift are Carcara holes). Needs Carcara
   bit-blast rules or the miter-`hole` route.
3. **DatatypeElim general case** (`is_certified` still false; the field axioms are
   Carcara+Lean-certified but the *elimination dispatch* isn't end-to-end witnessed).
4. **NRA/NIA `unsat` Lean evidence beyond the closed synthetic rows** — bounded
   NIA and the graduated NRA even-power/SOS slice are now certified and
   Lean-checked; the remaining certify-gap is broader high-degree/cvc5 NRA and
   genuinely symbolic nonlinear arithmetic.

### Tier D — soundness hardening (ongoing). Differential fuzzes are the highest-yield
bug-finders (they caught 3 wrong-unsats + the FP `±0` wrong-unsat this session). The
new theories (Strings/Seq/Sets/FF) need adversarial differential fuzzes vs Z3 — a
**string fuzz is in progress** (this commit's neighbor); extend to FF/Seq/Sets.

## 4. Reflection on PLAN.md

**The 2026-06-23 "MEASURE, don't seed" course-correction was right and is now
discharged.** Its diagnosis — "ledger-over-corpus, only QF_BV measured" — has been
answered: 24 fragments are measured vs Z3 with a committed, regenerable scoreboard +
the oracle-free frontier dashboard. The dominance-readiness report now adds the
proof-route audit queue for the Pareto-dominance strategy, and the
`audit_dominance` harness supplies the per-instance evidence/Lean fields. Complete
committed audit artifacts are now ingested for 12 rows across BV, QF_ABV,
QF_AUFBV, QF_BV, QF_LIA, QF_LRA, QF_NIA, QF_NRA, QF_UFBV, and QF_UFLIA, so exact
dominance coverage has replaced readiness labels on the first queue. Measurement
is **no longer the blocker** for decide-rate or first-queue dominance coverage;
remaining dominance work is now Lean/proof fixes and evidence-performance fixes
for the concrete gaps already exposed. The scoreboard's weak rows now *name* the blockers precisely (Tier A
above), and exact audit rows now also name missing Lean coverage and trust holes
rather than reporting only runtime audit failures.

Updates the PLAN should absorb:
- **The seed moratorium can relax for *build-and-measure* theory opens** (Sets/Strings/
  Seq/FF were opened AND immediately measured DISAGREE=0 — that satisfies measure-first;
  a seed without a number is still forbidden).
- **The QF_BV bottleneck framing holds** (word-level reduction / native-core, not the
  theory-loop heuristics) — untouched this session; it's the parallel agent's perf lane.
- **The Certifying moat widened materially** (complete datatype Lean chain + 4 trust
  holes witnessed) — PLAN's "ahead of Z3 on certification" is now concretely true and
  real-Lean-validated, not just DRAT.
- **The maturity ladder is accurate.** Most divisions sit at *Decides*; QF_ABV/QF_FP are
  *Measured-competitive*; the *Certifying* rung is uniquely ours and broadened.

**The path is clear and the next mover per item is unambiguous:** Tier A (deciders/IR) is
the parallel agent's active lane; Tier B/C/D are the parser/cert/fuzz lanes. A from-
scratch reader: read this → SCOREBOARD.md → pick the highest-decide%-gain weak row whose
mechanism is in your lane → advance one sound, DISAGREE=0-gated increment → regenerate the
scoreboard. The soundness floor (DISAGREE=0) must never move off zero; that is the line.
