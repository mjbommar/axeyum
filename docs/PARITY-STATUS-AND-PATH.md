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
vs Z3 4.13.3 — 992 files, 572 oracle-compared — DISAGREE = 0. Zero wrong sat/unsat,
anywhere.** Soundness is the settled foundation. The gap to Z3/cvc5 is **decide-rate
and depth, never correctness.**

### 2a. The Z3-functionality axis — measured (see SCOREBOARD.md for live numbers)

The capability frontier (decide% per division) partitions cleanly:

- **Strong / competitive (≥80%):** QF_ABV 88%, QF_AUFBV 93%, QF_FP 100%, QF_UFBV
  100%, QF_UFFF 100%, QF_FF 80%, QF_LIA 91%, QF_NRA-synthetic 91%, quantified-BV
  69–80%, QF_SEQ 79%, QF_BVFP 88%, QF_LRA 82%.
- **Mid (40–70%):** QF_UF 43–56% (capped by the uninterpreted-sort modeling), QF_NIA
  51%, QF_S 44%, QF_DT 67%, QF_AUFBV-cvc5 56%, QF_UFLIA 50–83%.
- **Weak / open (<40%) — the real frontier:** QF_SLIA 30% (bounded-string length
  wall), QF_NRA-cvc5 24% (high-degree nonlinear), QF_AX 38%, QF_AUFLIA 14%,
  **QF_ALIA/Int-indexed arrays ~0–3%**, **quantified-LIA/UF over infinite domains 0%**.
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

### 2c. Two progress instruments (both regenerable, both committed)

- **`bench-results/SCOREBOARD.md`** (`python3 scripts/gen-scoreboard.py`) — the
  division-level measured view vs Z3. Aggregate "are we competitive."
- **`crates/axeyum-solver/tests/progress_frontier.rs`** (oracle-free, CI-gated) — a
  per-roadmap-lever *frontier* (largest difficulty-knob N axeyum decides): bv_reduction
  33, lia_cuts 26, nia_unsat **0→40** (closed this session), nra_degree 2,
  string_bound 8. Each is a single integer that *rises* when its lever improves — the
  "gradual progress" signal. Self-checking, so it's also a soundness gate.

## 3. The remaining path to 100% — partitioned by who/what, prioritized

The remaining distance is legibly partitioned. **Nothing here is vague; each item has
a named mechanism.**

### Tier A — decide-rate keystones (the biggest capability gaps). Mostly the
**deciders/IR**, actively advanced by the parallel agent's `axeyum-ir`/`axeyum-rewrite`/CAD work.

1. **Int-indexed arrays** (QF_ALIA/QF_AUFLIA/QF_AX ~0–38%). The blocker is the IR:
   `Sort::Array{index:u32, element:u32}` is **BV-width-only**. Needs a first-class
   sort-valued array index/element + `eliminate_arrays` over Int (read-over-write +
   Ackermann + const-array → LIA). **Keystone, ~111-file `Sort` blast radius.** Const-array
   sub-case already closed at the parser (`c469cb1`).
2. **QF_NRA high-degree** (cvc5 24%). Linear/McCormick → **CAD/nlsat**; high-degree SOS
   needs SDP. The CAD decision side + bignum algebraic path are landing (parallel agent).
3. **QF_NIA** beyond bounded-box. Bounded integer-nonlinear UNSAT is **closed** via exact
   int-blast (`2b91542`, nia_unsat frontier 0→40); the residual is unbounded/symbolic
   div-mod + genuinely-nonlinear — the multiplier no-overflow guard (parallel agent,
   NIA Unknown 498→146) is the lever.
4. **Uninterpreted-sort QF_UF** (43% modeled-as-BV vs 56% bounded). The "right" fix is a
   first-class IR uninterpreted sort routed through pure congruence closure
   (`check_qf_uf`), not the BitVec over-approximation. IR keystone.
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
4. **NRA/NIA `unsat` Lean evidence** beyond degree-2 SOS — the certify-gap on the
   nonlinear frontier.

### Tier D — soundness hardening (ongoing). Differential fuzzes are the highest-yield
bug-finders (they caught 3 wrong-unsats + the FP `±0` wrong-unsat this session). The
new theories (Strings/Seq/Sets/FF) need adversarial differential fuzzes vs Z3 — a
**string fuzz is in progress** (this commit's neighbor); extend to FF/Seq/Sets.

## 4. Reflection on PLAN.md

**The 2026-06-23 "MEASURE, don't seed" course-correction was right and is now
discharged.** Its diagnosis — "ledger-over-corpus, only QF_BV measured" — has been
answered: 24 fragments are measured vs Z3 with a committed, regenerable scoreboard +
the oracle-free frontier dashboard. Measurement is **no longer the blocker**; the
scoreboard's weak rows now *name* the blockers precisely (Tier A above).

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
