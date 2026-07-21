# Z3/cvc5 gap analysis (2026-07-07)

> **Historical / superseded.** The current scoped evidence map is
> [gap-analysis-z3-lean-2026-07-21.md](gap-analysis-z3-lean-2026-07-21.md).
> This document's original p4dfa premise was corrected by ADR-0059: the
> registered 20-second controls decide 8/113 for Axeyum and 8/113 for the Z3
> crate on different sets, rather than a Z3 sweep. Retain this file for the
> historical leverage analysis, not current parity numbers.

Status: historical audit — supersedes
[`gap-analysis-z3-cvc5-2026-06-22.md`](gap-analysis-z3-cvc5-2026-06-22.md) as
the priority map (the 06-22 doc remains the historical baseline).
Scope: top-down, practical delta between axeyum's measured state and the public
Z3/cvc5 surfaces, ordered by ROI toward **100% Pareto dominance** (decided +
DISAGREE=0 + Lean-certified unsat + pure-Rust route — the four-constraint
metric in [DOMINANCE](../../bench-results/DOMINANCE.md)).

## Inputs

- The generated [SCOREBOARD](../../bench-results/SCOREBOARD.md) (authoritative:
  992 files / 727 decided ≈ 73% / 661 oracle-compared / **DISAGREE = 0**) and
  [DOMINANCE](../../bench-results/DOMINANCE.md) (23 complete audits, all 100%
  dominant on their decided sets).
- The frontier ratchets (`bench-results/frontier/*.json`).
- Direct code inspection, independently re-verified by a second read
  (`qinst_egraph.rs`, `auto.rs` MBQI loop + dispatch, `cdclt.rs`,
  `combined_theory.rs`, `uflia_online.rs`/`uflra_online.rs`,
  `axeyum-cnf/{simplify,bve,vivify,proof_sat}.rs`, `backend.rs` config
  defaults, `capabilities.rs`).
- [decide-rate-frontier-2026-06-28.md](decide-rate-frontier-2026-06-28.md)
  (the per-fragment undecided census).

## Executive read

Since the 06-22 audit the *categorical* holes narrowed further (NIA
`int.pow2`/congruent-div-0, NRA CAD-entry slices, string Phase B/C/D word +
regex cores, four soundness P0s closed, Lean reconstruction at 8+ fragments
incl. regex-derivative emptiness). **The remaining gap is three things, in
priority order:**

1. **Raw performance** — Z3 decides all 113 public p4dfa QF_BV in ≤1s; axeyum
   decides 8/113 at 20s. This is the parity-defining number.
2. **Two keystone completions** — (a) the **sat-direction of quantifiers**
   (MBQI model-finding; today's engine is refutation-only outside finite
   domains, which is why quantified LIA/UF rows sit at 0%), and (b) the
   **CDCL(T) migration** (the generic `CdclT<T: TheorySolver>` driver with
   1-UIP exists and online Nelson–Oppen UFLRA/UFLIA is the first route —
   remaining work is *porting* arrays/BV/datatypes onto the spine and the
   default-dispatch ADR, not building the driver).
3. **Encoding depth** on the two hard frontiers — strings past the residual
   unsupported fragment (to_int/replace_re/seq.*) and NRA CAD/nlsat depth
   (ADR-0058's funded arc; deliberately last).

Soundness is holding (DISAGREE = 0 everywhere measured) and the certifying
moat is real and widening (23 audited 100%-dominant rows). **Do not chase new
theory columns**; the breadth tail
([P2.10](track-2-theories/P2.10-breadth-backlog.md)) stays counted, not built.

## Corrections to the 06-22 framing (verified in code)

Three claims in the earlier doc/PLAN text are now stale — two in axeyum's
favor:

- **"Still eager Ackermann today" is wrong.** The online Nelson–Oppen
  UFLRA/UFLIA CDCL(T) route (interface-equality literals, theory propagation,
  1-UIP over the mixed implication graph, non-chronological backjump —
  `cdclt.rs`, `combined_theory.rs`) is **first** in `check_auto` dispatch;
  eager Ackermann is the fallback. The gap is spine *migration + default-on*,
  not spine existence.
- **"No inprocessing" is wrong.** Subsumption/self-subsumption
  (`axeyum-cnf/src/simplify.rs`), BVE (`bve.rs`), and vivification
  (`vivify.rs`) all exist — gated **off by default**
  (`cnf_inprocessing: false`, `cnf_vivify: false` in `backend.rs`). Gap 1's
  first step is therefore a *measurement* (flip the flags on the committed
  pulse), not a build.
- **"Quantifiers = special-case fragments only" is overstated.** A real
  instantiation engine exists: congruence-aware e-matching over the e-graph
  keystone with single/multi-pattern trigger selection (`qinst_egraph.rs`)
  plus an MBQI refutation loop with model-based projection (`auto.rs`,
  capped rounds/instances). The precise hole is that **only the unsat
  direction is reachable outside finite domains** — no MBQI completeness
  machinery / model finder (P2.6 T2.6.5), no MAM bytecode matcher (T2.6.1),
  no production trigger inference with loop detection (T2.6.2).

## The gaps, itemized

### Gap 1 — Performance (the defining chasm)

Measured: p4dfa QF_BV — Z3 113/113 in ≤1s vs axeyum 8/113 at 20s
(`582ecba8`); the `bv_reduction` frontier decides n=32 at ~3.9s and times out
at n=33. Where axeyum decides, it is orders of magnitude slower.

Causes (both concrete): word-level reduction (`solve_eqs`,
`propagate_values`, `elim_unconstrained`, T1.2 passes) and SAT inprocessing
are **built but default-off**; batsat remains the primary SAT core with the
proof-producing CDCL opt-in and slower.

Next increments:
1. **Measure the built levers**: enable inprocessing + the reduction passes
   on the committed p4dfa pulse; re-run PAR-2; split every `unknown` into
   `EncodingBudget` / `SearchBound` / `LargeCnf` / real-timeout. This is a
   flag-flip + measurement, not new code.
2. Compare post-reduction CNF size vs Z3's on the same instances — the
   diagnostic that decides whether the next dollar goes to encoding or
   search.
3. Then (and only if search-bound): SAT-core modernization
   ([P1.3](track-1-engine/P1.3-sat-core-modernization.md)) toward a
   default-capable custom core.

Exit signal: a committed head-to-head where the p4dfa PAR-2 gap *narrows*
(not merely DISAGREE=0). No parity claim without it
([00-north-star](00-north-star.md)).

### Gap 2 — Quantifier sat-direction (the biggest categorical hole)

Measured: quantified LIA 0/12, quantified UF 0/5, BV-quantified ~70%
(finite/bounded routes). The engine can *refute* by instantiation but cannot
*decide sat* outside finite domains.

Next increments, in order:
1. **T2.6.5 MBQI model-finding** for the almost-uninterpreted fragment —
   opens the entire sat direction, which the current architecture
   structurally cannot reach; `unknown`-safe outside the fragment. The 16
   existential/nested census files are the demand signal.
2. T2.6.1 MAM + T2.6.2 trigger inference as the throughput follow-up
   (today's `EGraph::ematch` walk is correct but not incremental).
3. Migrate `axeyum_rewrite`'s bespoke instantiation onto the keystone.

See [P2.6](track-2-theories/P2.6-quantifiers.md).

### Gap 3 — Finish the CDCL(T) migration (build-once, unlock-many)

The driver exists (`CdclT`, EUF + String adapters landed, 1-UIP verified by
fuzz); online NO combination is the first UF+arith route. Remaining:

1. The **default-dispatch ADR** — the routes are built but opt-in ("built,
   not yet banked"); termination/livelock re-verify, then default-on + broad
   re-measure.
2. Port **arrays-lazy** ([P2.2](track-2-theories/P2.2-arrays-lazy.md)) onto
   the spine with real theory propagation — the measured combination tail
   (QF_AUFBV cvc5 56%, QF_AUFLIA 71%, `bug337`/`bug330`, the
   deadline-robustness defect) lives here.
3. Arithmetic theories onto the driver (#35 currently shelved — unshelve
   *after* the default-dispatch ADR proves the spine).

This is the substrate under Gap 2 and the theory-combination tail; see
[P1.5/P1.6](track-1-engine/README.md).

### Gap 4 — Strings residual (largest by count, now a machinery tail)

Measured: QF_S 82/134 (per the scoreboard's latest regeneration), QF_SLIA
18/50, QF_SEQ 26/33. Phases A–D landed; the theory-coupled frontier is
closed on this corpus. The remaining declines are the **unsupported
fragment** — `str.to_int` reasoning beyond bounded, `replace_re`, `seq.*`
depth — plus the sliced follow-ups (concat-unsat via coarse-shape emptiness,
the joint product-automaton search). Each is new machinery in
[P2.7](track-2-theories/P2.7-strings.md), demand-ranked by the corpus census.
The QF_SLIA 36% row is the concentrated target (bounded string+int coupling).

### Gap 5 — NRA/NIA depth (the genuine 15-year catch-up — last)

Measured: QF_NRA cvc5 32/38 (84%), QF_NIA cvc5 33/39 (85%); the bounded
levers (div/mod-0, `iand`, `pow2`, threshold-1, CAD-entry slices) are
**harvested**. The 6–12-row residue is multi-week Boolean-CAD / nlsat /
transcendental work — the funded
[ADR-0058](../research/09-decisions/adr-0058-funded-nra-cad-nlsat-engine-arc.md)
arc, not a slice. Honest `unknown` is acceptable parity here; NIA before NRA
if anything moves.

### Gap 6 — Genuinely absent theories (defer; label honestly)

Zero wiring vs cvc5: separation logic, finite sets/relations, bags,
transcendentals, SyGuS grammar synthesis. Vs Z3: full OMT beyond LIA/BV
(MaxSMT hardening), SPACER-class multi-predicate CHC. All stay in
[P2.10](track-2-theories/P2.10-breadth-backlog.md) / P4.6 — counted, not
built, per the standing "stop adding seeds" rule. cvc5's own precedent:
breadth is allowed *if labeled experimental*.

### Gap 7 — The dominance denominator (the 100%-Pareto path)

Dominance is currently claimed per-row over the **decided** set (23 rows at
100% of decided). Reaching *100% Pareto dominance* means driving **both**
factors: decide% → ~100 per division (Gaps 1–5) **and** audit coverage over
all 35 rows (12 rows still lack a complete audit — chiefly the strings/SEQ/
SLIA, QF_NIA-cvc5, QF_NRA-cvc5, QF_AUFBV-cvc5, QF_AUFLIA, and quantified
LIA/UF rows). Concretely:
- Run `audit_dominance` on every decide-strong row still missing an audit;
  file the gaps it finds as Track-3 work.
- Drive the trusted-reduction ledger to zero — `Fpa2Bv` faithfulness is the
  load-bearing hole; extend Track-3 certificates with every decide-rate
  increment so `Lean unsat` coverage never regresses.
- The scoreboard denominator itself is work: an unmeasured division is an
  unknown gap, not a closed one (grow via `bench --backend solver`).

## Leverage order (2026-07-07)

| # | Move | Gap | Nature |
|---|------|-----|--------|
| 1 | Enable + measure built inprocessing/reduction on p4dfa; PAR-2 + unknown-cause split | 1 | flag-flip + measurement |
| 2a | MBQI model-finding (T2.6.5) — open the quantified sat direction | 2 | build (M–L) |
| 2b | CDCL(T) default-dispatch ADR, then arrays-lazy onto the spine | 3 | ADR + port |
| 3 | Strings unsupported-fragment machinery, QF_SLIA first | 4 | build, census-ranked |
| 4 | Dominance audits for the 12 unaudited rows; ledger → 0 (Fpa2Bv) | 7 | audit + certify |
| 5 | NIA residue, then the ADR-0058 NRA arc | 5 | funded engine arc |
| — | New theory columns / API surface | 6 | deferred, demand-pull only |

Every step is gated by the standing discipline: re-run the committed
scoreboard slice (decide% must move, DISAGREE must stay 0), and for `unsat`
gains extend proof/cert coverage so the Lean ledger does not regress.

## How to keep this honest

- This audit is scoped to the **35 measured baselines**; the true Z3/cvc5
  surface is larger. Growing the measured-division count is itself gap work.
- "Supported an operator" ≠ "decide% rose" until the corpus says so; no
  hand-copied totals (they rotted three times — link the generated
  scoreboard).
- Any nonzero DISAGREE preempts everything above.
