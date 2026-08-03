# Review synthesis — what nine branch reviews found

Date: 2026-08-01. Reviewers: nine independent read-only agents, one per branch,
each with web access and instructions to be blunt.

This file records what survived review, what did not, and the corrections that
change the work. **Read the corrections before planning any phase.**

## Verdict roll-up

| Branch | Verdict | One-line reason |
|---|---|---|
| Bridge catalogue | needs revision | Edge identity, validation method, and edge set were all wrong |
| Direction algebra | needs revision | Three-way classification is inadequate; direction is per-instantiation |
| Search algorithms | needs revision | MCTS is at the wrong locus; online learning breaks determinism |
| Eqsat + walk-back | needs revision | The e-graph is not a saturation engine; the walk-back is stronger than claimed |
| Evaluation harness | needs revision | Labels are excellent; difficulty is degenerate — no learning signal |
| Lateral CAS bridges | pending | — |
| Parallel / cube-and-conquer | correct core, two wrong facts | Prerequisite claim holds; repo has far more than credited |
| Agentic loop | yes, but narrow | The pattern already exists in `abduct.rs`; the gap is *unsupported*, not *unknown* |
| Lean / Comparator | pending | — |

No branch came back "sound as proposed." That is the useful outcome.

## Correction 1 — the bridge graph is not 14 edges, and `TrustId` is not the edge set

The proposal treated `TrustId`'s 14 variants as the bridge set and
"source fragment → target fragment" as edge identity. Both are wrong.

- `auto.rs` carries **45 distinct route labels** (43 literals + 2 dynamic).
- Dispatch is conditioned on a **10-flag `Features` vector**
  (`auto.rs:7171-7191`), finer than the 10 atlas rows — e.g. the `bv2nat-blast`
  guard (`auto.rs:3026-3031`) describes roughly QF_BVLIA, which has *no atlas row*.
- Guards include **opaque Rust shape probes** returning `Option`
  (`blast_bv2nat_linear`, `decide_real_poly_constraint`), config flags, and a
  **runtime cost measurement** (`reduction_shrinks_encoding`, `auto.rs:1519-1550`,
  comparing lowered AIG node counts) that cannot be a static edge label.
- At least a dozen reductions in `auto.rs` carry **no `TrustId` at all**:
  `lift_arith_ite`, the four `preprocess_reduce` passes, skolemization, the
  coercion relaxation, MILP LP-relaxation, `nia-linearize`, `int-real-relax`,
  the lazy-BV abstraction.
- Conversely `SatRefutation`, `Farkas`, `Sos`, `Diophantine` are **terminal
  one-sided certificates**, not bridges — modelling them as edges is a category
  error.

**Consequence:** edge identity is the *route attempt* (the stable `&'static str`
already threaded through `RouteTrace`), with atlas fragments as advisory
annotations and `trust_ids` as a cross-reference field.

## Correction 2 — "replay the existing RouteTrace logs" is impossible

`RouteTrace` has no serde, is never persisted by `axeyum-bench`, and covers only
the quantifier-free `check_auto` region — the quantifier pipeline in `solve()`
(`auto.rs:318` onward) is entirely untraced. There are no logs to replay.

**Consequence:** validation must be **re-run based** (feasible; the harness
pattern exists in `crates/axeyum-solver/tests/route_trace.rs`), and it validates
only up to two known blind spots: silent `Ok(None)` guard skips, and the
flattening of reduced-query attempts into the outer trace by `dispatch_reduced`
(`auto.rs:1566`). Both need additive changes before the validator has teeth.

**Also consequence:** do not hand-transcribe 8,616 lines into JSON. Generate the
catalogue from a Rust route registry and golden-test it — the exact pattern
`trust_ledger_markdown` already uses (`trust.rs:343-387`).

## Correction 3 — direction is per-instantiation, not per-reduction

`IntBlast` is the disproof of a static direction column: the **width ladder** is
an under-approximation (sound for `Sat` only, `auto.rs:3470-3476`) while the
**proven-box** sub-case is an equivalence (`trust.rs:67-76`). One `TrustId`, two
opposite directions, selected by a per-query precondition. `Fpa2Bv` is the same
per *operator set*. A static direction table would itself be a soundness bug.

The three-way lattice is also too small. The review's actual algebra:

- Direction = subsets of `{SAT, UNSAT}` licensing verdict transfer; composition
  is **intersection** (commutative, associative, idempotent monoid, identity
  `Equivalence`, absorbing `Heuristic`).
- **Guarded direction**: applying an edge to a query *returns* a direction plus a
  witness fingerprinted to that exact input.
- **Model-lift is a separate axis** from direction: direction licenses attempting
  a `sat`; replay validates it.
- **CEGAR is a combinator, not an edge**: `cegar(over_approx, refiner)` *derives*
  `Equivalence`, degrading to `OverApprox` on budget exhaustion.

And the sharpest finding: **direction is primarily an UNSAT-soundness
mechanism.** The Hard Rule already forces every `sat` to replay against the
original term, which catches under-approximation violations end-to-end regardless
of chain shape. But `Evidence::Unsat(None)` is a legal terminal — a mis-licensed
unsat ships silently with no analogous backstop.

## Correction 4 — `axeyum-egraph` is congruence closure, not equality saturation

`crates/axeyum-egraph/src/lib.rs` (2,355 lines) is a proof-producing,
backtrackable congruence-closure engine with e-matching — a CDCL(T) and
quantifier-instantiation keystone. It has **no rewrite-rule application engine,
no saturation loop, no cost functions, no extraction, no e-class analyses, and no
deferred rebuilding**. "Use equality saturation, the crate already provides it"
conflates the substrate (excellent, real) with the driver (absent).

The inverse is the good news: **the walk-back is stronger than claimed.** The
whole chain already works end to end for EUF —
`explain_steps` (Nieuwenhuis–Oliveras proof forest, `lib.rs:1154`) → Alethe
`eq_transitive`/`eq_congruent`, self-validated by `check_alethe` before return →
Lean-kernel-checked proof terms (`reconstruct/equality.rs:315-367`), plus an
independent non-proof-forest re-validator `check_congruence` (`lib.rs:1311`).

**Consequence:** the usual situation is inverted. Axeyum can walk back but cannot
yet saturate. Say that in the plan; three M-sized tasks of new code sit behind
the word "saturation."

## Correction 5 — the reward signal does not exist yet

The claim "the foundational artifacts already ARE the reward signal" is half
right and half fatal.

Verified counts (2026-08-01, `main` at `5dbae3a0`):

- `artifacts/examples/math/` holds **174 pack directories**, not ~50.
- **1,131 checks: 581 sat, 414 unsat, 136 not-run** (lean-horizon, no ground
  truth). Usable labels: **995**.
- **243 `.smt2` files**: QF_LRA 192, QF_UF 23, QF_LIA 18, QF_BV 10.
- Largest instance: **28 lines, 11 declarations**. Two are fully ground constant
  formulas decided by constant folding.
- `docs/curriculum/curriculum.toml` has **23 nodes**, not 342 (342 is the line
  count). Decidability: 16 bounded, 6 computable, 1 decidable, **0 undecidable**.
- `just foundational-resources` runs **pure Python** — a 41,696-line validator
  with 834 distinct validation identifiers. **The Rust solver is never invoked by
  that gate.** Only ~a dozen pack instances reach real bit-blast+DRAT, via
  `crates/axeyum-solver/tests/math_resource_{bv,lia,lra,uf}_routes.rs`.

Label quality is genuinely strong — sat rows carry replayed witnesses, unsat rows
carry exhaustive enumeration or Farkas/Alethe/DRAT evidence. But **difficulty is
degenerate**: every instance decides in milliseconds. A policy trained on them
receives zero discriminative reward. "No signal" is the default outcome, not a
tail risk.

**Consequence:** labels and trust classes from the packs; **difficulty from the
`progress_frontier` parametric families** (difficulty knob `N` per family,
oracle-free self-checks, committed ratchets — this file is the closest existing
thing to the proposed harness), the `axeyum-scenarios` generators (scalable
width/rounds), and the public corpora + `axeyum-bench`. And gate everything on
**G1**: measure the VBS–SBS gap first.

## Correction 6 — MCTS is at the wrong locus

The bridge chain space is **small enough to enumerate**: with composability and
reaches-a-decider constraints, at most a few hundred chains survive. Enumeration
is trivially cheap; *executing* chains is what costs. Within one query under a
timeout you get 3–5 censored observations — no bandit converges in 5 pulls, and
per-instance variance swamps within-instance signal.

The literature is unambiguous about placement:

- **MCTS offline over a corpus** — Z3alpha (IJCAI 2024) does layered/staged MCTS
  offline and emits a static strategy; 42.7% more QF_BV instances than Z3 default.
- **Selection plus capped scheduling online** — SATzilla presolvers/backup,
  MedleySolver sequences, aspeed timeout-optimal schedules.

And **online learning collides with the determinism promise**: MedleySolver-style
in-flight updates make verdicts depend on query arrival order.

**Consequence:** split into a nondeterministic **offline learner** that emits a
committed, versioned, hash-pinned policy artifact, and a pure **deterministic
online executor** that is a function of (query, policy, budgets, seed). Learning
becomes a data-release process. FastSMT is the precedent: ship the synthesized
program, not the learner.

## Correction 7 — the parallel branch undercounted the repo

`crates/axeyum-cnf` is **24,836 lines across 18 modules**, not a minimal
Tseitin+DRAT crate. It has Luby + Glucose EMA restarts, phase saving with target
rephasing, `reduce_db`, a deterministic conflict-cadence budget model, **LRAT
already implemented** (`check_lrat`, `write_lrat`, `elaborate_drat_to_lrat`), BVE
/ vivification inprocessing, and a 4,556-line Alethe module. `axeyum-bench`
already has rayon with `--jobs`, per-worker stack sizing, and ADR-0235 killable
subprocess isolation — the exact skeleton a cube worker needs.

Two claims corrected: cube-and-conquer appears **three times** in
`beyond-bit-blasting.md` (not once), and the SAT core's standing **is partially
measured** — ADR-0220/0221 ran 244 CNFs through BatSat, the proof core, Z3
Boolean, and Kissat 4.0.4 with full agreement, the proof core 2.627× faster than
fresh BatSat; but PLAN.md:8381 records ~9 public QF_BV instances that are
explicitly search-bound where kissat-class CDCL wins and the native cores miss.

The prerequisite claim itself holds, quantitatively: Pythagorean triples took
~35,000 CPU-hours solving plus ~16,000 verifying, 10⁶ cubes, ~200 TB of DRAT
compressed to a 68 GB certificate; Schur 5 took 14+ CPU-years with 10.3M
top-level cubes and 65 billion subproblems, where **DRAT→LRAT conversion (20.5
CPU-yr) plus checking (15.6 CPU-yr) cost more than solving (14 CPU-yr)**.

And the blocking local fact: `check_drat` is **in-memory with linear-scan
deletion and unindexed RUP** — roughly quadratic and RAM-bound. It cannot check
one hard cube's proof, let alone an aggregate.

## Correction 8 — the agentic loop's target is smaller than assumed

`crates/axeyum-solver/src/abduct.rs` already states the required architecture in
its module doc: candidate generation is entirely untrusted; soundness comes only
from re-checking every candidate with the trusted decider before it is returned.
The agentic loop is that module with an LLM as generator. The precondition
FunSearch and AlphaEvolve needed — a fast, automatic, ungameable evaluator —
axeyum already has.

But the measured gap is dominated by `DeclineReason::Unsupported`, not by
`unknown-with-a-clever-encoding`. Curated residual is 762/992 decided; strings
residual is "QF_SLIA 21 unsupported + 4 unknown"; quantified logics sit near zero
because **mechanisms are missing, not because search lacks imagination**. No
runtime LLM loop converts `Unsupported` — only engine code does.

**Consequence:** the loop's honest runtime target is the `Incomplete`/`Budget`
slice plus open-conjecture exploration, and its most durable output is artifacts
that get **baked back into deterministic routes**. Cost anchors: Haiku 4.5
best-of-8 over the ~230-problem curated unknown bucket is **$12–20 per sweep**;
Sonnet $50–70; an Opus pass on ~30 survivors $15–25. Pilot budget ≤ $100.

## What survived unchanged

- The identity argument. Every reviewer independently reached the same
  conclusion: the checker is the asset, and it is what makes searching safe.
  The parallel reviewer went further — the identity sentence **licenses external
  solvers as untrusted conquer engines**, because subprocess DIMACS-in/proof-out
  transfers no trust and adds no link-time C/C++ dependency.
- The funnel diagnosis (bridge graph points downward toward SAT; lateral moves
  are scarce) was not contradicted by any reviewer who touched it.
- Trust-cost as a budget dimension distinct from step count.
- The proposal-ledger pattern for making nondeterministic discovery yield
  reproducible results.

## Cross-cutting themes

1. **Measure before building.** Three phases independently converged on a
   measurement gate (G1, G2, G3). None of the expensive work should start before
   its gate reports.
2. **The `auto.rs` refactor is the riskiest engineering in the track.** 8,616
   lines of order-dependent fast paths. The only safe path is a policy-v0 that
   encodes today's fixed order as data and is proven byte-identical to legacy
   dispatch on the full corpus *before* any learning exists.
3. **Generate, don't transcribe.** Three separate artifacts (bridge catalogue,
   direction ledger, policy) should be generated from Rust and golden-tested,
   following `trust_ledger_markdown`. Hand-maintained JSON mirroring code is the
   top rot risk in every branch.
4. **Every new mechanism needs a soundness-negative generator**, per CLAUDE.md's
   `a946f925` lesson: chain-direction flips, corrupted certificates, dropped
   cubes, adversarial LLM proposals. A gate that only sees honest inputs is blind
   where it matters.
