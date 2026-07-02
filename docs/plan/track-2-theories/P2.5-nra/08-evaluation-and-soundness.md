# P2.5 · 08 — Evaluation, soundness gates, and ADRs

How we know each phase worked, and how we never ship a wrong verdict.

## Measured baseline (2026-06-30) — the grounding number

First head-to-head of the **existing** engine (`check_auto`) vs the `z3` 4.13.3
binary on the curated non-incremental corpus (`measure_corpus`, 5 s cap, via
`scripts/mem-run.sh`):

| Division | axeyum decided | z3 decided | DISAGREE | axeyum PAR-2 | z3 PAR-2 |
|---|---|---|---|---|---|
| **QF_NRA** (curated, 36 considered) | 9 → **10 / 36** (28%) | 36 / 36 | **0** | ~7.3 s | 0.01 s |
| **QF_NIA** (curated, 28 considered) | **20 / 28 (71%)** | 28 / 28 | **0** | 2.985 s | 0.025 s |

> **LANDED 2026-06-30 — Boolean case-split (B.0b) shipped: QF_NRA 9 → 10** (commit
> `5ede57f4`). `check_with_nra_dpll` (a lazy-SMT loop deciding each Boolean-skeleton
> cube with `decide_real_poly_constraint`) unlocked the Boolean-structured
> `issue3656` (`(distinct (and (>= c …)(< c …)) (= (* b c) 0))`), which the
> flat-conjunction CAD declines.
>
> **The soundness gate earned its keep.** The first prototype *failed the
> `nra_differential_fuzz`* and was reverted in full before any commit. Full-capture
> diagnosis (task #68) showed the failure was **not** a DISAGREE / wrong verdict —
> it was `"solve returned an error"`: `finish_sat` propagated an **i128 eval-overflow
> during sat-replay** as a `SolverError::Backend` instead of a graceful `unknown`
> (the same class as the `lra.rs` fix, commit `1f615670`). So the case-split was
> **sound all along**; the blocker was a benign robustness gap. Fixing `finish_sat`
> (eval-error → graceful `unknown`; a *definitely-violated* model stays a loud
> alarm) let the case-split land. Verified: `nra_differential_fuzz` 2000 seeds
> **DISAGREE=0, no error**; `nia_differential_fuzz` **DISAGREE=0**; lib 613/613;
> clippy clean.
>
> **Next NRA levers** (the case-split only gains where each cube is within CAD
> reach): most remaining Boolean-structured curated instances (`ones`,
> `simple-mono-unsat`) have cubes with higher-degree / more-variable products
> (`a·b·c·d`) that the CAD *component* decider (`decide_component` at
> `nra_real_root.rs`) declines, or > 2 cross-products the relaxation caps. So the
> next gains are **(Phase D)** widening `decide_two_var_component` /
> `decide_*_cad_nvar` reach (degree/variable) and **(Phase B)** a proper
> incremental-linearization tier lifting the ≤ 2-cross-product cap.

**Reading:** soundness holds (DISAGREE=0). The CAD is decision-complete *in
principle* but decides only 25% of curated QF_NRA within 5 s — axeyum's high PAR-2
(7.5 s vs z3's 0.01 s) says the gap is dominated by **timeouts / not reaching a
verdict**, not wrong answers. The per-instance `explain_corpus` route trace
determines how much is (a) CAD too slow / cell blow-up (→ Phase B cheap tier +
Phase D projection) vs (b) shapes not routed to CAD (→ dispatch/coverage). NIA at
71% is closer; its residual is the UNSAT-side gap (→ Phase E incr-lin).

> This table is the P2.5 scoreboard anchor. **Re-run it after every phase** and
> record the delta here; no decide-rate claim without a re-run
> ([SCOREBOARD](../../../../bench-results/SCOREBOARD.md)).

### Why QF_NRA is 25% — per-instance decline breakdown (`explain_corpus`, 3 s)

The route trace on the 27 undecided QF_NRA instances localizes the gap precisely:

| Decline reason | ~count | Meaning |
|---|---|---|
| `nra: nonlinear abstraction: N cross-products exceed the bound of 2` | **~15** | the ADR-0024 ≤2-cross-product cap rejects N∈{3,6,7,9,12,14,15,20,31,322} |
| `lra: Fourier–Motzkin elimination exceeded the wall-clock/size budget` | **~7** | the LRA relaxation's FM elimination blows the budget |
| `milp: declined (unsupported)` (mixed real+int) | several | the {real,int} fragment isn't routed to a nonlinear path |
| i128 overflow in LRA replay (`approx-sqrt-unsat`) | 1 | `real_cmp` evaluation overflows i128 → backend **error** (should be graceful unknown) |
| parse-error | 1 | `real-numerals` front-end gap |

**The decisive observation:** on *every* multi-variable instance the trace shows
`nra-real-root: declined (not-applicable)` **before** falling to `nra.rs`. So the
**CAD that is "decision-complete" almost never fires on real benchmarks** — its
applicability gate only admits narrow conjunction/strict shapes, and Boolean-
structured / mixed real-int instances bypass it entirely. The 25% is therefore a
**routing + cap** problem, not a missing-algorithm problem.

### Re-prioritized next levers (measured, not assumed)

1. **Widen the CAD applicability gate** so the existing decision-complete CAD fires
   on more multi-variable polynomial conjunctions (the biggest lever — the engine
   exists, it just declines). → [Phase D](06-phaseD-nlsat-cac.md) / dispatch.
2. **Raise/remove the ≤2 cross-product cap** in `nra.rs` now that the algebraic
   path is bignum (the cap's stated reason — "multi-variable can OOM, needs CAD" —
   is exactly what the CAD now provides). → [Phase B](04-phaseB-incremental-linearization.md).
3. **Make the i128 LRA-replay overflow a graceful `unknown`**, not a backend error
   (the [Rational-overflow class](../../../research/)). Quick soundness-hygiene win.
4. **Route mixed real+int nonlinear** into the NRA path instead of `milp: unsupported`.

#### Re-measured 2026-07-01 (after the sign-refutation pass landed, `f9e06baf`)

Re-run of `explain_corpus` on the same QF_NRA `cvc5-regress-clean` set:
**decided 10 → 12** (5 sat, 7 unsat, 25 unknown). The new **sign/zero refutation
before the cross-product cap** (add only the cheap linear sign/zero product
lemmas — no `McCormick`, no SOS — and one bounded LRA-DPLL solve; `unsat`
transfers) captured the *sign-refutable* subset of the 14 cap-declines:
`simple-mono-unsat` and `subs0-unsat-confirm` now `unsat` (DISAGREE=0 on `nra`+
`nia` fuzz). The residual cap/FM declines split as:

- **Fully-free many-product cases** (`metitarski-*`, `poly-1025`, `nt-lemmas-bad`,
  9–20 cross-products, several `{real,int}`): the sign-lemma LRA system (or the
  full relaxation) exceeds the **Fourier–Motzkin `MAX_FM_CONSTRAINTS` budget**
  (`lra_online.rs`/`lra.rs`, ADR-0015). *Both* `check_with_lra` and
  `check_with_lra_within` are FM-based, so the sign pass's reach on these is
  capped by FM, not by the sign reasoning. **The load-bearing next lever is
  FM → an incremental simplex feasibility core** (a new LRA-backend ADR); it
  unlocks both the fully-free cap cases *and* the ~8 standalone `Fourier–Motzkin
  exceeded` declines, and lifts the sign pass's ceiling.
- **`ones`-class** (bounded product `≥ 1` needs the *threshold-1 monotonicity*
  lemmas, not sign alone): those lemmas are what the cap was created to avoid
  (OOM inside one solve), so a monotonicity-augmented pre-check must be
  product-count-gated; low marginal yield (~+1) vs the FM lever.
- **Division-heavy** (`issue9164-2`, `1/(a/b) > a²/a`): tied to the free-division
  `/0` witness gap (above).

So the refreshed priority is: **FM → simplex (biggest, unblocks both cap and FM
declines)** > CAD-gate widening > mixed-int routing > monotonicity pre-check.

NIA at 71% is closer; its residual is the UNSAT side → [Phase E](07-phaseE-nia.md)
incremental linearization over UFLIA.

#### Re-measured 2026-07-01 (CAD-gate widening: coprime-split in the projection)

Re-run of `explain_corpus` on the QF_NRA `cvc5-regress-clean` set (4 s cap, via
`scripts/mem-run.sh`): **decided 13 → 20** (`sat` 6 → 9, `unsat` 7 → 11, `unknown`
24 → 17; the parse-error is unchanged). **DISAGREE = 0** — every one of the seven
newly-decided instances matches its declared `set-info :status`:

| Instance | verdict | declared |
|---|---|---|
| `issue3003` | sat | sat |
| `mult-po` | sat | sat |
| `solve-eq-small-qf-nra` | sat | sat |
| `coeff-unsat-base` | unsat | unsat |
| `red-exp` | unsat | unsat |
| `simple-mono` | unsat | unsat |
| `zero-subset` | unsat | unsat |

> The 13-baseline is the current HEAD re-measurement (the earlier "12" was at
> `f9e06baf`; the sign-refutation and other work since moved it to 13). `13 → 20`
> is the measured delta of *this* change alone.

**What the route trace actually showed (measured, not assumed).** Instrumenting the
CAD *component* decider (`decide_component` / `project_strict` in
`crates/axeyum-solver/src/nra_real_root.rs`) revealed that the dominant decline on
these instances was **not** a degree / variable-count / product-count cap. On every
one of `simple-mono`, `mult-po`, `coeff-unsat-base`, `ones`, `zero-subset` the
projection declined with `pairwise Res ≡ 0 (shared factor)`: two constraint
polynomials share a common factor in the elimination variable (e.g.
`xz − yz = z·(x − y)`, `a² − 3ab = a·(a − 3b)`), so their Sylvester resultant
vanishes identically, which the delineability-preserving projection conservatively
declined. Raising `MAX_MULTI_SYLVESTER_DIM` / the cell budget would move **none** of
these; the blocker is a *coprimality* gap, not a size cap.

**The fix — coprime-split (McCallum-style irreducible-factor projection).** Before
each projection level the decomposition polynomials are refined so no distinct pair
couples by exact divisibility: whenever a non-constant `a` exactly divides a distinct
`b`, `b` is replaced by the cofactor `b / a` (fixpoint, bounded by
`MAX_COPRIME_SPLIT_ITERS`). This is a *verdict-invariant* refinement — the union of
zero sets `Z(b) = Z(a) ∪ Z(b/a)` is unchanged, so the cell arrangement is identical,
and each atom is still evaluated on its **original** polynomial at every rational
sample. It only removes the shared factor that makes `Res ≡ 0`, letting the existing
decision-complete CAD proceed. New pure-Rust helpers: `multipoly_exact_divide`
(exact multivariate division under the admissible grlex leading-term order),
`coprime_split`, and `mono_key_cmp_grlex`; applied in `project_strict` (covers both
the strict and non-strict N-var recursions) and in the four component deciders
(`decide_strict_cad_nvar`, `decide_nonstrict_cad_nvar`, `decide_strict_cad_two_var`,
`decide_nonstrict_cad_two_var`).

**Soundness held.** `sat` still requires a replay-checked rational witness; `unsat`
is still the exhaustive cell/CAD coverage over the (unchanged) arrangement. Verified:
`nra_differential_fuzz` + `nia_differential_fuzz` (z3-gated) **DISAGREE = 0**; lib
640/640; nra integration suites green; 7 new unit tests (grlex admissibility, exact
division recovering the monotone-product cofactor, non-factor rejection, split
idempotence, and a `simple-mono`-style all-strict 3-var `unsat`).

**Residual on this corpus (still declining).** `ones` (`b·c·d < 1` with `b,c,d ≥ 1`)
no longer hits `Res ≡ 0`, but the 4-var **degree-4** non-strict decomposition still
declines deeper in the CAD — it needs the *threshold-1 monotonicity* argument the doc
already flags as low marginal yield. The remaining `unknown`s are the many-product
`{real,int}` `metitarski-*` / `poly-1025` / `nt-lemmas-bad` cases (FM budget / mixed
int-real routing) — the FM → simplex lever, unchanged by this pass.

### ROOT CAUSE (2026-06-30): Boolean structure, not the polynomial algorithms

Inspecting the small undecided instances shows the real bottleneck. They are
**Boolean combinations of nonlinear atoms**, e.g.:
- `ones`: `(>= a 1)…(>= d 1) ∧ (or (= a 1)(= b 1)(= c 1)(= d 1)) ∧ (< (* a b c d) 1)`
- `simple-mono-unsat`: `(or (= a 4)(= a 3)) ∧ (> b 0) ∧ (> c 0) ∧ (< (* a b c d d) 0)`
- `issue3656`: `(distinct (and (>= c …)(< c …)) (= (* b c) 0))`

axeyum's CAD + sign-cell decider are mathematically strong but **only accept a flat
conjunction** (`decide_real_poly_constraint` declines on *any* non-conjunctive
structure; `decompose_multivariate` declines on coupled shapes). The moment an
`or` / `distinct` / `ite` appears — i.e. essentially every real benchmark — the
whole NRA stack declines and falls to the ≤2-cap `nra.rs`. **There is no
DPLL(T)/case-split over the Boolean skeleton feeding conjunctions (cubes) to the
CAD.** That missing lazy-SMT loop — not the polynomial math — is the dominant
QF_NRA gap.

**This reframes the priority order:**
1. **Boolean-case-split over NRA atoms (the keystone lever).** Enumerate the
   Boolean skeleton's satisfying assignments of theory atoms (DPLL(T)-lite, bounded
   cube count) and run the *existing* flat-conjunction CAD/decider on each cube;
   all-unsat ⇒ `unsat`, any cube `sat` (replay-checked) ⇒ `sat`, too many cubes /
   any cube `unknown` ⇒ `unknown`. Sound by construction (case analysis). This is
   the tractable precursor to the full [CDCL(T) loop (P1.5)](../../track-1-engine/P1.5-cdcl-t-loop.md)
   and is the **single highest-leverage NRA increment** — it unlocks the strong CAD
   on real (Boolean-structured) benchmarks. *(Next task; see #66.)*
2. Then the ≤2 cap matters less (cubes are conjunctions the CAD handles); raise it
   for the residual non-CAD multivariate cubes.
3. Graceful `unknown` on the LRA-replay i128 overflow (soundness hygiene).

The full CDCL(T) loop (P1.5) generalizes step 1 to incremental, conflict-driven
theory propagation; the bounded case-split is the measured-justified first slice.

## Measurement protocol (no claim without a re-run)

- **Corpus:** the public QF_NRA / QF_NIA / QF_UFNRA divisions (the gitignored NAS
  symlink + `corpus/public-curated/`), measured with `bench` `--backend solver`
  (`check_auto`) head-to-head against the `z3` binary.
- **Metric:** decide-rate (sat+unsat / total) and PAR-2, per division, vs Z3
  4.13.3, recorded in [bench-results/SCOREBOARD.md](../../../../bench-results/SCOREBOARD.md).
- **Rule:** *no decide-rate claim without re-running the scoreboard.* Each phase's
  exit criterion is a **measured** delta, not an asserted one.
- **Baseline to beat:** the residual hard instances on measured divisions are
  nonlinear (e.g. issue5836-2 = QF_UFNRA). Phase B should move the needle first;
  Phase D closes the completeness gap.
- **64 GB cap:** all runs via `scripts/mem-run.sh` — the multivariate blow-up is
  exactly what OOMs the box.

## DISAGREE=0 (the soundness floor)

Every phase is gated by the z3-differential fuzzes before commit:

- `crates/axeyum-solver/tests/nra_differential_fuzz.rs`
- `crates/axeyum-solver/tests/nia_differential_fuzz.rs`
- (shared multivariate path) run **both** when touching either decider.

These found 4 real defects the 1370+ unit tests missed (wrong-unsats from
`isolate_roots` midpoint, `cell_samples` overflow, `lift_candidate` positive-dim
collapse; + a nested-UF projection crash). The new code is far larger surface —
**expand the fuzzers** to generate multivariate polynomials, transcendental atoms,
and `iand` constraints as those land.

### Known completeness gap — free real division `/0` witnesses (tracked follow-up)

There is a genuine **semantic divergence** on real division by zero that the
solver currently reconciles to a sound `unknown`, at the cost of decide-rate:

- **axeyum's ground evaluator commits to `x/0 = 0`** (a totality convention, like
  SMT-LIB `bvudiv x 0 = all-ones`), tested by `axeyum-ir`'s
  `real_division_evaluates_exactly`. Because the evaluator is the trusted anchor
  for every `sat` replay (and for the `nra_differential_fuzz` `Replay::Violated`
  gate), any model that requires `x/0 ≠ 0` is refused.
- **Z3/SMT-LIB leave real `/0` unspecified** — a free value the solver may choose.
  `eliminate_real_div` already models this faithfully (fresh `r`, `(y=0) ∨ (x=r·y)`,
  + **complete** Ackermann div-congruence), so the eliminated form is
  equisatisfiable with Z3's semantics.

Net: on a query that *forces* `y=0` and constrains `x/y` to a nonzero value (e.g.
`y=0 ∧ x=5 ∧ x/y=100`), Z3 says `sat` but axeyum cannot emit a model its own
`/0=0` evaluator accepts, and a definite `unsat` would be a wrong-unsat vs Z3. The
only verdict sound under both commitments is **`unknown`** (see
`crates/axeyum-solver/tests/nra.rs::real_division_by_zero_is_sound_unknown`).
The `check_with_nra` replay guard (`b38c0439`) + in-engine replay retarget
(`a06dc46a`) enforce this; they close a real congruence-gap wrong-sat.

**Recovery route (decide-rate follow-up, not a soundness bug):** make free-division
witnesses first-class — the returned `Model` carries the solver's chosen value for
each `(/ a b)` term (the internal `r`), and the evaluator/replay consult it for the
`b=0` case instead of the fixed `0`. Then these promote from `unknown` to `sat`,
matching Z3, while the congruence axioms keep multi-occurrence `x/0` consistent.
This is the div analogue of a first-class uninterpreted-function interpretation in
the model; scope it alongside the Phase-B lemma work.

#### LANDED 2026-07-02 — first-class `/0` division witnesses (`unknown → sat`)

The recovery route above shipped. The interpretation is now an **additive part of
the model**, exactly like an uninterpreted-function interpretation:

- **`axeyum-ir` (`Assignment`, `eval.rs`):** a new `real_div_zero` map (numerator
  value → chosen quotient; lazily boxed so the common witness-free assignment
  pays one word) with `set_real_div_zero` / `real_div_zero` / `real_div_zeros`
  accessors. `Op::RealDiv`
  now consults it when the denominator evaluates to `0`: a hit by the **numerator
  value** returns the chosen quotient, a miss keeps the total `x/0 = 0` convention.
  An empty map is byte-for-byte today's behavior, so the evaluator stays the trust
  anchor — the witness is model data, not an evaluator change.
- **`axeyum-solver` (`Model`):** carries the same map (sorted for determinism by an
  overflow-free `(numerator, denominator)` key, *not* the panic-prone `Rational`
  `Ord`), plumbed through `to_assignment`.
- **`nra.rs`:** after the internal engine returns `Sat` on the div-**eliminated**
  form, `div_zero_witness` reads each eliminated `(x, y, r)` whose divisor `y`
  evaluates to `0` and records `value(x) → value(r)`. Two occurrences with the same
  numerator value that disagree on `r` (a division-congruence violation — impossible
  in a real model given the Ackermann axioms) **decline loudly to `unknown`**, never
  guess. The witness is injected into the replay assignment (so the in-engine replay
  against the *original* division semantics accepts the forced `x/0` model) and
  attached to the returned `Model` (so the outer `check_with_nra` guard and any
  consumer validate it). Internal `!div_` vars are no longer leaked as model symbols.

- **Witness plumbing through the preprocessed dispatch** (the fuzz caught this):
  the first cut passed the direct `check_with_nra` tests but the
  `nra_differential_fuzz` sweep failed at seed 51 (`1/w < 0`, `w` free) with a
  **wrong sat** — through the default `solve` route, the preprocessing layers
  (`dispatch_reduced` in `auto.rs`, `replay_preprocessed_model` in
  `preprocess.rs`) rebuild the returned `Model` symbol-by-symbol and were
  **dropping the witness after their own replay had already passed under it**
  (the reconstruction trail clones the assignment, witness included). Both
  rebuild sites now carry `real_div_zeros` through — exactly as
  `dispatch_reduced` already carried uninterpreted-function interpretations for
  the same reason.

Soundness is unchanged in kind: `sat` still requires a replay-checked model under the
ground evaluator, now with the witness consulted; no `unsat` path is touched (the
witness helpers only transform `Sat` results). For **nested** divisions the witness
build can mis-key an entry (the divisor is evaluated before enrichment), but that is
decline-only: the enriched replay against the original assertions is the acceptance
gate, so a bad witness can only miss (`unknown`), never fabricate a `sat`. Gates:
`axeyum-ir` full suite green (incl. new hit/miss eval test); `axeyum-solver` lib
640/640 + full integration sweep (one pre-existing red in
`pbls.rs::returns_unknown_for_an_unsupported_sort`, confirmed failing at clean HEAD,
unrelated); `nra` integration green with the div-by-zero test rewritten to assert
`sat` + a replaying witness, plus multi-occurrence-consistency and
contradictory-atoms (no-wrong-sat) cases; **both** `nra_differential_fuzz` and
`nia_differential_fuzz` (z3-gated, division shapes included) green on the final code
— **DISAGREE = 0, every axeyum `Sat` replayed**; clippy `-D warnings` clean.

**Measured effect** (`cvc5-regress-clean` QF_NRA, `--backend solver --compare-z3`,
10 s, 4 jobs, via `scripts/mem-run.sh`): **decided 20 → 21 (sat 9 → 10), unknown
17 → 16, PAR-2 9.194 → 8.660, DISAGREE = 0** against a same-command clean-HEAD
re-run. The mover is `cli__regress1__arith__div.06` (`n=0 ∧ x/n=0 ∧ y/n=1`,
declared/Z3 `sat`) — exactly the forced-div-by-zero class. `issue9164-2`
(`1/(a/b) > a²/a`, nested division) still declines: it additionally needs the
FM → simplex lever above. The committed baseline
`bench-results/baselines/qf-nra-cvc5-regress-clean-solver-vs-z3-10s.json` and the
[SCOREBOARD](../../../../bench-results/SCOREBOARD.md) QF_NRA row are refreshed (the
row also absorbs the prior sign-refutation/coprime-split landings that had not been
re-measured on this route: committed row 9 → 21 decided).

## Per-phase soundness obligations

| Phase | `sat` checkable by | `unsat` certified by | `unknown` triggers |
|---|---|---|---|
| A | (infra; differential vs `nra_real_root.rs`) | — | — |
| B incr. lin. | replay (drop fresh vars) | linear refutation retained | no refinement / budget |
| C ICP | **exact witness only** (δ-sat ⇒ unknown) | contraction trace | δ-small box / transcendental sat |
| D CAC | algebraic assignment `sign_at` replay | **covering + projection chain (re-checkable)** | budget / degree / time |
| E NIA | integer witness replay | Layer 1 relaxation / Layer 2 over-approx | branch depth / width ceiling |

**Non-negotiable invariants** (audited by dedicated tests):
1. No tier ever returns `sat` from a non-replayable witness (ICP δ-sat audit).
2. No tier converts another's `unknown` into a verdict without independent
   justification.
3. Width-ladder bit-blast (E Layer 4) never emits `unsat` for unbounded integers.
4. SOS/SDP certificates (if ever used) re-checked in exact rationals, never trusted
   from floating point.

## Proof / Lean-parity obligations (Track 3)

- Every new `unsat` route gets an independent checker or a
  [trust-ledger](../../track-3-proof-lean/P3.0-trust-ledger.md) entry, ideally an
  Alethe reduction proof ([P3.5](../../track-3-proof-lean/P3.5-reduction-proofs.md)).
- **CAC coverings are the natural certificate** — re-derivable by replaying
  projections. This is *why* we chose CAC over NLSAT.
- The degree-2 **SOS fragment already reconstructs to kernel-checked Lean** — extend
  it as the certified-nonlinear-`unsat` seed (p>0 cases, evidence wiring).

## ADRs to write (in order)

1. **ADR-A0** — `axeyum-poly`: a pure-Rust polynomial & real-algebraic core
   (bignum strategy, representation split, no-C/C++ + WASM constraints). *(Phase A)*
2. **ADR — incremental-linearization loop** semantics & lemma set, the lifted
   cross-product cap, transcendental UNSAT-only stance. *(Phase B)*
3. **ADR — ICP δ-sat ⇒ unknown** discipline and transcendental handling. *(Phase C)*
4. **ADR — CAC as the complete oracle** (vs NLSAT), the covering certificate
   format, and the SMT-LIB-division undecidability boundary. *(Phase D)*
5. **ADR — NIA portfolio**: undecidable-honest design, SAT/UNSAT layer split,
   width-ladder repositioning, `iand` semantics, div/mod axiomatization. *(Phase E)*

## Definition of done for P2.5

- `axeyum-poly` exists, pure-Rust, WASM-green, property-tested.
- Tiered NRA engine: incremental linearization → ICP → CAC, with measured
  decide-rate on public QF_NRA approaching Z3/cvc5 and **DISAGREE=0**.
- NIA portfolio decides UNSAT instances the bounded ladder cannot, measured.
- Every `unsat` route carries a checker / trust-ledger entry / Alethe proof; CAC
  coverings re-checkable.
- All five ADRs merged; foundational DAG + research-questions updated; STATUS.md
  reflects the measured pulse.
