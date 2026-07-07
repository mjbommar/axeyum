# P2.5 · 09 — The next arithmetic decide-rate lever: census + sliced decomposition

> **Scope of this doc (2026-07-06).** The string program has reached its
> theory-coupled ceiling (QF_S 58 %, QF_SLIA 36 %); the residual decide-rate gap
> vs z3/cvc5 is now dominated by **nonlinear arithmetic**. This is a *census +
> decomposition* — it names every arithmetic `unknown`/`unsupported` instance,
> classifies what each needs, characterizes what the existing NRA/CAD machinery
> already decides and why the residue escapes, and lays out the next lever as
> **bounded, individually-shippable slices ordered by ROI**. It lands **no source
> change**. The measured anchors are the committed baselines under
> [`bench-results/baselines/`](../../../../bench-results/baselines/) and
> [SCOREBOARD.md](../../../../bench-results/SCOREBOARD.md); the engine
> characterization is grounded in `nra.rs`, `nra_even_power.rs`,
> `nra_real_root.rs` (read 2026-07-06). It extends
> [00-current-state](00-current-state.md), [07-phaseE-nia](07-phaseE-nia.md), and
> [08-evaluation-and-soundness](08-evaluation-and-soundness.md); the orchestrator
> should link it from PLAN.md / STATUS.md (this lane may not edit those).

## 1. ROI census — every arithmetic decline, classified

Read straight from the committed baselines (10 s cap, z3-binary ground truth).
The arithmetic divisions with headroom:

| Division | Baseline | Files | Decided | Decide% | Unknown | Unsup |
|---|---|---:|---:|---:|---:|---:|
| QF_NIA | `qf-nia-cvc5-regress-clean` | 39 | 21 | 54 % | 10 | 8 |
| QF_NRA | `qf-nra-cvc5-regress-clean` | 38 | 26 | 68 % | 11 | 1 |
| QF_NIA | `qf-nia-curated-iand` | 3 | 1 | 33 % | 2 | 0 |
| QF_LRA | `qf-lra-cvc5-regress-clean` | 11 | 9 | 82 % | 2 | 0 |
| QF_LIA | `qf-lia-cvc5-regress-clean` | 11 | 10 | 91 % | 1 | 0 |
| QF_NIA | `qf-nia-synthetic-graduated` | 32 | 32 | 100 % | 0 | 0 |
| QF_NRA | `qf-nra-synthetic-graduated` | 33 | 30 | 91 % | 3 | 0 |

The two rows with real, *cheaply reachable* headroom are the **cvc5-regress**
QF_NIA (18 undecided) and QF_NRA (12 undecided). LIA/LRA residue is huge-instance
simplex scaling (`miplib-*`, 16 k-node), a separate perf track — not this lever.

### 1a. QF_NIA cvc5-regress — 10 unknown + 8 unsupported

| Instance | Verdict | Shape (what it needs) | Class |
|---|---|---|---|
| `arith__div.03` | unsat | `n>0 ∧ x≥n ∧ (div x n)<1` — variable-divisor Euclidean + sign lemma | **A · div/mod-linearize** |
| `arith__div.08` | unsat | nested `(div n n)` idempotence, `n=0` pin | **A · div/mod-linearize** |
| `arith__mod.02` | unsat | `n≠0 ∧ (mod n n)>0` — Euclidean `0≤r<|n|` + `n(1−q)=r` | **A · div/mod-linearize** |
| `arith__mod.03` | sat | `(mod x n)<0 ∧ (div x n)<0` — model over Euclidean vars | **A · div/mod-linearize** |
| `arith__issue3480` | unsat | `a=7−a² ∧ …(div 7 c)(div 45 b)` — div/mod ∧ nonlinear `a²` | **A+ (coupled)** |
| `nl__learned-rewrite-int-mod-range` | unsat | `abs`, `sgn`, mod-range interval reasoning | **A+ (mod range)** |
| `nl__nl-eq-infer` | unsat | `i=−2s+i²` quadratic identity inference | **E · nl-int (engine)** |
| `nl__iand-native-2` | unsat | `((_ iand 4) x y)>0 ∧ x·y=0 ∧ x+y=15`, `x,y<16` | **B · iand bounded-blast** |
| `nl__iand-native-granularities` | unsat | `or((_ iand 5),(_ iand 6))≥32`, `x+y≤32` | **B · iand bounded-blast** |
| `nl__ext-rew-aggr-test` | sat | dag=610, sym=88 — huge rewrite stress | **E (large)** |
| `nl__pow2-native-1..7` (7×) | — | `(int.pow2 x)` operator unparsed | **C · pow2 operator** |
| `parse-skolem-test-int-div-by-zero` | sat | `:parse-skolem-definitions`, `@int_div_by_zero` | **niche parser** |

### 1b. QF_NIA curated-iand — 2 unknown

`iand-native-2`, `iand-native-granularities` — the **same two** `((_ iand k) x y)`
instances (a 3-file baseline, so closing them moves 1→3 = 33 %→100 %). Class **B**.

### 1c. QF_NRA cvc5-regress — 11 unknown + 1 unsupported

| Instance | Verdict | Shape (what it needs) | Class |
|---|---|---|---|
| `nl__very-simple-unsat` | unsat | `(= (* a a) (- 2))` — a²≥0 refutes `=−2` | **D · even-power-equality** |
| `parser__real-numerals` | sat | `(define-fun x () Real 0)` + chained `(<= -1 x 3)` | **G · parser** |
| `nl__very-easy-sat` | sat | 5 vars, two *independent* circles `s²=1−c²`, `skoX≈0` | **F · grid witness (>4 var)** |
| `arith__real2int-test` | sat | 3 vars, degree-3 strict, conjunction | **F/CAD** |
| `nl__approx-sqrt` | sat | `x²=2 ∧ x>0 ∧` 3 tight ineqs — √2 witness, conj. | **H · algebraic witness** |
| `nl__approx-sqrt-unsat` | unsat | `x²=2 ∧ x>0 ∧` **or** of 28-digit-rational ineqs | **H+ · √2-through-disjunction** |
| `nl__factor_agg_s` | sat | 3 vars, nested `or`/`not` over degree-3 atoms | **I · Boolean-CAD (engine)** |
| `nl__metitarski-1025` | sat | skolem sin/cos, `pi` bounds | **J · transcendental (engine)** |
| `nl__metitarski-3-4` | sat | idem, dag=67 | **J · transcendental (engine)** |
| `nl__metitarski_3_4_2e` | sat | idem, dag=91 | **J · transcendental (engine)** |
| `nl__sin-cos-346-…0169` | sat | degree-8 poly in skoX, `skoSQ3²=3`, `pi` bounds | **J/K · high-degree+algebraic** |
| `nl__nt-lemmas-bad` | unsat | degree-10 univariate `p(skoX)=p(265/128)`, `pi` | **K · high-degree CAD (engine)** |

### 1d. Class rollup (reachable rows per class)

| Class | Instances | Baselines touched | Effort | Soundness risk |
|---|---:|---|---|---|
| **A** div/mod Euclidean-linearize | 4 clean + 2 partial | qf-nia-cvc5 | M | low (theory-valid axioms) |
| **B** iand bounded-blast | 2 (+2 curated = 4 rows) | qf-nia-cvc5, qf-nia-iand | M | low (bounded, exact) |
| **C** `int.pow2` operator + positivity | up to 7 | qf-nia-cvc5 | M | low (bounded / axiom) |
| **D** even-power *equality* | 1 | qf-nra-cvc5 | **XS** | very low (SOS≥0 identity) |
| **F** grid witness, >4-var / per-var | 1–2 | qf-nra-cvc5 | S | very low (sat replay-only) |
| **G** parser (define-fun const, chained ≤) | 1 | qf-nra-cvc5 | S | very low (sat replay) |
| **H** algebraic √2 witness (conj / disj) | 2 | qf-nra-cvc5 | M | medium (bignum on CAD guard) |
| **I/J/K** Boolean-CAD / transcendental / degree-10 | 5 | qf-nra-cvc5 | **multi-week engine** | — |

## 2. ROI verdict

**Best next division = QF_NIA (cvc5-regress, 54 %).** Its 18 undecided instances
cluster into three *bounded, theory-valid* levers — div/mod Euclidean
linearization (A, 4–6 rows), `iand` bounded-blast (B, 4 rows across two
baselines), `int.pow2` (C, up to 7 rows) — that together address ~13 of 18 and
reuse machinery that already exists (the product abstraction + sign/monotonicity
lemmas in `nra.rs`, the width-ladder blast in `auto.rs`). Only `nl-eq-infer` and
the dag=610 `ext-rew-aggr-test` are genuine-engine.

**QF_NRA (68 %) is mostly the opposite:** of 12 undecided, **7 are
genuine-engine** (Boolean-CAD `factor_agg_s`; transcendental MetiTarski ×3;
degree-8/10 `sin-cos`/`nt-lemmas-bad`) — the multi-week nlsat/ICP arc. Only ~5 are
cheap (D even-power-equality ×1, F grid ×1–2, G parser ×1, H algebraic-√2 ×2).

**Extension-vs-engine, cited:**
- **Extension of existing machinery** (raise a guard / add an axiom / route
  through code already present): **A, B, C, D, F, G** — and **H** (the algebraic
  layer is already bignum; the conjunctive `approx-sqrt` needs only the i128
  coefficient guard raised, and the disjunctive `approx-sqrt-unsat` needs the
  existing `check_with_nra_dpll` cubes routed back into the CAD — an added edge, not
  a new procedure).
- **Genuinely-new engine**: **I** (Boolean structure whose *cubes* exceed CAD
  reach), **J** (transcendental → needs ICP with δ-sat discipline, Phase C), **K**
  (degree-8/10 with algebraic coupling → CAD projection quality / cell-count,
  Phase D). These are the `metitarski-*` / `nt-lemmas-bad` / `factor_agg_s` cases
  the 08-eval residual already flags.

So the next *lever* is not "build CAD" — it is **harvest the bounded NIA
levers first (A→B→C), then the cheap NRA pickups (D→F/G→H)**, deferring the
NRA engine (I/J/K) to the funded Phase B/C/D arc.

## 3. Existing NRA/CAD machinery — what it decides, why the residue escapes

**Dispatch order for a QF_NRA/NIA query** (from `nra.rs` +
`nra_real_root.rs`, `check_auto` tail):

1. **even-power / sign refutation** (`nra_even_power::nra_even_power_refutation`) —
   matches a top-level conjunct `nonnegative_even_power_sum < 0` (RHS **zero**,
   **strict**), refutes it (SOS ≥ 0). Re-checked against the original.
2. **bounded rational sat-witness probe** — a fixed grid `{0, ±1, ±2, ±1/2}`,
   *full product* for **≤ 4 free reals**, *uniform* (all-vars-equal) above; returns
   `sat` only when a candidate replays **every original assertion** true under the
   ground evaluator.
3. **cross-product-cap relaxation** (`check_nonlinear_abstraction`, ADR-0024) —
   each product `a·b` → fresh var + valid product/McCormick/SOS lemmas + spatial
   B&B (depth ≤ 6) + incremental point-lemma loop (≤ 12 rounds). Admits only when
   **distinct-operand cross-products ≤ `MAX_CROSS_PRODUCTS = 2`** (`nra.rs:107`);
   squares are excluded from the count. Past the cap it still runs the cheap
   **sign-only** and **threshold-1 monotonicity** stages (the `ones` refutation) —
   valid `¬p∨q` facts about `r=a·b`, no McCormick.
4. **CAD** (`decide_real_poly_constraint`, `nra_real_root.rs:251`) — sign-cell
   decomposition: "a conjunction holds on a whole cell or nowhere." Reached
   **before** the cross-product cap (both in `auto.rs:1983` and again at
   `nra.rs:196`). 2-var (`decide_two_var_component`, resultant, needs ≥2
   equalities), N-var (`decide_strict_cad_nvar` all-strict / `decide_nonstrict_cad_nvar[_algebraic]`
   mixed). Accepts **conjunctions only** of polynomial comparisons (equalities,
   strict, `≤/≥`, `≠`, mixed). **Disjunctions are NOT in the CAD collector** —
   `collect_conjuncts`/`collect_multi_conjuncts` have no `BoolOr` arm, so a
   top-level `or` makes the *top-level* CAD collector decline. **CORRECTED
   (2026-07-07, 10th review): `check_with_nra_dpll_within` (`dpll_t.rs:253`,
   commit 5ede57f4) DOES hand each split theory cube to the exact CAD
   (`decide_real_poly_constraint`), not only to the linear abstraction** — the
   DPLL→CAD edge exists (task #43 `4d74b288` then added the equality-anchored
   decision + bignum coefficients that use it to close `approx-sqrt-unsat`). The
   original text below claimed the edge was missing; it was not. A disjunction of
   nonlinear atoms whose cubes are within CAD reach now decides; what still
   escapes is CAD *reach* (degree/variable/cell guards) and the absence of a
   transcendental substrate — not routing.

**The CAD's hard guards** (each a *decline-to-`unknown`*, never a wrong verdict):

| Guard | Value | File | Bites on |
|---|---|---|---|
| `MAX_CROSS_PRODUCTS` | 2 | `nra.rs:107` | ≥3 distinct products (any 3-var `ab,bc,ca`) |
| `MAX_ABS_COEFF` | `2^40` (i128) | `nra_real_root.rs:78` | 28-digit rationals (`approx-sqrt-unsat`) |
| `MAX_DEGREE` | 64 | `nra_real_root.rs:81` | (not the current residue) |
| `MAX_SYLVESTER_DIM` | 24 | `nra_real_root.rs:2169` | high-degree resultants |
| `MAX_CAD_CELLS` | 256 | `nra_real_root.rs:2408` | cell blow-up |

**Why each residue escapes (verified):**
- `very-simple-unsat` (`a²=−2`) — a *clean* single-var Real equality would be
  decided exactly by `decide_eq` → `isolate_roots(a²+2)` → no real root → `Unsat`.
  It escapes because the atom **does not match** `match_real_poly_constraint`
  (which requires `Sort::Real` on the `Eq`): the `(- 2)` numeral triggers an
  **int↔real coercion** so the CAD declines, and the fall-through abstracts `a·a →
  r = −2` (losing `a²≥0`) → `Unknown` (the residual the 08-eval already named).
  Step 1 (even-power) also skips it — it matches only `sum < 0`, not an equality.
  **Escapes on coercion routing + shape, not on CAD completeness.**
- `very-easy-sat` (5 vars, two independent circles) — step 2's grid would find
  `c=1,s=0` *per variable*, but with **5 free reals it uses the uniform (all-equal)
  grid**, and all-equal never satisfies two decoupled circle equalities; steps 3–4
  face 2 cross-products (`s²`,`c²` are squares, excluded) but the coupling +
  `skoX≈0` linear pins time out. **Escapes the ≤4-var product-grid boundary.**
- `approx-sqrt` (sat, conjunction) — `x²=2` needs the **algebraic √2** witness;
  the algebraic layer is bignum (ADR-0046), but the CAD *entry* coefficient guard
  `MAX_ABS_COEFF = 2^40 ≈ 1.1×10¹²` (an i128 clearing bound) **declines the tight
  rational** coefficients (`1.9999999999999` etc.). **Escapes on the i128
  coefficient guard, not on CAD completeness.**
- `approx-sqrt-unsat` (unsat) — additionally sits under a **top-level `or`**, which
  the CAD collector has no arm for, so it **never reaches the CAD**; only
  `check_with_nra_dpll` splits it and hands each cube to the *abstraction* (not the
  CAD). Closing it needs **both** (a) routing DPLL cubes back into the exact CAD
  **and** (b) a bignum coefficient path for the 28-digit rational
  `2.0000000000000000000000000001` (denominator ~10²⁸). **Escapes on disjunction
  routing + the i128 coefficient guard.**
- `factor_agg_s`, MetiTarski ×3, `sin-cos`, `nt-lemmas-bad` — genuine-engine:
  cubes past CAD degree/variable reach, transcendental atoms, or degree-8/10
  univariate with algebraic coupling. **These are the Phase B/C/D arc, not a
  bounded slice.**

**One-sentence characterization:** the CAD is decision-complete in principle for
polynomial conjunctions (disjunctions via DPLL case-split) but the *reachable*
residue is gated by four **bounded engineering guards** (cross-product count,
i128 coefficient magnitude, ≤4-var grid, cell cap) plus the even-power **shape**
restriction — not by a missing decision procedure; the *unreachable* residue
(transcendental, high-degree, Boolean-heavy) is the funded multi-week engine.

## 4. The sliced plan (ordered by ROI: cheapest-highest-yield first)

Every slice is additive (`unknown → decision`, never flips a decided verdict),
sat is ground-evaluator-replay-checked, unsat is a re-checkable certificate or a
theory-valid refutation, and every slice is gated by **both**
`nra_differential_fuzz` **and** `nia_differential_fuzz` (shared multivariate path,
DISAGREE=0), `progress_frontier`, `corpus_regression`, and a same-command
re-measure of the touched baseline. All new arithmetic uses `checked_*` ops
(graceful `unknown` on overflow, never a panic/wrong verdict — the standing
i128/Rational lesson).

### Slice 1 — NIA div/mod Euclidean linearization (Class A) · **first slice**
- **Targets:** `div.03`, `div.08`, `mod.02`, `mod.03` (clean); reaches toward
  `issue3480`, `learned-rewrite-int-mod-range` (partial).
- **Mechanism:** this is Phase E task **E.0a–c** (see [07-phaseE-nia](07-phaseE-nia.md)),
  crystallized by the census. For each `(div x n)`/`(mod x n)` term with a
  **variable** divisor, introduce fresh `q,r` and the **theory-valid Euclidean
  constraints** `x = n·q + r ∧ 0 ≤ r < |n|` (SMT-LIB total semantics; `n=0` handled
  by the existing total-division encoding). The `n·q` product feeds the **existing**
  product-abstraction + **sign/zero/threshold-1 monotonicity lemmas** already in
  `nra.rs`, but the relaxation is solved over the **integer** solver
  (`check_with_lia_dpll`) so integrality is preserved (`q<1 ⇒ q≤0`) — the exact
  combination the E.0 experiment proved necessary (`div.03`: `q≤0 ∧ n>0 ⇒ n·q≤0 ⇒
  x=n·q+r<n`, contradicting `x≥n`). Route in `dispatch_nonlinear_int_tail` **before**
  the width-ladder blast; strictly additive.
- **Soundness:** the Euclidean identity + `0≤r<|n|` are valid over ℤ for `n≠0`;
  the product lemmas are already sound (relaxation only grows the model space);
  **replay against the true original**, never the eliminated form (the div-by-zero
  lesson). `unsat` from the LIA refutation is retained as the certificate. `sat`
  witness (integer) replays through the ground evaluator.
- **Gate:** `nia_differential_fuzz` (extend seeds with variable-divisor div/mod
  scripts, both polarities) + `nra_differential_fuzz` (shared path) DISAGREE=0;
  `progress_frontier` (protect `nia_unsat.json`); re-measure `qf-nia-cvc5`.
- **Size:** **M**. **Yield:** 4 clean rows (54 %→~65 %), 2 more within reach.

### Slice 2 — NRA `a²=−2`: fix the int↔real coercion routing (+ even-power equality arm) (Class D)
- **Target:** `very-simple-unsat` (`(= (* a a) (- 2))`).
- **Root cause (verified):** the atom is a clean single-var Real equality that
  `decide_eq` → `isolate_roots(a²+2)` would refute exactly, **but** the `(- 2)`
  numeral makes `match_real_poly_constraint` (requires `Sort::Real` on `Eq`) reject
  it → CAD declines → the abstraction loses `a²≥0` → `Unknown`.
- **Mechanism (primary):** normalize the int↔real numeral coercion so an integer
  literal on one side of a Real `Eq` is admitted as a Real coefficient, letting
  `match_real_poly_constraint` accept the atom and the exact `decide_eq` fire.
  **Belt-and-suspenders (fallback):** also add an equality arm to `nra_even_power`
  matching `(= nonnegative_even_power_sum c)` with `c < 0` → `unsat` (sum of even
  powers + nonnegative constant is `≥ 0 > c`), so the refutation survives even if a
  future routing regresses. Prefer the coercion fix as the real closer.
- **Soundness:** the coercion is a value-preserving normalization; `decide_eq`'s
  `Unsat` is the existing exact no-real-root certificate. The even-power arm is a
  checked SOS ≥ 0 ring identity, re-scanned against the original, adds only
  `unsat`. Near-zero risk.
- **Gate:** `nra_differential_fuzz` DISAGREE=0; `corpus_regression`; re-measure.
- **Size:** **XS**. **Yield:** 1 row.

### Slice 3 — NRA sat-witness grid: per-variable coordinate for >4 free reals (Class F)
- **Targets:** `very-easy-sat` (5 vars); likely `real2int-test` (3 vars, strict).
- **Mechanism:** replace the *uniform (all-equal)* fallback above 4 free reals
  with a **bounded per-variable coordinate probe** — try each variable over
  `{0,±1,±2,±1/2}` while holding the rest at a running best (bounded round-robin,
  hard iteration cap), replaying **every original assertion**. This finds
  decoupled-witness models (`c=1,s=0` per circle) the uniform grid cannot. Keep the
  ≤4-var full product as-is.
- **Soundness:** `sat`-replay-only — a candidate is returned **only** if it makes
  every original assertion evaluate true under the ground evaluator; it can never
  emit a wrong `sat` and never touches `unsat`. Near-zero risk.
- **Gate:** `nra_differential_fuzz` (sat-replay audit) DISAGREE=0; re-measure.
- **Size:** **S**. **Yield:** 1–2 rows.

### Slice 4 — NRA parser: nullary `define-fun` constant + chained n-ary compare (Class G)
- **Target:** `parser__real-numerals` (`(define-fun x () Real 0)` + `(<= -1 x 3)`).
- **Mechanism:** in `axeyum-smtlib`, support a **nullary `define-fun`** binding to a
  numeric literal (macro-expand to the constant) and desugar an **n-ary chained
  `<=`/`<`/`>=`/`>`** into the conjunction of adjacent pairs (SMT-LIB semantics).
  Turns the current `unsupported` into a parsed, trivially-`sat` script.
- **Soundness:** parser desugaring only; the resulting `sat` replays as any other.
- **Gate:** `corpus_regression`, smtlib parse round-trip; re-measure.
- **Size:** **S**. **Yield:** 1 row (may unlock others across the corpus).

### Slice 5 — NIA `iand` bounded bit-blast (Class B)
- **Targets:** `iand-native-2`, `iand-native-granularities` (cvc5 **and** curated —
  4 rows; curated goes 1→3).
- **Mechanism:** Phase E task **E.4** scoped to the **bounded** case. When
  `((_ iand k) x y)` appears with `x,y` provably in `[0, 2^k)` (from asserted
  bounds), lower it to the exact `k`-bit `bvand` via int↔BV width-`k` and route the
  fresh result var back into the integer solver (the int-blasting bridge, Layer 3).
  Start with the bounded-blast; the lazy-UF partial-lemma portfolio is a later
  extension.
- **Soundness:** exact bit-level semantics of `iand` for in-range operands; `sat`
  replays through the ground `iand` evaluator; `unsat` from the bounded blast is
  sound **only under the asserted bounds** (guard: decline if operands are not
  provably bounded — never claim unbounded `unsat`).
- **Gate:** `nia_differential_fuzz` extended with `iand` scripts; `bv_differential_fuzz`
  (the blast path); re-measure both NIA baselines.
- **Size:** **M**. **Yield:** 4 rows across two baselines.

### Slice 6 — NIA `int.pow2` operator + positivity/monotonicity (Class C)
- **Targets:** `pow2-native-1..7` (currently `unsupported`).
- **Mechanism:** wire `int.pow2` in `axeyum-smtlib` + IR; add the **theory-valid
  axioms** `int.pow2 x ≥ 1` for `x ≥ 0`, `int.pow2 x > 0` (total-semantics
  positivity), and strict monotonicity `x<y ⇒ pow2 x < pow2 y`; for **bounded**
  `x ∈ [0,b]` with small `b`, expand `int.pow2 x` to its finite value table (blast).
  Several instances (`pow2-native-1` sat, `-4` unsat) close on positivity alone.
- **Soundness:** the axioms are valid for the SMT-LIB `int.pow2` domain; `sat`
  replays through a ground `int.pow2` evaluator; the finite table is exact for the
  asserted bound (decline unbounded).
- **Gate:** `nia_differential_fuzz` extended; re-measure.
- **Size:** **M**. **Yield:** up to 7 rows (realistically 4–5 on positivity+table).

### Slice 7 — NRA algebraic √2 witness: bignum coefficient path + disjunction (Class H)
- **Targets:** `approx-sqrt` (sat, conj), `approx-sqrt-unsat` (unsat, disj).
- **Mechanism:** two coupled changes. **(a)** raise the CAD-entry coefficient
  handling off the i128 `MAX_ABS_COEFF = 2^40` guard onto the **already-bignum**
  algebraic path (ADR-0045/0046) for the coefficient-clearing branch, so a 28-digit
  rational no longer forces a decline (closes `approx-sqrt`, a conjunction). **(b)**
  for the unsat disjunctive variant, route each `check_with_nra_dpll` theory cube
  **back into `decide_real_poly_constraint`** (the exact CAD) instead of only the
  abstraction — the missing edge the source audit found (cubes currently reach only
  the ≤2-cross-product relaxation). Sub-slice (a) and (b) can ship independently;
  (a) alone moves `approx-sqrt`.
- **Soundness:** the algebraic arithmetic is exact bignum; `sat` replays the
  algebraic assignment via `sign_at`/ground eval; `unsat` is the CAD covering
  (re-checkable). Medium risk — touches the CAD coefficient path, so the full
  `nra_differential_fuzz` sat-replay + unsat-recheck audit is mandatory, plus a
  targeted giant-rational fuzz slice.
- **Gate:** `nra_differential_fuzz` (giant-rational + disjunction seeds) DISAGREE=0;
  `progress_frontier` (`nra_degree.json`); re-measure.
- **Size:** **M**. **Yield:** 2 rows.

### Deferred — the genuine engine (Classes I/J/K), NOT bounded slices
- **`factor_agg_s`** (Boolean-CAD): cubes whose products exceed the CAD reach →
  Phase D projection quality + Phase B incremental-linearization tier.
- **MetiTarski ×3** (transcendental sin/cos): Phase C **ICP** with the δ-sat ⇒
  `unknown` discipline (exact witness only) — see [05-phaseC-icp](05-phaseC-icp.md).
- **`sin-cos-346` / `nt-lemmas-bad`** (degree-8/10 + algebraic coupling): Phase D
  CAD projection / `MAX_CAD_CELLS` / `MAX_SYLVESTER_DIM` scaling.
- **`nl-eq-infer`, `ext-rew-aggr-test`** (NIA nonlinear-int / dag=610): Phase E
  Layer-2 incremental linearization over UFLIA.

These are **weeks, not a slice**; do not attempt them as bounded increments.

## 5. First-slice recommendation (ready to hand to an implementation agent)

**Ship Slice 1 — NIA div/mod Euclidean linearization (Phase E · E.0a–c).**

- **Why first:** highest verified-rows-per-effort among sound, bounded levers
  (4 clean QF_NIA rows, 54 %→~65 %, plus reach into 2 more), reuses the existing
  product-abstraction + sign/monotonicity lemma machinery in `nra.rs`, and is
  backed by a *clean root-cause experiment already recorded* in
  [07-phaseE-nia §First slice](07-phaseE-nia.md) — no research risk remains, only
  implementation.
- **Concrete steps:**
  1. `check_with_nia` (mirror `check_with_nra`): product abstraction + the existing
     sign/zero/monotonicity lemma builders, relaxation solved by `check_with_lia_dpll`
     (integer DPLL(T)), sat replayed against the **original** assertions.
  2. `dispatch_nonlinear_int_tail`: route the integer nonlinear tail into
     `check_with_nia` **before** the width-ladder blast; strictly additive
     (`unknown → decision`).
  3. Extend `eliminate_int_divmod` to **variable divisors** — introduce `q,r` with
     `x = n·q + r ∧ 0 ≤ r < |n|` (with `n=0` on the existing total-division
     encoding + division congruence), so `div.03`/`mod.02`-style instances reach
     `check_with_nia`.
- **Soundness contract:** Euclidean axioms theory-valid over ℤ (`n≠0`); replay
  against the true original (div-by-zero lesson); `unsat` only from the LIA
  refutation (retained); `checked_*` arithmetic → graceful `unknown` on overflow.
- **Gate before commit:** `nia_differential_fuzz` **and** `nra_differential_fuzz`
  (shared path) DISAGREE=0; `cargo test -p axeyum-solver --test progress_frontier`;
  `corpus_regression`; re-run the same `qf-nia-cvc5-regress-clean` measure command
  (10 s / 4 jobs via `MEM_LIMIT_GB=64 ./scripts/mem-run.sh`) and record the
  decided/unknown/PAR-2 delta + DISAGREE=0 in
  [08-evaluation-and-soundness](08-evaluation-and-soundness.md) and the SCOREBOARD.

## 6. Honest scope boundaries

- **Bounded, individually-shippable slices** (weeks *total*, days each): Slices
  1–7 above. Each closes named instances, reuses existing machinery or adds a
  theory-valid axiom / a bounded blast / a parser desugaring / a guard-raise, and
  is gated identically.
- **Genuine multi-week engine** (do not slice into "one increment"): the
  transcendental ICP tier (Phase C), the Boolean-CAD + incremental-linearization
  tier (Phase B/D), and CAD projection/cell scaling (Phase D). These carry their
  own ADRs (see [08 §ADRs to write](08-evaluation-and-soundness.md)) and per-cell
  Positivstellensatz evidence for Lean parity — out of scope for the *next lever*.

**Bottom line:** the next arithmetic decide-rate lever is **QF_NIA’s bounded
levers (div/mod → iand → pow2), starting with div/mod Euclidean linearization**,
followed by the cheap QF_NRA pickups (even-power-equality, grid, parser,
algebraic-√2). The QF_NRA *engine* residue (transcendental / high-degree /
Boolean-heavy) stays on the funded Phase B/C/D arc — not the next slice.
