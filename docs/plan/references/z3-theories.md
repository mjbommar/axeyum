# Z3 theory solvers & quantifiers

Top-down review of Z3's per-theory decision procedures, read against axeyum.
**Dominant finding:** Z3's theories are **lazy, CDCL(T)-integrated** plugins hung
off a shared **e-graph (`euf::egraph`)** that is the equality bus, the model
substrate, and the proof-forest. axeyum's theories are mostly **eager/one-shot
reductions to QF_BV or exact simplex**. The single highest-leverage gap is not
any one theory — it is the absence of that shared incremental e-graph + CDCL(T)
loop. Z3 has two cores: legacy `src/smt/theory_*` and new `src/sat/smt/*_solver`;
the new core is the cleaner port target throughout.

## BV (bit-vectors)
**Files:** `references/z3/src/sat/smt/bv_solver.cpp`, `bv_internalize.cpp`,
`bv_delay_internalize.cpp`, `bv_ackerman.cpp`, `bv_theory_checker.cpp`;
`references/z3/src/ast/rewriter/bit_blaster/bit_blaster_tpl_def.h` (gate circuits);
`references/z3/src/ast/euf/euf_bv_plugin.cpp` (word-level slicing); legacy
`src/smt/theory_bv.cpp`.

**Z3 approach.** *Lazy bit-blasting*: `should_bit_blast` delays the hard ops
(`BMUL`, div/rem, no-overflow predicates, big `BADD`) unless small (`size≤12`) —
a delayed op gets fresh bit literals and **no circuit**. At final check,
`check_delay_internalized` evaluates under the current model; if consistent the
circuit is never built; if not it tries **cheap multiplier axioms** (`x·0=0`,
`x·1=x`, the Niemetz–Preiner invertibility lemma `x*y=z ⇒ (y|-y)&z=z`) before
committing to the full blast. Circuits: ripple-carry adder, shift-add array
multiplier (constant-case ITE specialization), restoring division, barrel
shifters. Structural ops (concat/extract/repeat) **alias the same SAT literals**.
`euf_bv_plugin` does a slice-tree congruence proving word equalities structurally.
Ackermannization of repeatedly-derived var equalities via an activity-keyed queue.
Models fold assigned bits into a numeral; conflicts use five justification kinds
emitted as DRAT hints (`bv::theory_checker` defines the rules but ships stubs).

**axeyum gap.** Foundation done (eager QF_BV). Gaps: lazy/delayed multiplier
blasting (*M*, the biggest practical BV win; needs the CDCL(T) loop + cheap mul
axioms); word-level slicing congruence (*M*, needs e-graph); bit-literal aliasing
for structural ops (*S*); real BV theory-checker rules (*S*, on-identity).

## Arrays
**Files:** `references/z3/src/sat/smt/array_solver.cpp`, `array_axioms.cpp`,
`array_model.cpp`; legacy `src/smt/theory_array{,_base,_full}.cpp`.

**Z3 approach.** Everything reduces to beta-reduction of `select` over
const/store/map/as-array/lambda, driven by e-graph merges. Axioms are queued,
deduped, tri-state. `store(a,i,v)[i]=v` is **eager**; read-over-write
`store(a,i,v)[j]=a[j] ∨ i=j` is **lazy** (instantiated when congruence merges put
a select and a store in one class), with a further delay heuristic.
**Extensionality** triggers on disequality (`e1=e2 ∨ select(e1,diff)≠select(e2,diff)`
with per-dimension diff skolems). Models are finite `func_interp` graphs with a
**majority-vote else value**.

**axeyum gap.** axeyum does eager elimination (read-over-write + Ackermann,
ADR-0010) — complete for QF_ABV but blows up on store chains. **Lazy axiom
instantiation (*L*)** is the single biggest array item (needs e-graph +
class-merge hooks + axiom queue); extensionality via on-demand diff skolem (*M*);
`func_interp` else-value models (*M*); lambda/map/default (*M*, beyond plain ABV).

## EUF (congruence closure)
**Files:** `references/z3/src/ast/euf/euf_egraph.cpp`, `euf_enode.cpp`,
`euf_etable.cpp`, `euf_justification.cpp`, `euf_ackerman.cpp`;
`references/z3/src/sat/smt/{euf_solver,euf_model,euf_proof_checker,euf_relevancy}.cpp`.

**Z3 approach.** A proper e-graph: signature table over argument roots
(`euf_etable`), one per `(decl,arity)`; two nodes collide iff congruent under the
union-find. **Two structures per node**: union-find (`m_root`, union-by-size) for
membership and a separate **proof forest** (`m_target`+`m_justification`) for
explanations. Merge is deferred (worklist), removing/re-inserting parents to drive
the congruence cascade. **Explanations to the LCA** (not root); congruence
justifications store only a timestamp, premises recovered structurally. The
independent `eq_theory_checker` re-derives transitivity/symmetry with its own
union-find — a clean "trusted small checking" template. The e-graph is the shared
equality bus: theory vars attach to nodes; merges emit `th_eq` records to theory
solvers. Models on union-find roots, topologically ordered, with `validate_model`.

**axeyum gap.** axeyum does UF by Ackermann — complete but quadratic and can't
share equality reasoning. **A real incremental e-graph with explanation tracking
(*L*) is the keystone.** Plus an independent congruence checker (*S/M*, on
identity); theory-var equality bus + `th_eq` dispatch (*M*); relevancy + dynamic
Ackermannization (*M*, deferrable).

## Arithmetic (LRA / LIA / NRA / NIA)
**Files:** `references/z3/src/sat/smt/arith_solver.cpp`, `arith_theory_checker.h`;
LRA `references/z3/src/math/lp/{lar_solver,lp_primal_core_solver,numeric_pair}.*`;
LIA `int_solver.cpp`, `gomory.cpp`, `int_gcd_test.cpp`, `int_cube.cpp`,
`int_branch.cpp`, `hnf_cutter.cpp`, `dioph_eq.cpp`; nonlinear `nla_core.cpp`,
`emonics.cpp`, `nla_tangent_lemmas.cpp`, `nla_grobner.cpp`,
`math/grobner/pdd_solver.cpp`, `nlsat/nlsat_solver.cpp`, `nlsat_explain.cpp`,
`math/lp/nra_solver.cpp`.

**Z3 approach.** *LRA*: Dutertre–de Moura general/bounded simplex over
delta-rationals (`numeric_pair`, `x+δ·y`); no explicit RHS (constraints = slack
bounds); tableau invariant `A·x=0`; Bland anti-cycling. **Farkas conflicts**: the
infeasible row's coefficients *are* the Farkas multipliers. *LIA*: short-circuit
dispatch (`int_solver::check`): GCD test → patch → cube test → HNF cut → Gomory
cut → Diophantine (Griggio) → branch-and-bound; `lia_move` enum is the contract;
cuts must cut off the current fractional point and carry explanations.
*Nonlinear*: incremental linearization in `nla_core` (emonics monomial congruence,
sign/zero lemmas, monotonicity, interval propagation, **McCormick tangent
planes**, Horner/cross-nested refutation) + **Gröbner via PDD** + the **nlsat CAD
oracle** (MCSAT, projection via resultants/discriminants/PSC) reached by
`nra_solver`, with a bounded-nlsat fallback. Proofs reduce to the Farkas rule.

**axeyum gap.** axeyum has Farkas-certified exact-rational simplex LRA (strong),
bit-blast+B&B LIA, sound-incomplete NRA. Gaps: **LIA cut portfolio (*M/L*)** —
Gomory + GCD test first (axeyum's existing simplex makes a native int solver more
attractive than bit-blasting); delta-rational strict models (*S/M*); **nonlinear
incremental-linearization loop + CAD (*L/XL*)** — emonics, Gröbner/PDD, and the
nlsat CAD oracle for NRA completeness; theory↔SAT integration (*L*, the CDCL(T)
gap — Z3 interleaves `make_feasible`/`check_lia`/`check_nla`/`assume_eqs`).

## FP (floating point)
**Files:** `references/z3/src/ast/fpa/fpa2bv_converter.cpp` (the blaster: `unpack`,
`round`, `mk_rounding_decision`, per-op encoders), `bv2fpa_converter.cpp` (model
lifting); `src/smt/theory_fpa.cpp`, `src/sat/smt/fpa_solver.cpp`.

**Z3 approach.** **No FP decision procedure** — FP reduces to BV (`fpa2bv`) and
bit-blasts, exactly axeyum's strategy. Triple `(sgn[1], exp[ebits],
sig[sbits-1])` in biased IEEE form; RM as 3-bit code. Reusable circuit: `round` +
`mk_rounding_decision` (GRS bits, all rounding modes, overflow→{inf,max} table).
Per-op unpack/add/mul/div, **fma with single rounding (double-width
intermediate)**, sqrt. Variables tie to bits via wrap/unwrap UFs with
`unwrap(wrap(n))=n`; `nan_wrap` canonicalizes unspecified results.

**axeyum gap.** axeyum's **closest-to-parity theory** (F16–F128, validated). Small
gaps: fp.to_real / fp.to_*bv unspecified-value handling (`nan_wrap` + `_I`
internal-op trick) (*S/M*); lazy "eager-once-touched" conversion (*S*); min/max ±0
selector (*S*). No large gap.

## Datatypes
**Files:** `references/z3/src/sat/smt/dt_solver.cpp`; legacy
`src/smt/theory_datatype.cpp`.

**Z3 approach.** Oppen procedure over well-founded ADTs, e-graph-driven: **eager
accessor axioms** (`acc_i(C(a))=a_i`); recognizer⇔constructor coupling with
**exactly-one propagation**; **case-split biased to the non-recursive
constructor** (guarantees a finite witness); **iterative occurs-check DFS** for
acyclicity; models from the determined constructor; conflicts via `th_explain`.

**axeyum gap.** axeyum has datatypes. Parity item is *how*: lazy, e-graph-driven
splitting + occurs-check (*M*, depends on the e-graph); acyclicity across
array/seq nesting (*S/M*). Not a priority vs arrays/EUF/arithmetic.

## Quantifiers
**Files:** E-matching `references/z3/src/ast/euf/euf_mam.cpp` (the MAM; legacy
`src/smt/mam.cpp`), `src/ast/pattern/pattern_inference.cpp`,
`src/sat/smt/{q_ematch,q_clause,q_eval,q_queue}.cpp`; MBQI
`src/smt/{smt_model_finder,smt_model_checker}.cpp`,
`src/sat/smt/{q_mbi,q_model_fixer}.cpp`; QE `src/qe/{qsat,qe_mbp}.cpp`,
`src/qe/mbp/*`.

**Z3 approach.** *E-matching* via the **Matching Abstract Machine**: patterns
compile to bytecode (`BIND`/`COMPARE`/`CHECK`/`GET_CGR`/`CHOOSE`/`YIELD`), one
shared **code tree** per top-level symbol with prefix sharing; the interpreter
walks the e-graph three ways (equiv-class ring, O(1) congruence hash, inverted
parent index for multi-patterns); an inverted path index drives **incremental**
matching on merges. *Trigger selection* (`pattern_inference`): post-order
candidates, forbidden symbols, minimality, **loop detection**, weight ranking,
multi-patterns only when needed, fallback ladder ending in patternless→MBQI.
*Instance management*: fingerprint dedup canonicalized to e-class roots; a parsed
15-variable cost function. The new core models quantifiers as **clauses of
(dis)equality literals, lazily evaluated** (`q_eval`): instantiate only the
undetermined literal, all-false=conflict, any-true=redundant. *MBQI*
(Ge–de Moura): build/repair a candidate model, model-check each universal in a
sub-solver, lift counterexamples; **complete on the almost-uninterpreted
fragment**. *QE*: **MBP** (model-based projection, per-theory plugins) as the
reusable primitive; **QSAT** (predicate abstraction + two alternating kernels +
MBP blocking) as the modern engine.

**axeyum gap (large, broad).** axeyum has finite-domain + first-slice
E-matching/MBQI. Gaps: **MAM-based incremental e-matching (*L*, needs e-graph)**;
trigger inference (*M/L*); lazy clause-form quantifier evaluation (*M*, adopt
directly); MBQI completeness machinery (*L*); QE/MBP/QSAT (*L*, MBP first);
cost/fingerprint instance management (*S/M*).

## Cross-cutting priorities (ranked)

1. **Incremental e-graph (congruence closure) with explanation tracking — *L*, do
   first.** The keystone for EUF, lazy arrays, datatypes, arithmetic equality,
   and *all* quantifier work. Port the `euf_egraph` design + an independent
   `eq_theory_checker`-style congruence checker.
2. **CDCL(T) final-check / theory-propagation loop — *L*, alongside/after #1.**
   The eager→lazy gap is this loop. Unlocks lazy BV mul, lazy array axioms, the
   arithmetic interleave, quantifier rounds.
3. **Theory combination bus (`th_eq` + interface equalities) — *M*, depends on #1.**
   Required before multi-theory (QF_AUFLIA) works well.
4. **LIA cut portfolio (Gomory + GCD first) — *M*.** Highest-value single-theory
   upgrade independent of the big infra; axeyum already has the exact simplex.
5. **Lazy array axiom instantiation — *M/L*, depends on #1/#2.**
6. **MAM e-matching + trigger inference — *L*, depends on #1/#2.**
7. **NRA completeness via nlsat (CAD) — *L/XL*, lower priority.** Incremental
   linearization (emonics, Gröbner/PDD) is a cheaper middle step.
8. **Real theory-checker rules (BV eq2bit/bit2eq; reuse arith Farkas) — *S*,
   high identity-value, opportunistic.**

**Already near parity:** FP (validated; only small corners) and LRA conflict
certificates (Farkas, exact). Datatypes present; lazy splitting rides #1.
