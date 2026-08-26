# ADR-0543: Cube-And-Conquer Certificate Composition, With A Splitter-Blind Checker

Status: accepted
Index-summary: Compose per-cube DRAT refutations with an independently checked covering proof
Date: 2026-08-22

## Context

`artifacts/facts/smt2/neg-fp16-add-monotone-rne.smt2` (fp16 add-monotonicity
under RNE, negated) **decides** `unsat` in 11.5 s — faster than z3's 30.6 s on
the same box. **Certifying** it — running it through the proof-producing CDCL
core (ADR-0012) to get a DRAT refutation `check_drat` (ADR-0011) can verify —
ran 5 h 59 m and did not terminate; it was reaped rather than left to become
another orphaned-task hazard (the CLAUDE.md gotcha on an 85-hour-old ghost
process taxing every measurement afterward applies to any unbounded solve, not
just accidental ones). Its 8-bit sibling
(`neg-fp8-add-monotone-rne.smt2`, 2²⁴ assignments over 3 operands vs. fp16's
2⁴⁸) certifies in 25 m 46 s as a single monolithic proof. Linear extrapolation
from that ratio puts fp16 at roughly 822 CPU-years monolithically, and the
observed memory growth of the monolithic run would exhaust the host in 2–4
weeks regardless of CPU time (both figures as measured and reported in this
task's brief).

So the decision gap against z3/bitwuzla on this class of query has closed, and
the **certificate** gap is now the binding one. This is exactly the situation
cube-and-conquer exists for (Boolean Pythagorean triples, Schur number five,
Keller-7, the empty-hexagon problem all needed it — see
`docs/plan/exploration-track/phase-6-parallel/README.md` for the calibration
table), and unusually well-suited here: an IEEE-754 miter's hard cases are not
an arbitrary CNF's hard cases, they are the case structure a paper proof of the
same fact would use — special-value class (NaN / ±Inf / ±0 / subnormal /
normal) and sign per operand, then exponent bands where the rounding argument
itself differs by relative magnitude. Most cells of that case table are
trivial or vacuous (e.g. any cell with a NaN operand is closed by the
antecedent guards in the fact's own text); the real work concentrates in
normal/normal/normal, which subdivides further by exponent relationship.

This is also not a green-field design. `docs/plan/exploration-track/phase-6-parallel/`
(tasks T6.1–T6.10) already surveyed this ground for a different motivating
case (open combinatorial problems: Rado/van der Waerden numbers via
`axeyum-search`'s existing `cube-cover.tsv` / `cube-tree-cover.tsv` artifacts)
and reached three conclusions this ADR adopts directly:

- T6.4's note that `proof_sat.rs` (the proof-producing core) **has no
  assumption interface** — `grep assum` in that file returns nothing, unlike
  `IncrementalSat::solve_assuming` (`lib.rs:878`) — so a cube cannot be handed
  to the core as a solver assumption; it can only be handed to it as extra
  root-level unit clauses. Confirmed unchanged as of this ADR.
- T6.3's observation that a cube split forms a **binary decision tree**, and
  that exhaustiveness of such a tree "has a linear-size DRAT proof checkable
  by the existing `check_drat` on a small input" — i.e. the covering argument
  is itself an ordinary UNSAT instance, not a new proof object.
- The Phase-6 README's three-part composition pattern, which is also exactly
  how the Boolean Pythagorean Triples certificate is structured in the
  published record: a transformation proof, a cube manifest **plus a
  tautology proof that it is exhaustive** (365 MB of the published 68 GB), and
  per-cube proofs.

This ADR is narrower than the Phase-6 program: it decides the **composition
format** (T6.4/part of T6.2) for the FP-miter motivating case, and lands the
generic combinator. It explicitly does not decide the splitter heuristic
(T6.3's lookahead splitter), external conquer engines (T6.1), the parallel
orchestrator (T6.6), or LRAT-scale streaming (T6.5) — those stay open and are
listed under Consequences.

The through-date literature audit was refreshed when this decision landed. In particular,
Szeider's *LRAT-Catcher* (arXiv:2607.00815v1, submitted 2026-07-01) already composes
per-cube refutations and an LRAT cover-completeness certificate entirely inside Lean, with
Schur `S(4)=44` and Ramsey `R(4,4)=18` evaluations. The Empty Hexagon Lean artifact likewise
checks a tautology proof plus every cube. Axeyum therefore claims neither the composition
argument nor formal cube-and-conquer checking as novel. Its narrower contribution is an
in-tree DRAT implementation sharing Axeyum's existing CNF/checker types and a file-backed
route usable by its current search encodings.

## Decision

**A cube is a conjunction of CNF literals, refuted as extra unit clauses
against the base formula; the composite certificate is per-cube DRAT proofs
plus one small separate DRAT proof that the cubes are exhaustive; the checker
recomputes every formula it checks from the base formula and the cube literals
themselves, never accepting a derived formula from the producer.**

Concretely, in a new `axeyum-cnf::cube` module:

1. **A cube is `Vec<CnfLit>`** — literals over the base formula's own
   variables. No new literal or clause representation; no new proof format.

2. **Per-cube refutation is F ∧ cube, not F under an assumption.** Given base
   formula `F` and cube `C = {l_1, …, l_k}`, the augmented formula `F_C = F ∪
   {unit(l_1), …, unit(l_k)}` is built by literally cloning `F` and appending
   unit clauses — the only operation `CnfFormula::add_clause` needs, and it
   already range-checks every literal against `F`'s variable count
   (`CnfError::InvalidVariable`), so a cube literal naming a variable outside
   `F` is rejected before anything is solved. `F_C` is solved with the
   existing, **unmodified** `solve_with_drat_proof_with_limits` (deadline +
   conflict budget, exactly as today) and its output is an **ordinary DRAT
   proof of an ordinary CNF formula**, checked by the **unmodified**
   `check_drat`. This is T6.4's "cube-as-units with proofs relative to F ∧
   cube" branch of its own decision point, chosen over teaching `proof_sat.rs`
   an assumption interface: it needs zero changes to the proof-producing core
   or to `check_drat`, both of which are exactly the soundness-critical files
   the task brief says must not be weakened to fit a new format.

3. **Exhaustiveness is a second, independent, ordinary UNSAT instance —
   not a property asserted by the producer.** Given cubes `C_1, …, C_n`, form
   `G = {¬C_1, …, ¬C_n}`: one clause per cube, each clause the De Morgan
   negation of that cube's literal conjunction (a plain disjunction). `G` is
   satisfiable exactly when some total assignment falsifies every cube, i.e.
   exactly when the cubes fail to cover the space; `G` is **unsatisfiable**
   exactly when every assignment satisfies at least one cube. `G` is refuted
   the same way any other formula in this codebase is refuted — solved by
   `solve_with_drat_proof_with_limits`, checked by `check_drat` — with its own
   (small) conflict budget, since it lives over only the case-split variables,
   never the full miter. Concretely for a decision-tree-shaped cube generator
   (§5) `G` reduces to a tautology by construction and its proof is a handful
   of resolution steps; the machinery does not special-case that, it is just
   what a trivial `G` costs.

4. **The composite artifact and its soundness argument:**

   ```
   CubeRefutation {
       cubes:          Vec<Vec<CnfLit>>,   // the case split, literals only
       cube_proofs:    Vec<Vec<DratStep>>, // cube_proofs[i] refutes F ∧ cubes[i]
       covering_proof: Vec<DratStep>,      // refutes {¬cubes[i] : i}, i.e. proves the cubes exhaust the space
   }
   ```

   Argument the checker (`check_cube_refutation`) evaluates, and the only
   argument it evaluates — plain propositional reasoning over already-checked
   facts, not a new trusted primitive:

   > For all `i`, `F ∧ cubes[i]` is UNSAT (checked in step 2 above). Suppose,
   > for contradiction, `F` is SAT with witness `a`. `G` is UNSAT (checked in
   > step 3), so `a` cannot falsify every `cubes[i]` — some `cubes[i]` is true
   > under `a`. Then `a` satisfies `F ∧ cubes[i]`, contradicting that it is
   > UNSAT. So `F` is UNSAT.

5. **First cube generator: the full boolean product over an explicit selector
   list**, `boolean_product_cubes(selectors: &[CnfVar]) -> Vec<Cube>` — all
   `2^k` sign combinations over `k` given variables, capped at
   `MAX_PRODUCT_CUBE_SELECTORS = 24` (a named constant; `2^24` cubes is already
   a lot to enumerate eagerly and exists to catch a caller error, not to
   suggest that scale is reasonable to run). This is the degenerate case of a
   balanced binary decision tree, chosen first because it needs no lookahead
   heuristic and its exhaustiveness is obvious *and still independently
   checked exactly as any other cube set would be* — the checker does not
   know or care that this generator happens to be trivially exhaustive.
   Selector variables for the FP case structure are ordinary boolean subterms
   (`axeyum_fp::is_nan`/`is_infinite`/`is_zero`/`is_subnormal`/`is_normal`,
   sign bits) lowered through the existing `axeyum-bv` pipeline
   (`BitLowering::literal_for_term_bit`) and Tseitin-encoded
   (`tseitin_encode`) alongside the miter itself, so their CNF variables are
   ordinary variables of `F` — no new lowering machinery. A depth-adaptive
   splitter (T6.3's lookahead heuristic, needed once `normal/normal/normal`
   itself needs subdividing) is future work and slots in as a second generator
   behind the same `CubeRefutation`/`check_cube_refutation` contract, since
   nothing about the contract assumes the product-cube shape.

## The crux: how the checker avoids trusting the splitter

The task brief calls this the hard part, correctly. The design property that
makes it hold: **the checker is only ever given `(F, cubes)` — a base formula
and a plain list of literal lists — plus two families of DRAT proofs, and it
builds every formula it checks (`F_C` for each cube, and `G`) itself, from
that data, before calling `check_drat`.** The producer never hands the checker
a formula; it only ever hands the checker literals and proofs. Concretely,
this rules out every way an adversarial or buggy splitter could force a false
`unsat`:

- **Bad cube (doesn't actually imply what the proof claims):** irrelevant —
  `check_cube_refutation` builds `F_C` itself from `F` and `cubes[i]`, so the
  producer cannot substitute an easier formula. The per-cube proof must refute
  the checker's own construction.
- **Non-covering cube set:** `G` is built the same way, from the same
  `cubes` list used in step 2 — not from a second, possibly-inconsistent
  channel. If the cubes genuinely miss part of the space, `G` is genuinely
  satisfiable and **no DRAT proof of it exists to check** — `check_drat` is
  already trusted (ADR-0011/0012) not to accept a forged UNSAT of a SAT
  formula, so this fails at step 3, not by trusting an extra claim from the
  splitter.
- **Cube literal naming a variable outside `F`:** rejected by
  `CnfFormula::add_clause`'s existing bounds check when the checker builds
  `F_C`, before any solving happens.
- **Mismatched proof (proof for a different cube, or a stale proof for an
  earlier miter):** the checker always reconstructs `F_C` freshly from the
  *current* `F` and `cubes[i]` immediately before calling `check_drat(&F_C,
  &cube_proofs[i])`; a proof for anything else fails RUP/RAT checking against
  that specific formula.

So the checker's trust surface is exactly `check_drat`, unchanged and reused
twice (per cube, and once for the covering formula) — no new trusted
component, per the "checker must not trust the splitter" and "do not weaken
`check_drat`" constraints. This is also why the design rejects the two
alternatives below: both would either enlarge that trust surface or make an
error in the splitter's covering claim unfalsifiable rather than merely
un-checkable-until-fixed.

## Evidence

- Publicly activated in `axeyum-cnf::cube` on 2026-08-26. The substantial implementation and
  twelve controls already existed as a dormant, unexported source file; this increment
  preserved them, exported the module, and added the textual file-backed backward route plus
  deterministic emitter/checker examples. The checker reconstructs every `F AND cube`
  formula and the covering CNF from the same literal lists; neither route accepts a
  splitter-supplied formula.
- Fourteen focused controls now check complete composition, stable Boolean-product order,
  selector admission, SAT discovery, file-backed equivalence, proof-count mismatch, a
  missing leaf, a forged or incomplete proof, an empty cover, and an out-of-range literal.
  Each malformed composition fails closed.
- The generic emitter first exposed source variable 1 as already forced, then produced an
  adaptive four-leaf cover of the PRIMATEs-inverse MC=7 frontier over source variables 2 and
  3. The independently generated covering formula has four clauses, and its two-step DRAT
  proof checks before any leaf search is credited. All four live leaves interrupted at 600
  seconds, so the composition is incomplete and no bound is credited.

- `docs/plan/exploration-track/phase-6-parallel/README.md`'s calibration
  table: Boolean Pythagorean Triples' published certificate is literally
  {transformation proof, cube summary, **365 MB tautology proof that the cube
  set is exhaustive**, per-cube proofs} — the three-part structure this ADR
  adopts, independently arrived at for a different domain (Rado/vdW numbers)
  before this task started.
- `grep assum crates/axeyum-cnf/src/proof_sat.rs` — no matches, confirming
  T6.4's finding that the proof-producing core has no assumption interface, so
  cube-as-units is not a workaround but the only route that needs no new API
  on the soundness-critical core.
- `CnfFormula::add_clause` (`crates/axeyum-cnf/src/lib.rs:251`) already
  returns `CnfError::InvalidVariable` for a literal outside the formula's
  variable count — the bounds check the checker relies on already exists and
  needed no new code.
- `axeyum_fp::is_nan`/`is_infinite`/`is_zero`/`is_subnormal`/`is_normal`
  (`crates/axeyum-fp/src/lib.rs`) already produce boolean `TermId`s per format,
  and `BitLowering::literal_for_term_bit` (`crates/axeyum-bv/src/lib.rs:585`)
  already exposes the AIG literal for any lowered term bit — the selector
  variables this ADR's cube generator needs are already producible from
  existing public API, wired at the call site rather than added to either
  crate.

## Alternatives

- **LRAT-style stitching (resolve sibling per-cube lemmas up a binary split
  tree into one proof whose root is the empty clause).** This is the
  asymptotically better answer at Schur-5 scale (one proof, no separate
  covering artifact) and is exactly what a decision-tree cube generator makes
  *possible*: reformulating each leaf's "`F ∧ cube ⊢ ⊥`" proof as a RUP
  derivation of the clause `¬cube` from `F` alone (dropping the assumed
  units), then resolving sibling lemmas `¬(cube∧l)` and `¬(cube∧¬l)` on `l` to
  get the parent's `¬cube`, bottoming out at the root's empty clause. Rejected
  **for this increment**: the correctness of that reformulation step (which
  learned-clause steps under assumed units remain RUP against `F` alone, and
  which literals must be stripped from which clauses) is itself a new
  soundness-relevant transformation with no independent check of its own — it
  would either need a new verified transform or it would need to modify
  `check_drat`/`check_drat_backward`'s trusted core to understand
  "proof-relative-to-assumptions," which is exactly what the task's hard
  constraint forbids. The two-artifact design above gets the same soundness
  property (one committed sentence: "cubes cover, and each cube's conjunction
  with F is impossible") by calling the *existing, unmodified* checker twice
  instead of teaching it a new proof shape. Revisit once Schur-5-scale
  cube counts make per-cube proof duplication of `F`'s clauses (recall: `F_C`
  clones every clause of `F` for every cube) a measured problem — flagged
  under Consequences.
- **A single "top-level tautology proof that the cubes cover," folded into the
  same proof stream as the per-cube refutations (one combined DRAT file).**
  Rejected as a false economy: it is the same content as the two-artifact
  design's `covering_proof`, just concatenated into one file instead of kept
  separate. Keeping it a separate, independently-checkable artifact is
  strictly better for the sharding goal this task exists for — the covering
  check is tiny and can be validated once while per-cube proofs are still
  streaming in from parallel workers, and `check_cube_refutation` can report
  *which* cube failed instead of an opaque failure partway through one
  monolithic proof.
- **Emit per-cube proofs plus a machine-checkable covering argument that is
  *not* itself a DRAT/SAT instance** (e.g. a hand-verified enumeration that a
  decision tree's leaves partition the boolean cube). Rejected: this is
  strictly weaker evidence for a strictly narrower class of generator (only
  works for a literal decision tree, not e.g. exponent-band cubes expressed as
  ranges) and reintroduces exactly the "trust how the cubes were chosen"
  problem for any generator whose exhaustiveness isn't syntactically obvious.
  Expressing covering as an ordinary UNSAT instance is *more* general (works
  for any literal-based cube family) and *cheaper to build* (no new checker
  logic) than a bespoke combinatorial proof of tree-completeness.
- **Add an assumption interface to `proof_sat.rs`** (T6.4's other branch) so
  cubes can be handed to the core as native assumptions rather than as cloned
  unit clauses. This would avoid re-cloning `F`'s clauses per cube (a real
  cost — see Consequences) but means extending the soundness-critical
  proof-producing core's search *and* its proof-emission logic (assumption
  literals must not appear in the emitted DRAT, or `check_drat` would need
  changes too) before any cube work could land. Deferred: cube-as-units is
  strictly simpler to get right first, and nothing in the composite-artifact
  design forecloses swapping the per-cube solve for an assumption-based one
  later — `CubeRefutation`'s shape (cubes + independent per-cube DRAT proofs)
  does not care how each proof was produced, only that `check_drat` accepts
  it against `F_C`.

## Consequences

- **Easier now:** any hard `unsat` whose case structure is known up front (FP
  miters via classification predicates; the existing Rado/vdW `cube-cover.tsv`
  artifacts in `axeyum-search`, which can now target a real DRAT-checked
  certificate instead of an ad hoc cover file) can be certified by cubes that
  are each independently bounded, independently retryable, and independently
  parallelizable — a timed-out cube is a counted non-certification, not a
  6-hour unbounded hang. Per-cube checking is embarrassingly parallel for the
  same reason production is: `check_cube_refutation`'s loop over cubes has no
  cross-cube state.
- **Harder now, explicitly deferred:** cube counts stay small enough that
  cloning `F`'s clauses into every `F_C` is cheap. At PTN/Schur-5 scale this
  clone becomes the dominant cost long before proof size does (T6.4/T6.5's
  own warning: "conversion + checking cost more than solving" for Schur-5).
  This is exactly the LRAT-stitching alternative's motivating case; revisit
  when a measured cube count makes per-cube `F` duplication material, not
  before — no premature generalization to a proof shape this task cannot
  independently verify today.
- **Not decided here, and not blocked by this ADR:** the lookahead/adaptive
  splitter (T6.3), external conquer engines as untrusted search amplifiers
  (T6.1), the parallel orchestrator and budget ledger (T6.6), streaming/LRAT
  at scale (T6.5), and a hardness predictor for adaptive re-splitting (T6.8).
  Each can be built against the `CubeRefutation`/`check_cube_refutation`
  contract without revisiting this ADR, since none of them changes what a
  cube *is* or how it is checked.
- **Measurable immediately:** cube count, how many cubes are closed
  trivially (near-zero conflicts / a NaN-guard unit propagation away from
  empty), and the cost of the hardest surviving cube — the exact three
  numbers the task asks for — become ordinary per-cube statistics rather than
  requiring the monolithic run to finish first.
- `proof_sat.rs` and `drat.rs`/`drat_backward.rs`/`lrat.rs` are **untouched**
  by this decision, satisfying the hard constraint not to weaken any existing
  checker to accommodate the new composite format.
