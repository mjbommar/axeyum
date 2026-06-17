# The multiplier SAT wall — why it's hard, and the paths through it

Status: **design note (measurement-grounded).** Records, for the next session, what
the curated-slice performance ceiling actually is, *why* the remaining hard
instances resist CDCL, and the concrete technique options — so the "custom CDCL
core / algebraic BV reasoning" item is approached with the right tool, not a
generic "make the SAT solver faster."

## The measurement (what's actually unknown)

On the committed 43-file curated QF_BV slice (`sat-bv`, 2 s), after the
AC-normalization preprocessing win, **35/43 decide; the 8 remaining are ALL
`rustsat-batsat` SAT-solver timeouts on multiplier-equivalence instances**:
`brummayerbiere3 mulhs08/16/32/64` (multiply-high), `calypto problem_12/16`,
`stp_samples 22930-*`. Their CNFs are small-to-mid (2.7k–200k clauses), so it is
**SAT-solving time, not encoding size**, that dominates — and CNF preprocessing
(subsumption + BVE) is already applied and does not crack them.

## Why CDCL alone cannot crack these cheaply

These are **multiplier-equivalence / multiply-high** problems. Bit-blasted integer
multiplier circuits are the canonical hard case for resolution: proving two
multiplier encodings equivalent (or a multiplier UNSAT) has **exponential
resolution lower bounds** — CDCL, whose proof system is resolution, inherits them.
A faster CDCL (better restarts/VSIDS/inprocessing, as in CaDiCaL/Kissat) shifts the
constant but not the asymptotics; pure bit-level search will not scale on
multipliers. This is a *proof-system* limitation, not an implementation one.

## The paths through the wall (in increasing power and cost)

1. **Word-level structural equality (cheapest; partly done).** Many "hard"
   multiplier goals are actually *structural*: commutativity (`a*b = b*a`) and
   associativity-commutativity over multiplier trees. axeyum's
   **AC-normalization canonicalizer** already dissolves these before bit-blasting
   (it cracked `wienand commute08/16`). Extending the structural net — distributivity
   normal forms, `mul`-by-constant strength reduction, common-subexpression sharing
   across the operand trees — catches more *without any SAT*. This is the
   highest-ROI next step and stays in `axeyum-rewrite` (sound, denotation-preserving).

2. **XOR extraction + Gaussian elimination (medium).** Multiplier/adder CNF carries
   dense XOR (parity) structure. Extracting XOR constraints and solving them by
   **Gaussian elimination** (as CryptoMiniSat does — `references/cryptominisat/src/`
   `xorfinder.cpp`, `gaussian.cpp`, `matrixfinder.cpp`, `packedmatrix.h`) lets the
   solver reason about parity in polynomial time instead of resolving it out
   bit-by-bit. This is a real, in-scope engine technique with a Rust-portable
   reference design; it cracks the XOR-structured fragment that defeats plain CDCL.
   It is a *new SAT-engine capability* (CDCL(XOR)), not a rewrite.

3. **Algebraic / Gröbner-basis reasoning (the SOTA; large).** The state of the art
   for *multiplier verification* is algebraic: model the circuit as polynomials
   over `Z` / `GF(2)`, and reduce the specification polynomial modulo the gate
   polynomials' Gröbner basis (AMulet/PolyCleaner-style). This certifies multiplier
   equivalence in polynomial time and even emits a **Nullstellensatz/PAC proof
   certificate** — which would slot into the proof track (an algebraic certificate
   alongside the bit-level DRAT/Alethe). This is a substantial research-scale
   subsystem (a polynomial arithmetic engine), the genuine "algebraic BV reasoning"
   item, and the only path that fully scales on dense multipliers.

4. **Word-level BV reasoning (orthogonal; large).** z3's polysat and bitwuzla's
   propagation-based local search avoid bit-blasting multipliers entirely. axeyum's
   planned **PBLS engine (P1.7)** is the local-search half of this for *satisfiable*
   instances; it does not help the *unsat* multiplier-equivalence cases here.

## Recommendation / staging

- **Now (sound, bounded, no SAT):** keep extending the word-level structural net
  (path 1) — it is the cheapest decided-rate gain and reuses the AC-normalization
  machinery; measure each addition on the curated slice (`DISAGREE=0` is the
  invariant).
- **Next engine step (medium):** CDCL(XOR) via XOR-finding + Gaussian elimination
  (path 2), porting the CryptoMiniSat design — the first real attack on the
  remaining 8, and a self-contained SAT-engine feature.
- **The frontier (large, research):** an algebraic/Gröbner multiplier engine (path
  3) with a PAC/Nullstellensatz certificate — the SOTA, and the one that also
  *produces a proof*, fitting the project's "untrusted search, trusted checking"
  identity.
- A *generic* "faster CDCL core" (path: better resolution heuristics) is explicitly
  **not** the answer to this slice — the lower bounds make it a dead end for
  multipliers. Invest the custom-core effort in CDCL(XOR) and the algebraic engine.

## Measured: path 1 has a ceiling on this slice (2026-06)

After landing the sound word-level structural rules of path 1 — strength reduction
(`bvmul`/`bvudiv`/`bvurem` by `2^k` → shift/mask) and the BV slice family
(extract-of-concat, extract-of-extend, concat-of-adjacent-extracts), on top of
commutative/AC operand ordering, involutions, reflexivity, and `ite`/identity folds
— the curated QF_BV slice (`sat-bv`, `--rewrite default --preprocess`, 2 s) measures
**35/43 decided, 8 unknown, DISAGREE=0, replay failures=0, `rewrite_apps`=443**.

That is **unchanged from the 35/43 before this batch** (the AC-normalization piece is
what moved it 32→35 by dissolving the *commutativity* trees), even though
`rewrite_apps` rose (the new rules fire across the corpus and are sound). This
**empirically confirms** the diagnosis above: the remaining 8 are genuine
**`var*var` multiplier-equivalence** instances (`mulhs`, `calypto`, `stp_samples`)
with no constant divisor/shift and no commutativity/associativity structure to
exploit — so **no word-level structural rule can crack them**. Path 1 is therefore
*sound general value* (it helps other corpora and never regresses, `DISAGREE=0`) but
has reached its ceiling on this slice. The remaining 8 require **path 2 (CDCL(XOR))
or path 3 (algebraic)** — there is no path-1 shortcut left for them.

## Bottom line

The curated wall is multiplier-equivalence, which is provably hard for the
resolution proof system CDCL uses. Do not "tune the SAT solver"; instead (1) widen
the sound word-level structural simplifications, then (2) add XOR+Gaussian
reasoning, then (3) build the algebraic engine — the last two are the substance of
the P1/P2 "custom core / algebraic BV reasoning" item, now diagnosed rather than
guessed.
