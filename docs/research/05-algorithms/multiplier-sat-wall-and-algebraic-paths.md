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

## Path 2 implemented: CDCL(XOR) foundation (2026-06, slices 1-3)

The reasoning *engine* for path 2 now exists in `crates/axeyum-cnf`, built as
three sound, independently-tested slices (the SAT-loop *integration* is slice 4,
still pending — see below):

1. **`gf2.rs` — GF(2) linear (XOR) system solver.** `Gf2System::new/add_constraint/
   solve` Gaussian-eliminates a system of `(⊕ of a variable set) = parity`
   constraints (bit-packed `Vec<u64>` rows; duplicates cancel by parity) to RREF.
   A `0 = 1` row ⇒ `Unsat`; otherwise a satisfying assignment plus the derived
   facts that make this useful for SAT: `implied_units` (single-variable rows) and
   `implied_equalities` (two-variable rows: `xi == xj` or `xi == !xj`). Backbone
   test invariant: the returned assignment satisfies every input constraint.
2. **`xor_extract.rs` — sound XOR-gate extraction from CNF.** `extract_xors(cnf)`
   groups clauses by their repeat-free variable set and recognizes a width-`k`
   gate **only** when the group is exactly the `2^(k-1)`-clause complete encoding
   of one popcount-parity class (the gate's `rhs` is derived from that parity).
   `k` capped at `MAX_XOR_VARS = 8` (as CryptoMiniSat caps). The recognition is
   *exact*: a missing/extra/duplicate clause, mixed parity, or over-cap group is
   not recognized — false negatives are safe, false positives would be a soundness
   bug. Proven by no-false-positive tests plus a brute-force truth-table parity
   check.
3. **`xor_propagate.rs` — preprocessing pass.** `xor_propagate(cnf) ->
   { Unsat, Propagated { formula, stats } }`, in the pure-function idiom of
   `simplify`/`eliminate_variables`. Each recognized gate is logically equivalent
   to a clause-subset of the formula, so the formula entails the whole XOR
   subsystem: a contradictory subsystem proves the formula UNSAT, and the solver's
   implied units (entailed, hence model-preserving) are appended as unit clauses.
   Soundness is the contract, proven by brute-force over all `2^n` assignments:
   model-set preservation, UNSAT soundness *and its converse* (a satisfiable
   formula is never reported UNSAT), and the no-op case.

**Slice 4 done & measured (2026-06, commit edf65b8):** `xor_propagate` is wired
into `sat_bv_backend`'s `inprocess` (behind `cnf_inprocessing`, off by default),
using only the sound Propagated branch (entailed units appended; no unchecked
UNSAT shortcut), with a 20k-clause cap on the deadline-less Gaussian. Curated
slice (sat-bv `--inprocess`, 2 s): **33 decided, DISAGREE=0, 0 replay failures,
PAR-2 0.968 s vs 0.963 s plain** — sound, no regression, decides none of the
unknowns. The informative part: **extraction fired on 20/43 files, recognizing
12 908 XOR gates, yet derived only 1 implied unit across the whole slice** (5 big
multipliers skipped on the cap). This is the concrete, on-corpus confirmation of
the prediction above — multiplier parity structure forces essentially no units at
preprocessing time. **The gates are relational, so the payoff is in the
equalities, not the units.**

**Slice 5 (equality substitution) — measured low-value, deprioritized
(2026-06).** A follow-up measurement counted the implied *equalities* the GF(2)
solve exposes (`equalities_available`): across the 20 firing files, 12 908 gates
yield **351 equalities** — but they concentrate on the **AC-structured**
`commute`/`distrib`/`bit-counting` instances (`commute08`=101, `commute04`=53,
`distrib04`=40, `bit-counting`=128), **not** the core multiplier-equivalence
unknowns: `mulhs16` has 1626 gates but **1** equality; `mulhs08`=1;
`stp_samples`=0; `calypto_9`=1. So equality substitution would help (at most) the
instances the AC canonicalizer already targets by another route, and is ~0 on the
genuine multiplier wall. Building its variable-merge + model-reconstruction
machinery is therefore low marginal value; it stays unbuilt until a corpus shows
equality-rich *hard* instances. **The static-preprocessing investigation of path 2
is closed: neither units nor equalities crack the curated multiplier unknowns.**

**Slice 6 (the real lever) — full CDCL(XOR).** In-search Gaussian re-derivation on
the CDCL trail (CryptoMiniSat `gaussian.cpp`/`packedmatrix.h` design): the solver
maintains the XOR matrix as the search assigns variables, so it sees the
structure the *static* system cannot — the nonlinear AND-gate partial-product
values that only the search fixes. This is where multiplier parity is actually
exploited, and it is a genuine SAT-engine capability (a new propagator alongside
unit propagation), not a preprocessing pass. It composes with the now-validated
`gf2`/`xor_extract` foundation (the extraction + matrix are reused on the trail).
This is the substantial next slice; the preprocessing slices 1–4 are the sound,
measured groundwork it builds on.

## Bottom line

The curated wall is multiplier-equivalence, which is provably hard for the
resolution proof system CDCL uses. Do not "tune the SAT solver"; instead (1) widen
the sound word-level structural simplifications, then (2) add XOR+Gaussian
reasoning, then (3) build the algebraic engine — the last two are the substance of
the P1/P2 "custom core / algebraic BV reasoning" item, now diagnosed rather than
guessed.
