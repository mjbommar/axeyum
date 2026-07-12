# ADR-0107: Checked Boolean-guard models for quantified SAT

Status: accepted
Date: 2026-07-11

## Context

After ADR-0106, every decided row in the 12-file quantified-LIA slice has
checked evidence and a Lean proof, but three rows remain unsupported. Two are
satisfiable: `015-psyco-pp` and `psyco-196`. Both assert large closed Int/Bool
universals under a ground Boolean configuration. They do not require Skolem
functions; they require finding a free-Boolean model under which each universal
body is true for every bound value.

The rejected concrete-tuple CEGQI prototype attacked the separate UNSAT row and
made no progress after 32 large tuples. For the SAT rows, model-based search is
the correct direction: first choose the ground Boolean configuration, then check
the quantifiers against that candidate model. Z3's MBQI model checker follows
this broad architecture, but Axeyum needs a smaller replayable certificate
before claiming `sat`.

## Decision

Add a deterministic Boolean-skeleton model search for Bool/Int quantified
queries:

1. replace quantifier subterms by `true` only in an untrusted search clone;
2. solve the resulting quantifier-free skeleton for a candidate model;
3. complete every free Boolean symbol deterministically;
4. check every untouched original assertion with a separate abstract evaluator
   or a source-bound arithmetic refutation;
5. when a concrete counterexample exists, trace its false path to a sufficient
   free-Boolean cube and block that cube; otherwise block the complete assignment;
6. try the next candidate within explicit case and shared deadline limits; and
7. return `sat` only with a typed certificate that canonical `check_model`
   independently rechecks.

The checker uses exact three-valued reasoning:

- free Boolean symbols take only their carried values;
- bound Boolean quantifiers are exhaustively enumerated under a hard case cap;
- bound Int values remain symbolic;
- Boolean connectives use sound short-circuit semantics;
- integer `ite` follows a guard only when that guard is definitely known;
- linear integer expressions are compared by checked affine normalization; and
- every unsupported or unresolved proposition is `unknown`, never `true`.

When structural evaluation remains unknown, the checker drops only
positive-position universal binders, substitutes the carried free-Boolean
values, and negates the resulting universal closure. Integer `ite` terms are
lifted exactly to fresh variables plus guarded equalities. The existing
LIA-DPLL certifier must then refute that exact QF formula. Its theory cores are
rechecked by exact arithmetic procedures, and its propositional skeleton is
bound back to the source assertions. Small closures are checked by Boolean
enumeration; larger closures carry a deterministic DIMACS/DRAT proof whose
source encoding and proof are both rechecked. Arena-local proof terms are never
stored in `Model`: replay regenerates and checks the refutation in its own arena
from original symbol IDs and Boolean values.

Thus the certificate proves that the original formula is true for all bound
values. Quantifier erasure and QF models are candidate generation only. The
default product remains pure Rust; native solvers remain differential oracles.

This decision does not claim general quantified model construction. It covers
only formulas whose validity under a concrete free-Boolean assignment is proved
by the independent checker. It also does not address the remaining UNSAT row,
which still needs symbolic or clause-level CEGQI.

## Acceptance

- Both measured SAT rows move from unsupported to replay-checked `sat` within
  the 10-second corpus budget.
- `006-cbqi-ite` remains `unsat` or undecided, never `sat` through this route.
- Synthetic tests cover free guards, bound Bool enumeration, affine/reflexive
  Int atoms, unresolved arithmetic rejection, generalized candidate blocking,
  source-bound large-skeleton DRAT, case caps, and certificate tampering.
- Every returned model passes canonical replay against untouched assertions;
  removing or changing a carried Boolean value fails replay.
- Fresh corpus measurement and dominance audit report no disagreement, model
  replay failure, audit error, timeout, or trust hole.
- Focused tests, solver/evidence/bench splits, workspace Clippy,
  warning-denied rustdoc, links, foundational resources, formatting, and golden
  matrices pass; the known whole-aggregate limitation is recorded.

## Validation

- The focused default and all-feature integration suites pass 6/6; the solver
  all-feature library suite passes 830/830, including the hard checker-cap
  regression. Evidence and benchmark splits pass 69/69 and 7/7.
- Capability and support goldens pass 2/2 and 12/12. Workspace all-target,
  all-feature Clippy with warnings denied, warning-denied rustdoc, links,
  formatting, and the 137-concept/174-pack foundational-resource check pass.
- A fresh 10-second release measurement decides 11/12 rows (sat 4, unsat 7,
  unsupported 1), with DISAGREE=0 and no model-replay failure. The independent
  audit checks and certifies 11/11 decisions, kernel-checks all 7 UNSAT rows,
  and records 11/11 dominant candidates with no mismatch, audit error, timeout,
  or trust step.
- No external Lean binary is installed. No whole-workspace aggregate is claimed
  because of the known pre-existing Sturm nontermination.

## Alternatives

- **Treat a quantifier-erased skeleton model as proof.** Rejected: it says
  nothing about the original universal.
- **Replay one or several concrete Int tuples.** Rejected for SAT: finitely many
  instances cannot establish an infinite-domain universal.
- **Call Z3/cvc5 to validate the candidate.** Rejected as a product dependency;
  native solvers remain optional oracles.
- **Implement full MBQI model repair now.** Deferred: Boolean-guard models are a
  measured, independently checkable class and exercise the same candidate/check
  contract without inventing function interpretations prematurely.

## Consequences

- The two remaining SAT rows can receive genuine replay and Pareto credit if
  their Boolean configurations lie in the checked class.
- `Model` gains a second arena-stable quantified-SAT certificate family
  alongside affine Skolem recipes.
- The division can reach 11/12 decided without obscuring that the last UNSAT row
  still requires scalable CEGQI.
- Broader arithmetic model checking, piecewise Skolem functions, and function
  interpretations remain explicit future work.
