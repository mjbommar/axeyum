# agent-i — roadmap feedback for axeyum itself

Cited by file and line. Everything here was hit during the CAS bridge work on
2026-08-13.

---

## F1. `interval_arith.rs::abs()` can panic, alone among its siblings

`crates/axeyum-cas/src/interval_arith.rs:211` returns `Interval`, not
`Option<Interval>`, and reaches that by calling `.expect("interval abs overflow")`
twice at `crates/axeyum-cas/src/interval_arith.rs:223-224`.

Every other operation in the module — `add`, `sub`, `mul`, `neg`, `div`, `pow`,
`intersection`, `hull`, `evaluate_polynomial` — returns `Option` and the module
header at `crates/axeyum-cas/src/interval_arith.rs:12-14` states the reason
explicitly: "operations that would overflow return `None` rather than a wrapped
(unsound) result, so a graceful failure never masquerades as a valid enclosure."

`abs()` violates its own module's stated contract, and it is reachable from any
consumer that hands it an interval with an endpoint near `i128::MIN`. A CAS
function that *aborts the process* cannot be called from a solver route, because
`unknown` is a first-class result and a panic is not. This is the single reason a
bounded-box interval refuter is not buildable on `interval_arith` today without a
wrapper.

**Ask:** make it `Option<Interval>`. It is a one-line signature change with two
call sites in-crate.

## F2. `nra-real-root` discards its decline reason, and that made the demand invisible

`crates/axeyum-solver/src/auto.rs:3334-3336` records
`DeclineReason::NotApplicable` with **no payload**, for a route
(`crates/axeyum-solver/src/nra_real_root.rs`, 7684 lines) with at least fifteen
distinct reasons to decline — `MAX_ABS_COEFF`, `MAX_DEGREE = 64`,
`MAX_SYLVESTER_DIM = 24`, `MAX_MULTI_SYLVESTER_DIM = 6`, `MAX_CAD_CELLS = 256`,
"more than one distinct variable", "a non-polynomial operator", an unresolvable
algebraic-vs-algebraic ordering.

The NIA side has `record_nia_decline` (`crates/axeyum-solver/src/auto.rs:3697`)
and a documented history of the bug that motivated it. The real side has nothing
equivalent, so the real-arithmetic demand is **un-instrumented**. I could only
find the two real-side gaps this bridge closes by writing probe queries and
guessing; a payload would have handed them to me.

**Ask:** give `nra-real-root` the `record_nia_decline` treatment. It is the
highest-value diagnosability change in the dispatch, because it is the widest
route with the least visibility.

## F3. A route that returns `Some(Unknown)` silently truncates the ladder

`crates/axeyum-solver/src/auto.rs:3324-3333`: when
`nra_real_root::decide_real_poly_constraint` returns `Some(Unknown)`, the real
branch returns immediately and `nra` below (`auto.rs:3356`) is never reached. The
same shape exists elsewhere.

This is invisible in the trace — the trace shows `nra-real-root` deciding, which
reads as "the route answered", not "the route ended the ladder". It cost me a
measurement cycle: `x+y+z = 1 ∧ xy+yz+zx = 1 ∧ xyz = 1 ∧ x²+y²+z² ≥ 0` stayed
`unknown` after my route was correctly placed, because the route was placed after
the *decline* path and this query took the *Some(Unknown)* path.

I worked around it locally (`auto.rs`, the `matches!(result, CheckResult::Unknown(_))`
guard) but the general shape deserves a decision: **an `unknown` should never be a
`return` in a ladder unless the ladder is provably exhausted.** Either make these
routes return `None` on `unknown`, or make `record_result` distinguish "decided"
from "gave up and stopped everything".

## F4. `--lib` runs 23 of 968 solver unit tests on default features, and CLAUDE.md's own gate list has been inert before

Confirmed again today: `cargo test -p axeyum-solver --lib --features full` is 1121
tests; without `--features full` it is a fraction. CLAUDE.md already documents
this trap at length, including the 15-day inert `corpus_regression` and the
`progress_frontier` line that lacked `--features full` until 2026-08-04.

The pattern is now three-for-three. **Ask:** make the flag impossible to omit —
either a `required-features` on the test targets so the bare form fails to build
rather than passing vacuously, or a `#[test] fn suite_is_not_empty()` in each
`#![cfg(feature = "full")]` suite that is *outside* the cfg and asserts the suite
compiled. An exit-0-with-zero-tests is the house failure mode and it is still
possible today.

## F5. Multi-agent: a shared file was clobbered mid-session, and pathspec discipline did not prevent it

My export edit to `crates/axeyum-solver/src/lib.rs` was silently reverted between
two of my own commands. `git status --short` showed the file clean against a HEAD
that had moved to `1b2b13c70` ("compact clausal reconstruction"), a commit from
another lane that also touches `lib.rs`. My other seven files were untouched.

I followed rule 4 (pathspec-only) and rule 7 (own snapshot) throughout; neither
protects a *working-tree* edit to a file another lane commits. This is the same
class as frontier rule 9 ("shared append points are not protected by pathspecs")
but for source, not docs — and `lib.rs` is the most-shared file in the crate,
because every new module has to export through it.

**Ask:** add to the hygiene doc that `crates/*/src/lib.rs` is a shared append
point, and that a lane should commit its export line **immediately** rather than
carrying it in the working tree. I lost ~10 minutes; a lane that noticed later
would have lost a green gate to a mystery.

## F6. `groebner.rs`'s round-trip through `to_cas_expr` is the whole cost of the new route

`crates/axeyum-cas/src/groebner.rs:255-260`: `leading_term` recovers a
polynomial's terms by rendering it to a `CasExpr` and re-expanding, because
`MvPoly` exposes no leading-term accessor under `lex`
(`crates/axeyum-cas/src/groebner.rs:34-42` documents the workaround). That call is
in the inner loop of every reduction step.

It is why `cas-ideal-refuter` costs milliseconds where the ADR-0386 routes cost
microseconds, and therefore why it had to be moved off the fast path. Exposing
`MvPoly::leading_term_lex()` — the data is already in the `BTreeMap` — would
likely be a one-to-two order of magnitude improvement and would let the route sit
earlier in the dispatch.

## F7. Twelve CAS modules have no possible consumer, and that is a scoping signal

`orthopoly`, `series`, `ratint`, `stats`, `sets`, `combinatorics`, `gfp`,
`geometry`, `boolean`, `permutation`, `special`, `hyperbolic` — no solver route
asks the questions they answer, and no plausible near-term route does either.
That is roughly 5 000 lines of tested, documented, correct code with no path to a
dependent.

This is not a bridge problem and it should not be framed as one. Either the CAS is
a **product surface in its own right** (a library users call directly, with its own
README and examples), in which case the "no dependents" observation is not a defect
— or it is solver infrastructure, in which case those modules are speculative and
new CAS work should be demand-driven. The current framing ("the CAS has no
dependents") implies the second while the code was built as the first.

**Ask:** decide which, in an ADR. The answer changes what "wire the CAS in" even
means, and it is the reason item 2 of NEXT-MATH-STACK reads as a bigger gap than it
measured out to be.

## F8. Tamper tests across this project may be testing one thing six times

This is the finding I would most want propagated, because the pattern is not
specific to my code.

`crates/axeyum-solver/src/cas_certificate.rs` has seven independent guards. I
wrote eight tamper tests, confirmed they all failed when the checker was stubbed
to `return true`, and reported "8 of 8 controls fire". Then I ran the strong
mutation — **delete one guard at a time** — and six of the seven guards could be
removed with every tamper test still green.

The reason generalises to any certificate checker in this project. A tamper test
mutates a *valid* certificate; the mutation breaks the arithmetic identity; the
identity check rejects it before any specific guard is consulted. So the suite
tests the identity check N times and nothing else.

The fix that worked is a different construction, which I would suggest as the
house pattern: a **forgery** — a certificate for a query that is genuinely
*satisfiable*, built so the arithmetic is perfect and exactly one guard stands
between it and a wrong verdict. Six of those map 1:1 onto six guards: each guard
deletion kills exactly one forgery and no other.

ADR-0386's own evidence section says "Four tamper tests confirm the checker
rejects a truncated normal form, a foreign assertion, an inflated bound, a
misattributed bound source, and a relabelled refutation kind"
(`docs/research/09-decisions/adr-0386-cas-refutation-routes.md`). Those are the
same construction as mine, on the same expander, so they are worth re-measuring
with per-guard mutation. I did not touch them (they pass, and they are not my
lane), but I would expect several to be in the same position.

**Ask:** adopt per-guard mutation as the standard for "this control fires", not
whole-checker stubbing, and record the guard→control mapping. It is cheap — one
`sed` and one test run per guard — and it is the difference between a checker
that is guarded and a checker that appears to be.

A related, smaller finding from the same exercise: one of the seven guards (an
equality cited as a product factor) is **not soundness-critical** — an equality's
polynomial is zero in every model, so the product contributes zero. No forgery of
that shape can exist. Being able to *say which guards are load-bearing* is itself
worth the exercise, and it is not visible any other way.
