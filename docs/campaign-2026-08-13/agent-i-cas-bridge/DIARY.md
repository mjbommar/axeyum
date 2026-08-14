# agent-i — CAS/solver bridge diary

Append-only. Order of discovery is the useful part.

## 2026-08-13 — orientation

Read `NEXT-MATH-STACK.md` item 2, ADR-0386, `CLAUDE.md`, frontier README.

Snapshot at `~/.cache/axeyum-agent-i` from `git archive HEAD` (rule 7 — on disk,
not `/tmp`). Baseline build of `-p axeyum-solver --features full --tests`:
1m21s, clean. Host: s1.

## Surface reading (I1, supply side)

Read `sturm.rs` (303 lines) end to end, and the public signatures of
`groebner.rs`, `algebraic.rs`, `interval_arith.rs`, `mvpoly.rs`.

First real finding: the solver **already has** a 7684-line univariate real-root
decider, `crates/axeyum-solver/src/nra_real_root.rs`, which does exactly what
`axeyum-cas/src/sturm.rs` (303 lines) does — Sturm chains, sign-cell
decomposition, exact rational arithmetic — and does it *better* (it handles
conjunctions of constraints, produces `RealAlgebraic` witnesses, replay-checks
them). So the naive read "wire Sturm into the solver" is **wrong**: that
capability is not missing, it is duplicated. The doc header of
`nra_real_root.rs:14-31` says the scope is "one shared `Real` variable `x`" and
it declines on "more than one *distinct* variable".

That relocates the gap. It is not univariate real algebra. It is **multivariate**.
And multivariate is exactly where `groebner.rs` lives and where the solver has
nothing.

Second finding, from reading `groebner.rs:415-426`: `ideal_contains` returns
`Option<bool>`. A bare bool. Under ADR-0386's own standard ("a CAS answer that
cannot be re-checked is not evidence") that is unusable as-is — you would have to
trust Buchberger, the lex leading-term selection, `MvPoly` canonicalization and
every exact-rational op underneath. The subagent survey confirmed: groebner.rs
has **zero** occurrences of certificate/witness/proof vocabulary, and the crate
has no public `verify`/`check_certificate` free function at all.

So the bridge has two halves and the first half is a *missing artifact*, not
missing plumbing.

## Decision: which capability

Picked **multivariate ideal refutation with a Nullstellensatz / Positivstellensatz
certificate**, because:

- it is the one thing `nra_real_root.rs` structurally cannot do (it declines on
  a second variable);
- the certificate is a *polynomial identity*, which the ADR-0386 checker's
  existing independent expander (`cas_certificate.rs:87` `expand`, plus its own
  `add`/`multiply`) can re-derive with no CAS code in the loop;
- it generalises `cas-identity-refuter` exactly (that route is the n=1,
  cofactor=1 special case);
- it is the shape the Rado k=3 obstacle has: degree-3/4 relations in three
  variables.

Rejected for now: SOS/Positivstellensatz with polynomial multipliers on the
inequalities (needs semidefinite or at least LP search — no LP over ℚ wired to
the CAS), and interval branch-and-bound over boxes (needs bounded variables,
which the Rado symbolic case does not have).

## Build 1 — `crates/axeyum-cas/src/groebner_cert.rs`

Cofactor-tracking Buchberger. Every polynomial in the algorithm carries its
representation in the *original* generators, so the output is the identity

    target = Σ cofactor_i · generator_i + remainder

Invariant maintained through three places: initial basis (`rep = e_i`),
S-polynomials (`S.rep = f·A.rep − g·B.rep`), and the division loop
(`target = current + remainder + Σ q_j·basis_j`, so `remainder.rep = target.rep −
Σ q_j·basis_j.rep`).

Deliberately does **not** trim to the reduced Gröbner basis — trimming would need
its own representation bookkeeping for no gain, since reduction to zero modulo
*any* Gröbner basis is already the membership test.

Needed `pub(crate)` on seven private helpers in `groebner.rs` (`Exponents`,
`lex_cmp`, `monomial_lcm`, `monomial_divides`, `monomial_quotient`,
`leading_term`, `single_term`) rather than re-implementing them — a second copy
of the monomial order is exactly the kind of drift that produces a wrong answer.

Gave it explicit `Limits` (step counts, not a clock — determinism is a public API
promise). `Limits::fast()` = 20k reduction steps / 4k pairs / 64 basis / 512
terms. The existing `groebner.rs` caps (1M/5M/100k) are far too generous for a
route that sits on the fast dispatch path.

7 unit tests pass, including `three_variable_cubic_system_is_refuted_with_a_witness`
(elementary symmetric functions of `t³ − 1` plus a false power-sum) and
`a_tight_budget_declines_rather_than_guessing`. Each test **recombines** the
cofactors independently and asserts the identity — the same thing the solver-side
checker will do.

## Build 2 — the solver bridge

Certificate format designed once to cover all three refutation shapes: entries
are either a cited conjunct with a multiplier, or a tautological
`coefficient · monomial` with every exponent even. Sum must be a constant `k`;
three refuting conditions.

The `EvenMonomial` entry is the design decision that made the route useful.
Without it the route only closes systems inconsistent over ℂ. With it,
`x + y = 3 ∧ x·y = 5` closes — because `x² + y² ≡ −1` mod the ideal — and
**nothing in the query mentions `x² + y²`**. The certificate supplies a fact
nobody asserted, and can, because a square is non-negative for free.

Discovery: unit ideal, then sums of atom squares, then asserted inequalities.
All three go through `reduce_with_cofactors` and hand the same certificate type
to the same checker.

## DEAD END 1 — my flagship case was already decided

Wrote 7 positive tests, all passing end-to-end via `cas-ideal-refuter`. Then ran
the same 7 against a pristine `git archive HEAD` snapshot. **Six of the seven
were already `unsat` on the baseline** — `nra-real-root` at 961 µs, `int-real-relax`
at 3.8 ms, `uf-arithmetic` at 6.3 ms.

And my route was *slower*: `x + y = 3 ∧ x·y = 5` over ℝ went 0.96 ms → 3.96 ms.
So placing it beside the ADR-0386 routes on the fast path was a performance
regression dressed up as a capability win. If I had not measured the baseline I
would have shipped it and written the ADR around the wrong claim.

ADR-0386 put its two routes at the top of the dispatch and argued for it: they
are microsecond-scale and exact. That argument does not transfer to a route that
computes a Gröbner basis. Moved it behind `nra-real-root` and
`nia-bounded-blast`.

## DEAD END 2 — the placement did not reach the case it was for

After moving, `x+y+z = 1 ∧ xy+yz+zx = 1 ∧ xyz = 1 ∧ x²+y²+z² ≥ 0` was **still**
`unknown`. Cause: `nra_real_root::decide_real_poly_constraint` returned
`Some(Unknown)`, and `auto.rs:3324` returns immediately on `Some(_)` — the real
branch is over, `nra` below never runs, and my route sat after the *decline*
path, which that query never took.

Fixed with a strictly-additive guard: on `Some(Unknown)` from `nra-real-root`,
offer the ideal route before returning the unknown. Only an `unknown` is ever
replaced, only by a certificate-checked `unsat`. Filed as F3 — a route that
returns `Some(Unknown)` silently truncating a ladder is a general shape, not a
one-off.

## The re-measurement, cleanly

Baseline vs. after, same box, 10 s budget. Five classes moved:

| | before | after |
|---|---|---|
| real `div` atoms | unknown 282 ms | unsat 4.5 ms |
| 3 coupled reals past the CAD caps | unknown 11 ms | unsat 38 ms |
| int `mod` atoms | unknown 801 ms | unsat 83 ms |
| int `div` atoms | unknown 1.24 s | unsat 60 ms |
| int `div` atoms + inequality | unknown 1.73 s | unsat 80 ms |

Everything the existing engines decided keeps its route and its timing.

The pattern in what moved: **it is not "systems of polynomial equations"** — the
existing engines have that covered. It is systems whose *atoms leave the
polynomial fragment*, where `int-real-relax` aborts and `nra-real-root` declines
on a non-polynomial operator. Opaque-atom abstraction is the actual value the CAS
bridge adds, not Gröbner per se.

## Negative controls, and proving they fire

First draft asserted the sat-controls end-to-end ("query stays sat, no cas route
decided"). After the placement move, satisfiable queries get decided by
`nia-linearize`/`nra-real-root` *before* my route runs — so the control would
have passed while the route never looked at the query. Exactly the vacuous shape
the brief warned about. Rewrote all controls to assert on the **route's own
outcome**: `NotRefuted`, never `NoCandidate`.

Then verified each by mutation:

- checker stubbed to `return true` → all **8** tamper tests fail;
- both sign guards mutated off → all **4** behavioural controls fail;
- nonlinearity admission gate mutated off → the linear-system control fails.

13 of 13. No dud.

The odd-exponent tamper is the one I care most about: `x³` is not non-negative,
and admitting it as a square term is the single arithmetic step in the checker
where a wrong `unsat` is possible. It fires.

## Gates and a clobbered file

All green: `axeyum-cas --lib` 572, `axeyum-solver --lib --features full` 1121,
`cas_bridge_routes` 25, `corpus_regression` 1, `route_trace` 12,
`nia_tiny_witness` 4, `progress_frontier` 9/9 (including `frontier_bv_reduction`,
which ADR-0386 saw fail on a loaded box), clippy `-D warnings` clean, links ok.

Mid-session my export edit to `crates/axeyum-solver/src/lib.rs` vanished — HEAD
had moved to another lane's `1b2b13c70`, which also touches `lib.rs`, and my
working-tree edit went with it. Seven other files survived. Pathspec discipline
does not protect a working-tree edit to a file another lane commits. Re-applied,
re-synced the snapshot to the new HEAD, re-ran, committed immediately. Filed as
F5.

Landed `119858e2c` (bridge, 8 files) and `46fa155e3` (ADR-0429).

## I3 — not attempted end to end, and why

Route B's `k = 3` blocker needs degree-3/4 inequalities in three variables over
**unbounded ℤ with a symbolic parameter**. This route is insensitive to degree and
variable count, which is the half it helps with. But its certificate is a
statement about ℝ, and the Rado lemmas are true over ℤ for reasons involving
integrality and the ordering. Where the real relaxation is already unsat,
`int-real-relax` was going to catch it anyway; where it is not, this route
correctly declines.

The missing piece is precise and bounded: **non-negative polynomial multipliers on
the asserted inequalities**. Today an inequality multiplier must be a positive
rational constant, because a polynomial multiplier can go negative. Allowing
`σ · p` where `σ` is itself certified non-negative — and `even_nonnegative_monomial`
in the checker *is* that certificate — turns "multiply `b < a` by a positive
rational" into "multiply it by `t²`". That is exactly the degree-3/4-in-three-
variables shape. Discovery needs a small exact-rational LP over the residues.

That is roadmap item 1, and it is the piece I would build next.

---

## Round two — going after the Rado shape, and finding my controls were fake

## Build 3 — products of asserted bounds

Went back to Route B's blocker. Its micro-lemma `M6` (`M ≥ 1 ∧ w ≥ 1 ⊢ M·w ≥ M`)
is the essence of the degree-3 `L3` that timed out at 60 s, and its refutation is
`(M − M·w) + (M−1)(w−1) + (w−1) = 0` against a floor of 1. The middle term is a
**product of two asserted bounds** — degree 2, and no rational multiplier can
express it.

Added `CasIdealEntry::AssertedProduct` plus a fourth search shape: non-negative
combinations of hypotheses, their pairwise products and atom squares. Added
`reduce_many_with_cofactors` to the CAS so the candidate set shares one Gröbner
basis instead of recomputing it per candidate.

## DEAD END 3 — the Rado lemmas were already solved

Encoded `M6` and `L3` minimally and ran them on the pristine tree.
**Both already `unsat` in ~1 ms via `int-real-relax`.** The campaign's 60 s
timeout was the monolithic hypothesis set, not the shape; the log's `L3` line
elides its hypotheses behind `...` and the control witness mentions a variable my
encoding does not have.

So the product shape earns its place the same way everything else in this route
does — over opaque atoms:

- the `L3` shape over three `div` atoms: **20 s timeout → 207 ms unsat**
- `M6` over real `/` atoms: 60.6 ms via `nra` → 1.2 ms

And one measured miss that pins the incompleteness: `x ≥ y ≥ 0 ∧ x² < y²` over
`div` atoms needs coefficient **2** on a product, and the unit-coefficient search
does not find it. Still `unknown`.

## THE FINDING — six of seven guards could be deleted with every tamper test green

I had reported "13 of 13 controls fire", on the strength of stubbing the whole
checker to `return true`. That is a weak mutation: it only shows the checker is
*called*.

Ran the strong version — delete **one guard at a time**:

| guard deleted | tamper tests that failed |
|---|---|
| even-exponent parity | 0 |
| square coefficient > 0 | 0 |
| conjunct is asserted | 0 |
| kind label matches | 0 |
| product factors asserted | 0 |
| product multiplier positive | 0 |
| stored constant matches | 1 |

Every tamper test rejects through the **identity** check: mutate any number in a
real certificate and the combination stops being a constant, so `as_constant`
kills it before any guard is consulted. My tamper tests were testing the identity
check six times over and nothing else.

This is precisely the failure the brief warned about, and I had walked straight
into it while writing a section claiming I had not.

## The fix — forgeries, not tampers

A tamper starts from a valid certificate and breaks it. A **forgery** starts from
a *satisfiable query* and builds a certificate that is arithmetically perfect —
the combination really is a constant of the refuting sign — with exactly one guard
between it and a wrong `unsat`.

Six of them. The parity one is the clearest:

    x³ = −1                      satisfiable, x = −1
    x³ + (−1)·(x³ + 1) = −1      a genuine constant, refuting sign

Only the even-exponent check stops it, and `x³` is negative exactly where the
model is.

Verified 1:1: each of the six guard deletions kills **exactly one** forgery and no
other.

## And one guard that is not a guard

The checker rejects an equality cited as a product factor. I could not make that
one fire, and then worked out why: an equality's polynomial is **zero in every
model**, so the product contributes zero, which is non-negative. Using an equality
as a product factor is *sound*. The rejection is conservative, not load-bearing,
and no forgery of that shape can exist.

Deleted the three product tamper tests built on it and documented the reason,
rather than shipping a control that tests nothing. That is the whole lesson of the
round: a control you cannot make fail is not conservative, it is decorative.

Landed the product shape + forgeries, and amended ADR-0429 with both findings.
