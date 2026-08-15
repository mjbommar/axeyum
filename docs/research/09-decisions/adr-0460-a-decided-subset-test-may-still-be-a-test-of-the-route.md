# ADR-0460: A Decided Subset Test May Still Be A Test Of The Route

Status: accepted (refines [ADR-0455](adr-0455-minimality-is-relative-to-decidedness.md))
Index-summary: Decidedness is necessary but not sufficient for an absolute minimality claim; the test must also be independent of the producer's decomposition
Date: 2026-08-15

## Context

[ADR-0455](adr-0455-minimality-is-relative-to-decidedness.md) drew a distinction
that has already earned its keep: a minimality claim is **absolute** when every
removal test returned a definite verdict, and **budget-relative** when at least
one was inconclusive. The rule it derived is right, and the failure it prevents
is real.

It is also not the whole test, and `pappus-hexagon` is the counterexample. That
theorem's condition set was reported as **three**. Every one of the eight subset
tests was *decided*: the linear-elimination route settles a subset by dividing
its multiplier, exact division always terminates and always answers, and the
route's own documentation said so in as many words —

> Here every subset test is *decided* — factoring a multiplier by exact division
> always terminates and always answers — so the reported set is smallest among
> the subsets this route can use.

Read against ADR-0455's dichotomy, that is the **absolute** regime: no budget, no
`unknown`, no timeout, nothing a bigger machine could change. And the answer was
wrong. Each of the three conditions suffices **on its own**; the minimal sets are
the three singletons; the theorem now certifies with one condition in 6.7 ms
where it took 292 s with three.

The mechanism is worth stating precisely, because it is not exotic. The route
picks a block decomposition from the *shape of the generators*, knowing nothing
about which conditions the caller is inverting. That decomposition fixes a
multiplier — here the product of all three conditions — and the subset test then
asks:

> can this subset's conditions divide **that** multiplier?

That question is decided. It is also not the question the claim is about. The
claim is about the theorem; the test was about the theorem *under a decomposition
the producer chose for its own reasons*. Every proper subset failed, definitively,
for a reason with nothing to do with the theorem.

The tell was visible and nobody read it: the same three attempts to find a
configuration necessitating one condition kept collapsing, always by the same
mechanism. That was recorded as an obstruction to *claiming* minimality. It was
in fact a proof that the conditions were **redundant** — a collapsing search for a
counterexample is evidence about the theorem, and the sign was read backwards.

## Decision

**An absolute minimality claim requires two things, not one.** ADR-0455's
condition stands and a second joins it:

1. *(ADR-0455)* Every removal test returned a definite verdict.
2. **The removal test must be a test of the subset, not of the subset under a
   representation the producer fixed.** Where a producer chooses anything —
   a decomposition, a multiplier, an elimination order, a variable ordering — that
   choice must be **re-made per subset**, or the claim is relative to the choice
   and must say so.

A test that fails (2) is not budget-relative. It is worse: it is *decided and
wrong*, and it will report as absolute. So it needs its own name and its own
remedy.

- **Absolute.** Both conditions hold.
- **Budget-relative.** Some test was inconclusive (ADR-0455). A stronger run
  might shrink the answer.
- **Representation-relative.** Every test was decided, but against a fixed
  producer-side choice. A *different choice* might shrink the answer — and unlike
  the budget case, no amount of patience will find that out.

**The remedy is preferred to the disclosure.** Where the producer's choice can be
made a function of the subset, do that rather than labelling the claim. In this
instance that is one filter — `licensed_blocks` — admitting a block only when its
determinant is a nonzero rational times a product of powers of the conditions
*currently being inverted*. It is a soundness-shaped rule (never divide by
something no declared condition licenses) doing an honesty-shaped job, and it
turns the reported set from three conditions into one.

**A collapsing search for a necessitating witness is evidence, and its sign must
be stated.** When repeated attempts to show a condition is *needed* all collapse
through the same mechanism, the two live hypotheses are "our witnesses are too
weak" and "the condition is redundant". Those license opposite ledger actions —
the first invites a budget-relative fact, the second forbids filing the larger set
at all — so the report must say which one it is checking, and how.

## Evidence

- `crates/axeyum-cas/src/geometry_certify.rs` — `licensed_blocks` and
  `factors_into`. The certificate for `pappus-hexagon` goes from three conditions
  in 292 s to one in 6.7 ms, with no change to the checker and none to the eight
  certificates that predate it (`emit_geometry_certificates`: **8 unchanged, 1
  written**).
- `crates/axeyum-cas/src/geometry_certify.rs::each_pappus_condition_alone_certifies`
  — the redundancy stated as three certificates rather than as three searches
  that found nothing. All three stated conditions certify alone, at cofactor
  degree 2.
- `crates/axeyum-cas/examples/pappus_condition_subsets.rs` — the same question
  decided exhaustively over `F_p` for `p = 5, 7, 11, 13, 17, 19, 23`: of the
  eight zero/nonzero patterns of the three conditions, exactly one admits a
  configuration satisfying every hypothesis and falsifying the conclusion, and it
  is the all-zero pattern. Cross-checked at `p = 5` against a full, non-orbit
  enumeration.
- `artifacts/facts/F-geometry-pappus-hexagon.json` — the fact, with the
  redundancy carried as its own evidence row rather than as prose.
- The counter-case that keeps this honest: `euler-line`'s minimality really *is*
  absolute under both conditions, and it was established by the cheapest possible
  instrument — its own committed counterexample refutes the only proper subset of
  a singleton. Adding a second requirement does not make the strong claim
  unreachable; it makes it earned.

## Consequences

**ADR-0455 is refined, not withdrawn.** Its regime names are still the ones to
use, and its rule — measure the absolute regime where it is affordable rather
than assuming the weaker one — is unchanged. What changes is that "every test was
decided" stops being sufficient evidence for the strong claim.

**Where else this shape lives.** Any procedure that reports a minimal or
irreducible subset by removing elements and re-testing, where the *test* is
parameterised by something the producer picked: monomial order in a Gröbner
route, elimination order in a linear route, the clause-selection heuristic behind
a deletion-based unsat core, the abstraction level of a refinement loop. The
question to ask of each is not "did the test return an answer" but "would a
different producer-side choice have returned a different answer". Where it would,
say so; where the choice can be derived from the subset instead, derive it.

**Not decided here**, and now on its third instance so the argument for deferring
is thinner: whether `fact.schema.json` should carry a structured field for the
minimality regime rather than prose in `formal.statement` and `notes`. This
instance argues for it more strongly than the first two, because the wrong value
here would have been the *strong* one — a schema field with an enum would at
least have made "absolute" a thing someone had to type.
