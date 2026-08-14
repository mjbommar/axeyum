# ADR-0408: Rewrite preconditions are enforced where rewrites are applied

Status: accepted
Date: 2026-08-13

## Context

[ADR-0005](adr-0005-phase3-query-evidence-rewrite-contracts.md) established that
every rewrite rule declares "a stable ID, name, sort/width/operator
precondition, preservation class, model-projection obligation, required test
routes, and whether it is enabled by default". Every one of those fields except
the precondition is a typed value the code can act on. The precondition was a
`String`, and the only thing `validate_rules` checked about it was that it was
not empty — that a human had written *something*, never that the something bore
any relation to when the rule fires.

That gap is the same defect found twice elsewhere in this repository on
2026-08-13:

- `axeyum-search`'s colour-class symmetry breaking was sound only for
  interchangeable colours, a condition stated in prose. For an off-diagonal
  family it turned a **satisfiable** instance into `unsat` (`S(3;3,4,5)` at
  `n=41`), and every downstream stage would have certified that proof happily —
  because it would have been a valid proof of the wrong formula (fixed in
  `c0403d000`).
- `axeyum-lean-kernel`'s `lean_pp.rs` documents a guard at `:214-216` and again
  at `:420-421` restricting `inductive` rendering to flat enums.
  `render_real_inductive` performs no such check. The guard exists only in
  prose.

The through-line: **a transform's precondition must be carried in the interface,
because a precondition in a doc comment is a wrong-`unsat` waiting for the first
input that violates it.**

Nothing in the repository stated whether `RewriteRule::precondition` was
intended to stay prose or to become executable; the field's entire documentation
was one line. This ADR closes that.

## Decision

**Every rewrite rule carries a machine-checked precondition alongside its prose
one, and the canonicalizer refuses — never silently commits — any rule
application that falls outside it.**

Three parts.

1. `RewriteRule` gains a `guard: PreconditionGuard` field. The prose
   `precondition: String` is **kept**, unchanged, as documentation: the prose
   says *why*, the guard says *what is checked*. `PreconditionGuard` is either
   `RootOperators(Vec<Op>)` — the operator variants the rule may fire on,
   compared by discriminant so parameterized operators match regardless of their
   parameters — or `AnyOperator`, for rules whose real gate is on the operands
   rather than the operator. `RewriteManifest::new` rejects an empty operator
   list (`ManifestError::EmptyGuard`), since a rule admitting no operator could
   never legally fire.

2. Enforcement happens at the point of application, not at manifest build time.
   Every rewrite the canonicalizer commits passes through two lines in
   `canonicalize_root_bounded`; both now call `PreconditionCheck::check` before
   recording, and a failure returns
   `RewriteError::PreconditionViolated { rule, before, after, violation }`.

3. Checking has two tiers. The **structural** tier — declared operator scope,
   plus sort agreement between the term and its replacement — is `O(1)` per
   application and runs in every build, unconditionally; there is no policy that
   disables it. The **semantic** tier holds each rule to the
   `Preservation::Denotation` + `ModelProjection::Identity` classification the
   manifest already declares for it, by evaluating both sides under
   `DENOTATION_GUARD_SAMPLES` fixed assignments using the `axeyum-ir` ground
   evaluator — an independent code path from the matcher that decided to fire.
   It is selected by `PreconditionPolicy` and **defaults on in every build,
   release included**.

`RewriteReport::precondition_audit` reports how much checking actually happened,
including the coverage holes where the evaluator could not reach a term. A guard
that silently declines to check is the defect it exists to prevent, so its
coverage is measured rather than assumed.

## Evidence

**The semantic tier is free end to end.** `axeyum-bench corpus/qfbv-curated
--backend sat-bv --timeout-ms 2000`, release:

| policy | wall | PAR-2 mean | verdicts |
|---|---|---|---|
| Denotational | 21.51 s | 0.963 | sat=9 unsat=24 unknown=10, DISAGREE=0 |
| Structural | 21.55 s | 0.964 | sat=9 unsat=24 unknown=10, DISAGREE=0 |

In isolation it costs 2.2x on canonicalization (946 corpus files, 380 524 rule
applications: 0.363/0.379/0.414 s structural vs 0.806/0.853/0.883 s
denotational), which is roughly 0.2% of solve time. The verdicts are identical
both ways: the guard never changes an answer, only refuses a wrong one. The
default was chosen from these numbers, not from an argument — a `debug_assertions`
gate had been the plan, and it was abandoned because a guard that runs only in
debug is absent exactly where the wrong `unsat` would ship.

**Linearity, not quadratic blowup.** The naive form of the semantic tier
re-evaluates each `before`/`after` pair and is quadratic in formula size. Fixing
the sample assignments for the whole pass and carrying one `eval_with_memo` memo
per sample across every application makes total work `O(K x nodes)`. Arena terms
are immutable and hash-consed, so a memo entry cannot go stale within a pass.

**The guard finds nothing wrong today, and the search is described.** With the
guard live: `axeyum-rewrite` 129 passed / 0 failed; `cargo test --workspace
--lib` clean; `axeyum-solver --lib --features full` **1121 passed / 0 failed**.
A purpose-built sweep (`crates/axeyum-rewrite/tests/precondition_fuzz.rs`)
generated 4096 terms over the full default-rule operator surface, committing
**11 972 checked rule applications with 11 972 denotation-checked and 0 coverage
holes**, plus 163 840 further comparisons by a second independent judge replaying
on assignments the guard never sampled. Zero violations. Per the repository's
hard rule on partial operators, the generator deliberately emits the degenerate
arguments — constant-zero divisors for `bvudiv`/`bvurem`/`bvsdiv`/`bvsrem`/
`bvsmod` and integer `div`/`mod`, shifts at and past the operand width, rotates
by a full width — because the `a946f925` wrong-`unsat` survived a differential
gate whose generator structurally could not produce `(div x 0)`.

**The controls fail without the guard, demonstrably.** Neutering
`PreconditionCheck::check` makes 5 of the 8 controls fail. The canonicalizer then
returns `Ok` for a rewrite of `bvadd(x, 0)` to `bvnot(x)` — a perfectly
well-formed bit-vector term that the bit-blaster, the SAT core, and the DRAT
checker would each certify without complaint. The remaining 3 controls test the
manifest *data* rather than the commit path and fail if the `guard` field is
removed instead; which control covers which half is stated in the test module,
because a control that passes while testing nothing is the failure mode here.

**Half of all applications get no structural protection.** In the sweep, 5947 of
11 972 applications were by the two `AnyOperator` constant folds. That measured
share is the strongest argument for the semantic tier being on by default.

## Alternatives

**Leave the precondition as prose and rely on the test routes.** Rejected: this
is exactly the position the two sibling defects were in. `RewriteTestRoute`
records the routes a rule *should* be validated by; nothing ties a route to an
application, and a rule that starts firing on a new shape after a refactor is
covered by no existing test by construction.

**Restate each precondition structurally in full** — operand shapes, constant
values, index arithmetic. Rejected as a second source of truth: a structural
restatement of the matcher is written by copying the matcher, so it agrees with
the matcher's bugs. The operator scope is deliberately coarse (it is read off
the *dispatch*, which is one level above the match arms), and everything finer
is checked semantically by code that shares nothing with the rewriter.

**Gate the semantic tier behind `debug_assertions`.** Rejected on the measured
end-to-end cost above.

**Emit a checkable rewrite certificate per application.** Not rejected —
deferred. That is the genuinely large version of this work and it is already
scoped in `docs/plan/exploration-track/phase-4-eqsat-walkback/`. This ADR is the
bounded slice that makes the precondition enforced *now*;
`RewriteTestRoute::ProofObligation` still has no consumer.

## Consequences

- A rewrite rule can no longer fire outside its declared operator scope, and a
  `Preservation::Denotation` rule can no longer change denotation on the sampled
  assignments, without the canonicalizer refusing.
- `RewriteError` gains a variant; callers matching it exhaustively must handle
  `PreconditionViolated`. It is a refusal, not an `unknown` — the rewriter has
  detected that it cannot justify its own output.
- Adding a rule to `default_rules()` without an entry in `default_guard` panics
  at `default_manifest()`. This is deliberate and loud.
- **This ADR covers the 57 manifest rules only.** The roughly 20 non-manifest
  transformation entry points in `axeyum-rewrite` (`eliminate_arrays`,
  `solve_eqs`, `elim_unconstrained`, `blast_integers`, `expand_quantifiers`, …)
  carry their preconditions in module doc comments and remain unenforced. That
  boundary is stated in `crates/axeyum-rewrite/README.md:8-11` and
  `docs/internals/rewriting.md:27-36`, contradicted by
  `docs/contributor-guide/adding-a-rewrite.md:38-39` ("Do not bypass it with an
  unregistered local fold"), and asserted away by ADR-0005's own Consequences
  section. Reconciling those three statements, and extending enforcement past
  the manifest, is the next slice.
