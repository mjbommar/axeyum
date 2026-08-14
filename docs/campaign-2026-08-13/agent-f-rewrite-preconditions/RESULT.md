# agent-f — rewrite preconditions: result

**Headline: no currently-violable precondition found among the 57 manifest rules.**
That is a negative result, and section 3 describes the search behind it so it can
be weighed. What changed is that the manifest's preconditions are now *enforced
where rewrites are applied* rather than described beside them, so the next rule
that violates one is refused instead of shipped.

Landed as ADR-0408 plus code in `crates/axeyum-rewrite/`.

---

## 1. F1 — what is in the manifest, and what is not

### The manifest has 57 rules, not 5

My brief counted 5, from `grep "RewriteRule {"`. That counts struct *literals*.
`crates/axeyum-rewrite/src/canonical.rs:622` defines a helper
`fn rule(id, name, precondition)`, and `default_rules()` (`canonical.rs:332-620`)
calls it **57 times**.

Every one of the 57 is built by that single helper, which hard-codes
`preservation: Denotation`, `projection: Identity`,
`tests: [ExhaustiveSmallWidth, OracleDifferential]`, `enabled_by_default: true`.
So the 57 rules differ from one another in exactly three fields: `id`, `name`,
and the prose `precondition` string.

That sharpens the original complaint rather than softening it. The precondition
string was the **only** per-rule field carrying the rule's applicability
condition, and it was the one field nothing read. `validate_rules`
(`lib.rs:196-213`) checked only `!precondition.trim().is_empty()` — that a human
had written *something*.

### The manifest/non-manifest boundary: intentional, documented twice, and contradicted

Roughly 20 public transformation entry points across 11 modules are outside the
manifest (`eliminate_arrays`, `abstract_arrays`, `elim_unconstrained`,
`solve_eqs`, `solve_eqs_bounded`, `lower_derived_bv`, `eliminate_int_divmod`,
`blast_integers`, `abstract_functions`, `eliminate_functions`,
`simplify_datatypes`, `expand_quantifiers`, `instantiate_universals`,
`instantiate_with_triggers`, `propagate_values`).

**The boundary is intentional and it is stated — in two places, neither an ADR:**

- `crates/axeyum-rewrite/README.md:8-11` — "Array, function, bounded-integer,
  quantifier, equation-solving, value-propagation, and unconstrained-elimination
  passes are separate APIs with their own admission and reconstruction
  contracts."
- `docs/internals/rewriting.md:27-36` — "**They are not silently part of the
  default canonicalizer.**"

**But the documentation is inconsistent, and that is itself a finding:**

1. **Both enumerations are incomplete.** Neither names `simplify_datatypes`,
   `lower_derived_bv`, or `eliminate_int_divmod`.
2. **It is directly contradicted.** `docs/contributor-guide/adding-a-rewrite.md:38-39`
   says "Do not bypass it with an unregistered local fold." Read literally, the
   20 non-manifest entry points violate the contributor guide. The guide links to
   neither carve-out.
3. **ADR-0005 asserts the opposite.** Its Consequences section
   (`adr-0005-…:83-87`) claims "every future rewrite result has a manifest route
   into logs, benchmark artifacts, and certificates." Untrue of the non-manifest
   passes, corrected nowhere. ADR-0005 predates every one of them.
4. **Two disjoint registries exist and no document says so.** `RewriteManifest`
   governs local rules; `TrustId` (ADR-0031, rendered at
   `docs/research/08-planning/trust-ledger.md:13-30`) governs reductions. Nothing
   states that this split is the design or which registry a new transformation
   should join.
5. **The `precondition` field's own status was never stated.** Negative result:
   nothing in the repo said it was prose-only, and nothing proposed making it
   executable. Its entire documentation was `lib.rs:144-145`,
   `/// Sort/width/operator precondition.`

**Non-manifest passes' own contracts** exist, but only as module doc comments and
unevenly. `elim_unconstrained.rs:1-31` is exemplary (precondition, model
soundness, termination, and an explicit *negative* scope). At the other end,
`eliminate_int_divmod` introduces fresh `q`/`r`/`v` symbols and declares **no
model-reconstruction route at all**; `lower_derived_bv` likewise. None is
machine-checked — there is no `validate_projection` analogue outside the manifest.

---

## 2. F2 — what is now enforced that was not

`RewriteRule` keeps its prose `precondition` (it is genuinely useful — it says
*why*) and gains `guard: PreconditionGuard`, the half the code consults.

**Tier A, structural, unconditional in every build, `O(1)` per application:**

- **Declared operator scope.** Each rule declares the `Op` variants it may fire
  on, compared by discriminant so parameterized operators match regardless of
  parameters. A rule firing outside its scope is refused.
- **Sort agreement** between the rewritten term and its replacement.
- `RewriteManifest::new` rejects an empty operator list
  (`ManifestError::EmptyGuard`) — a rule admitting no operator could never fire.

**Tier B, semantic, `PreconditionPolicy`, defaults ON in every build:**

- Every default rule declares `Preservation::Denotation` + `ModelProjection::Identity`.
  That declaration *is* the semantic precondition, so the guard holds each rule
  to it: both sides are evaluated under 4 fixed assignments by the `axeyum-ir`
  ground evaluator — **independent code from the matcher that decided to fire**.
- Cost is linear, not quadratic: assignments are fixed for the pass and one
  `eval_with_memo` memo per sample is carried across every application, so each
  arena node is evaluated at most 4 times in total.

**Where enforcement sits.** Every rewrite the canonicalizer commits passes
through exactly two lines (`canonicalize_root_bounded`, formerly `:690` and
`:709`). Both now check before recording. A violation returns
`RewriteError::PreconditionViolated(Box<PreconditionFailure>)` — a **refusal**,
never a silent rewrite.

**Coverage is reported, not assumed.** `RewriteReport::precondition_audit()`
returns applications, scope-checked, scope-unconstrained, denotation-checked, and
`denotation_unavailable` — the coverage holes where the evaluator could not reach
a term. A guard that silently declines to check is the defect it exists to
prevent.

**The guard table was read off the dispatch, not off the prose.** Transcribing
the precondition strings would have made the guard a restatement of the thing it
is meant to catch. `is_ac`/`is_commutative` gave `commutative.operand_order.v1`
its 12-operator scope; `fold_ground_int` gave `int.const_fold.v1` a precise
13-operator scope; `rewrite_bv_compare` confirmed saturation is unsigned-only.

### Release default: decided by measurement, not by argument

I planned to gate Tier B behind `debug_assertions` and abandoned that when the
numbers came in.

`axeyum-bench corpus/qfbv-curated --backend sat-bv --timeout-ms 2000`, release:

| policy | wall | PAR-2 mean | verdicts |
|---|---|---|---|
| Denotational | 21.51 s | 0.963 | sat=9 unsat=24 unknown=10, DISAGREE=0 |
| Structural | 21.55 s | 0.964 | sat=9 unsat=24 unknown=10, DISAGREE=0 |

In isolation the semantic tier costs **2.2x on canonicalization** (946 corpus
files, 380 524 applications: 0.363/0.379/0.414 s vs 0.806/0.853/0.883 s over 3
runs) — about 0.2% of solve time, invisible end to end. Verdicts are identical
both ways: **the guard never changes an answer, only refuses a wrong one.** A
guard that runs only in debug is absent exactly where the wrong `unsat` ships.

---

## 3. Is any current precondition violable? How hard I looked

**Not that I could find, in the manifest.** The search:

1. **The guard live on every existing test.** Because the guard adjudicates every
   committed rewrite, every test in the workspace that canonicalizes anything
   became a precondition test.
   - `axeyum-rewrite`: **129 + 2 + 2 + 1 passed, 0 failed**
   - `cargo test --workspace --lib`: clean
   - `axeyum-solver --lib --features full`: **1121 passed, 0 failed** at the HEAD
     I started from; **1114 passed / 7 failed** at final HEAD `44c2e136b`. Those
     7 are `reconstruct::tests::*_family_generated_source_is_byte_stable` and are
     **pre-existing** — a pristine `git archive HEAD` build fails identically,
     same tests, same counts. Same story for
     `axeyum-cnf --test colouring_encoding_parity`
     (`stored_ledger_cnf_artifacts_regenerate_byte_identically`), in a crate that
     does not even depend on `axeyum-rewrite`. Nonzero counts confirmed
     throughout — the `--features full` form is the one that is inert without the
     flag.
   - `corpus_regression --features full`: passed
   - `progress_frontier --features full`: **9 passed, 0 failed**
2. **A purpose-built wide sweep** — `crates/axeyum-rewrite/tests/precondition_fuzz.rs`.
   Measured on this run:
   - 4096 generated terms, depth 4, over the full default-rule operator surface;
   - **11 972 rule applications** committed and checked;
   - 6025 scope-checked, 5947 by an `AnyOperator` rule;
   - **11 972 denotation-checked, 0 coverage holes**;
   - a second independent judge: 40 replay assignments x 4096 terms =
     **163 840 further evaluator comparisons**, on assignments the guard never
     sampled (the guard uses 4; a defect hiding from 4 but not 40 is exactly what
     this catches);
   - **zero violations.**
3. **Degenerate arguments generated on purpose**, per the repo's hard rule. The
   `a946f925` wrong-`unsat` survived a differential gate whose generator
   structurally could not emit `(div x 0)`. This generator carries literal zeros
   among both its integer and bit-vector leaves, so it emits constant-zero
   divisors for `bvudiv`, `bvurem`, `bvsdiv`, `bvsrem`, `bvsmod`, `div`, and
   `mod`; shift amounts at and past the operand width; rotates by a full width;
   extends by zero bits.
4. **946 real corpus files** canonicalized through the guard during timing runs.
   No refusal.

**What this does not cover:** the ~20 non-manifest passes. They have no guard to
enforce, which is the section 1 finding, not a claim about their correctness.

**One measurement that argues against complacency:** 5947 of 11 972 applications
— **half** — were by the two `AnyOperator` constant folds, which by construction
receive no structural protection at all. Their only check is the semantic tier.

---

## 4. F3 — controls, and the demonstration that they fail without the guard

8 controls in `canonical.rs::precondition_control_tests`, plus 2 in the fuzz file.
I neutered `PreconditionCheck::check` (made it return `Ok(())` on entry, as if
never written) and re-ran. Raw output: `logs/control-fails-without-guard.txt`.

**5 of 8 failed.** Verbatim, the headline:

```
denotation guard did not refuse the wrong rewrite: Ok(CanonicalizeOutcome {
  term: TermId(3), report: RewriteReport { applications: [RuleApplication {
    rule_id: RewriteRuleId("control.denotation_violation.v1"), ... }] ... } })
```

That `Ok` is the pathology entire. `bvadd(x, 0)` became `bvnot(x)`; the
canonicalizer returned success; the term is a perfectly well-formed bit-vector
that the bit-blaster, the SAT core, and the DRAT checker would every one of them
certify — because they would be certifying the wrong formula.

**3 passed without the guard, and I am not calling those controls of the
enforcement.** `manifest_rejects_an_empty_operator_scope`,
`only_the_two_generic_constant_folds_waive_operator_scope`, and
`every_default_rule_declares_a_guard` test the manifest *data*; they fail if the
`guard` field is removed, not if the check is. Stating which control covers which
half is the whole lesson from agent-a's five-instances-one-flip.

**The control's own vacuity was tested.** The planted rewrite is wrong on **all
16** inputs at width 4 and the test asserts that count. A control that merely
usually disagreed would let a badly-sampling guard pass.

Two further controls guard the guard itself:
`denotation_guard_actually_covers_the_applications_it_reports` asserts zero
coverage holes on a pure Bool/BV workload, and
`unsamplable_sorts_are_reported_as_holes_not_as_passes` asserts an array-sorted
rewrite is counted as **unchecked**, not as a pass.

---

## 5. Comment-vs-code discrepancies found and closed

Per the brief's instruction not to leave a third instance of the pathology:

- `lib.rs:144-145`'s `/// Sort/width/operator precondition.` described a field
  nothing enforced. **Implemented** rather than reworded: the doc now says
  plainly that the prose is documentation and `guard` is what the code enforces.
- `default_manifest`'s doc said "All rules in this manifest are exact-denotation
  rules with identity model projection" — true, but unchecked at application
  time. Now checked at application time.

I found **no** comment in `axeyum-rewrite` describing a check the code does not
perform, other than the precondition field itself.

---

## 6. What remains

1. **The ~20 non-manifest passes are still unguarded.** Extending enforcement
   past the manifest is the natural next slice; `elim_unconstrained.rs:1-31`
   already states its contract precisely enough to be mechanized.
2. **`eliminate_int_divmod` and `lower_derived_bv` declare no model-reconstruction
   route.** `eliminate_int_divmod` introduces fresh symbols, so this is the more
   pressing of the two.
3. **The three contradictory statements about manifest scope** (crate README,
   `adding-a-rewrite.md:38-39`, ADR-0005's Consequences) need reconciling. ADR-0408
   records the contradiction but deliberately does not silently resolve someone
   else's ADR.
4. **`RewriteTestRoute::ProofObligation` still has zero consumers.** The guard
   checks a rewrite; it does not *certify* one. Rewrite certificates remain the
   large version of this work.
5. **A pre-existing QF_ABV canonicalize error** —
   `Ir(SortMismatch { expected: "Bool or BitVec", found: Array {...} })` on raw
   array assertions. **Verified against a pristine `git archive HEAD` build:
   identical, not a regression from this slice.** Not on the solver's real route
   (which elides arrays first). Unchased.
