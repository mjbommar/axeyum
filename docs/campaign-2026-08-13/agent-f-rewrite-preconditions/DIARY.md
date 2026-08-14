# agent-f diary — rewrite preconditions

Append-only. Times are wall-clock local.

## 1. Orientation

Read the campaign README and `CLAUDE.md`. Target crate `crates/axeyum-rewrite/`
(11.7 kLOC across 13 modules). Snapshot built from `git archive HEAD` into
scratchpad per campaign rule 7.

## 2. First measurement — the "5 rules" figure in my brief is wrong

The brief counted `RewriteRule {` literal constructions and found 5. That is a
count of *struct literals*, not of rules. The real number:

- `crates/axeyum-rewrite/src/canonical.rs:622` defines a helper
  `fn rule(id, name, precondition) -> RewriteRule`.
- `default_rules()` (`canonical.rs:332-620`) calls it **57 times**.

So the manifest has 57 rules, all built by one helper that hard-codes
`preservation: Denotation`, `projection: Identity`, `tests: [ExhaustiveSmallWidth,
OracleDifferential]`, `enabled_by_default: true`. Every one of the 57 differs from
every other **only** in `id`, `name`, and the prose `precondition` string.

That sharpens the finding: the precondition string is the *only* per-rule field
that carries the rule's actual applicability condition, and it is the one field
nothing reads.

## 3. The enforcement point is narrow — good news for a bounded slice

`grep -n "report.record"` in `canonical.rs` returns exactly three sites:

- `:690`  `report.record(rule_id, term, rewritten)` — first local application
- `:709`  `report.record(rule_id, rewritten, next.term)` — reprocessing chain
- `:723`  `report.record_local_fuel_exhaustion()` — not an application

So *every* rewrite the canonicalizer ever commits passes through two lines. A
guard placed there is universal by construction, not by convention. This is what
makes the "enforce at the application site" design a small diff rather than a
57-site audit.

## 4. Design decision — two tiers, and why

Tier A (always on, O(1) per application):
  - root-operator scope: the rule declares which `Op` variants it may fire on,
    and the committer checks the actual root op against it;
  - sort agreement: `sort_of(before) == sort_of(after)`.

Tier B (policy-gated, linear in the pass):
  - denotational agreement: the manifest declares every default rule
    `Preservation::Denotation` + `ModelProjection::Identity`. That *is* the
    semantic precondition, and it is checkable by an independent code path — the
    ground evaluator in `axeyum-ir`, which is the crate's declared "executable
    semantic reference" (`eval.rs:1-5`).

The cost objection to Tier B is that re-evaluating each `before`/`after` pair
would be quadratic in formula size. It is not, if the sample assignments are
fixed for the whole pass and the evaluator memo is shared across every
application: `eval_with_memo` (`axeyum-ir/src/eval.rs:239`) exists precisely for
this. With K fixed assignments and one memo per assignment held across the pass,
total work is O(K x total nodes) — linear. Arena terms are immutable and
hash-consed, so a memo entry can never go stale within a pass.

Whether Tier B defaults on in release will be decided by **measurement**, not by
argument. Implement first, time it, then choose.

## 5. Guard table derived from the code, not from the prose

Read the dispatch to derive each rule's true operator scope, rather than
transcribing the precondition strings (transcribing would make the guard a
restatement of the prose, which tests nothing):

- `is_ac` (`canonical.rs:1005`) and `is_commutative` (`:976`) give
  `commutative.operand_order.v1` its 12-operator scope.
- `rewrite_bv_compare` (`:1661`, `:1672`): reflexivity covers all 8 comparisons;
  saturation covers only the 4 **unsigned** ones — which matches its prose, so
  the two agree here.
- `fold_ground_int` (`:2254-2266`) gives `int.const_fold.v1` a precise
  13-operator scope, so it does **not** need an `AnyOperator` escape.

Only the two generic constant folds (`bool.const_fold.v1`, `bv.const_fold.v1`)
are genuinely operator-agnostic: they are gated on the *operands* being literals
(`all_constant`, `canonical.rs:752`), not on the operator. Those get an explicit
`AnyOperator` scope — an honest declaration, not a hole, because their real gate
is checked by Tier B.

## 6. F1 documentation survey came back — the boundary is documented twice, and contradicted once

Delegated survey (results verified by spot-reading the cited lines):

- The manifest/non-manifest boundary IS stated, in exactly two places, neither an
  ADR: `crates/axeyum-rewrite/README.md:8-11` and
  `docs/internals/rewriting.md:27-36` ("They are not silently part of the default
  canonicalizer."). **Both enumerations are incomplete** — neither names
  `simplify_datatypes`, `lower_derived_bv`, or `eliminate_int_divmod`.
- It is **contradicted** by `docs/contributor-guide/adding-a-rewrite.md:38-39`:
  "Do not bypass it with an unregistered local fold." Read literally, the ~20
  non-manifest entry points violate the contributor guide, and the guide links to
  neither carve-out.
- ADR-0005's Consequences (`adr-0005-…:83-87`) claims "every future rewrite result
  has a manifest route into logs, benchmark artifacts, and certificates." That is
  not true of the non-manifest passes and is corrected nowhere.
- The repo has **two disjoint registries** — `RewriteManifest` for local rules and
  `TrustId` (ADR-0031, rendered at `docs/research/08-planning/trust-ledger.md:13-30`)
  for reductions — and no document states that this split is the design or which a
  new transformation should join.
- On the `precondition` field itself: **negative result**. Nothing anywhere states
  it is prose-only, and nothing states executable checking as intent. Its entire
  documentation is `lib.rs:144-145` `/// Sort/width/operator precondition.` The
  only checked property is that a human wrote something.
- The non-manifest passes DO mostly carry contracts, but only in module doc
  comments, and unevenly: `elim_unconstrained.rs:1-31` is exemplary (precondition,
  model-soundness, termination, and an explicit negative scope);
  `eliminate_int_divmod` introduces fresh `q`/`r`/`v` symbols and **declares no
  model route at all**; `lower_derived_bv` likewise. None is machine-checked —
  there is no `validate_projection` analogue outside the manifest.

So the boundary is *intentional but under-documented and self-contradictory*. That
is a finding in its own right, per the brief. Recorded in FEEDBACK.md.

## 7. The guard is live and the existing suite is clean

Built and ran `cargo test -p axeyum-rewrite` in the snapshot with the guard
enforcing on every commit: **121 passed, 0 failed**. So on the crate's own suite:

- no default rule ever fires on an operator outside the scope I derived from the
  dispatch — the guard table and the code agree everywhere;
- no default rule ever changes denotation under the 4 sample assignments;
- no rewrite ever changes a term's sort.

That is a **negative result on the manifest rules**, and it is worth stating
plainly rather than dressing up: I did not find a violable manifest precondition.
Section 10 records how hard I looked.

## 8. Controls — 5 of 8 fail without the guard, and here is the failure

Wrote 8 controls, then NEUTERED the guard in the snapshot only (made
`PreconditionCheck::check` return `Ok(())` on entry, as if it had never been
written) and re-ran. Raw output in `logs/control-fails-without-guard.txt`.

**5 failed.** The headline one, verbatim:

```
denotation guard did not refuse the wrong rewrite: Ok(CanonicalizeOutcome {
  term: TermId(3),
  report: RewriteReport { applications: [RuleApplication {
    rule_id: RewriteRuleId("control.denotation_violation.v1"),
    before: TermId(2), after: TermId(3) }], ... } })
```

That `Ok` is the whole pathology in one line. `bvadd(x, 0)` became `bvnot(x)`,
the canonicalizer returned success, and the term it returned is perfectly
well-formed — the bit-blaster, the SAT core, and the DRAT checker would every
one of them certify it, because they would be certifying the wrong formula.

And the scope control, also verbatim:

```
scope guard did not refuse the out-of-scope rewrite: Ok(... rule_id:
  RewriteRuleId("bv.add_zero.v1"), before: TermId(2), after: TermId(0) ...)
```

**3 passed without the guard**, and I am not going to pretend otherwise:
`manifest_rejects_an_empty_operator_scope`,
`only_the_two_generic_constant_folds_waive_operator_scope`, and
`every_default_rule_declares_a_guard` test the manifest *data*, not the commit
path, so neutering `check()` leaves them untouched by construction. They fail if
the `guard` field is removed, not if the enforcement is. Stating which control
covers which half matters — agent-a's lesson was precisely that a control can
pass while testing nothing.

On the control's own design, the same lesson applied: the wrong rewrite
`bvadd(x,0) -> bvnot(x)` is wrong on **all 16** inputs at width 4, and the test
asserts that count. A control that merely *usually* disagreed would let a guard
that samples badly slip through.

## 9. The release-default question, settled by measurement

I refused to argue this one. Two measurements:

**Canonicalization in isolation** (946 real corpus files from `corpus/qfbv-curated`
and `corpus/public-curated`, 380 524 rule applications, release build, 3 runs):

| policy | canonicalize time | ratio |
|---|---|---|
| Structural | 0.363 / 0.379 / 0.414 s | 1.00x |
| Denotational | 0.806 / 0.853 / 0.883 s | **2.2x** |

So the semantic tier really does cost slightly more than double — of
canonicalization.

**End to end** (`axeyum-bench corpus/qfbv-curated --backend sat-bv
--timeout-ms 2000`, release, guard default flipped in the snapshot):

| policy | wall | PAR-2 mean | verdicts |
|---|---|---|---|
| Denotational | 21.51 s | 0.963 | sat=9 unsat=24 unknown=10, DISAGREE=0 |
| Structural | 21.55 s | 0.964 | sat=9 unsat=24 unknown=10, DISAGREE=0 |

The 2.2x on canonicalization is 0.2% of solve time and vanishes into noise. The
verdicts are bit-identical both ways, which is the other half of the claim: the
guard never changes an answer, it only refuses a wrong one.

**Decision: the denotation guard defaults ON in every build, release included.**
I had planned to gate it behind `debug_assertions` and would have, had the number
come out differently. It did not, and a guard that runs only in debug is a guard
that is absent exactly where the wrong `unsat` would ship. `PreconditionPolicy`
still exists so a caller with a measured reason can lower it, and the structural
tier is not lowerable at all.

## 10. A side observation the harness produced: a pre-existing QF_ABV canonicalize error

While building the timing harness I hit
`RewriteError::Ir(SortMismatch { expected: "Bool or BitVec", found: Array {...} })`
canonicalizing raw `QF_ABV` assertions. **I checked this against a pristine
`git archive HEAD` build before believing it was mine: identical error, same
files.** Pre-existing, not a regression from this slice, and not on the solver's
real route (which runs `check_with_array_elimination` first). Noted in FEEDBACK,
not chased.

## 11. The violability hunt — what I did and what I did not find

The headline: **I did not find a violable precondition among the 57 manifest
rules.** Because a negative result is only worth the search behind it, here is
the search.

1. **The guard itself, live on every existing test.** This is the broadest probe:
   the guard adjudicates every rewrite the canonicalizer commits, so every test in
   the workspace that canonicalizes anything is now also a precondition test.
   - `cargo test -p axeyum-rewrite`: 121 passed (now 129 with controls), 0 failed.
   - `cargo test --workspace --lib`: clean, 0 failures.
   - `cargo test -p axeyum-solver --lib --features full`: **1121 passed, 0 failed**
     (nonzero count confirmed, per the `--features full` trap in CLAUDE.md).
2. **A purpose-built wide random sweep** (`tests/precondition_fuzz.rs`), designed
   to hit the shapes a focused unit example cannot. Measured on this run:
   - 4096 generated terms, depth 4, over the full default-rule operator surface;
   - **11 972 rule applications** committed and checked;
   - 6025 checked against a declared operator scope, 5947 by an `AnyOperator` rule;
   - **11 972 denotation-checked, 0 coverage holes**;
   - plus a second, independent judge: 40 replay assignments x 4096 terms
     (163 840 further evaluator comparisons) on assignments the guard never sampled.
   - Result: **zero violations**.
3. **Degenerate arguments deliberately generated**, per the repository's hard rule
   — the `a946f925` lesson is that a fuzz which structurally cannot emit
   `(div x 0)` is blind on exactly the axis where soundness is most fragile. The
   generator carries a literal `0` among its integer leaves and among its
   bit-vector leaves, so it emits constant-zero divisors for `bvudiv`, `bvurem`,
   `bvsdiv`, `bvsrem`, `bvsmod`, `div` and `mod`; shift amounts at and past the
   operand width; rotates by a full width; and extends by zero bits.
4. **946 real corpus files** canonicalized through the guard during the timing
   runs. No refusal.

What that does and does not license me to say: the 57 manifest preconditions are
not violable by anything I could reach. It does **not** cover the ~20 non-manifest
passes — they have no guard to enforce, which is the finding in section 6, not a
result about their correctness.

Notably, `scope_unconstrained` was 5947 of 11 972 — **half of all applications
are by the two `AnyOperator` constant-fold rules**, which by construction get no
structural protection. That is the strongest single argument for keeping the
semantic tier on by default, and it is a measurement, not a hunch.

## 12. Clippy pushed the error type into a better shape

`result_large_err` fired 8 times: `PreconditionViolation::DenotationChanged`
carries two `Value`s, and `Value` is large (it holds `Rational`, `WideUint`,
datatype trees). Since `RewriteError` rides on the return type of the *default*
canonicalization path, a fat `Err` variant taxes every successful rewrite.

Fixed by hoisting the payload into `PreconditionFailure` and boxing it:
`PreconditionViolated(Box<PreconditionFailure>)`. This is the same reasoning
`axeyum-ir` already applies to `Assignment::real_div_zero` ("keeps `Assignment`
at one extra word instead of a full inline `HashMap`"). The lint was right and
the result is a better API than what I wrote.

Also fixed: `unnecessary_wraps` on the `cfg(not(test))` arm of `control_rewrite`
(allowed with a stated reason — the signature must match the `cfg(test)` arm,
which genuinely can fail), and several pedantic lints in the fuzz file
(cast truncation, an if-chain, and `seed ^ 11` reading as a bitwise op on a
decimal literal — replaced with a salted `mix` helper, which is clearer anyway).

## 13. A hygiene fix found by re-reading my own diff

The commit site built the exact local pre-image (`App { op, rewritten_args }`)
**unconditionally**, including when the policy is `Structural` and nothing would
evaluate it. That interns terms for a check that does not run. Added
`needs_pre_image()`; under a lowered policy the site passes the original node
instead, which is sound for the sort check because child rewrites preserve sort —
a property this very guard enforces. Small, but "the fast path allocates for the
slow path's benefit" is the kind of thing that gets copied.

## 14. Infrastructure, not code: three link failures were tmpfs, not compiler

`cargo test -p axeyum-solver --test progress_frontier` and a doctest both died
with `collect2: fatal error: ld terminated with signal 7 [Bus error], core
dumped`. That reads like a compile error. It is not: `/tmp` on this host is a
62 GiB **tmpfs** sitting at 80% with several agents' `target/` directories in it,
and the linker could not get memory.

This matters beyond my lane, because campaign rule 7 tells every agent to
snapshot into scratch, and on this host scratch *is* tmpfs. I moved the whole
build to `/home/mjbommar/.cache/agent-f-snap` with `TMPDIR` pointed there too,
and every failure vanished — same code, same commands. Recorded in FEEDBACK as an
infrastructure item, because "measure, do not trust a message" cuts both ways:
the message said my code did not compile, and it did.

## 15. Gate results on the final code

All run from the disk-backed snapshot. Nonzero counts confirmed everywhere, per
the `--features full` inertness traps in CLAUDE.md.

| gate | result |
|---|---|
| `cargo test -p axeyum-rewrite` | 129 + 2 + 2 + 1, 0 failed |
| `cargo test --workspace --lib` | all green, 0 failed |
| `cargo test -p axeyum-solver --lib --features full` | 1121 passed, 0 failed |
| `cargo test -p axeyum-solver --features full --test corpus_regression` | passed |
| `cargo clippy --workspace --all-targets --all-features -- -D warnings` | clean |
| `RUSTDOCFLAGS="-D warnings" cargo doc --workspace --all-features --no-deps` | clean |
| `./scripts/check-links.sh` | all links ok |
| `rustfmt --edition 2024 --check` on my 3 files | clean |

## 16. main is RED at HEAD 44c2e136b, and it is not me

The full sweep came back with 8 failures. I did not assume they were mine and I
did not assume they were not. I rebuilt a **pristine `git archive HEAD`** at the
same commit and ran the same two gates:

| gate | my branch | pristine HEAD 44c2e136b |
|---|---|---|
| `axeyum-solver --lib --features full` | 1114 passed, **7 failed** | 1114 passed, **7 failed** |
| `axeyum-cnf --test colouring_encoding_parity` | 2 passed, **1 failed** | 2 passed, **1 failed** |

Identical failures, identical counts:

- `reconstruct::tests::{arithmetic,bitblast,cnf,datatype,equality,quantifier,resolution}_family_generated_source_is_byte_stable`
- `stored_ledger_cnf_artifacts_regenerate_byte_identically`

Both families are byte-stability checks on generated artifacts (Lean
reconstruction sources; stored CNF ledger artifacts) and both are other lanes'
areas — `axeyum-cnf` does not even depend on `axeyum-rewrite`, so my change
cannot reach it.

The explanation for my own earlier green run is that **HEAD moved**. My first
snapshot predated those lanes' commits and gave 1121 passed / 0 failed on the
same solver gate; the current HEAD gives 1114/7 with or without my diff. So this
is not a regression I introduced and not one I can fix from this lane.

Reported to the coordinator. Worth saying plainly for the campaign record: a
shared default branch that is red makes every other agent's gate ambiguous, and
the only thing that disambiguated it here was building the pristine tree and
running the same command. That is cheap and I would do it before believing any
gate failure in a multi-agent checkout.

## 17. Committed, and one multi-agent incident on the way out

Commit `64bafa9fc`, pathspec-only, verified with `git show --stat`: exactly four
files (`canonical.rs`, `lib.rs`, `tests/precondition_fuzz.rs`, `adr-0408`), and
`git status` afterwards shows the other lanes' WIP untouched.

A fifth file was supposed to be in it and was not. I had added my ADR index row
to `docs/research/09-decisions/README.md`, and before I committed, the Lean
lane's commit `5f07145e1` ("feat(lean): prove Nat order antisymmetry", 22:08)
picked it up along with their own 0410 row — its `--stat` shows
`docs/research/09-decisions/README.md | 2 +` for a commit that should have added
one line. No harm done in the end (the content was right), but it left HEAD in a
state where the ADR index linked to `adr-0408-…md` that was not yet committed,
i.e. `./scripts/check-links.sh` would have failed on HEAD for 13 minutes. It
passes now.

The general lesson, which CLAUDE.md already states and which I would restate more
sharply: in a shared checkout, an *index* file that many lanes append to is a
collision point even when everyone uses pathspecs, because the pathspec names the
file, not the line. Commit the ADR and its index row in the same breath, or
expect someone else to carry your line.

## 18. Final state

| gate | result |
|---|---|
| `cargo test -p axeyum-rewrite` (from committed HEAD) | 129 + 2 + 2 + 1, **0 failed** |
| `cargo clippy -p axeyum-rewrite --all-targets --all-features -D warnings` | clean |
| `cargo clippy --workspace --all-targets --all-features -D warnings` | clean |
| `cargo test --workspace --lib` | clean |
| `cargo test -p axeyum-solver --features full --test corpus_regression` | 1 passed |
| `cargo test -p axeyum-solver --test progress_frontier --features full` | **9 passed** |
| `cargo doc --workspace --all-features --no-deps` (RUSTDOCFLAGS=-D warnings) | clean |
| `./scripts/check-links.sh` | all links ok |
| `axeyum-solver --lib --features full` | 1114/7 — the 7 **pre-existing**, proven by pristine A/B |

Headline for the report: **no violable precondition found among the 57 manifest
rules**, and they are now enforced at the point of application rather than
described beside it.
