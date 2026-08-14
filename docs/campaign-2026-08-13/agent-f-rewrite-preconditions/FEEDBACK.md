# agent-f — roadmap feedback

Cited by file and line. Ordered by how much soundness rides on each.

## 1. Three documents disagree about what the rewrite manifest governs

- `crates/axeyum-rewrite/README.md:8-11` — non-manifest passes "are separate APIs
  with their own admission and reconstruction contracts."
- `docs/internals/rewriting.md:27-36` — "**They are not silently part of the
  default canonicalizer.**"
- `docs/contributor-guide/adding-a-rewrite.md:38-39` — "**Do not bypass it with an
  unregistered local fold.**"
- `docs/research/09-decisions/adr-0005-phase3-query-evidence-rewrite-contracts.md:83-87`
  — "every future rewrite result has a manifest route into logs, benchmark
  artifacts, and certificates."

The first two carve out the ~20 non-manifest entry points. The third forbids
them. The fourth asserts they do not exist. ADR-0005 predates every one of them
(`eliminate_arrays` is ADR-0010, int-blast ADR-0014, quantifiers ADR-0016,
datatypes ADR-0022), so this is drift, not disagreement — but drift that a
contributor reads as a rule.

Concretely: a contributor following `adding-a-rewrite.md` literally cannot tell
whether a new preprocessing pass belongs in `RewriteManifest`, and the two
carve-outs are not linked from the guide. **Recommend:** one ADR stating the
split, `adding-a-rewrite.md` linking both carve-outs, and ADR-0005's Consequences
superseded rather than left standing as false.

## 2. Two registries, no document explaining which one to join

`RewriteManifest` (`crates/axeyum-rewrite/src/lib.rs:157-194`) governs local
rules. `TrustId` (ADR-0031, rendered at
`docs/research/08-planning/trust-ledger.md:13-30`) governs reductions —
array-elim, Ackermann, int-blast, datatype-elim, fpa2bv, xor-Gaussian. Both are
"the register of things that transform a formula and must be trusted."

Nothing states that this split is deliberate or what determines membership. The
exploration track has already noticed the underlying issue and drawn the line
differently again:
`docs/plan/exploration-track/phase-4-eqsat-walkback/README.md:72-77` — "the
correct regime boundary is **equivalence-preserving vs equisatisfiability-only**,
not intra-theory vs inter-theory. Redraw it." That is the right boundary and it
is not the one either registry uses.

## 3. `eliminate_int_divmod` declares no model-reconstruction route

`crates/axeyum-rewrite/src/int_divmod.rs:1-19` documents its precondition
carefully — constant divisor, `c != 0`, with a genuinely good argument about why
committing to `div a 0 = 0` would be "a valid *witness* but an unsound *unsat*".
Then it introduces fresh `q`, `r`, `v` symbols and never says what becomes of
them in a returned model. No `ModelReconstructionTrail`, no `project_model`, not
even a statement that original symbols are untouched so projection is identity.
Grep for `model|reconstruct|project` in that file returns only incidental
comments.

`lower_derived_bv` (`crates/axeyum-rewrite/src/lower_bv.rs:1-19`) has the same
omission, though it introduces no fresh symbols so the risk is lower.

Compare `elim_unconstrained.rs:1-31`, which states precondition, model soundness,
termination, **and an explicit negative scope** ("`bvmul` by an even or
non-constant factor, and the non-injective `bvand`/`bvor`/`bvudiv`/... are left
alone"). That is the standard the others should meet, and it is already in the
tree — this is a matter of levelling up, not inventing.

## 4. Half of all canonicalizer rule applications have no structural precondition

Measured, not estimated: in a 4096-term sweep, 5947 of 11 972 applications were
by `bool.const_fold.v1` and `bv.const_fold.v1`, which are gated on the operands
being literals rather than on the operator (`canonical.rs`, `all_constant`). They
declare `PreconditionGuard::AnyOperator` — an honest declaration, and now a
pinned one (`only_the_two_generic_constant_folds_waive_operator_scope` fails if a
third rule joins them), but still half of all rewrites protected only
semantically.

This is the single strongest argument for the denotation guard defaulting on, and
it is why I did not gate it behind `debug_assertions`.

## 5. `RewriteTestRoute::ProofObligation` has zero consumers

`crates/axeyum-rewrite/src/lib.rs:133-134` defines it; nothing reads it. Two
plan documents already say so —
`docs/prover-track/plan/P6.3-certificate-tactics.md:36` ("it **emits no
proofs**") and
`docs/plan/exploration-track/phase-4-eqsat-walkback/README.md:57-67` ("nothing
consumes yet"). ADR-0408 checks a rewrite; it does not certify one. The gap
between "checked" and "certified" is the Lean-parity gap for the rewriter and it
is unbudgeted.

Related trap already recorded at
`docs/plan/exploration-track/phase-4-eqsat-walkback/T4.4-rule-ledger-patterns.md:29-30`:
"**Dual representations are two sources of truth.**" I hit exactly this while
designing the guard, which is why the operator scope is deliberately coarse (read
off the dispatch, one level above the match arms) and everything finer is checked
semantically by independent code rather than restated structurally.

## 6. `docs/reviews/` has never flagged any of this

Zero occurrences of "manifest" in that directory. The gap between "a rule
declares a precondition" and "anything checks it" survived every review, in a
codebase whose own guidance says tools "have lied more often than the solver has
been weak."

## 7. Minor: a pre-existing QF_ABV canonicalize error

Canonicalizing raw `QF_ABV` assertions returns
`RewriteError::Ir(SortMismatch { expected: "Bool or BitVec", found: Array {...} })`.
Verified against a pristine `git archive HEAD` build — pre-existing, not from
this slice, and not on the solver's real route (`check_with_array_elimination`
runs first). Worth a decline path rather than an `Err` if any caller ever
canonicalizes pre-elimination.

## 8. Infrastructure: `/tmp` is a 62 GiB tmpfs and the campaign fills it

Three link steps died with `collect2: fatal error: ld terminated with signal 7
[Bus error]` while `/tmp` sat at 80% with multiple agents' `target/` directories
in it. This reads as a compile error and is not one. Campaign rule 7 tells agents
to snapshot into scratch; on this host that scratch is tmpfs. **Recommend the
rule name a disk-backed path**, or that agents set `CARGO_TARGET_DIR` and
`TMPDIR` off tmpfs. I moved to `/home/mjbommar/.cache/` and every failure
vanished.
