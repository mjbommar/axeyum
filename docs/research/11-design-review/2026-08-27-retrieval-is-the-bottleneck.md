# Retrieval, not proof difficulty, is the measured bottleneck

Status: **open deficiency**, Opus lane dispatched 2026-08-27.

## The observation

Repeatedly this session, a lane declared itself blocked on a lemma that already
existed, proved, in the tree. The count reported by lanes reached **thirteen**
by the end of the day. That number is a lane-reported tally and has **not** been
independently audited — auditing it is part of the dispatched work, not a
conclusion this file asserts.

The most expensive single instance, because it stalled a whole rung of `supOn`:

    CReal.congr_of_uniformly_continuous :
      ∀ (F : CReal → CReal) (a b : CReal),
        UniformlyContinuousOn F a b →
        ∀ x y : CReal, le a x → le x b → le a y → le y b →
          Equiv x y → Equiv (F x) (F y)

A lane needed exactly this, searched `creal/uniform_continuity.rs` — the module
where it *belongs* — found nothing, and reported the obstacle as its stopping
point. The lemma lives in `creal/integral.rs`, because
`riemann_sum_split_exact_of_uc` consumed it first.

**The search was competent and the answer was correct.** Nothing about the query
was wrong. The lemma is simply not filed where its subject matter says it should
be, and a by-name search cannot find a thing whose name you do not know.

## The three hiding places, all measured

1. **General infrastructure filed under its first consumer's module.**
   `CReal.bucketIndex` (with four clamp lemmas) lives in `uniform_continuity.rs`
   because a covering argument needed it first; it is now consumed by three
   other modules. `congr_of_uniformly_continuous` is the same shape.
2. **A reusable step built INLINE inside a larger declaration, never named.**
   `nat_prelude/powsq.rs`'s `declare_pow_half_split` performs a complete `Nat`
   even/odd split purely as scaffolding. **An inline step has no name to find**,
   so no name-based index can ever surface it.
3. **A lemma whose stated hypothesis is WEAKER than everyone assumes.**
   `CReal.sumRange_cauchy_of_dominated` never required `f` nonnegative, so it
   already covers signed series. Two lanes discovered this independently, both
   against briefs asserting the opposite.

## Why the existing tools cannot fix this

`prelude_theorem_inventory` lists **theorems only**, so every `Definition` —
`Nat.add`, `CReal.integral`, `Rat.polyEval` — returns **zero rows**. Worse, a
prefix grep for `Rat.polyEval` returns 16 hits, every one a *lemma about* it and
none the definition. So the careless query confirms presence and the careful
anchored query reports absence, and **both are wrong about the definition**.

And none of these tools answer the question a blocked lane actually has, which
is never *"is this name taken?"* but:

> **Does something of this SHAPE exist — anywhere, under any name?**

## Why this is the right thing to fix now

`docs/formalized-math-2026-08/07-the-cost-model-and-pareto-position.md` names
three gates on marginal cost per theorem: **contracts, retrieval, sharding**.
Retrieval is one of them, and it is the one with a running measurement.

The cost is not the rebuild. It is that each blocked lane first *sizes its task
as new*, and several came close to building a duplicate. A duplicate is worse
than a delay: **it leaves two proofs of one fact that must stay in sync, and the
kernel happily verifies both.** That has already happened once, with six private
helpers copied verbatim rather than reported.

Prose has not fixed it. CLAUDE.md has carried "search for the STEP, not the
NAME" for some time, and every brief this session repeated it, and the thirteenth
instance still happened — to a careful lane, following the instruction.

## What is dispatched

A shape-indexed retrieval tool over `kernel.environment()` — matching on the
structure of a declaration's type (conclusion head symbol, hypothesis shapes)
rather than on its name — covering **every** declaration kind, not just
`Theorem`, so it answers the definition question the theorem inventory
structurally cannot.

Two things it must do that no current tool does:
- **Fail on absence**, so a fact-ledger `checker_command` can depend on it.
- **Pair every negative with a positive control of the SAME declaration kind.**
  A theorem is not a control for a definition; `Nat.add` returning zero rows is
  the fastest way to learn you are asking the wrong tool.

Hiding place 2 (inline, unnamed steps) is likely **out of reach** for any index
over declared names, since there is no declaration to index. Say so explicitly
rather than implying coverage that does not exist.

---

# Appendix (lane `retrieval`, 2026-08-27): the audit, the tool, and a fourth hiding place

Decision: [ADR-0608](../09-decisions/adr-0608-retrieval-is-by-shape-and-absence-is-distinct-from-unanswerable.md).

## 1. The audit of "thirteen"

The thirteen was a lane-reported tally. Audited independently against commit
messages on `main` from 2026-08-25 to 2026-08-27 — **1,032 commits**, matched
against a deliberately wide phrase family (`already exist`, `already prov`,
`already had`, `already covers`, `not new`, `instead of re-deriv`, `duplicate`,
…) giving **65 candidates**, then judged by hand one at a time. The classifier's
only job was to produce the candidate set: a crude classifier that flags a whole
shape is not a measurement.

**The audited count is seventeen distinct instances — higher than thirteen, not
lower — and it is a lower bound**, because it can only see cases a lane wrote
down in a commit message. A lane that was blocked, sized the work as new, and
never said so is invisible to this method.

Counted as an instance: a lane, a brief, a module doc or a curriculum row
treated something as absent or as new work when a declaration providing it
already existed. Ordinary reuse of a known lemma is **not** counted.

| # | What already existed | How it surfaced | Commit |
|---|---|---|---|
| 1 | `pow half n <= 1/(n+1)`, rational form (`Rat.bernoulli_harmonic_bound`) | Blocked Spivak Ch. 7, 12, 18, 21, 22, 23; **three lanes arrived at it independently** | `e94537f7a`, `a7534f280` |
| 2 | `CReal.pow_half_le_nat_div_succ` | `geometric.rs`'s own module doc named it as the last blocker; it was built elsewhere for the IVT bisection modulus. Two lanes. | `885f468da`, `8e6b98e43` |
| 3 | The exact lower-bound rate inside `strict_mono_of_pos_deriv` | Inline, unnamed; extracted as `CReal.strict_mono_magnitude` | `0b0633b68` |
| 4 | `Complex`'s `abs_nonneg` | Rebuilt by hand for `CReal.sqrt_nonneg` because `complex.rs` sits outside `creal` | `27fd19a0d` |
| 5 | `converges_of_cauchy` / `regular_of_scaled_cauchy` | A lane's own doc asserted "no witness to an actual limit anywhere in this development" | `301a7fa58` |
| 6 | `CReal.le_min` and the `lattice.rs` min family | "directly contradicts an earlier guess that it was missing" | `b52979366`, `335ab9671` |
| 7 | `CReal.two_le_e` / `e_le_three` / `e_le_four` | A curriculum row said "2 <= e <= 3 open"; stale | `cbcce411d` |
| 8 | `import_statement_ndjson` (since 2026-08-18) | ADR-0604 asserted it absent "from an uncontrolled grep"; amended | `5881bac4e` |
| 9 | The `factorQuotient` correction equation | Sized as a fresh induction; was "one existing equation" | `fdd4d4b11` |
| 10 | `CReal.BoundedOn` | Near-miss: a new predicate was assumed necessary | `49fa00986` |
| 11 | The `Nat` even/odd split inside `declare_pow_half_split` | Inline, unnamed; "prior art found", packaged as `Nat.even_or_odd` | `88c516432` |
| 12 | `CReal.bucketIndex` + its clamp lemmas | Near-miss: a crossing-index lane found it in step 0 and reduced its task to a rescaling | `b24447548` |
| 13 | `CReal.sumRange_cauchy_of_dominated`'s hypothesis is weaker than assumed | **Two lanes discovered it independently**, both against briefs asserting the opposite | `220ce34f1` |
| 14 | `CReal.equiv_of_le_le` | Budgeted as new work in a brief | `cc32c7a9a` |
| 15 | `CReal.equiv_zero_of_small` | Budgeted as new work in a brief | `cc32c7a9a` |
| 16 | `CReal.congrOfUniformlyContinuous` | Searched for in the module where it belongs; lives in `integral.rs` | `04269dfab` |
| 17 | `integral_converges`, already kernel-checked | Its witness triple had been **re-derived by hand**; the duplicate cost a measured **92 s -> 18 s** on every prelude build until it was found | `aedf9bb3e`, `9926bb68c` |

**Three of these landed as real duplicates rather than being caught in time**:
#17 above; `step_le_outer_bound` + `magnitude_times_frac_eq_outer` "duplicated
verbatim from `monotone.rs`" (`44ed9d326`); and the `abs_neg_le` / `double_neg`
/ `neg_unique` group copied because the originals are private in
`creal/derivative.rs` (`fb2c703a6`).

Two adjacent measurements, reported separately because they are a different
defect — the *ledger* not knowing rather than a lane not knowing: 28 facts
already proved in this kernel were registered late in one batch (`e5ef628f3`),
and 5 of 57 held-out propositions were already proved in the kernel while the
gate read `epistemic_status` (`b38920a72`).

**So the motivating statistic survives auditing and understates the problem.**

## 2. A fourth hiding place the write-up does not name: there is no single spelling

`CReal.congrOfUniformlyContinuous` is the **kernel** name. The Rust field is
`congr_of_uniformly_continuous`, and that is the spelling this design document,
the dispatching brief and CLAUDE.md's gotcha all use. A lane that greps the
kernel inventory for `congr_of_uniformly_continuous` gets **zero rows for a
declaration that exists** — the exact failure this document is about, arriving
by a route nobody had named.

It is not an isolated inconsistency. Over the 464 `CReal` declarations in the
built environment:

| | count |
|---|---|
| names containing `_` | 315 |
| names containing an internal capital | 200 |
| names containing **both** | 114 |

`CReal.equiv_of_le_le` and `CReal.congrOfUniformlyContinuous` sit in one
namespace, and `CReal.abs_sumRange_le` mixes the conventions inside a single
name. There is nothing to guess.

`--name-like` normalises case, `_` and `.` on both sides, so `--name-like
congr_of_uniformly_continuous` retrieves `CReal.congrOfUniformlyContinuous`; the
nearest-name hint printed with an absent or unanswerable verdict uses the same
normalisation.

## 3. What was built

`crates/axeyum-lean-kernel/src/shape_index.rs` (index + query engine + its
controls) and `crates/axeyum-lean-kernel/examples/shape_search.rs` (CLI).

    cargo run --release -p axeyum-lean-kernel --example shape_search -- --help

A lane's first query, before sizing any task as new:

    …--example shape_search -- --include-constructed \
        --concl CReal.Equiv --hyp CReal.UniformlyContinuousOn --hyp CReal.Equiv

**This does not replace `kernel_declaration_projection --require-declaration`**,
which already answers *"does a declaration with EXACTLY this name exist?"* with a
non-zero exit on absence, across every kind — a lane built it earlier the same
day for precisely the `Definition`-shaped fact-ledger checkers. Use that when
you know the name. `shape_search` is for when you do not, which is the case that
has cost this repository real work. (Noticing that tool existed at all was
itself an instance of the defect: the brief stated no such checker existed.)

Measured in `--release`: **1,838 distinct declarations across ten prelude
groups, ~21 s under lane contention (13 s idle)** to build the index. `--index-values` adds no measurable cost
(13.5 s vs 13.0 s). The whole run executes on
`axeyum_lean_kernel::on_a_deep_stack`, so a debug invocation cannot SIGABRT and
be mistaken for an absent declaration.

### The five named test cases

| case | query | result |
|---|---|---|
| `congr_of_uniformly_continuous` (by shape, not name) | `--concl CReal.Equiv --hyp CReal.UniformlyContinuousOn --hyp CReal.Equiv` | **exactly 1** row, `CReal.congrOfUniformlyContinuous` |
| `equiv_of_le_le` | `--concl CReal.Equiv --hyp CReal.le --hyp CReal.le --arity 4` | 2 rows, `CReal.equiv_of_le_le` first |
| `equiv_zero_of_small` | `--concl CReal.Equiv --const CReal.zero --ns CReal` | 13 rows including it |
| `CReal.bucketIndex` | `--kind definition --ns CReal --concl Nat` | 10 rows — every `CReal` index computation, `bucketIndex` and `crossingIndex` among them |
| `Rat.polyEval` (the **definition**) | `--name Rat.polyEval --kind definition --expect 1` | **exit 0**, one `definition` row |

The last is the case `prelude_theorem_inventory` returns zero rows for and a
prefix grep returns sixteen wrong rows for.

### The weaker-hypothesis case (hiding place 3)

Partially, and usefully. It cannot tell a lane "this is more general than you
think" — nothing can, without knowing what the lane thinks. What it does is put
the **real** signature in front of them:

    CReal.sumRange_cauchy_of_dominated  theorem  arity=4
      CReal -> CReal -> CReal.le -> CReal.Cauchy -> CReal.Cauchy
      consts=[CReal, CReal.Cauchy, CReal.abs, CReal.le, CReal.sumRange, Nat]

There is no nonnegativity predicate anywhere in that constant set, and the
absence is the evidence. `--concl CReal.Cauchy --hyp CReal.le` returns four rows
— a readable list — and surfaced `CReal.sumRange_cauchy_of_abs_cauchy` (arity 2)
beside it, which is more general still.

Reading a hypothesis head **under its own telescope** is what makes this work.
The domination premise is `(k : Nat) -> le (abs (f k)) (g k)`; taking only the
outermost node files it as `Nat` or as nothing, and `--hyp CReal.le` then misses
every domination, modulus and "for all k" premise in the library — which is most
of the interesting ones. That guard is mutation-verified below.

### Hiding place 2, honestly

An inline step has no declaration, so an index over declared names is
structurally blind to it, and this tool does not claim otherwise.

`--index-values` is a **partial** route and is documented as one: it indexes the
constants appearing in each declaration's checked *value*, answering "which
declarations' proofs already perform this step?" when you can name one lemma the
step uses. On the case the write-up names — the `Within` -> `close_within` step
built inline in `converges_of_scaled_cauchy` —

    --index-values --value-const CReal.speedup_close --ns CReal

returns six rows, `CReal.converges_of_scaled_cauchy` among them, in 13.5 s. It
returns the enclosing declaration rather than the step, and it cannot help at
all if you cannot name an ingredient.

**A route to the rest, described and deliberately not built here:** the inline
steps that matter are `Kernel::infer`-able subterms of a checked proof value
whose inferred type is a `Prop`. Indexing those types — one `infer` per
application/`let` node, memoised on `ExprId` — would give inline steps a
searchable statement without declaring them. The cost is an `infer` per node
rather than a name lookup, so it belongs behind its own flag and its own
measurement, and it should be sized against the cheaper alternative first: a
lint flagging any proof value containing a `Prop`-typed subterm reused three or
more times, which is the shape worth extracting anyway.

### Duplicate detection, and what it found

`--duplicates` groups declarations whose types are identical up to binder
naming. Restricted to theorems by default — a `Definition`'s type is not its
statement, `Nat.add` and `Nat.mul` are both `Nat -> Nat -> Nat`, and the
unrestricted scan returns 67 groups of noise against 6 real ones — the
constructed library contains **ten pairs of theorems stating literally the same
proposition under two names**:

    Rat.chebyshev_sampleMean_uncorrelated   Rat.weak_law_of_large_numbers
    CPoint.apollonius_from_stewart          CPoint.apollonius_median
    CReal.rat_approx_upper                  CReal.sampleUpperBound
    CReal.rat_approx_lower                  CReal.sampleLowerBound
    Nat.succ_sub_succ                       Nat.succ_sub_succ_eq_sub
    Nat.le_succ_succ                        Nat.succ_le_succ
    Int.Characterization.zero_lt_one        Int.zero_lt_one
    Int.Characterization.le_total           Int.le_total
    Int.Characterization.discrete           Int.no_int_between
    Nat.Peano.succ_injective                Nat.succ_injective

The last four are cross-package restatements — the `Nat.Peano.*` /
`Int.Characterization.*` packages exist to state the characterizing axioms — and
are plausibly deliberate; the first six are within-package and none was
previously reported. Each is two proofs of one fact that must stay in
sync while the kernel happily verifies both. (`Nat.le.refl` / `Nat.le_refl` and
`Nat.le.step` / `Nat.le_succ_of_le` are the same shape across a
constructor/theorem boundary and are hidden by the theorem-only default;
`--kind theorem --kind constructor` shows them.)

## 4. How it fails on absence, and the evidence that it can

Three outcomes, checked in this order:

* **unanswerable, exit 3** — the query named a constant, a declaration kind or a
  namespace root the built index does not carry. Checked *before* matching and
  not overridable by any assertion flag.
* **absent, exit 1** — answerable, nothing matched. Printed with its own
  same-kind positive control on the same line, e.g.
  `verdict: ABSENT (positive control: theorem=822 ns Nat=406)`.
* **found, exit 0**.

The same-kind control is therefore structural, not advisory: `--concl
CReal.Equiv` without `--include-constructed` is exit 3 with a reason, never a
confident zero, and `--name AxNat.add` — a `lean_pp` export name with no kernel
declaration behind it — is exit 3 pointing at `Nat.add`.

`--expect N` / `--min N` / `--expect-absent` make the exit status depend on the
count, so a fact-ledger `checker_command` can assert a construction exists
(`--name CReal.integral --kind definition --expect 1`), which
`prelude_theorem_inventory` structurally cannot.

### Mutation evidence, including three guards that were decoration

Eighteen guards deleted one at a time, in this lane's own worktree (never the
shared checkout), with the suite re-run after each. **Fifteen were killed by a
named test; three survived, and all three were real gaps in the controls rather
than redundant guards.**

    BASELINE  17 passed / 0 failed
    KILLED    empty-index-guard                  16 passed / 1 failed       an_empty_index_is_unanswerable
    KILLED    unconstrained-query-guard          16 passed / 1 failed       an_unconstrained_query_is_unanswerable
    KILLED    value-index-guard                  16 passed / 1 failed       value_const_without_value_indexing_is_unanswerable
    KILLED    vocabulary-guard                   15 passed / 2 failed       an_export_name_is_unanswerable_with_a_pointer_to_the_kernel_name an_undeclared_constant_is_unanswerable
    KILLED    kind-census-guard                  16 passed / 1 failed       a_kind_the_index_does_not_carry_is_unanswerable
    KILLED    namespace-census-guard             16 passed / 1 failed       an_unbuilt_namespace_is_unanswerable
    KILLED    distinct-binder-consumption        16 passed / 1 failed       repeated_hypothesis_needs_distinct_binders
    KILLED    kind-filter                        16 passed / 1 failed       the_definition_is_retrievable_and_its_lemmas_do_not_stand_in_for_it
    KILLED    arity-filter                       16 passed / 1 failed       a_genuine_zero_is_absent_not_unanswerable
    KILLED    concl-filter                       16 passed / 1 failed       repeated_hypothesis_needs_distinct_binders
    SURVIVED  type-const-filter                  17 passed / 0 failed       -
    SURVIVED  value-const-filter                 17 passed / 0 failed       -
    KILLED    name-exact-filter                  15 passed / 2 failed       the_definition_is_retrievable_and_its_lemmas_do_not_stand_in_for_it the_nat_prelude_yields_definitions_and_theorems
    KILLED    like-key-sort                      16 passed / 1 failed       like_key_ignores_hypothesis_order
    KILLED    duplicate-group-threshold          16 passed / 1 failed       duplicate_shapes_are_grouped
    KILLED    namespace-root-first-component     15 passed / 2 failed       namespace_root_is_the_first_component a_shape_query_over_the_nat_prelude_retrieves_by_structure
    KILLED    deep-hypothesis-head               16 passed / 1 failed       a_quantified_hypothesis_is_headed_by_its_own_conclusion
    SURVIVED  nearest-hint                       17 passed / 0 failed       -

The three survivors are worth reading, because each failed for a different
reason and one of them is this repository's own documented hazard biting the
test written to catch it:

* **`--const` (type-constant) filter.** The test asserted a row was PRESENT and
  never that the conjunct EXCLUDED anything, so deleting the filter widened the
  answer and the assertion still held. Fixed by asserting `Nat.mul_comm` — same
  shape `Nat -> Nat -> Eq`, constants `[Eq, Nat, Nat.mul]`, no `Nat.add` — is
  **absent** from the `--const Nat.add` result.
* **`--value-const` filter.** Every other row in the fixture was excluded by the
  *"values were not indexed"* arm before the membership loop was reached, so the
  loop was never exercised. Fixed by adding a row that HAS an indexed value not
  containing the queried constant.
* **The nearest-name hint.** The test asserted
  `reasons.iter().any(|r| r.contains("Nat.add"))` for a query on `AxNat.add` —
  and the reason string contains `AxNat.add`, which **contains `Nat.add` as a
  substring**. The assertion passed with an empty hint. This is exactly the
  hazard CLAUDE.md records for `contains("Real.")` matching `CReal.`, occurring
  inside the test written to catch a naming confusion. Fixed by asserting on
  `ShapeIndex::nearest` directly.

Confirming pass over the three repaired guards plus the two new ones:

    BASELINE  18 passed / 0 failed
    KILLED    type-const-filter          17 passed / 1 failed       a_shape_query_over_the_nat_prelude_retrieves_by_structure
    KILLED    value-const-filter         17 passed / 1 failed       value_const_without_value_indexing_is_unanswerable
    KILLED    nearest-hint-needle        17 passed / 1 failed       an_export_name_is_unanswerable_with_a_pointer_to_the_kernel_name
    KILLED    name-like-filter           17 passed / 1 failed       a_snake_case_guess_retrieves_a_camel_case_declaration
    KILLED    spelling-normalisation     17 passed / 1 failed       a_snake_case_guess_retrieves_a_camel_case_declaration

Timings: 18 tests in 0.50 s; each mutant costs a ~50–90 s release rebuild under
lane contention.

## 5. What is NOT covered

* Inline, unnamed steps (hiding place 2) — structurally, as above.
* Definitional unfolding: two statements that are defeq but structurally
  unrelated index differently. The index is syntactic and cheap on purpose.
* Anything outside the ten prelude groups it builds. Coverage is printed on
  every run and a query into an unbuilt namespace is exit 3, so this is a
  declared limit rather than a silent one.
* It does not rank. A broad query returns a list, and reading it is the lane's
  job; `--limit` truncates and says so.

---

# The running ledger: daily audits after 2026-08-27

The seventeen above are a one-off measurement over 2026-08-25..27. ADR-0608's
structural remedy is that **one lane per day audits the previous day's commits
by the same method**, so a duplicate costs hours instead of weeks. Each day's
audit gets its own write-up; this table is the ledger, and the running total is
what should be quoted, not the seventeen.

| day audited | audit | commits in window / kernel-path | candidates | confirmed | literal duplicates | deduped |
|---|---|---|---|---|---|---|
| 2026-08-25..27 | [§1 above](#1-the-audit-of-thirteen) | 1,032 / — | 65 | 17 | 3 | 3 (in-session) |
| 2026-09-01 | [2026-09-02-retrieval-audit-for-2026-09-01.md](2026-09-02-retrieval-audit-for-2026-09-01.md) | 240 / 69 | 17 | 4 | 1 | 1 (`b4fb008d8`) |
| 2026-09-02 | [2026-09-03-retrieval-audit-for-2026-09-02.md](2026-09-03-retrieval-audit-for-2026-09-02.md) | 81 / 28 | 7 | 0 | 0 | 0 |

**Running total: 21 audited instances, 4 of them landed as real duplicates.**
2026-09-02 added 7 candidates and 0 confirmed instances — the first clean day
in the ledger. The L0 duplicate gate also gained a no-cargo `--prebuilt` route
into `check-merge-hygiene.sh` that day (`63f887b89`), a direct structural
response to the 2026-09-01 audit's 25-hour red-gate finding.

Do not add the rows' *candidate* counts and read a rate off them: the windows
differ in length, the classifier widened between the first and second rows (it
adds `turns out`, `promote`, `hoist`, `unexpose`, `dedup`, `was already` and six
more), and only the first row is unscoped to `crates/axeyum-lean-kernel`. What
is comparable is the confirmed-per-audited-day figure, and only once there are
enough days to have one.
