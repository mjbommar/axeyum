# ADR-2135: arrays of datatypes as opaque elements — the refused sort is exactly what three lanes said it was, and it is the terminal blocker on 2 rows of 800

Status: proposed
Index-summary: Three lanes in succession named `register_datatype`'s field-closure refusal as the `AUFDTLIRA` datatype blocker, each from a different population, and this lane was dispatched to admit the refused sort -- an array whose ELEMENT is a datatype -- as an opaque container. **SIZING FIRST CONFIRMS THE PREMISE ABOUT WHICH SORT AND REFUTES IT ABOUT HOW MUCH.** The refused sort is `(Array Int <datatype>)` on **142/142** (DT-GROUND-PROBE's 83 files), **112/112** (`AUFDTLIRA` undecided), **86/86** and **112/112** ([ADR-2114]'s two populations) -- SPARK's `us_rep`/`us_rep1` array-of-record -- and **ZERO** refused sorts are an array with an uninterpreted domain or range, which is a DIFFERENT site (`auto.rs`'s lazy Bool/Int admission test, 4 of 81 `AUFDTLIRA` rows); folding the two would have reported one blocker where there are two. But the refusal is the TERMINAL reason on only **2 of 81** undecided `AUFDTLIRA` rows, **0 of 56** `UFDTLIRA`, **0 of 29** `QF_DT`: of the 12 `AUFDTLIRA` files that declare a refused datatype, 10 die at `quant:ematching` (6) or the [ADR-2103] quant-route decline (4). A column counting only "declares a refused datatype" would have read 12/81 and been six times too optimistic -- the same reach-vs-terminal gap [ADR-2128] measured as `LEVER CONVERTS=410` against +3/-0. Ceiling **6 of 800** rows across the four A/B divisions. THE REFERENCES: neither inspects an element sort anywhere in its array theory -- z3's store/select and extensionality axioms are built from `enode`s (`theory_array_base.cpp:110`, `:149`, `:331`; `theory_array.cpp:227-231` checks only that both terms are ARRAY-sorted) and the extensionality witness is typed by the INDEX sort (`array_decl_plugin.cpp:304-318`, range taken from `s->get_parameter(i)`), with `grep` for `get_array_range` / `is_datatype` / `is_uninterp` returning ZERO hits in both array files and arrays appearing in `theory_datatype.cpp` only for the acyclicity occurs-check (`:358`, `:923-926`, `:992-1000`); cvc5 the same, `checkRowLemmas` (`theory_arrays.cpp:1899`) and `getExtIndexSkolem` (`skolem_cache.cpp:27-37`) sort-agnostic, `grep isDatatype src/theory/arrays/*.cpp` **NOT FOUND**, the ONE element-sort case in the whole theory a Boolean-only trigger registration (`:896`), and datatype elements reaching `theory_datatypes` through the generic shared-term path (`:911-919`, `computeCareGraph:1030`). SHIPS OFF (`AXEYUM_DT_ARRAY_ELEMENT`, default `off`, registered as `DT_ARRAY_ELEMENT_DEFAULT` in `config_registry.rs` with `note_crossed` wired): ONE predicate `field_is_opaque` used by the three sites [ADR-1920] requires to agree -- `register_datatype` admits on it, `build_sym_vars` skips on it, `scan_fragment` refuses a `select` of it -- reducing with the lever OFF to `matches!(sort, Sort::Datatype(_))`, the pre-change predicate verbatim. The field gets NO expansion variable, so `datatype_expansion_is_exact` stays false, no congruence is emitted over it and `build_dt_eq` keeps the free-boolean relaxed form -- the SAME regime a datatype-typed field has run on since [ADR-1930] -- and traversal is refused TWICE, by the new scan arm and by the UNCHANGED `refuse_if_datatype_survives`. 12 tests in a pre-push-gated suite whose OFF arm asserts the refusal AND ITS WORDING, run in the default loop and again under `AXEYUM_DT_ARRAY_ELEMENT=on` because the process value is resolved once; 2 mutations, 2 killed, exactly one named fixture each (`--check-anchors` stale=0). **THE A/B IS A CLEAN NULL: 0 gains, 0 stable losses, 0 flips in 800 rows** across `AUFDTLIRA`, `UFDTLIRA`, `QF_DT` and a `QF_ABV` array control, one binary two env values, arms back to back per file on one pinned s7 core, divisions serial. The one raw mover (`vlsat3_b84.smt2`) rechecks NEITHER-DECIDES 3-of-3 per arm AND contains **0 occurrences of `Array`** and one field-free nullary enum, so both arms run identical code on it. The all-agreeing tables are a genuine null rather than an unarmed run, and the file that proves it is `arm-liveness.sh`: on both terminal files the ON arm emits **0** of the W1 refusals the OFF arm emits, changes the route, and still does not decide -- at 117x and 5x the solver's own `--trace` wall time and 14x the attempts. Also found, because the cost pass over this lane's own captures returned **-20,454,778,950,164,076,537 ms**: s7 runs **uutils coreutils 0.8.0**, whose `date` ignores the width modifier in `%3N` and prints nine nanosecond digits, so the `_ms` columns of BOTH this lane's and [ADR-2128]'s shard TSVs are nanoseconds under a millisecond header (30 of 30 samples are 19 chars where GNU gives 13) -- `ab-run.sh` now times with the `EPOCHREALTIME` builtin and ABORTS before any solve if a 200 ms sleep does not read as 150-400 ms. PROPOSED, NOT ACCEPTED: 0 gains is the whole reason, there is no soundness objection, and the next lane's real target -- reaching the array's ELEMENTS, which is SPARK's actual `(select (rec__content r) i)` -- is not a widening of this predicate but [ADR-2065]'s sort-abstraction route, because a residual carrying an array-of-datatype term re-enters `datatype_native` through its own `solve` call and that is [ADR-1920]'s measured 1 GiB stack overflow. Price it against 2 rows of 800 before starting.
Index-status: proposed
Date: 2026-09-16

## Context

Three lanes narrowed the datatype side of `AUFDTLIRA` to one refusal.
`register_datatype` (`crates/axeyum-solver/src/datatype_native.rs`) walks a
datatype's constructor fields and refuses the first sort `field_sort_expands`
does not accept. [ADR-1935] made that predicate admit `Bool`/`BitVec`/`Int`/
`Real`, uninterpreted sorts, and **arrays whose component sorts mention no
datatype**; [ADR-2128] added depth-bounded expansion of a datatype-TYPED field
and measured that it reaches none of the remaining refusals.

This lane's brief: admit the rest — an array whose element sort is a datatype —
by treating the element as an **opaque term of its sort**.

## 1. Sizing first, and it is the finding

Exit criterion 1 required the sizing before any code. Three sources, none
re-derived: the shipped `--trace` ledgers
(`bench-results/ledger/t1-{AUFDTLIRA,UFDTLIRA}-db31113fa.tsv`, 200 rows each),
[ADR-2128]'s per-datatype reach census (`reach-*.tsv`, carrying `today_w1` and
**`w1_sort`** — which sort was refused), and DT-GROUND-PROBE's
`terminal-reasons.tsv`. Buckets use [ADR-2128]'s `blocker-buckets.py` SITES
table verbatim so the two censuses compare; an unmatched sentence is reported as
`OTHER` with its text, never dropped. Full method and per-file names:
[`bench-results/dt-array-element-20260916/README.md`](../../../bench-results/dt-array-element-20260916/README.md).

### 1a. WHICH sort — the premise is exactly right

| population | W1-refused datatypes | `(Array Int <datatype>)` | array w/ uninterpreted domain-or-range |
|---|---:|---:|---:|
| probe-stripped-83 | 142 | **142 (100%)** | 0 |
| `AUFDTLIRA` undecided (82 files) | 112 | **112 (100%)** | 0 |
| [ADR-2114] cores-55 | 86 | **86 (100%)** | 0 |
| [ADR-2114] originals-79 | 112 | **112 (100%)** | 0 |
| `UFDTLIRA` undecided (57 files) | **0** | 0 | 0 |
| `QF_DT` undecided (29 files) | **0** | 0 | 0 |
| `UFDT` undecided (150 files) | **0** | 0 | 0 |

Two sorts account for all of it — `('Array', ('Int',), ('D', 'us_rep'))` and
`…('D', 'us_rep1')`, SPARK's array-of-record. **Zero** refused sorts are an array
with an uninterpreted domain or range. That case is a *different site* —
`auto.rs`'s lazy Bool/Int array admission test — and the brief's instruction to
split the count is what made the difference visible; folding them would have
reported one blocker where there are two.

### 1b. HOW MUCH — the premise does not survive

| division | rows | decided | undecided | files declaring ≥1 W1-refused datatype | rows whose **terminal** reason IS the refusal |
|---|---:|---:|---:|---:|---:|
| `AUFDTLIRA` | 200 | 119 | 81 | **12 / 81** | **2 / 81** |
| `UFDTLIRA` | 200 | 144 | 56 | **0 / 56** | **0 / 56** |
| `QF_DT` | 200 | 171 | 29 | **0 / 29** | **0 / 29** |
| `QF_ABV` (control) | — | — | — | 0 by construction (datatype-free logic) | 0 |

The two `AUFDTLIRA` rows are
`S702-024__record_attributes_in_allocators__test_constrained.adb_45_22_assert___00.smt2`
and `P518-021__loop_frame_condition__do_loops.adb_112_22_assert___00.smt2`. The
other **10** of the 12 die at `quant:ematching` (6) or the [ADR-2103]
quant-route decline (4) — lifting the array refusal changes their route but does
not remove what stops them.

**A column that counted only "declares a W1 datatype" would have reported 12/81
and been six times too optimistic.** That is the same reach-vs-terminal gap
[ADR-2128] measured (`LEVER CONVERTS=410` datatypes against a measured +3/−0)
and it is why the terminal column is the one that sizes a lever.

The second bucket (`auto.rs`, uninterpreted array component) is **4 of 81**
`AUFDTLIRA` and **0 of 56** `UFDTLIRA`. Ceiling across the four A/B divisions:
**6 of 800 rows (0.75%)**, and that assumes all six then decide — they all still
carry quantifiers.

DT-GROUND-PROBE's **8 of 14** largest bucket is reproduced exactly (8 at
`datatype_native.rs:1511`, 5 at `auto.rs:8527`, 1 at `sat_bv_backend.rs:122`,
`arm=default`), and it is corroboration that the site is live, not sizing: that
population is quantifier-stripped and `sat` on 83 of 83 by the reference's own
verdict, as the probe's own README states.

## 2. The references — an element sort is never inspected

Read at `file:line` in `references/{z3,cvc5}` before designing.

**z3.** The store/select axioms are built from `enode`s and never look at the
element sort: `assert_store_axiom1_core` (`references/z3/src/smt/theory_array_base.cpp:110`)
and `assert_store_axiom2_core` (`:149`, which compares only index
`enode`s — `idx1->get_root() == idx2->get_root()`). `assert_extensionality`
(`:331`) dedupes by fingerprint and is sort-agnostic;
`theory_array::instantiate_extensionality` (`references/z3/src/smt/theory_array.cpp:227-231`)
asserts only that both terms are ARRAY-sorted. The extensionality WITNESS is
typed by the **index** sort, not the element sort: `mk_array_ext`
(`references/z3/src/ast/array_decl_plugin.cpp:304-318`) takes the skolem's range
`r` from `s->get_parameter(i)`, and `assert_extensionality_core`
(`theory_array_base.cpp:358-366`) applies one such skolem per dimension.
`grep` for `get_array_range|is_datatype|is_uninterp` in `theory_array_base.cpp`
and `theory_array.cpp` returns **zero hits**; the only element-sort-adjacent
lines in `theory_array_full.cpp` are `:820`
(`SASSERT(m.is_bool(get_array_range(pred_sort)))`, in the unrelated
`choice`/epsilon operator) and `:258-339`, which case-analyses the **index**
sort's cardinality for const-array disequality. **z3 has no refusal of an array
sort based on its element sort.**

In `theory_datatype.cpp`, arrays appear in exactly two places and both are the
acyclicity occurs-check: `internalize_term` at `:358`
(`if (m_autil.is_array(s) && m_util.is_datatype(get_array_range(s)))`, to
internalize the array's `default` as a theory-var proxy) and `process_arg`
inside `occurs_check_enter` at `:923-926`, fed by `get_array_args`
(`:992-1000`). No per-element-sort expansion anywhere.

**cvc5.** The ROW lemma sites operate on index/store `TNode`s only:
`checkRowLemmas` (`references/cvc5/src/theory/arrays/theory_arrays.cpp:1899`),
`checkRowForIndex` (`:1829`), `queueRowLemma` (`:2043`); `d_infoMap`
(constructed `:86`) tracks indices and stores, never element sorts.
Extensionality is `notifyFact`'s `:1479-1481` → `:1503-1506`, and its witness
`SkolemCache::getExtIndexSkolem`
(`references/cvc5/src/theory/arrays/skolem_cache.cpp:27-37`) asserts only that
both sides are arrays of the same type. `grep isDatatype` in
`src/theory/arrays/*.cpp` returns **NOT FOUND**; the ONE element-sort special
case in the whole array theory is `:896`, a Boolean-only trigger-predicate
registration. A datatype-sorted `select` reaches `theory_datatypes` through the
generic shared-term mechanism — `notifySharedTerm` (`:911-919`) sets
`d_sharedTerms` for any non-array shared term regardless of sort, and
`computeCareGraph` (`:1030`) pairs shared ARRAYS and shared INDICES and never
branches on the value sort.

**Ours.** The refusal is `register_datatype`'s default arm in
`crates/axeyum-solver/src/datatype_native.rs`, gated by `field_sort_expands`
(`Sort::Array { .. } => !sort_mentions_datatype(arena, sort)`). The lazy array
route's admission test is `scalar_alia_auflia_arrays_supported`
(`crates/axeyum-solver/src/auto.rs:9561`), which requires `!features.has_datatype`
— and its own doc comment already records the [ADR-1960] precedent for lifting
such a clause: *"The CEGAR engine is element-sort-agnostic: `RowCtx::resolve_select`
reads `element_sort` out of `Sort::array_sorts()` and declares a fresh symbol at
that sort. Nothing in it branches on `Int`."* `eliminate_arrays` ([ADR-0010])
lives in `crates/axeyum-rewrite/` and is the eager read-over-write + Ackermann
route for QF_ABV.

## 3. What was built — one predicate, three sites, an OFF lever

`field_is_opaque(arena, sort)` is the single definition of "opaque field":

```rust
Sort::Datatype(_) => true,
Sort::Array { .. } => dt_array_element_admitted()
    && crate::datatype_elim::sort_mentions_datatype(arena, sort),
```

Three sites call it, because [ADR-1920]'s measured lesson is that two predicates
written twice in different words do not stay the same predicate:
`register_datatype` admits on it, `build_sym_vars` skips on it, `scan_fragment`
refuses a `select` of it. With the lever OFF it reduces to
`matches!(sort, Sort::Datatype(_))` — the pre-ADR-2135 predicate — so the
shipped encoding is unchanged.

**Why this is sound, and it is the SAME argument a datatype-typed field has run
on since [ADR-1930].** The field gets no expansion variable, so:

* `field_sort_expands` still answers false for the array sort and
  `datatype_expansion_is_exact` is still false for the owning datatype. No
  congruence is emitted over it ([ADR-1935]/[ADR-1946]) and `build_dt_eq` keeps
  the FREE-boolean relaxed form ([ADR-1930]) — the sufficiency clause says
  `tag_l != j` for a constructor whose fields are not all comparable, which is
  what stops the wrong `unsat`.
* Traversal is refused **twice**: the new `scan_fragment` arm, and the UNCHANGED
  `refuse_if_datatype_survives` on any residual term whose sort mentions a
  datatype. Neither guard is weakened. What the lever lifts is the refusal that
  fires on the DECLARATION, before any traversal is known about.
* Model projection already has a value: `well_founded_default`
  (`crates/axeyum-ir/src/eval.rs:236`) answers `(Array Int D)` with a
  `Value::GenericArray` whose default is `D`'s own well-founded default, so a
  projected model is total and replays.
* `relaxed_eq` widens from `dt_has_datatype_field` to `dt_has_opaque_field`, so
  a replay mismatch on such a query is the `unknown` it is and not an ERROR.

**What it deliberately does not do.** It does not recurse into the array's
component datatypes — a closure that reaches a datatype only THROUGH an array is
not registered at all. The array is a container, not a field to expand.

Lever: `AXEYUM_DT_ARRAY_ELEMENT=on|1`, default OFF
(`DT_ARRAY_ELEMENT_DEFAULT`), plus `DatatypeArrayElementGuard` for a thread so
no test is a gate on one shell. Registered in `config_registry` with a dated
justification and `note_crossed` wired, so a `--trace` run can say the shipped
default is not what decided the query.

## 4. The half this lane did NOT build, and why the cost is real

SPARK's actual VC shape is `(select (rec__content r) i)` — it **traverses** the
array field. That is a decline here, so the two terminal files are not reached.

Giving the field a real expansion variable does not work by itself: the residual
then carries an `(Array Int us_rep1)` term, and `check_with_datatype_native`
solves its residual by calling `solve(arena, &reduced, config)` — a full
re-dispatch. `Features::note_sort` recurses into array component sorts, so
`has_datatype` is set again and the dispatcher routes straight back into the
same function with the same input. That is [ADR-1920]'s measured failure
verbatim: a 22 KB file that overflowed a **1 GiB** stack. `refuse_if_datatype_survives`
exists precisely to stop it, and widening it is not a local change.

The route that would work is [ADR-2065]'s `OpaqueReals` shape: abstract the
array-of-datatype to an array over a fresh uninterpreted sort, which is an
OVER-approximation (dropping constructor distinctness, injectivity and
exhaustiveness enlarges the model set), so `unsat` transfers and every `sat` is
replayed. Both references say that is the right shape — neither inspects an
element sort anywhere in its array theory. At **2 of 800** rows it is not the
next thing to spend on, and saying so with the number is this ADR's main
deliverable.

## 5. The A/B — 800 rows, 0 gains, 0 stable losses, 0 flips

One binary (`smtcomp_cli-2135`, sha256 `66604134b6ec…`, built from `9fab977cc`
and licensed by a `find -newer` check over `crates/**/*.rs`), two env values,
both arms of a file back to back on the same pinned s7 core, order alternated
per file, 24 s / 8 GiB, four divisions run SERIALLY across cores 1/3/5/6 — one
thread of each of this lane's physical pairs, never both threads of a pair.

| division | base | arm | gains | losses | flips |
|---|---|---|---:|---:|---:|
| `AUFDTLIRA` | unsat 119, unk 81 | unsat 119, unk 81 | 0 | 0 | 0 |
| `UFDTLIRA` | unsat 138, **sat 6**, unk 56 | unsat 138, **sat 6**, unk 56 | 0 | 0 | 0 |
| `QF_DT` | unsat 107, sat 64, unk 29 | unsat 106, sat 64, unk 30 | 0 | 1 raw → **0 stable** | 0 |
| `QF_ABV` (control) | sat 132, unsat 55, unk 13 | sat 132, unsat 55, unk 13 | 0 | 0 | 0 |
| **all** | | | **0** | **0** | **0** |

`UFDTLIRA` is the soundness-load-bearing division — the only one with `sat` rows
on both arms, so the only one where the lever had the OPPORTUNITY to turn a
`sat` into an `unsat`. It did not, and there were **0 flips across all 800
rows**.

### 5a. The all-agreeing tables are a NULL, not an unarmed run

`ab-summarize.py` prints, on an all-agreeing A/B, that the result *"is
consistent with the lever changing nothing on this population AND with the arm
never having been enabled — the two are not distinguishable from this file."*
It is right, and this is the file that distinguishes them
(`scripts/arm-liveness.sh`, `census/arm-liveness.txt`, exit status depends on
the finding):

| file | base W1 refusals | arm W1 refusals | |
|---|---:|---:|---|
| `S702-024__record_attributes_in_allocators__…_45_22_assert___00.smt2` | 2 | **0** | LIVE |
| `P518-021__loop_frame_condition__do_loops.adb_112_22_assert___00.smt2` | 2 | **0** | LIVE |

The arm removes the refusal it was built to remove, on both of the only two
rows whose terminal reason it is. The route then changes and still does not
decide, which is what §1b predicted:

```
S702-024 base  bound_by=q:eq-partition  last=fd:bounded-completeness-unsat  total_ms=13     attempts=22
S702-024 arm   bound_by=q:mbqi-quick    last=q:mbqi-quick                   total_ms=1525   attempts=9
P518-021 base  bound_by=q:egraph        last=fd:bounded-completeness-unsat  total_ms=2705   attempts=23
P518-021 arm   bound_by=q:egraph        last=fd:bounded-completeness-unsat  total_ms=13707  attempts=325
```

Those numbers are the SOLVER's own `--trace` clock. They say the arm costs 117x
and 5x the wall time and 14x the attempts on these two files, for no verdict.

### 5b. The one mover, and why it is not this lever

`QF_DT/20210312-Bouvier/vlsat3_b84.smt2`, `unsat` → `unknown`. Re-run **three
times per arm** on one pinned core at 24 s / 8 GiB
(`scripts/recheck-movers-env.sh`, the method of
`bench-results/route-ownership-20260915/recheck-movers.sh` with the arms
selected by env instead of by two binaries):

```
file                                    A1       A2       A3       B1       B2       B3       verdict
QF_DT/20210312-Bouvier/vlsat3_b84.smt2  unknown  unknown  unknown  unknown  unknown  unknown  NEITHER-DECIDES
```

**NEITHER-DECIDES**, so it is not a stable loss. Independently of the re-run,
the lever is structurally incapable of firing on this file: it contains **0
occurrences of `Array`** and declares exactly one datatype, a pure NULLARY enum
(`(declare-datatype Unit ((u0) (u1) … ))`) with no fields at all.
`field_is_opaque` matches only `Sort::Datatype(_)` and `Sort::Array { .. }` and
is never reached; `dt_has_opaque_field` and `dt_has_datatype_field` both answer
false for a field-free datatype. The two arms execute identical code here. The
file is 8.0 MB / 266,733 lines at a 24 s budget, i.e. exactly the shape this
repository's measured 1–1.5 % ambient flip rate lands on. (`census/vlsat3-b84-shape.txt`.)

### 5c. The held-out draw — NOT RUN, and why that is not a gap

The brief's sequence is "ship ON only with 0 stable losses and 0 flips; **then**
the held-out draw on every division that moved". **No division moved**: 0 stable
gains and 0 stable losses across 800 rows. A held-out draw is the confirmation
step for a lever that passed the pinned list, and it cannot turn 0 gains into a
reason to ship. Saying "not run" is the honest report; running it would have
produced a second null and dressed the decision up as better-evidenced than it
is.

### 5d. A tool that lied, found by this lane's own cost pass

**The `base_ms`/`arm_ms` columns of these shard TSVs are unusable, and so are
[ADR-2128]'s.** Both lanes' `ab-run.sh` timed with `date +%s%3N`; s7 carries
**uutils coreutils 0.8.0**, not GNU coreutils, and its `date` ignores the width
modifier — `%3N` prints all NINE nanosecond digits. Measured 2026-09-16: 30
consecutive `date +%s%3N` calls on s7 are **19 characters** each, where GNU
gives 13. The column is nanoseconds under a header that says milliseconds, and
the differences taken from it are not even consistently positive: this lane's
first cost pass over its own captures reported a total elapsed of
**−20,454,778,950,164,076,537 ms**, which is how it was found.

No timing claim in this ADR comes from that column; §5a's numbers are the
solver's own `--trace` clock. `scripts/ab-run.sh` now times with the
`EPOCHREALTIME` bash builtin and **self-checks before any solve** — a 200 ms
sleep must read as 150–400 ms, so a nanosecond clock (200,000,000) or a stopped
one (0) aborts the run instead of filling a column with garbage. Verified on s7
end to end: `v1l30030.cvc.smt2  unsat  114  unsat  113`.

## 6. The decision

> **THE LEVER STAYS OFF AND THIS ADR IS `proposed`.** `AXEYUM_DT_ARRAY_ELEMENT`
> defaults to `off`. The criterion for shipping a lever ON here — 0 stable
> losses, 0 flips, **and at least one stable gain**, on the pinned list and then
> on a held-out draw — fails at the gain requirement: **0 gains in 800 rows**,
> on the two divisions that carry the refused sort, on the division that does
> not, and on the array control. `accepted` is reserved for a default that
> moved.

There is no soundness reason to keep it off — 0 flips in 800 rows, the
`UFDTLIRA` `sat` rows unchanged on both arms, two mutations each killing exactly
one named fixture, and the encoding regime provably the one a datatype-typed
field has run on since [ADR-1930]. It stays off because it does not pay, and
because the traces in §5a show it costing 5–117x the wall time on the very two
files it was built for.

**What this lane establishes for the next one, and it is the useful part.** The
`register_datatype` refusal has been named as the AUFDTLIRA datatype blocker by
three lanes in succession, each reading it off a different population. It is
real, it is exactly the sort those lanes said, and it is the terminal blocker on
**two competition rows**. Admitting the DECLARATION is cheap and this ADR does
it. Reaching the ELEMENTS — SPARK's actual `(select (rec__content r) i)` — is
not a widening of this predicate but a new route ([ADR-2065]'s sort abstraction,
§4), and it must be priced against 2 rows of 800 before anyone starts. A fourth
lane pointed at this site without §1b's terminal column in front of it would
spend that price by default.

[ADR-0010]: adr-0010-arrays-via-eager-elimination.md
[ADR-1920]: adr-1920-datatype-sorted-uf-signatures-are-admitted-the-capability-gate-moves-downstream.md
[ADR-1930]: adr-1930-a-wrong-constructor-selector-is-unspecified-not-defaulted.md
[ADR-1935]: adr-1935-the-congruence-precondition-is-exactness-not-scalarity.md
[ADR-1946]: adr-1946-a-datatype-valued-uf-result-the-witness-is-a-variable-and-the-scan-has-not-run-yet.md
[ADR-1960]: adr-1960-the-real-element-array-gate-was-three-gates-and-none-of-the-19620-were-behind-it.md
[ADR-2065]: adr-2065-the-real-collector-can-hold-a-term-and-the-sat-exits-close-by-type.md
[ADR-2103]: adr-2103-quantified-ladder-ownership-and-bounded-continuation.md
[ADR-2114]: adr-2114-aufdtlira-what-the-model-finder-cannot-represent.md
[ADR-2128]: adr-2128-nested-datatype-field-expansion.md
