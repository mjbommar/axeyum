# ADR-1672: A retrieval tool's group list is derived from the builder inventory, never written by hand

Status: accepted
Date: 2026-09-06
Index-summary: A retrieval or projection tool with partial coverage does not merely fail to find things — it MANUFACTURES findings in every gate built on top of it. `examples/shape_search.rs` is the instrument a lane runs to decide whether a lemma already exists, and its ABSENT verdict is what the lane acts on — but it built 17 of the crate's 31 `pub fn build_*_prelude` functions, so `--ns FO` returned nothing against a 4,839-row dump while all 141 `FO.*` declarations sat in the tree. Its own internal cross-check (declared `coverage:` groups vs. indexed groups) passed throughout, because both halves were hand-written and omitted the same builders: a check whose two sides are written by one hand at one moment cannot fail. This ADR makes the group list ONE `const GROUPS` table that is both the coverage line and the build calls, and adds an OUTSIDE gate — `tests/shape_search_index_coverage.rs` — whose subject is read from `src/` on every run, so it cannot be kept green by editing the example. `*_prelude` turned out not to be the whole builder surface: `List.Perm` comes from `build_list_perm` over `build_list_nat_bridge`, so there are two gates over disjoint denominators. Coverage after: 31/31 preludes and 9/9 exported non-prelude builders; `--ns FO` 0 → 141, `List` 15 → 31, `AxReal` 30 → 74, `Metric.prod*` 0 → 10. The cost is real and is reported, not buried: the default index went 3,340 → 3,558 declarations and roughly tripled in build time, and `shape_search` now prints a per-group `timing:` line so the next lane deciding what to gate reads a measurement. The strongest measured result is downstream: `examples/kernel_declaration_projection.rs` had the same gap, and `scripts/check-trust-closure.py` reads its environment, so that gate was RED on main with 21 SUBJECT-ABSENT rows — 16 `FO.*`, 4 `Top.*`, 1 `Metric.*`, exactly the namespaces the example omitted, every one of them present and proved. Building them takes the gate from 23 failures to 2. The same audit over all 45 kernel instruments is `scripts/audit-kernel-tool-prelude-coverage.py`, with a two-sided ratchet.
Index-status: accepted

## Context

More lane-hours in this repository have gone to re-deriving what already
existed than to proof difficulty — thirteen-plus measured instances. The
standing answer is `examples/shape_search.rs`: search for the SHAPE, not the
name, because you do not know the name. Its exit status is designed to depend
on the finding (0 found, 1 assertion failed, 3 **unanswerable**), and
`CLAUDE.md` sends every lane to it.

Measured 2026-09-06, by three independent readers:

* the crate defines **31** `pub fn build_*_prelude` functions;
* `shape_search` reached **17** of them — 15 called directly, 2 more
  transitively;
* it was blind to all eleven `fo_*` modules. `--ns FO` returned nothing
  against a 4,839-row dump, while 141 `FO.*` declarations sat in the tree;
* also blind to `metric_prod` (`Metric.prod*` — `build_metric_prod_prelude`
  was called only by its own tests and its own inventory example), to the list
  prelude, and to `ipc_eval`.

The tool has an internal cross-check for exactly this, and it passed the whole
time. `build_index` held a hand-written `groups` vector (the `coverage:` line)
and a hand-written sequence of `index_kernel` calls (what was actually
indexed), and asserted the two agreed. Both halves omitted the same fourteen
builders, so the assert compared a list against itself.

This is the failure mode the contributor guide already names — a checker that
cannot fail is worse than no checker, because it manufactures unfalsifiable
claims at full speed. What is new here is the mechanism: **the two sides of the
check were written by one hand at one moment.** Nothing about the check being
"derived" saved it; a comparison is only worth what its most independent side
is worth.

## Decision

**A retrieval tool's group list is derived from the builder inventory, never
written by hand — and the derivation is checked from OUTSIDE the tool.**

Three parts, in the order they must be built:

### 1. One table inside the tool

`shape_search` now carries a single

```rust
struct Group { name, constructed, build: fn(&mut Kernel), why }
const GROUPS: &[Group] = &[ … ];
```

The `coverage:` line is `GROUPS.name` and the kernels indexed are
`GROUPS.build`, so those two cannot drift again. The pre-existing runtime
assert is kept but re-aimed: it now catches a group that indexed **zero rows** —
a builder that succeeds while declaring nothing into its own namespace would
otherwise put a name on the coverage line that stands for nothing.

One row per builder, and one fresh `Kernel` per row. Only `Logic`, `List`,
`Nat`, `Int`, `Real`, `CReal` and `String` register a `PreludeKey` and are
therefore idempotent inside one kernel; every other builder re-declares its own
names and the trusted gate rejects the second call. Measured:
`build_ipc_eval_prelude` after `build_ipc_soundness_prelude` in one kernel
gives `DeclarationExists { name: NameId(2195) }`. So a package with
incomparable leaves — IPC (soundness, eval), FO (order, soundness,
substitution) — gets one row per leaf, not one row for the package.

### 2. An outside gate whose subject comes from the source

`crates/axeyum-lean-kernel/tests/shape_search_index_coverage.rs` reads:

* **the authority** — every `pub fn build_*_prelude` under `src/`;
* **the call graph** — the builders named inside each builder's own FUNCTION
  BODY (body only: a builder a *test* module happens to call is not coverage);
* **the tool's reach** — a walk that STARTS at the `build:` fields of the
  `GROUPS` table and follows local functions.

A builder is covered when it is reachable. Anything else must carry a measured
reason in an allowlist, and an allowlist entry naming a builder that does not
exist, or carrying no reason, fails its own test.

That reach walk is deliberately not "every call site in the file", and the
difference was measured rather than reasoned: with a whole-file scan, deleting
the `metric_prod` and `fo_substitution` `Group` rows left every test GREEN,
because the now-dead `fn build_metric_prod` still contained the call. The
census could be satisfied by a function nothing would ever run — the same
defect one level up from the one it was written to catch.

### 3. `*_prelude` is not the whole builder surface

`build_list_prelude` alone gives 15 rows under `List`, and
`--name-contains List.Perm` returned **nothing**: `List.Perm` is declared by
`build_list_perm` over `build_list_nat_bridge`, the three-step that
`kernel_declaration_projection`, `prelude_theorem_inventory`,
`theorem_dependency_inventory` and `list_theorem_inventory` all perform. Same
shape for `Str.length_append`, `Str.substr_append_split`, and the three
`AxReal.*Model` interpretations. A census restricted to `*_prelude` would have
called all of that covered.

So there are **two** gates, over **disjoint** denominators: `*_prelude`
builders, and exported builders that are not `*_prelude`. Disjoint on purpose —
two gates sharing a denominator both die to one deletion, and a guard set whose
members all fail through the same finding cannot tell you which guard is
load-bearing. That is not a hypothetical either: before the split, deleting one
`Group` row killed two tests.

## Consequences

### Coverage, measured

| | before | after |
|---|---|---|
| `pub fn build_*_prelude` reached | 17 / 31 | **31 / 31** |
| exported non-prelude builders reached | 2 / 9 | **9 / 9** |
| default `coverage:` groups | 8 | 13 |
| `--include-constructed` groups | 16 | 22 |
| `--ns FO` | 0 (empty against a 4,839-row dump) | **141** |
| `List` namespace | 15 | **31** (`List.Perm` resolves) |
| `AxReal` namespace | 30 | **74** (the Int and Rat models) |
| `--name-contains Metric.prod` | 0 (ABSENT, exit 0 under `--expect-absent`) | **10** |

### Cost, measured and reported rather than buried

Interleaved runs of the pre-change and post-change release binaries on the same
box, load average beside every number (this is a shared machine, so a single
timing is not evidence):

| index | before | after |
|---|---|---|
| default declarations | 3,340 | 3,514 |
| default build | 26.7 s (load 16.8), 19.1 s (load 30.3) | 23.2 s (load 12.5) |
| constructed declarations | 4,839 | 5,025 |
| constructed build | 167.1 s (load 25.8), 183.0 s (load 12.1) | 181.4 s (load 12.5) |

The `after` column for build time is measured with the three `AxReal.*Model`
groups removed (see below); the intermediate state that carried them ran
235.6 s (load 12.6) and 303.4 s (load 21.3), and the default index 58.0 s /
52.2 s.

The default index roughly tripled. That is the price of never again reading an
empty answer from a tool that was not pointed at the subject, and it is paid on
a tool a lane runs a handful of times a session. It is nonetheless a real cost,
so `shape_search` now prints a per-group `timing:` line beside `coverage:`,
and `--list-groups` answers "what could this tool ever have seen?" **without**
building the index at all — a reader deciding whether an ABSENT verdict is
trustworthy is not charged a minute to find out.

The `timing:` line says where the money goes, and it contradicts the obvious
guess. Measured, default index (load 17.8 → 15.4, 53.1 s total):

    logic=0.0s nat=4.8s axreal=0.0s integer=3.2s rat=13.1s ipc=0.2s
    ipc_eval=0.1s fo_order=0.8s fo_soundness=0.4s fo_substitution=0.3s
    characterization=0.3s list=5.2s int_model=7.6s rat_model=14.4s string=2.3s

The **FO groups, the largest blind spot, are the cheapest thing added**: 1.5 s
for all three leaves and all eleven builders. What actually tripled the default
index is `int_model` (7.6 s) and `rat_model` (14.4 s) — each rebuilds `arith`
plus its carrier from scratch — with `list` (5.2 s) third.

And constructed (load 13.4 → 13.1, 232.3 s total):

    … creal_model=43.9s creal=36.7s complex=4.2s cpoint=14.9s metric=12.5s
    metric_prod=18.9s intspace=24.5s rn=21.7s geo=23.5s top=2.4s

**No group was put behind a flag on cost grounds, and the two 22-second models
are the deliberate case.** The `--include-constructed` design is safe only
because an unbuilt group's namespace is absent ENTIRELY, so a query for it
comes back `UNANSWERABLE` (exit 3) rather than ABSENT. That property does not
hold for the models: they declare into `AxReal.IntModel` and `AxReal.RatModel`,
and `namespace_root` is the first segment, so `AxReal` is present in the index
either way. A gated model group would therefore produce a confident, wrong
ABSENT for `AxReal.IntModel.add_comm` — exactly the defect this ADR exists to
close, reintroduced by the fix for its cost. `creal_model` (43.9 s, the single
most expensive group) has the same shape and is behind
`--include-constructed` only because it transitively builds all of `creal`,
which is already gated; the same hazard applies to it and is the reason it is
not gated further.

The rule this leaves for a future lane: **a group may go behind a flag only if
its whole namespace root goes with it.** Read the `timing:` line, then check
that.

### Partial coverage manufactures findings; it does not only miss them

This is the sharper form of the rule, and it was measured after the fact rather
than anticipated. `examples/kernel_declaration_projection.rs` had the same gap
as `shape_search` — it referenced 22 of the 31 builders and built neither the
first-order package, nor `Top.Frame`, nor `Metric.prod`, nor `ipc_eval`.
`scripts/check-trust-closure.py` runs that example to obtain an admitted
environment, so on main that gate was RED with 21 SUBJECT-ABSENT rows:

    16  FO.*        4  Top.*        1  Metric.*

which is exactly the set of namespaces the example omitted. Every one of those
subjects exists, proved, in the tree. The gate was not reporting a finding; it
was producing one, and nothing downstream could distinguish it from a real one.

Measured, same box, `python3 scripts/check-trust-closure.py`:

| | before | after |
|---|---|---|
| declarations | 4,817 | 5,023 |
| subjects | 2,503 | 2,524 |
| `absent` | **21** | **0** |
| `guard population` rejected | 21 | 0 |
| failures | 23 | 2 |

The two remaining are a different class: `guard alias_occurrence rejected=1`
was in the baseline too, and `IDENTITY-MAP-DRIFT` is the script's deliberate
review event — a wider environment changes the derived identity map and it
refuses to accept that silently. Neither was auto-updated here.

So the census covers that file too
(`kernel_declaration_projection_builds_every_prelude`), over the same builder
inventory read from `src/`. Its measure is the weaker whole-file call-site scan
rather than the `GROUPS`-table walk, because that file has no such table; the
test says so rather than implying it.

### The three `AxReal.*Model` groups came back out

Indexing them was an over-reach, and running the downstream gates rather than
reasoning about them is what showed it. `scripts/check-shape-duplicates.py`
went from 20 duplicate groups to **85**, of which **66** were a model law
beside its own carrier law:

    DUPLICATE  Int.lt  AxReal.IntModel.zero_lt_one
                       Int.Characterization.zero_lt_one Int.zero_lt_one

A model law is by construction a restatement of the carrier law it interprets —
that is what a model IS — so these are not re-derivations to adjudicate, they
are noise in the gate whose whole job is to find re-derivations. They also cost
7.6 s + 14.4 s by default and 43.9 s under `--include-constructed`, most of the
tripling reported above.

They are now in `DELIBERATELY_UNINDEXED_NON_PRELUDE` with that measurement as
their reason, sharing one constant so three entries cannot drift into three
stories. Nothing a lane would search for is lost: every law they restate is
indexed under its carrier, and `kernel_declaration_projection
--require-declaration` answers by name across all 31 preludes.

With them out, the cost regression is gone. Final, load 12.5:

    default  3,514 declarations, 23.2 s   (baseline 3,340, 19.1-26.7 s)
    timing:  logic=0.0s nat=4.0s axreal=0.0s integer=3.0s rat=9.3s ipc=0.1s
             ipc_eval=0.1s fo_order=0.4s fo_soundness=0.2s
             fo_substitution=0.1s characterization=0.2s list=3.4s string=2.2s

The default index is back in the baseline's range while carrying 174 more
declarations and every `FO`, `IPC` and `List` namespace. **All eleven FO
builders cost 0.7 s.**

### The same audit, over every instrument

`scripts/audit-kernel-tool-prelude-coverage.py` runs the measurement over all
45 examples that build a prelude. Seventeen build three or more; before this
work exactly one of them said which. The rule it gates is derived, not a list —
**an instrument building three or more preludes must print a `coverage:`
line** — and it is a two-sided ratchet, because the rule was introduced against
a population that already violated it thirteen times. Two-sided matters: a
one-sided ratchet stops measuring the moment somebody fixes a tool faster than
they update the number.

Four instruments now declare coverage (`shape_search`,
`footprint_closure_audit`, `prelude_theorem_inventory`,
`theorem_dependency_inventory`), plus `nat_theorem_inventory`, whose whole
failure mode is being read as a statement about the kernel when it builds one
prelude. Thirteen remain, held by the pin.

The tool × preludes table, for the record:

| instrument | preludes built (of 31) |
|---|---|
| `shape_search` | 31 |
| `kernel_declaration_projection` | 17 |
| `prelude_theorem_inventory` | 13 |
| `theorem_dependency_inventory` | 10 |
| `footprint_closure_audit`, `kernel_stack_envelope`, `nat_axiom_inventory`, `prelude_axiom_inventory`, `structural_index_extract` | 9 |
| `fo_order_inventory` | 8 |
| `fo_robinson_inventory`, `prelude_build_timing` | 7 |
| `fo_code_inventory` | 6 |
| `fo_soundness_inventory` | 5 |
| `ipc_soundness_inventory`, `metric_prod_theorem_inventory` | 4 |
| `theorem_axiom_footprint` | 3 |
| 28 further single-subject probes | 1–2 |

### What this does NOT fix

The blind spots `shape_search` already documents are untouched and remain
true: a reusable step built INLINE inside a larger declaration has no
declaration and no index over declared names can list it; a lemma more general
than its reputation is found only if you query the general shape; definitional
unfolding is not searched.

And a second, narrower gap is now named rather than left implicit: three
`pub fn build_*` helpers (`build_add_le_add_left`, `build_distrib_r`,
`build_mul_one_l`) are not exported from `lib.rs`, so no example can call them
and neither gate covers them. They declare into preludes that ARE covered, so
nothing they produce is missing from the index — but the census cannot prove
that, and says so rather than implying it.

## Alternatives considered

**Keep the hand-written group list and just add the missing builders.** This is
what every previous fix to this file did — the `metric`, `intspace`, `rn`,
`geo`, `top` and `ipc` rows each carry a comment saying "without this call the
tool reports a confident ABSENT", added one shelf at a time. Six such repairs
had not stopped the seventh. The list is not the defect; a list nothing checks
is.

**Make the internal cross-check stricter.** It cannot help. Its two sides live
in one function and are edited together; strictness does not create
independence. The gate has to read the crate, from outside the file.

**Scope the census to `*_prelude` only, as originally framed.** Rejected once
`List.Perm` was measured missing: the tool would then have certified as covered
exactly the case the brief named as the example of the problem.

**Put the FO groups behind `--include-constructed` to keep the default index
cheap.** Rejected: `FO.*` is the largest single blind spot and it is
first-order LOGIC, which is not "constructed" in the sense that flag means
(reals and the spaces built on them). A lane asking about `FO.Provable` would
then get UNANSWERABLE by default and would have to know to pass a flag named
for something else. The per-group `timing:` line exists so this can be revisited
against numbers.

## References

* `crates/axeyum-lean-kernel/examples/shape_search.rs`
* `crates/axeyum-lean-kernel/tests/shape_search_index_coverage.rs`
* `scripts/audit-kernel-tool-prelude-coverage.py`
* [Finding Existing Lemmas](../../contributor-guide/finding-existing-lemmas.md)
* [Measurement Hazards](../../contributor-guide/measurement-hazards.md)
* [Evidence and Checker Discipline](../../contributor-guide/evidence-and-checker-discipline.md)
* [ADR-0464](adr-0464-prelude-reuse-is-a-cloned-template-not-a-snapshot.md) — the
  process-wide prelude cache, and why it does not make repeated builds free
  inside ONE kernel.
