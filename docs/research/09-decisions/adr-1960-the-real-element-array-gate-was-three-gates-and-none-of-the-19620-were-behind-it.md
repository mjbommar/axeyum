# ADR-1960: the Real-element array gate was three gates, and none of the 19,620 were behind it

Status: accepted
Index-summary: `scalar_alia_auflia_arrays_supported`'s `!features.has_real` was stale conservatism — born in an unexplained checkpoint commit, never argued for in any ADR or comment, over a CEGAR engine that is element-sort-agnostic and a scalar backend that has had exact-rational simplex all along — and it was never the binding gate. Two EARLIER returns in `check_auto` terminate a Real query before the array ladder is reached at all, so ADR-1955's attribution was to a predicate that was never consulted. Two of the three are lifted (the third's mutation SURVIVED and three purpose-built probes are all decided earlier, so it is documented rather than changed on speculation) and a flat `(Array Int Real)` read-over-write now decides, agreeing with z3 and cvc5 on every probe. The corpus value is **zero files**: censusing all 29,564 files of the divisions ADR-1955 named finds **0** whose only refusal is the Real clause, because those files are the SAME files as the 27,150 behind the parse refusal (ADR-1945's sequential-caps rule, applied to its own successor) and the ones that do parse contain no array at all.
Index-status: accepted
Date: 2026-09-13

## Context

[ADR-1955](adr-1955-the-nested-array-sort-is-the-first-of-three-gates-and-the-only-one-the-ir-owns.md)
closed with a chain and an instruction:

```
parse refusal            27,150 files    IR   — that ADR's design
  +  nested select base   7,530 files    solver — abv.rs:2735, incremental.rs:6014
  +  Real-element arrays 19,620 files    solver — auto.rs:6098
```

> and the third line is the one worth noticing: **it is the larger prize, it is
> not blocked by the IR at all, and a flat array demonstrates it in one query.**
> A lane can attack `!features.has_real` today without touching `Sort`.

and its Consequences: *"The next lane on this file is pointed at
`auto.rs:6098`, not `sort.rs`."* This ADR is that lane. Two questions had to be
answered in order, and the second one changed the answer to the first.

## 1. Why the guard exists: it does not, in any written sense

`scalar_alia_auflia_arrays_supported` appeared with the ALIA/AUFLIA lazy-ROW
route itself, in `c093fa9111ba658b66c4f2f4c79a67d5c05b7737` (2026-06-25). That
commit's **entire** message is:

```
feat(solver): checkpoint dominance audit and ABV array certs
```

over a 100-plus-file diff. The `!features.has_real` clause is in the first line
of the function's existence, with no comment attached, and `git blame` shows it
was never edited afterwards; `0ed0c7990` appended `&& !features.has_datatype` a
day later and left it alone. `git log -S'check_qf_alia_lazy_row'` returns
exactly that one commit: the route and its Real exclusion were born together
inside an unexplained checkpoint.

No ADR argues for it. ADR-0010 (array elimination) does not contain the word
"Real". ADR-0030 and ADR-0072 do not. [ADR-1814](adr-1814-staged-eager-lazy-arrays.md)
lists `has_real` among the **route-selector** flags, not among evidence or
soundness gates. [ADR-0079](adr-0079-finite-scalar-array-admission.md) is the
closest thing to a deliberate exclusion and it is about a different route
(`has_non_bool_bv_array`, the canonical CDCL(T) bus) and rejects `Int` in the
same breath — and `Int` arrays are of course fully decided.

Three measurements say it is stale rather than load-bearing:

* **The scalar backend behind it is not integer-only.** `check_qf_alia_lazy_row`
  runs `ArithDpllBackend` → `crate::dpll_lia::check_with_arith_dpll`, documented
  in its own header as *"integer, real, or combined `QF_LIRA`"* over the
  exact-rational simplices. It is the same function the dispatcher calls as
  `lira-dpll`. The doc comment on `check_qf_alia_lazy_row` already said
  "linear-**arithmetic**/Bool elements" and "the arithmetic DPLL(T) backend" —
  the comment was broader than the guard.
* **The CEGAR engine is element-sort-agnostic.** `RowCtx::resolve_select` reads
  `element_sort` out of `Sort::array_sorts()` and declares a fresh symbol at
  that sort; nothing in it branches on `Int`. The `Sort::Int` hard-codings in
  `abv.rs` are all in the separate affine-index certified refuters, which run
  earlier and are gated independently.
* **The soundness argument does not mention element sorts, because it does not
  depend on one.** From the commit that built the ROW CEGAR (`3c816b42d`): the
  bare abstraction is a RELAXATION so its `unsat` transfers to the original, and
  every `sat` candidate is projected back to array variables and REPLAYED
  against the ORIGINAL assertions. Both halves are sort-uniform, and the ground
  evaluator has a `Sort::Real` case.

**Finding: conservatism that outlived its cause.** The guard is lifted.

## 2. It was never the binding gate

ADR-1955's probe `p5-row-real.smt2` is a flat `(Array Int Real)` read-over-write
at distinct symbolic indices. Its route trail at `57bd22d37` ends:

```
lira-dpll      declined (unsupported)
nra-real-root  declined (not-applicable)
nra            declined (unsupported: QF_LRA: non-linear or non-real subterm …)
fd:string-gate declined …                        ← and then only the front-door rungs
```

**`array-fast-path` is never recorded.** `scalar_alia_auflia_arrays_supported`
was not consulted for this query or any query like it. The real chain is three
sequential gates in `check_auto`, and ADR-1955 found only the last:

| # | site | who it stops | how it stops them |
|---|---|---|---|
| 1 | the pure-real branch, `Err(SolverError::Unsupported)` arm after `check_with_nra` | a Real array query with **no** UF | `return Ok(Unknown("nonlinear real route declined: …"))` — the array ladder is below it |
| 2 | `dispatch_uf_routes`, `CheckResult::Unknown(reason) if features.has_real` | a Real array query **with** UF | `return Ok(Some(Unknown))` — same effect, different rung |
| 3 | `scalar_alia_auflia_arrays_supported` | whatever reaches the ladder | `!features.has_real` |

Gates 1 and 2 are the same mistake made twice: a route that owns *arithmetic*
refuses an *array* subterm, and its refusal is returned as the query's verdict
rather than as a decline. That is precisely the shape
[ADR-1927](adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md)
named — *a ladder rung's fragment refusal is a decline, not the query's
verdict* — recurring in a branch ADR-1927 did not reach.

**Gate 2 is identified and deliberately NOT changed.** Relaxing it the same way
compiles, passes, and reaches nothing: its mutation control **SURVIVED** — nine
tests ran and none depended on it — and three probes built specifically to reach
that rung (`probes/r1`, `r6`, `r7`: UF + Real + array in read-over-write,
extensionality, and UF-applied-index shapes) are each decided earlier, two by
`uf-arithmetic` and one by `lia-dpll`. A change nobody can demonstrate is
decoration, and this one would have altered route order for a live population on
speculation. It carries a comment naming the three probes instead, so the next
lane does not have to rediscover either the gate or the fact that it is
unreachable today.

The fall-through at gate 1 is bounded rather than open: it fires only when
`features.has_non_bv_array`, which is exactly the population the array branch
terminates **itself**, at its own `non-bit-vector array sorts are represented in
IR` `Unknown`. So a Real query can never fall past it into
`check_with_all_theories`, which hard-errors on `Sort::Real`.

## 3. What it is worth: zero files, measured before the code

`crates/axeyum-smtlib/examples/array_real_gate_census.rs` classifies a file by
what the dispatcher's own predicate would do with it, and reports
`real_gate_only` — a non-bit-vector array query refused **on the `has_real`
clause and nothing else**. Over whole divisions, not a sample
([`bench-results/array-real-gate-20260913/`](../../../bench-results/array-real-gate-20260913/README.md)):

| division | files | parse_err | no_array | pass_today | blocked (other) | **real_gate_only** |
|---|---:|---:|---:|---:|---:|---:|
| AUFLIRA | 20,011 | 18,644 | 1,367 | 0 | 0 | **0** |
| AUFNIRA | 1,480 | 976 | 504 | 0 | 0 | **0** |
| AUFDTLIRA | 11,043 | 488 | 0 | 33 | 10,522 | **0** |
| AUFDTNIRA | 1,567 | 83 | 0 | 0 | 1,484 | **0** |
| AUFFPDTNIRA | 166 | 16 | 0 | 0 | 150 | **0** |
| ABVFPLRA | 77 | 77 | 0 | 0 | 0 | **0** |
| QF_ABVFPLRA | 74 | 40 | 0 | 0 | 34 | **0** |
| ALIA (control) | 3,098 | 3,028 | 0 | 70 | 0 | **0** |
| QF_ALIA (control) | 176 | 50 | 0 | 126 | 0 | **0** |

**ADR-1955's 19,620 and its 27,150 are the same files.** They are behind the
parse refusal *and* would be behind the Real gate; the two numbers are one
population counted once per gate. [ADR-1945](adr-1945-a-blocked-count-is-not-a-reachable-count-and-two-sequential-caps-are-not-two-caps.md)
is the rule and its own successor broke it: **two sequential caps are not two
caps**, and removing the second while the first stands decides nothing. ADR-1955
said exactly this about the IR change ("necessary for all 27,150 and sufficient
for none") and did not say it about the gate it pointed the next lane at.

The second half is worse for the estimate. Of AUFLIRA's 1,367 and AUFNIRA's 504
files that DO parse, **not one contains an array** — they are the
`why`/`FFT`/`aviation` families, and `grep -c Array` over them is 0. There was
never a control population for the Real array gate in those divisions because
there was no population at all.

The classifier is not trivially zero. On the probe set it returns
`real_gate_only` for the Real shapes and `pass_today` for their Int twins, and
the two no-Real control divisions reach 0 through the *other* bucket.
`census-all-array.sh` repeats the sweep over all 28 array-carrying divisions.

## 4. Soundness

The added reach is entirely through the existing lazy ROW/extensionality CEGAR,
whose two-sided argument is unchanged and sort-uniform: `unsat` transfers from a
relaxation, `sat` is projected and replayed against the originals. The
`QF_AUFLIA` arm additionally downgrades its own `Unsat` to `Unknown` at the
adapter boundary (no independently checked proof), so nothing new can export an
`unsat` from that branch.

`crates/axeyum-solver/tests/real_element_array_row.rs` is the fence, and five of
its nine tests are adversarial fixtures over **satisfiable** queries whose
plausible wrong answer is `unsat`:

* `a_strictly_fractional_read_is_satisfiable_over_reals` — `0 < m[i] < 1`, which
  is satisfiable over `Real` and **unsatisfiable over `Int`**. This is the one
  test that dies if anything on the newly reachable route integralizes the
  element sort. Its Int twin,
  `a_strictly_fractional_read_is_unsatisfiable_over_ints`, is in the same file so
  the pair cannot be read as a solver that answers `sat` to everything.
* `an_unconstrained_index_pair_does_not_force_the_read_to_agree` — dies if the
  read-over-write case split is lost.
* `distinct_indices_may_read_different_reals` — dies if the abstraction
  Ackermannizes without the index guard.

Every `Sat` in that suite is replayed against the **original** assertions inside
the test, not trusted from the route, because the route's own replay is part of
the subject.

`tests/nested_array_gate_map.rs`'s `flat_real_element_array_row_is_undecided`
fired its own "GOOD NEWS, STALE ARITHMETIC" panic, as designed. It is now
`flat_real_element_array_row_decides` with the regression message pointing back
here — kept rather than deleted, because the `Int`/`Real` pair is what carries
the meaning and a future divergence is the same finding in the other direction.

## Decision

1. **Lift gates 1 and 3, and leave gate 2 documented in place.** Gate 1 falls
   through when `features.has_non_bv_array`; gate 3 loses its
   `!features.has_real` clause; gate 2's mutation survived and its three probes
   are decided elsewhere, so it is named rather than changed.
2. **Do not claim a file count.** The corpus value of this change measured
   today is zero files, and the reason is ADR-1945's rule, not a defect in this
   change. The capability is real and pinned by probes and tests; the population
   is not reachable until the nested-array sort lands.
3. **ADR-1955's chain arithmetic is superseded.** The third line of its chain is
   not an independent 19,620-file prize; it is the same population as the first
   line, and the honest reading of that chain is one number (27,150 blocked,
   ~1,135 reachable) with three gates in front of it, not three numbers.

## Consequences

* The next lane on this file is back at `sort.rs` — the interned array-sort id
  of ADR-1955's Option B — because that is now the **only** thing between the
  27,150 and a verdict for the ALIA/ABV half, and one of two for the AUFLIRA
  half (the other being the nested `select` base in `RowCtx::resolve_select`).
* A route that answers an arithmetic question must not return its own fragment
  refusal as the query's verdict when a later route owns the construct it
  refused. ADR-1927 established this for the ladder rungs it audited; gates 1
  and 2 are the same defect in the real branch, and the audit was not
  exhaustive. Searching for the remaining instances — an `Err(Unsupported)` arm
  that `return`s rather than declining — is worth a lane of its own.
* A census whose numerator is a *gate* and whose denominator is a *blocked
  count* will keep producing phantom prizes. The instrument that does not is the
  one in this lane: classify each file by what the dispatcher's **own predicate**
  would do with it, and report the bucket that names one gate and no other.
