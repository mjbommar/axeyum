# ADR-1942: a constructor term as a UF argument — the congruence antecedent is built from the datatype axioms, and the slice it unblocks is the NEXT one

Status: accepted
Index-summary: ADR-1935's residual census put "UF applied to a datatype term that is not a free variable" at **173 of 600** and named the constructor case (`p(mk(a,b))`) as the next slice. Measured before any code (`docs/research/03-measurements/the-constructor-arg-slice-is-10-of-173-files-2026-09-12.md`, committed as `405066971`): that slice reaches **10** of the 173, because 87 of them are blocked by a datatype argument that is another function's RESULT, 75 by a constructor over a datatype whose expansion is not exact, and 67 by a plain variable argument that is inexact. The rung worth **57** of the 173 is the one ADR-1935 refused by name — Ackermannising a datatype-VALUED result — and **52 of those 57 also carry a constructor argument**, so this slice is its prerequisite, not its complement. Decision: `collect_ackermann_groups` admits a constructor application as a datatype argument, and `congruence_arg_eq` builds the antecedent's conjunct from the axioms that make datatypes freely generated — DISTINCTNESS (`c(…) = d(…)` is `false`, and the whole clause is dropped), INJECTIVITY (`c(x) = c(y)` is `⋀ xᵢ = yᵢ`), and the mixed case `c(x) = o` as `is_c(o) ∧ ⋀ xᵢ = sel_{c,i}(o)`, which is `is`/`select` over a free variable and therefore already in the fragment. Measured: **+10 net (AUFDTLIRA 69→71, UFDTLIRA 82→88, UFDT 27→29), 0 losses, 0 flips**, both controls flat, all 10 gains `unsat` under z3, cvc5 and the declared `:status`. Two things are recorded because they were measured and contradicted a draft of this ADR: a soundness-negative test SURVIVED its mutation because its wrong answer was merely *available* rather than forced, and the exactness precondition is again NOT what stands between this path and a wrong `unsat`.
Date: 2026-09-12

## Context

[ADR-1935](adr-1935-the-congruence-precondition-is-exactness-not-scalarity.md)
Ackermannised `f(o)` for a datatype VARIABLE `o` and refused `f(mk(a, b))` by
name, because the congruence antecedent it emits is a plain `Op::Eq` and the
tag/field expansion has no rewrite for an equality over a constructor term. Its
residual census, on its own new arm, put that refusal at the top:

| refusal | files |
|---|---:|
| UF applied to a datatype term that is **not a free variable** | **173** |
| congruence over a datatype argument whose expansion is not exact | 50 |
| a UF whose RESULT sort mentions a datatype | 47 |
| `is`/`select` over a non-variable datatype term | 22 |

and said the constructor case's argument equality "is structurally exact and
cheap". That is true, and it is what §1 below builds. The question this ADR
opens with is the arithmetic one.

## What was measured, before any code

[the-constructor-arg-slice-is-10-of-173-files-2026-09-12.md](../03-measurements/the-constructor-arg-slice-is-10-of-173-files-2026-09-12.md),
committed as **`405066971`** before the implementation commit, from a RUNTIME
census that classifies EVERY datatype-sorted argument of every collected
application rather than stopping at the first refusal:

| of the 173 | AUFDTLIRA | UFDTLIRA | UFDT | total |
|---|---:|---:|---:|---:|
| **reachable by this slice** | **8** | **2** | **0** | **10** |
| blocked by an `Op::Apply` datatype argument | 16 | 22 | 49 | 87 |
| blocked by a constructor over an INEXACT datatype | 17 | 22 | 36 | 75 |
| blocked by a VARIABLE over an inexact datatype | 3 | 15 | 49 | 67 |
| **reachable if a datatype-VALUED result is also Ackermannised** | 21 | 22 | 14 | **57** |
| … of those, also carrying a constructor argument | 19 | 22 | 11 | **52** |

**A blocker census names which refusal fires FIRST; the population a fix reaches
is strictly smaller, because the file must clear every OTHER precondition of the
same pass.** That is ADR-1935's headline lesson, and this is the second time in
one day it has caught a stated "BUILD NEXT". It should now be assumed rather
than rediscovered, and the sizing is therefore committed BEFORE the code so it
cannot be written to match the result.

The measurement is also why this slice ships rather than the bigger one: 52 of
the 57 files the datatype-valued-result capability would reach also apply a
function to a constructor term, so shipping that without this buys **5**.

## Decision

### 1. A constructor application is an admitted datatype argument

`collect_ackermann_groups`' shape check becomes "a free variable **or** a
constructor application", and refuses everything else by a message that names
both admitted shapes — a datatype-sorted `select`, an `ite` over datatypes,
another function's result. The exactness precondition
(`datatype_expansion_is_exact`) is unchanged and still applies to the argument's
datatype.

### 2. The antecedent's conjunct comes from the datatype axioms, not from `Op::Eq`

`congruence_arg_eq` replaces the bare `arena.eq(a, b)` in the congruence loop.
SMT-LIB datatypes are **freely generated**, which is what makes each of these an
equivalence rather than an approximation:

* **distinctness** — `c(x…) = d(y…)` with `c ≠ d` is `false`. No value is built
  by two constructors. The conjunct is not emitted as `false`; the whole clause
  is DROPPED, which is also what keeps the quadratic pair count affordable on
  divisions that apply one accessor to hundreds of records.
* **injectivity** — `c(x₁…xₙ) = c(y₁…yₙ)` is `⋀ᵢ xᵢ = yᵢ`. Exact both ways.
* **the mixed case** — `c(x₁…xₙ) = o` is `is_c(o) ∧ ⋀ᵢ xᵢ = sel_{c,i}(o)`. The
  expansion maps `is_c(o)` to `tag_o = c` and `sel_{c,i}(o)` to `o`'s own field
  variable for that slot, so the conjunction holds iff `o`'s value IS
  `c(x₁…xₙ)`; negated it is `tag_o ≠ c ∨ ⋁ᵢ xᵢ ≠ sel_{c,i}(o)`, which is exactly
  "not that value". The field variables of the OTHER constructors never enter,
  so their being unconstrained cannot weaken it. These are `is`/`select` over a
  free variable — the shapes `scan_fragment` already handles — so this case adds
  no new obligation to the expansion.
* two non-constructors — unchanged: a plain `Op::Eq` the tag/field expansion
  encodes through `build_dt_eq`, whose exactness the precondition already checked.

Exactness of the argument's datatype means no field of it is datatype-sorted, so
a constructor's arguments are never datatype-sorted and the decomposition does
not recurse. That is a consequence rather than an assumption, and it is why the
mixed case's `sel` never lands on a datatype-typed field (which
`unfold_traversals` would turn into an unconstrained child — a relaxation, and
the wrong-`unsat` shape).

### 3. The redundant guard is declared redundant

`reject_datatype_constructor_argument` refuses a datatype-sorted constructor
argument. By §2 it is **unreachable**, and it is not in the mutation suite
because no mutation of it could ever be killed — listing it would make that
control report a survivor forever and imply a coverage it does not have. It
exists so that a future widening of `field_sort_expands` trips over a refusal
rather than silently emitting the relaxed comparison this function exists never
to emit. The alternative to a dead guard here is a live fall-through, which is
worse.

## The measured result

1,000 files, both arms back to back on the same pinned core pair, arm order
alternating per file, 10 s / 8 GiB, twelve modulo-interleaved shards over
`s5`/`s6`/`s7`. Protocol and all 1,000 rows:
[`bench-results/dt-constructor-arg-20260912/ab/`](../../../bench-results/dt-constructor-arg-20260912/README.md).

| division | n | base | new | delta | gain | loss | flip | base wall | new wall |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 200 | 69 | **71** | **+2** | 2 | 0 | 0 | 223 s | 257 s |
| UFDTLIRA | 200 | 82 | **88** | **+6** | 6 | 0 | 0 | 124 s | 124 s |
| UFDT | 200 | 27 | **29** | **+2** | 2 | 0 | 0 | 484 s | 557 s |
| QF_DT *(control)* | 200 | 169 | 169 | 0 | 0 | 0 | 0 | 52 s | 52 s |
| UF *(control)* | 200 | 88 | 88 | 0 | 0 | 0 | 0 | 1,372 s | 1,371 s |

**+10 net, 0 decided→undecided, 0 flips.** The base arm reproduces ADR-1935's
committed new-arm rows exactly (69 / 82 / 27), which is what says the two arms
measure what that A/B measured.

**Soundness — 0 disagreements, three independent checks, on all 10 newly decided
files.** Each was re-run at 24 s against both oracles and its declared status
(`ab/verify-gains.sh`, rows in `ab/verify-gains.tsv`): axeyum `unsat`, z3
`unsat`, cvc5 `unsat`, declared `unsat`, **10 of 10**. Neither arm disagrees
with a declared `:status` anywhere in the 1,000 rows.

**Cost.** `UFDTLIRA` is free (124 s → 124 s) and takes the largest share of the
gain. `AUFDTLIRA` pays +15 % and `UFDT` +15 % for two files each — a query that
used to end at the shape refusal now runs further down the twenty-rung ladder.
Both controls moved within noise (0.4 s of 52 s; 1 s of 1,372 s), so the cost is
confined to the divisions this change touches. This is the same trade ADR-1927
and ADR-1935 recorded and is to be quoted with the gains, not separately.

*One caveat on the wall figures specifically:* another lane's benchmark process
was running on `s7` at 100 % of one core throughout, which the per-file
interleave with alternating arm order cancels in the DIFFERENCE (0 losses, 0
flips) but which inflates both arms' absolute wall numbers on that host's four
shards. The verdict columns are unaffected; the seconds are not a clean
machine-to-machine comparison.

## What the mutation run found that this ADR's draft had wrong

`scripts/tests/mutation_controls.py`, suite `dt-constructor-arg-1942`: six
mutations, one per conjunct-producing step, **all six killed, each killing
exactly one test**. Two of the findings on the way there are recorded because
they contradicted a draft of this document.

**A soundness-negative test SURVIVED, and the reason generalises.**
`sound_the_mixed_case_needs_the_tester` was `is-none(o) /\ p(o) /\ not
p(some(1))`. Delete the `is_c(o)` conjunct and the antecedent becomes
`1 = v(o)` over a field variable nothing constrains — so the search simply chose
`v(o) != 1`, the query stayed `sat`, and the guard read as untested. The fix is
one more assertion, `v(o) = 1`, which FORCES the antecedent. The rule this
teaches, and it applies to every `sound_*` test in the datatype suites: **a
soundness-negative test has to make the wrong answer forced, not merely
available.** An unconstrained variable in the antecedent gives the search a free
escape and the mutant survives.

**The exactness precondition is again NOT what stands between this path and a
wrong `unsat`.** Deleting it kills only
`refusal_names_the_inexact_expansion_for_a_constructor_argument`, not
`sound_a_constructor_over_an_inexact_datatype_is_not_merged_at_depth_two` — and
this ADR's draft asserted the opposite, with an argument about depth-2 child
variables that is wrong for the same reason the test above survived. ADR-1930's
relaxed equality encoding is a FREE Boolean carrying only necessary conditions;
a search looking for a model sets it FALSE, because a true antecedent would
force the two witnesses together and contradict `p` / `not p`. The antecedent is
never *forced* true, so the clause degenerates to vacuous rather than to a wrong
answer. That is ADR-1935's finding on the variable path, reproduced verbatim on
the constructor path.

So what the precondition buys, stated without inflation: every antecedent this
pass emits provably IS real equality, which is what makes §2's equivalences
reviewable; the census-readable refusal message, which by ADR-1920 decision 2 is
the product; and insurance against a change to ADR-1930's encoding. It is not
today's soundness. Today's soundness on this path is ADR-1930's encoding and the
replay, plus the four axiom-decomposition guards above, which ARE load-bearing
and each kill a test.

## Consequences

### What is now possible

- `p(mk(a, b))` decides. So does the mixed `p(o)` / `p(mk(a, b))` pair, which is
  the shape a SPARK verification condition produces when a record literal meets a
  record variable.
- Ten more files across the three divisions, all `unsat`, all three-way
  oracle-confirmed.

### What is still refused, with the measured residual census on the new arm

Taken over the three target divisions, undecided files only:

| refusal | files (was) |
|---|---:|
| congruence over a datatype argument whose expansion is not exact | 98 (50) |
| UF applied to a datatype term that is neither variable nor constructor | 72 (173) |
| a UF whose RESULT sort mentions a datatype | 51 (47) |
| `is`/`select` over a non-variable datatype term | 48 (22) |
| e-matching instantiation did not refute within the round budget | 40 (39) |

The top row moving 173 → 72 while three others GREW is the ladder doing its job:
a file that used to stop at the shape refusal now proceeds and stops at the next
precondition. Read the table the way ADR-1927 says — it names which refusal fires
first, not how many files a fix would win — and pair it with the sizing note,
which is what turns one into the other.

**The next capability is named by measurement, not by symmetry: Ackermannise a
datatype-VALUED UF result into a fresh datatype VARIABLE.** ADR-1935 refused it
on the grounds that "its witness would itself be a datatype-sorted term, which
the tag/field expansion would have to pick up in a scan that has already run" —
but `ackermannize_datatype_applications` runs BEFORE `scan_fragment`, so the
witness would be scanned like any other datatype variable, and that objection
does not survive the current pipeline order. The sizing puts it at 57 of the 173
with this slice already in place, and 5 without.

### What this ADR does not claim

- It does not claim the sizing predicted the gains. It did not: the strict
  per-file predicate named 11 files and 3 of them gained, while all 10 gains lie
  inside the loose predicate's 65. The measurement note carries that correction
  and why the strict form is wrong for a quantified division; the honest bracket
  was [3, 65] and the answer was 10.
- It does not claim the 302 files whose UF parameter datatype has a
  datatype-typed field are any closer. They need exact recursive equality and
  that is still a third capability.
- The 600 are three stride-pinned 200-file samples, not the divisions, and
  nothing here is parity: the references decide 176 / 181 / 78 on these lists at
  24 s.

## Evidence

- `crates/axeyum-solver/tests/dt_constructor_arg_1942.rs` — 11 tests. Four
  `congruence_*` positive controls that must decide `unsat` (without them a route
  that refused everything would satisfy every soundness test), five `sound_*`
  that assert the absence of a wrong `unsat` on a query both oracles call `sat`,
  and two `refusal_*` that pin the census-readable messages.
- `scripts/tests/mutation_controls.py`, suite `dt-constructor-arg-1942` — six
  mutations, all six killed, each killing exactly one test. The suite
  `dt-capability-1935` still passes with its shape-check anchor updated to the
  widened arm.
- Every fixture's expected verdict was checked against `z3` and `cvc5` before it
  was written down, not after it passed.
- [`bench-results/dt-constructor-arg-20260912/`](../../../bench-results/dt-constructor-arg-20260912/README.md)
  — the sizing census and its rows, the A/B protocol and all 1,000 per-file rows,
  the oracle re-validation of all 10 gains, and the scripts for both.
- Three suites this change overtook were replaced rather than deleted, each with
  a line saying why: `unknown_reason_coverage`'s dispatch-error fixture (for the
  THIRD time in two days, and this replacement is the rung the sizing MEASURED as
  next), and `dt_capability_1935`'s `refusal_names_the_non_variable_datatype_argument`,
  retargeted to the shape the same arm still refuses.
