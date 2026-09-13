# ADR-1946: a datatype-VALUED uninterpreted-function result — the witness IS a variable, and the scan has not run yet

Status: accepted
Index-summary: ADR-1935 refused this rung by name, arguing the Ackermann witness "would itself be a datatype-sorted term, which the tag/field expansion would have to pick up in a scan that has already run". Measured: `ackermannize_datatype_applications` runs BEFORE `scan_fragment`, so the witness is an ordinary free datatype variable by the time the scan walks the rewritten assertions, and the objection does not survive the current pipeline order. Decision: an application is an Ackermann site when its ARGUMENT *or* its RESULT is datatype-sorted; the result datatype must be exact (the congruence consequent is then a datatype equality) and an array-over-a-datatype result is refused by a separate message; an `Op::Apply` datatype ARGUMENT is admitted *because this pass replaces it*, checked by membership in the collected set rather than inferred from the operator; and `ack_sites` is sorted by `TermId` so a nested site is rebuilt before the site that reads it. Sized BEFORE the code (`0c96ac73e`): the inherited "57 of the 173" was the previous arm's `all()` figure over a population that no longer exists, and the honest bracket on THIS arm was [0, 52] newly-eligible with a point estimate of "low teens" plus one unquantified addition. Measured: **+35 net (AUFDTLIRA 71→90, UFDTLIRA 88→102, UFDT 29→31), 0 losses, 0 flips**, both controls flat, 34 of 35 gains three-way `unsat` (axeyum / z3 / cvc5 / declared) and the 35th confirmed by cvc5 on a file z3 times out on and SMT-LIB declares `unknown`. The point estimate was WRONG and the mechanism written down before the A/B is why: **28 of the 35 gains came from the `is`/`select`-over-a-non-variable bucket**, which no pre-pass predicate can see. Cost: the wall increase is 43 files that used to stop at a refusal in milliseconds and now spend the whole budget without gaining, not a uniform slowdown.
Index-status: accepted
Date: 2026-09-12

## Context

[ADR-1935](adr-1935-the-congruence-precondition-is-exactness-not-scalarity.md)
Ackermannised `f(o)` for a datatype VARIABLE and refused a datatype-VALUED
result by name:

> an uninterpreted function whose RESULT sort mentions a datatype (its Ackermann
> witness would itself be a datatype-sorted term)

with the reasoning that such a witness "would have to be picked up by a scan that
has already run".
[ADR-1942](adr-1942-a-constructor-term-as-a-uf-argument.md) checked that claim
against the pipeline and closed by saying it does not survive. This ADR is that
rung, and the first thing it does is verify the objection is really stale rather
than inherit the verdict — a doc that records obstacles accumulates stale ones by
construction.

**It is stale.** `decide_with_eq_mode` calls, in order:

1. `abstract_wrong_ctor_selects`
2. **`ackermannize_datatype_applications`**  ← the witness is declared here
3. `expand_datatype_equalities`
4. `unfold_traversals`
5. **`scan_fragment`**  ← the scan ADR-1935 meant

so a witness declared at step 2 is an ordinary free datatype variable when step 5
walks the rewritten assertions, and `build_sym_vars` gives it a tag and field
variables like any other. There is no extra obligation; there is one extra
precondition (§1.2 below), which is not the same thing.

## What was measured, before any code

[the-datatype-valued-result-rung-priced-on-its-own-arm-2026-09-12.md](../03-measurements/the-datatype-valued-result-rung-priced-on-its-own-arm-2026-09-12.md),
committed as **`0c96ac73e`** before the implementation commit.

**The inherited number was not reusable, and saying why matters more than the
number.** ADR-1942 §4 priced this rung at "57 of the 173". That is correct about
ADR-1942's own arm and wrong about this one, three ways: ADR-1942 shipped, so the
173-file population the 57 was a fraction of is now **72**; the predicate behind
it is the `all(route entries eligible)` one ADR-1942's own §7 retracted as a bound
for a quantified division; and this change is wider than its name, because making
a datatype-valued result usable requires admitting an `Op::Apply` term as a
datatype ARGUMENT as well.

Re-measured on the arm this ships against (600 files, runtime census classifying
every candidate per route entry, 12 shards over `s5`/`s6`/`s7`), over the **412
undecided** files:

| | AUFDTLIRA | UFDTLIRA | UFDT | total |
|---|---:|---:|---:|---:|
| **ADR-1946 eligible, ANY route entry** | 85 | 46 | 89 | **220** |
| ADR-1946 eligible, EVERY route entry | 67 | 28 | 22 | 117 |
| the arm as it stands, ANY route entry | 57 | 30 | 81 | 168 |
| **newly eligible under the ANY predicate** | 28 | 16 | 8 | **52** |

The census's base verdicts are 71 / 88 / 29 = 188 decided, which reproduces
ADR-1942's A/B new-arm rows exactly — the check that the two measurements are of
the same tree.

**The sizing committed: a bracket of [0, 52], point estimate "low teens",
plus one unquantified addition stated so the A/B could refute it** — that 48
files refuse first at `is`/`select` over a NON-VARIABLE datatype term, a refusal
that fires in `scan_fragment` where no pre-pass predicate can see it, and that in
many of them the offending operand is a UF result which this rung turns into a
variable.

The census also carries the term ADR-1942's rows structurally could not: the
congruence pair count under the WIDENED site set. Those applications were never
collected under the old rule, so their pairs were never counted, and the
widening's cost at `MAX_ACK_PAIRS` could not be read off them at all.

## Decision

### 1.1 An application is a site if its ARGUMENT *or* its RESULT is datatype-sorted

`collect_ackermann_groups`' collection predicate gains
`|| matches!(result, Sort::Datatype(_))`. Everything downstream already works:
the witness is declared at the result sort, `replace_subterms` rewrites every
occurrence of the application to it in the assertions AND in the congruence
antecedents, and the scan sees a variable.

A result sort that merely MENTIONS a datatype without being one — an array over
a datatype — is deliberately not collected, and is refused by its own message if
such a function is collected for its arguments instead. Its witness would be
array-sorted and the tag/field expansion cannot reach into the elements.

### 1.2 The result datatype's expansion must be EXACT

The congruence consequent `wₚ = w_q` is, for a datatype-valued result, a
DATATYPE equality. So the same precondition the arguments carry applies to the
result, and for the mirror-image reason: an antecedent weaker than real equality
makes the clause stronger than the axiom, and a consequent stronger than real
equality does the same. Under `EqMode::Restriction` — the arm whose encoding is
deliberately stronger — that is exactly the shape ADR-1930 measured a wrong
`unsat` from.

This keeps the whole pass's invariant statable in one sentence: **every datatype
this pass introduces or compares is exactly encoded.** §"What the mutation run
found" records what it is and is not buying today.

### 1.3 An `Op::Apply` datatype ARGUMENT is admitted because it is REPLACED

The shape check's third admitted shape is not "an `Op::Apply`" but "a term this
call will replace by a witness", looked up in the set of collected sites:

```rust
let collected: BTreeSet<TermId> = groups.values().flatten().copied().collect();
…
if !matches!(arena.node(arg), TermNode::Symbol(_))
    && construct_of(arena, arg).is_none()
    && !collected.contains(&arg)
```

The two formulations are extensionally equal today — a datatype-sorted
`Op::Apply` has a `Sort::Datatype` result and is therefore always collected — and
the membership form is the one that stays correct if the collection rule ever
narrows. It is also what makes `congruence_arg_eq` still total on exactly the
admitted shapes: the third shape is not a fourth case there, because
`replace_subterms` has turned it into the first before anything downstream reads
it.

The refusal message names all three shapes, because the DT blocker census is read
off exactly these strings (ADR-1920 decision 2).

### 1.4 `ack_sites` is sorted by `TermId`, across functions

`register_ack_interpretations` rebuilds each Ackermannised function by
EVALUATING its sites' argument terms, so a nested site must be rebuilt before the
site that reads it. `groups` is keyed by `FuncId`, which is declaration order, so
the push order interleaves parents and children arbitrarily. `TermId` order is
bottom-up in a hash-consed arena, so one stable sort fixes it.

With a datatype-valued result this is the COMMON shape rather than an edge case —
`p(g(a))` collects both `g(a)` and `p(g(a))` — which is why a latent ordering
weakness in ADR-1935's code becomes load-bearing here. Getting it wrong costs a
`sat` (the replay rejects a candidate that is not actually wrong, and an
Ackermann-expanded query is already flagged relaxed, so the result is `unknown`),
never soundness. It is mutation-covered.

## The measured result

1,000 files, both arms back to back on the same pinned core pair, arm order
alternating per file, 10 s / 8 GiB, twelve modulo-interleaved shards over
`s5`/`s6`/`s7`. Protocol and all 1,000 rows:
[`bench-results/dt-valued-result-20260912/ab/`](../../../bench-results/dt-valued-result-20260912/README.md).

| division | n | base | new | delta | gain | loss | flip | base wall | new wall |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 200 | 71 | **90** | **+19** | 19 | 0 | 0 | 257 s | 497 s |
| UFDTLIRA | 200 | 88 | **102** | **+14** | 14 | 0 | 0 | 123 s | 153 s |
| UFDT | 200 | 29 | **31** | **+2** | 2 | 0 | 0 | 553 s | 702 s |
| QF_DT *(control)* | 200 | 169 | 169 | 0 | 0 | 0 | 0 | 52.3 s | 52.1 s |
| UF *(control)* | 200 | 87 | 87 | 0 | 0 | 0 | 0 | 1,389 s | 1,386 s |

**+35 net, 0 decided→undecided, 0 flips.** The base arm reproduces ADR-1942's
committed new-arm rows exactly (71 / 88 / 29) and its `QF_DT` control (169),
which is what says the two arms measure what that A/B measured. `UF`'s base is 87
here against ADR-1942's 88; one file aborts (`RC134-ABORT`) on BOTH arms in this
run, so the difference is that file, not the change.

**Soundness — 0 disagreements, on all 35 newly decided files.** Each was re-run
at 24 s against both oracles and its declared status
(`ab/verify-gains.sh`, rows in `ab/verify-gains.tsv`):

* **34 of 35**: axeyum `unsat`, z3 `unsat`, cvc5 `unsat`, declared `unsat`.
* **1 of 35** (`UFDT/…/afp/lmirror/x2015_09_10_16_47_59_926_1084806`): axeyum
  `unsat`, cvc5 `unsat`, declared `:status unknown`, and **z3 times out** (it
  prints `timeout` at 40 s, re-checked). So there is no disagreement here either
  — one independent oracle confirms it, SMT-LIB does not claim otherwise, and it
  is a file we decide that z3 does not. That is stated as what it is and not
  inflated: one file, one reference, one sample list.

Neither arm disagrees with a declared `:status` anywhere in the 1,000 rows.

### The cost, diagnosed rather than quoted

An aggregate "+93 % on AUFDTLIRA" is compatible with every file slowing a little
and with a handful running the full budget where they used to refuse instantly.
Those are different findings and only the second is the expected shape of a
capability change, so the delta is split per file (`ab/wall-cost.py`):

| division | Δ on the files that GAINED | Δ on files slower WITHOUT gaining | n | Δ elsewhere |
|---|---:|---:|---:|---:|
| AUFDTLIRA | +14.4 s (19 files) | **+225.7 s** | 24 | +0.1 s |
| UFDT | +2.1 s (2 files) | **+145.9 s** | 16 | +1.6 s |
| UFDTLIRA | +3.9 s (14 files) | +26.8 s | 3 | −0.4 s |
| QF_DT *(control)* | — | 0 | 0 | −0.2 s |
| UF *(control)* | — | 0 | 0 | −2.9 s |

**The whole increase is 43 files that used to stop at the shape or result-sort
refusal in milliseconds and now run the ladder to the end of the 10 s budget
without gaining.** The 35 gains themselves cost 20 s in total. Both controls moved
within noise, so the cost is confined to the divisions this change touches. This
is the same trade ADR-1927, ADR-1935 and ADR-1942 recorded, at a larger scale
because this rung unblocks more files, and it is to be quoted WITH the gains
rather than separately.

*One caveat on the wall figures specifically:* another lane's benchmark was
running on all three boxes for part of the window. The per-file interleave with
alternating arm order cancels it in the DIFFERENCE (0 losses, 0 flips, controls
flat), but the absolute seconds are not a clean machine-to-machine comparison.

## The sizing was scored, and its point estimate was wrong

`bench-results/dt-valued-result-20260912/score-prediction.py` scores the
committed note against the A/B that followed it:

| | |
|---|---:|
| gains | 35 |
| inside the ANY-entry eligibility predicate | **35 of 35** |
| inside the EVERY-entry predicate | 34 of 35 |
| newly ANY-eligible (the "52") | 29 of 35 |
| predicted point estimate | "low teens" |

**The bracket held and the point estimate did not**, and the reason is the
paragraph the note wrote down specifically so the A/B could refute it. The
base-arm bucket each gain came from:

| bucket the gain's file was in | gains |
|---|---:|
| **`is`/`select` over a non-variable datatype term** | **28** |
| a UF whose RESULT sort mentions a datatype | 5 |
| a UF applied to a datatype term that is neither variable nor constructor | 2 |

So **only 5 of the 35 gains came from the refusal this rung is named after**, and
28 came from a downstream refusal in `scan_fragment` that the pre-pass predicate
structurally cannot see: `is_c(g(a))` was not collected under the narrow rule, so
no Ackermann refusal fired at all and the scan was the first thing to object.
That mechanism was the note's "unquantified addition… it may be the larger half".
It was.

**The rule to carry forward, which is a new one rather than a restatement.**
ADR-1927, ADR-1935 and ADR-1942 all taught *a blocker census over-counts what a
fix reaches*. This rung is the first in the series where the fix reached a
DIFFERENT refusal than the one it was named for, and by 5.6×. A pre-pass
eligibility predicate prices the pre-pass; it cannot price the rungs the pre-pass
unblocks downstream, and the honest form is therefore the bracket PLUS a written
argument about the downstream effect — committed before the A/B, so it can be
scored instead of remembered.

## What the mutation run found, rather than what this ADR's draft claimed

`scripts/tests/mutation_controls.py`, suite `dt-valued-result-1946`: **five
mutations, all five killed**, baseline 12 tests green.

| mutation | killed |
|---|---|
| a datatype-VALUED result makes an application a site | **5** tests |
| the RESULT datatype's expansion must be exact | 1 |
| an array-over-a-datatype result is refused rather than fallen through | 1 |
| a datatype argument is admitted only when this pass will replace it | 1 |
| the nested site is rebuilt before the site that reads it | 1 |

Three results are recorded because they are findings rather than confirmations.

**The RESULT-side exactness precondition kills only its refusal-message test.**
`sound_an_inexact_result_datatype_is_not_merged_at_depth_two` SURVIVES its
deletion. This is the third time in this family an exactness precondition has
measured as not-today's-soundness-boundary, and by now the reason should be
assumed rather than rediscovered: an `unsat` is only ever returned from the
`EqMode::Relaxation` arm (`check_with_datatype_native` takes only a `Sat` from
the restriction arm), and that arm's datatype equality is a free Boolean carrying
necessary conditions only — so a search looking for a model sets the antecedent
FALSE and the clause degenerates to vacuous rather than to a wrong answer. Stated
without inflation, what the precondition buys is: the equisatisfiability argument
in §1.2 is reviewable, the census-readable message exists, and a change to
ADR-1930's encoding trips over a refusal rather than silently producing the
comparison this pass must never emit. **It is not today's soundness.** Today's
soundness on this path is ADR-1930's encoding, the replay, and the argument-side
axiom decomposition ADR-1942 mutation-covered.

**The `collected.contains` guard also kills only its refusal test**, not a
soundness test. Admitting arbitrary argument shapes does not produce a wrong
answer on the fixtures here, because the shapes it would let through
(`DtSelect`, `ite`) are refused by `scan_fragment` a moment later. So that guard's
value is the census-readable message and the invariant, not a wrong `unsat` it
prevents, and it is recorded that way rather than as a soundness control.

**The ordering fix IS load-bearing and is mutation-covered.** Replacing
`sort_by_key(|s| s.site)` with `sort_by_key(|s| s.func)` reproduces the
pre-ADR-1946 order exactly (the sort is stable and `groups` is keyed by `FuncId`)
and kills `a_nested_application_replays_its_model` — a `sat` that becomes
`unknown`. The test declares `p` BEFORE `g` on purpose: with the declaration order
reversed the `FuncId` order already happens to be right and the sort is a no-op,
so a test written the other way round would have passed with the fix removed.
That is the same class as ADR-1942's surviving mutant — a guard that reads as
tested — caught before rather than after.

**One anchor in another suite had to grow.** ADR-1942's
"congruence needs an EXACT expansion" mutation anchored on
`if !datatype_expansion_is_exact(arena, dt) {`, which this change makes AMBIGUOUS
by adding a second exactness check at the same indentation. The harness would have
reported `AMBIGUOUS ANCHOR`, which is not a result and not a kill, so the anchor
now includes the preceding `let Sort::Datatype(dt) = arena.sort_of(arg)` lines.
Re-run after the change: all six of ADR-1942's mutations still killed, each
exactly one test.

## Consequences

### What is now possible

- `p(g(a))` decides, and so does `is_c(g(a))` / `sel_{c,i}(g(a))` — which is
  where 28 of the 35 gains came from.
- `g(0) = mk(1, 2)` relates a UF result to a constructor term through
  `construct_eq_term`, a path that previously only variables reached.
- 35 more files across the three divisions, all `unsat`, 34 three-way
  oracle-confirmed and the 35th confirmed by cvc5 where z3 times out.

### What is still refused, with the residual census

Among the 412 undecided files of the base census, counting each blocker wherever
it appears rather than only where it fires first:

| | AUFDTLIRA | UFDTLIRA | UFDT | total |
|---|---:|---:|---:|---:|
| a VARIABLE argument over an inexact datatype | 16 | 34 | 102 | 152 |
| an INEXACT datatype-valued RESULT | 18 | 26 | 103 | 147 |
| a CONSTRUCTOR argument over an inexact datatype | 21 | 36 | 66 | 123 |
| an `Op::Apply` argument over an INEXACT datatype | 12 | 12 | 47 | 71 |
| some other term shape | 6 | 15 | 13 | 34 |
| an ARRAY-over-datatype RESULT | 0 | 0 | 0 | **0** |

Every large row is one thing: **a datatype with a datatype-typed field**. That is
ADR-1935's third capability — exact RECURSIVE equality, by bounded unfolding with
a depth certificate or a native datatype theory with congruence and acyclicity —
and it is not a slice of this one. It is where the DT divisions' remaining mass
is, and **the next lane must size it on its own arm rather than inherit a number
from here**, which is the mistake this ADR opened by correcting.

The zero row earns its line. The array-over-a-datatype result, which §1.1 refuses
by name, occurs in none of the 600. The guard is reachable and mutation-covered —
a test reaches it — but "a test reaches it" and "the corpus contains it" are
different facts and are reported separately rather than one being quoted as the
other.

### What this ADR does not claim

- It does not claim the sizing predicted the gains. It did not: the point
  estimate was "low teens" and the answer was 35. What it predicted correctly was
  the BRACKET (35 of 35 gains inside the ANY predicate's 220) and the MECHANISM
  (28 of 35 from the `is`/`select` bucket the note named in advance).
- It does not claim the result-sort exactness precondition prevents a wrong
  `unsat` today. The mutation run says it does not, and the ADR says so where it
  will be read rather than in a footnote.
- It does not claim parity. The 600 are three stride-pinned 200-file samples of
  23,361 files; the references decide 176 / 181 / 78 on these lists at 24 s.
- It does not claim the cost is free. 43 files now spend the whole budget where
  they used to refuse instantly, and AUFDTLIRA's wall nearly doubles.

## Evidence

- `crates/axeyum-solver/tests/dt_valued_result_1946.rs` — 12 tests. Four
  positive controls that must decide (three `unsat`, one `sat` for the replay
  ordering), one that pins a shape an EARLIER rung decides so it is not mistaken
  for a control of this one, four `sound_*` over queries both oracles call `sat`,
  and three `refusal_*` that pin the census-readable messages.
- `scripts/tests/mutation_controls.py`, suite `dt-valued-result-1946` — five
  mutations, all five killed. ADR-1942's suite re-run after its anchor grew: six
  of six still killed, each exactly one test.
- Every fixture's expected verdict was checked against `z3` AND `cvc5` before it
  was written down, not after it passed — and two candidate positive controls
  were DISCARDED because the previous arm already decided them, which would have
  measured the ladder rather than this change.
- [`bench-results/dt-valued-result-20260912/`](../../../bench-results/dt-valued-result-20260912/README.md)
  — the sizing census and its 600 rows, the A/B protocol and all 1,000 per-file
  rows, the oracle re-validation of all 35 gains, the per-file wall-cost split,
  and `score-prediction.py`, which scores the committed sizing against the A/B.
- Two suites this change overtook were replaced rather than deleted, each with a
  line saying why: `dt_capability_1935`'s `refusal_names_the_datatype_valued_result`
  (retargeted to an INEXACT result datatype — the same arm, one shape further
  out), and `unknown_reason_coverage`'s dispatch-error fixture, **for the FOURTH
  time in two days** and again by the rung the previous replacement predicted in
  writing. Its replacement is the measured next rung: a UF over a datatype with a
  datatype-typed field.
- `hooks/pre-push` gates `dt_valued_result_1946`, named when the suite was
  written rather than after `scripts/check-suite-gating.py` refused the push.
