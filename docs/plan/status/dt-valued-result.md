# Lane: dt-valued-result — the witness IS a variable, and 28 of the 35 gains came from a refusal this rung is not named after

<!-- plan-section: lane-status -->

**Lane dt-valued-result (`DONE`, dt-valued-result, 2026-09-12).**
[ADR-1935](../../research/09-decisions/adr-1935-the-congruence-precondition-is-exactness-not-scalarity.md)
refused a datatype-VALUED uninterpreted-function result by name — the Ackermann
witness "would itself be a datatype-sorted term, which the tag/field expansion
would have to pick up in a scan that has already run".
[ADR-1942](../../research/09-decisions/adr-1942-a-constructor-term-as-a-uf-argument.md)
said that objection does not survive the pipeline order; this lane verified it
rather than inheriting it, because a file that records obstacles accumulates
stale ones by construction. It is stale:
`ackermannize_datatype_applications` runs at step 2 of `decide_with_eq_mode` and
`scan_fragment` at step 5, so a witness declared there is an ordinary free
datatype variable by the time the scan walks the rewritten assertions.

**The sizing, committed before a line of code (`0c96ac73e`).** The inherited
figure — ADR-1942's "57 of the 173" — was not reusable, and saying why mattered
more than the number: ADR-1942 shipped, so the 173-file population it was a
fraction of is now 72; the predicate behind it is the `all(route entries)` one
ADR-1942's own §7 retracted as a bound for a quantified division; and this change
is wider than its name, because making a datatype-valued result usable also
requires admitting an `Op::Apply` term as a datatype ARGUMENT. Re-measured on its
own arm, over the 412 undecided files of 600:

| | AUFDTLIRA | UFDTLIRA | UFDT | total |
|---|---:|---:|---:|---:|
| **ADR-1946 eligible, ANY route entry** | 85 | 46 | 89 | **220** |
| ADR-1946 eligible, EVERY route entry | 67 | 28 | 22 | 117 |
| the arm as it stands, ANY route entry | 57 | 30 | 81 | 168 |
| **newly eligible under the ANY predicate** | 28 | 16 | 8 | **52** |

committed as a **bracket of [0, 52], point estimate "low teens", plus one
unquantified addition written down so the A/B could refute it** — that 48 files
refuse first at `is`/`select` over a non-variable datatype term, a
`scan_fragment` refusal no pre-pass predicate can see, and that in many of them
the operand is a UF result this rung turns into a variable.
[The measurement.](../../research/03-measurements/the-datatype-valued-result-rung-priced-on-its-own-arm-2026-09-12.md)

**What landed, under
[ADR-1946](../../research/09-decisions/adr-1946-a-datatype-valued-uf-result-the-witness-is-a-variable-and-the-scan-has-not-run-yet.md).**
An application is an Ackermann site when its ARGUMENT *or* its RESULT is
datatype-sorted. A datatype-valued result is admitted when that datatype's
expansion is exact (the congruence consequent is then a datatype equality); an
array over a datatype is refused by its own message, because its witness would be
array-sorted. An `Op::Apply` datatype ARGUMENT is admitted **because this pass
replaces it** — membership in the collected set, not the operator, so the
collection rule and the shape check cannot drift apart — and the refusal now
names all three admitted shapes, which is what the blocker census reads. And
`ack_sites` is sorted by `TermId` across functions: with a datatype-valued result
nesting is the COMMON shape (`p(g(a))` collects both), so `g` has to be rebuilt
before `p`'s arguments are evaluated or a good `sat` candidate fails its replay.

**Measured: +35 net, 0 losses, 0 flips, both controls flat.**

| division | n | base | new | delta | base wall | new wall |
|---|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 200 | 71 | **90** | **+19** | 257 s | 497 s |
| UFDTLIRA | 200 | 88 | **102** | **+14** | 123 s | 153 s |
| UFDT | 200 | 29 | **31** | **+2** | 553 s | 702 s |
| QF_DT *(control)* | 200 | 169 | 169 | 0 | 52.3 s | 52.1 s |
| UF *(control)* | 200 | 87 | 87 | 0 | 1,389 s | 1,386 s |

The base arm reproduces ADR-1942's new-arm rows exactly (71 / 88 / 29) and its
`QF_DT` control (169). **Soundness: 0 disagreements on all 35 gains** at 24 s —
34 are axeyum / z3 / cvc5 / declared all `unsat`, and the 35th is `unsat` for us
and for cvc5 on a file z3 TIMES OUT on (re-checked at 40 s) whose declared
`:status` is `unknown`. Neither arm disagrees with a declared status anywhere in
the 1,000 rows.

**The cost, diagnosed rather than quoted.** AUFDTLIRA's wall nearly doubles. Split
per file: the 35 gains cost 20 s in total and the whole remaining increase is **43
files that used to stop at a refusal in milliseconds and now run the ladder to the
end of the 10 s budget without gaining** (AUFDTLIRA 24 / +226 s, UFDT 16 /
+146 s, UFDTLIRA 3 / +27 s). Both controls within noise, so the cost is confined
to the divisions this touches. Same trade as ADR-1927 / 1935 / 1942, larger
because this rung unblocks more.

**The sizing was scored, and its point estimate was wrong.** 35 of 35 gains lie
inside the ANY-entry predicate, so the bracket held; the point estimate said "low
teens" and the answer was 35. The mechanism named in advance is why:

| bucket the gain's file was in on the base arm | gains |
|---|---:|
| **`is`/`select` over a non-variable datatype term** | **28** |
| a UF whose RESULT sort mentions a datatype | 5 |
| a UF applied to a datatype term that is neither variable nor constructor | 2 |

**Only 5 of the 35 came from the refusal this rung is named after.** New rule for
the series, and it is a new one rather than a restatement of "a blocker census
over-counts": **a pre-pass eligibility predicate prices the pre-pass, not the
rungs the pre-pass unblocks downstream.** The honest form is the bracket PLUS a
written argument about the downstream effect, committed before the A/B so it can
be scored instead of remembered.

**Mutations: five, all five killed** (`dt-valued-result-1946`, baseline 12 tests
green), with two findings recorded because they contradict what a guard's name
implies. The RESULT-side exactness precondition kills ONLY its refusal-message
test — the third time in this family — because an `unsat` only ever comes from
the relaxation arm, whose datatype equality is weaker-or-exact, so an inexact
consequent makes the clause weaker than the axiom rather than stronger. The
`collected.contains` guard likewise kills only its refusal test. Both are worth
having (a reviewable equisatisfiability argument, the census-readable message, a
fence against a change to ADR-1930's encoding) and neither is today's soundness,
and the ADR says so where it will be read. ADR-1942's exactness anchor had to
GROW — this change adds a second exactness check at the same indentation, which
would have made it `AMBIGUOUS ANCHOR`, not a kill; re-run after the fix, all six
of its mutations still killed, each exactly one test.

**Two overtaken suites replaced, not deleted.**
`dt_capability_1935::refusal_names_the_datatype_valued_result` is retargeted to
an INEXACT result datatype — the same arm, one shape further out. And
`unknown_reason_coverage`'s dispatch-error fixture, **for the FOURTH time in two
days** and again by the rung its previous replacement predicted in writing.

**The next capability, named by measurement: exact RECURSIVE equality** — a
datatype with a datatype-typed field, which is 152 of the 412 undecided files by
variable argument and 147 by result, against 0 for the array-over-a-datatype
result this lane refuses by name. It needs bounded unfolding with a depth
certificate or a native datatype theory with congruence and acyclicity
(ADR-1935's third capability), and it is not a slice of this one. **Size it on its
own arm rather than inheriting a number from here** — which is the mistake
ADR-1946 opened by correcting.

Gates with the `test result:` line read: `-p axeyum-solver --lib --features full
-- --test-threads=4` 1720/1720, `corpus_regression` 2/2 (foreground — the first
backgrounded attempt was killed mid-run and printed NO result line, which reads
exactly like success), `dt_valued_result_1946` 12/12, `dt_capability_1935`
20/20, `dt_constructor_arg_1942` 11/11, `dt_uf_gate` 10/10,
`datatype_solve_path` 3/3, `quant_ladder_rung_refusal_declines` 3/3,
`unknown_reason_coverage` 7/7, `clippy -p axeyum-solver --all-targets
--all-features -D warnings` clean, `cargo check --workspace --all-targets` clean,
`cargo fmt --all --check` clean, `check-links.sh` all ok, `check-suite-gating.py`
PASS (27 gated), `check-merge-hygiene.sh` PASS. **Not run:** `just check`,
`progress_frontier`, and the z3 differential fuzzes — this change touches no
linear-arithmetic route.

Sizing `0c96ac73e`, implementation `47f3d61d8`. Rows, runner, instrumentation,
the prediction scorer and the wall-cost split:
[`bench-results/dt-valued-result-20260912/`](../../../bench-results/dt-valued-result-20260912/README.md).

<!-- plan-section: landed-changes -->

| 2026-09-12 | `0c96ac73e` | The datatype-VALUED result rung priced on its own arm — the inherited "57" was the previous arm's `all()` figure over a population that no longer exists. Bracket [0, 52], committed before the code. |
| 2026-09-12 | `47f3d61d8` | ADR-1946: a datatype-VALUED UF result and the `Op::Apply` datatype argument its witness makes admissible. +35 net (71→90, 88→102, 29→31), 0 losses, 0 flips, controls flat, all 35 gains oracle-confirmed. |

