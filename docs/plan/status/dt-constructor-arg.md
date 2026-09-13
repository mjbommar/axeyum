# Lane: dt-constructor-arg — the 173-file refusal was worth 10; the rung worth 57 needs this one first

<!-- plan-section: lane-status -->

**Lane dt-constructor-arg (`DONE`, dt-constructor-arg, 2026-09-12).**
[ADR-1935](../../research/09-decisions/adr-1935-the-congruence-precondition-is-exactness-not-scalarity.md)
closed with a residual census whose top row — "UF applied to a datatype term
that is **not a free variable**", 173 of 600 sampled files — it named as the next
slice, because the argument equality for a constructor term `p(mk(a,b))` "is
structurally exact and cheap". The equality claim is right. The arithmetic was
not checked, and this lane checked it first.

**The sizing, committed before a line of code (`405066971`).** A RUNTIME census
that classifies EVERY datatype-sorted UF argument in each query, rather than
stopping at the first refusal, which is all a blocker string can report:

| of the 173 | AUFDTLIRA | UFDTLIRA | UFDT | total |
|---|---:|---:|---:|---:|
| **reachable by this slice** | 8 | 2 | 0 | **10** |
| blocked by an `Op::Apply` datatype argument | 16 | 22 | 49 | 87 |
| blocked by a constructor over an INEXACT datatype | 17 | 22 | 36 | 75 |
| blocked by a VARIABLE over an inexact datatype | 3 | 15 | 49 | 67 |
| **reachable if a datatype-VALUED result is also Ackermannised** | 21 | 22 | 14 | **57** |
| … of those, also carrying a constructor argument | 19 | 22 | 11 | **52** |

So the ADR-1935 shape repeats one rung out, for the second time in one day: **a
blocker census names which refusal fires FIRST, and the population a fix reaches
is strictly smaller, because the file must clear every OTHER precondition of the
same pass.** It should now be assumed rather than rediscovered. It is also why
this slice shipped rather than the bigger one: 52 of the 57 files the
datatype-valued-result capability would reach also apply a function to a
constructor term, so shipping that without this buys 5.
[The measurement.](../../research/03-measurements/the-constructor-arg-slice-is-10-of-173-files-2026-09-12.md)

**What landed, under
[ADR-1942](../../research/09-decisions/adr-1942-a-constructor-term-as-a-uf-argument.md).**
`collect_ackermann_groups` admits a constructor application as a datatype
argument, and `congruence_arg_eq` builds the antecedent's conjunct from the
axioms that make datatypes freely generated — **distinctness** (`c(…) = d(…)` is
`false`, and the whole clause is dropped, which also keeps the quadratic pair
count affordable), **injectivity** (`c(x) = c(y)` is `⋀ xᵢ = yᵢ`), and the mixed
case `c(x) = o` as `is_c(o) ∧ ⋀ xᵢ = sel_{c,i}(o)` — `is`/`select` over a free
variable, so it adds no obligation to the tag/field expansion. The exactness
precondition is unchanged and is what keeps that `sel` off a datatype-typed
field, which `unfold_traversals` would turn into an unconstrained child.

**The A/B**, 1,000 files, both arms back to back on the same pinned core pair,
arm order alternating per file, 10 s / 8 GiB, twelve shards over `s5`/`s6`/`s7`:

| division | n | base | new | delta | gain | loss | flip | base wall | new wall |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 200 | 69 | **71** | **+2** | 2 | 0 | 0 | 223 s | 257 s |
| UFDTLIRA | 200 | 82 | **88** | **+6** | 6 | 0 | 0 | 124 s | 124 s |
| UFDT | 200 | 27 | **29** | **+2** | 2 | 0 | 0 | 484 s | 557 s |
| QF_DT (control) | 200 | 169 | 169 | 0 | 0 | 0 | 0 | 52 s | 52 s |
| UF (control) | 200 | 88 | 88 | 0 | 0 | 0 | 0 | 1,372 s | 1,371 s |

**+10 net, 0 decided→undecided, 0 flips**, both controls flat, and 0
declared-`:status` disagreements anywhere in the 1,000 rows. **All 10 newly
decided files re-run at 24 s against both oracles and their declared status:
axeyum `unsat`, z3 `unsat`, cvc5 `unsat`, declared `unsat`, 10 of 10 — 0
disagreements on three independent checks.** The base arm reproduces ADR-1935's
committed new-arm rows exactly (69 / 82 / 27).

`UFDTLIRA` is free and carries most of the gain; `AUFDTLIRA` and `UFDT` pay about
+15 % for two files each. One caveat on the seconds only: another lane's
benchmark held 100 % of one core on `s7` throughout, which the per-file
interleave cancels in the difference (0 losses, 0 flips) but which inflates both
arms' absolute wall on that host's four shards.

**Two measured corrections to things this lane first wrote down.**

1. **The sizing predicate is not a bound on a quantified division.** It named 11
   files and 3 of them gained; all 10 gains lie inside the loose (`any`-entry)
   predicate's 65. The datatype route is entered once per instantiation round and
   the file needs only ONE of those entries to succeed, so the honest bracket was
   [3, 65] and the answer was 10. §7 of the measurement note carries the
   correction and marks the wrong paragraph in place. The relative finding the
   build order turned on holds under either predicate.
2. **The exactness precondition is AGAIN not what stands between this path and a
   wrong `unsat`** — deleting it kills only the refusal-message test, because
   ADR-1930's relaxed encoding is a free Boolean the search sets FALSE rather
   than being forced true. Identical to ADR-1935's finding on the variable path.
   And one soundness-negative test SURVIVED its mutation because its wrong answer
   was merely *available* (an unconstrained field variable gave the search an
   escape) rather than FORCED; one more assertion fixed it. **A
   soundness-negative test has to make the wrong answer forced.**

`scripts/tests/mutation_controls.py` suite `dt-constructor-arg-1942`: six
mutations, **all six killed, each killing exactly one test**. `dt-capability-1935`
still six-for-six with its shape-check anchor updated to the widened arm.

**The next capability is named by measurement, not symmetry: Ackermannise a
datatype-VALUED UF result into a fresh datatype VARIABLE**, worth 57 of the 173
with this slice in place and 5 without. ADR-1935 refused it because "its witness
would itself be a datatype-sorted term, which the tag/field expansion would have
to pick up in a scan that has already run" — but
`ackermannize_datatype_applications` runs BEFORE `scan_fragment`, so that
objection does not survive the current pipeline order. Residual census on the new
arm, over the three target divisions:

| refusal | files (was) |
|---|---:|
| congruence over a datatype argument whose expansion is not exact | 98 (50) |
| UF applied to a datatype term that is neither variable nor constructor | 72 (173) |
| a UF whose RESULT sort mentions a datatype | 51 (47) |
| `is`/`select` over a non-variable datatype term | 48 (22) |
| e-matching instantiation did not refute within the round budget | 40 (39) |

The top row moving 173 → 72 while three others GREW is the ladder working: a file
that stopped at the shape refusal now proceeds to the next precondition.

Gates: `-p axeyum-solver --lib --features full -- --test-threads=4` 1720/1720,
`corpus_regression` 2/2, `dt_constructor_arg_1942` 11/11,
`dt_capability_1935` 20/20, `dt_uf_gate` 10/10, `datatype_solve_path` 3/3,
`quant_ladder_rung_refusal_declines` 3/3, `unknown_reason_coverage` 7/7,
`clippy -p axeyum-solver --all-targets --all-features -D warnings` clean,
`cargo fmt --all --check` clean, `check-links.sh` all ok.

Sizing `405066971`, implementation `2bc70b251`. Rows, runner, instrumentation and
analysis:
[`bench-results/dt-constructor-arg-20260912/`](../../../bench-results/dt-constructor-arg-20260912/README.md).

<!-- /plan-section -->
