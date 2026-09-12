# Lane: dt-capability — the ADR-1920 slice was 6 of 600 files, so its "complement" went first

<!-- plan-section: lane-status -->

**Lane dt-capability (`DONE`, dt-capability, 2026-09-12).** ADR-1920 named
"Ackermann congruence over expanded datatype arguments … restricted to datatypes
whose fields are all scalar" as BUILD NEXT, and
[the corrected blocker census](../../research/03-measurements/the-dt-blocker-census-was-measuring-the-ladder-2026-09-12.md)
§5 sized the refusal it addresses at 143 of 600 sampled files, beside a second
row — array/UF-sorted datatype FIELDS — at 152, with the instruction to price
both together or neither.

**The sizing, done before a line of code, inverted the build order.** Of the 438
files declaring a UF with a datatype-sorted parameter, ADR-1920's "all fields
scalar" precondition holds for **6** — zero in `AUFDTLIRA`, zero in `UFDT`, six
in `UFDTLIRA`. These divisions are SPARK/Ada verification conditions whose
records carry `(declare-sort …)` uninterpreted fields (`integer`, `us_private`,
`natural` — checked in the files, not assumed to be `define-sort` aliases) and
`(Array Int integer)` fields, which is exactly what the restriction excludes.
Admitting those field sorts raises the eligible population to **136**. So the
field half is the congruence half's PREREQUISITE, not its complement, and
ADR-1920's order buys 6 files.
[The measurement.](../../research/03-measurements/the-adr-1920-slice-is-6-of-600-files-2026-09-12.md)

**Both halves landed, under
[ADR-1935](../../research/09-decisions/adr-1935-the-congruence-precondition-is-exactness-not-scalarity.md).**
One predicate, `field_sort_expands`, decides which field sorts get an expansion
variable, and it now admits uninterpreted sorts and arrays whose component sorts
mention no datatype. `ackermannize_datatype_applications` replaces every
`f(…)` with a datatype-sorted argument by a fresh witness and asserts pairwise
congruence, leaving the argument equalities as plain `Op::Eq` for the existing
tag/field expansion to encode. **The checked precondition is exactness of the
expansion, not scalarity of the fields** — the property ADR-1920's soundness
argument actually needs, for which scalarity is sufficient and not necessary.

**The A/B**, 1,000 files, both arms back to back on the same pinned core pair,
arm order alternating per file, 10 s / 8 GiB, on three idle homogeneous boxes:

| division | n | base | new | delta | gain | loss | flip |
|---|---:|---:|---:|---:|---:|---:|---:|
| AUFDTLIRA | 200 | 41 | **69** | **+28** | 28 | 0 | 0 |
| UFDTLIRA | 200 | 72 | **82** | **+10** | 10 | 0 | 0 |
| UFDT | 200 | 26 | **27** | **+1** | 1 | 0 | 0 |
| QF_DT (control) | 200 | 169 | 169 | 0 | 0 | 0 | 0 |
| UF (control) | 200 | 88 | 88 | 0 | 0 | 0 | 0 |

**+39 net, 0 decided→undecided, 0 flips**, and both controls flat. **All 39
newly decided files re-run at 24 s against both oracles and their declared
status: axeyum `unsat`, z3 `unsat`, cvc5 `unsat`, declared `unsat`, 39 of 39 —
0 disagreements on three independent checks.** Neither arm disagrees with a
declared `:status` anywhere in the 1,000 rows. The base arm reproduces the
committed board rows exactly (41 / 72 / 26), which is the check that the two
arms are measuring what the board measured.

**The cost is wall clock, and it is real**: `AUFDTLIRA` 135 s → 224 s over the
200 files, `UFDTLIRA` 83 s → 122 s, `UFDT` 388 s → 480 s for its single gain. A
query the field refusal used to end in 44 ms now runs the whole twenty-rung
ladder. Both controls moved within noise (0.0 s of 52 s, 3 s of 1,374 s), so the
cost is confined to the divisions this change touches.

**The A/B found a defect reasoning did not.** The first run was +28/+10/**−1** on the targets and 0/0 on the controls:
one `UFDT` file `main` answers `unsat` returned `backend failure: datatype sat
model replay failed`. The replay was right to reject the candidate; the bug was
that `datatype_native` treats a replay failure on the exact path as a
`SolverError::Backend`, which ends the dispatch, so the ladder never reached the
route that decides the file. An Ackermann-expanded query's model reconstruction
is partial by construction — a site whose arguments do not all evaluate
contributes no entry — so it is a RELAXED query and a replay failure is a
decline. Fixed, plus two reconstruction holes that made correct models look
wrong; re-measured from scratch against a rebuilt binary, and that is the table
above.

**The mutation controls are a finding, not a formality.** Four of the six guards
SURVIVED their first run — deleted, all 16 tests still passed — because each is
an EARLY, PRECISE refusal of a shape a LATER, vaguer one also refuses. Worth
saying plainly: **it is ADR-1930's two-sided equality encoding and the replay,
not the exactness precondition, that stand between the solver and a wrong
`unsat` today.** What each guard uniquely produces is its MESSAGE, which
ADR-1920's second decision requires to name the actual missing capability
because these divisions' blocker census is read off exactly these strings. Four
tests now pin that; all six mutations kill, four of them exactly one test.

**The next capability is named by the residual census**, taken on the new arm
over the three target divisions:

| refusal | files |
|---|---:|
| UF applied to a datatype term that is **not a free variable** | **173** |
| congruence over a datatype argument whose **expansion is not exact** | 50 |
| a UF whose **RESULT sort mentions a datatype** | 47 |
| e-matching instantiation did not refute within the round budget | 39 |
| `is`/`select` over a non-variable datatype term | 22 |

The top row is new and was not on any previous census — it is a **constructor
term as a UF argument**, whose argument equality is structurally exact and
cheap (`mk(a₁,b₁) = mk(a₂,b₂)` iff the fields agree), so it is the obvious next
slice. The 50-file row is the 302-file datatype-field class this work
deliberately does not reach; it needs exact recursive equality, a third
capability.

Gates: `--lib --features full` 1718/1718, `corpus_regression` 2/2,
`dt_capability_1935` 20/20, `dt_uf_gate` 10/10, `datatype_solve_path` 3/3,
`quant_ladder_rung_refusal_declines` 3/3.

Rows, runner and analysis:
[`bench-results/dt-capability-20260912/`](../../../bench-results/dt-capability-20260912/README.md).

<!-- /plan-section -->
