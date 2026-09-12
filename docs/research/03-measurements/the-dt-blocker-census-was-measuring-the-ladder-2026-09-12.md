# The DT divisions' blocker census was measuring the ladder, not the solver

Measured 2026-09-12, lane `dt-divisions`. The decision this note supports is
[ADR-1927](../09-decisions/adr-1927-a-ladder-rungs-fragment-refusal-is-a-decline-not-the-querys-verdict.md).

**In one line: `AUFDTLIRA` scored 0 of 200 against two references that each
scored 176, because three quantified-ladder rungs propagated a speculative
sub-solve's `Unsupported` and ended the dispatch at `attempts=2` after one
millisecond — and the division's published blocker table was a picture of which
rung refuses first.**

## 1. The boards, which is what the lane was sent to produce

Four divisions with no parity row: `UFDT` (4,569), `UFDTLIRA` (7,749),
`AUFDTLIRA` (11,043), `UFDTNIRA` (4,424) — **27,785 files**.

Protocol, and every part of it is load-bearing:

* 200 files per division, from stride-pinned lists committed **before** anything
  was run (`UFDT` at `49a0e2698`, the other three at `62e55bdd1`). A stride
  sample through the division, never a path-sorted prefix — `UFDT`'s prefix-200
  is one author directory.
* 24 s wall, 8 GiB address space per run.
* Three solvers **interleaved per file**: all three finish file *N* before any
  starts *N+1*, on the same pinned core pair of the same idle homogeneous box
  (`s5`/`s6`/`s7`, Ryzen 7 7840HS, load < 0.1 at launch), with the first-mover
  rotating per file.
* `z3 -T:24` (SECONDS), `cvc5 --tlimit=24000` (MILLISECONDS). The units differ
  and getting one wrong cripples a reference silently.
* Wrapper timeout **24 + 16 s**, and every run records its own outcome (`ok`,
  `wrapper-killed`, `rc134`, `sigkill`). An earlier census used +8 under load,
  killed 17 processes, and produced rows that read as "no reason". **No row in
  these boards is `wrapper-killed`.**

| division | files | axeyum | z3 4.13.3 | cvc5 1.3.4 |
|---|---:|---:|---:|---:|
| UFDTLIRA | 200 | 66 | 181 | 158 |
| UFDT | 200 | 22 | 66 | 78 |
| UFDTNIRA | 200 | 5 | 173 | 183 |
| AUFDTLIRA | 200 | **0** | 176 | 176 |

Raw rows: `bench-results/dt-divisions-headtohead-20260912/`.

Two things to carry:

* **The reference is not one solver.** On `UFDTLIRA`, z3 decides 23 files cvc5
  does not and cvc5 decides **0** that z3 does not. In this division the leader
  is z3, not the datatype solver of record. Name the reference when you quote a
  gap.
* **cvc5's `UFDT` row is a badly depressed floor: 100 of its 200 runs ended in
  `rc134`**, the 8 GiB address-space cap. Those count as not solved under the
  parity protocol, but "cvc5 decides 78 of 200 UFDT benchmarks" is not what the
  number means. Bounded check: 5 of those 100 re-run at a **24 GiB** cap, same
  24 s — `unknown` on all 5, so the cap was not hiding verdicts on that sample.
  Five of a hundred is a spot check, not a clearance. `AUFDTLIRA` has 2 such
  rows, `UFDTNIRA` 13, `UFDTLIRA` none.

## 2. A zero is a different kind of number

`AUFDTLIRA` at **0 of 200**, against references that decide 88 % of the same
files and mostly in under a tenth of a second, is not what a capability gap
looks like. `--trace` on the first file took one command:

```
; give-up kind=Error detail=unsupported by backend: eager Ackermann elimination
  does not admit array-valued function results; use canonical AUFBV combination
; route decided_by=none bound_by=fd:parse last=q:ground-subset
  bound_ms=1 total_ms=1 attempts=2
```

`attempts=2` on a twenty-rung ladder. And the message is a `QF_UFBV` Ackermann
restriction, quoted for a quantified `AUFDTLIRA` benchmark containing no
bit-vector: it describes a query the solver *built*, not the query it was given.

The cause, and the fix, are ADR-1927. Three rungs — `eliminate_valid_universals`
(which sub-solves `¬body[x := c]`), the e-graph refuter, and the MBQI pass —
handed a *rewritten* query to a backend that refuses its fragment and let the
resulting `SolverError::Unsupported` travel out of `solve`.

**Bisecting it is the part worth repeating**: each guard, added one at a time,
moved `attempts` and the reported blocker.

| guards in place | attempts | reported give-up |
|---|---:|---|
| none | 2 | `eager Ackermann … array-valued function results` |
| + valid-universal | 7 | `` `is`/`select` over a non-variable datatype term `` |
| + e-graph | 8 | `native datatype solving … array/UF datatype fields` |
| + MBQI | **20** | the same message, now as a first-class `Incomplete` |

Four different "blockers" for one unchanged file. Only the last one is about the
file.

## 3. The A/B

Per-file A/B against the same binary without the guards, arms alternating per
file, back to back on the same pinned cores, 10 s and 8 GiB per run, 200-file
stride samples.

| division | base | guarded | newly decided | decided → undecided | `sat`↔`unsat` flips |
|---|---:|---:|---:|---:|---:|
| AUFDTLIRA | 0 / 200 | **62 / 200** | 62 | **0** | **0** |
| UFDTLIRA | 70 / 200 | **75 / 200** | 5 | **0** | **0** |
| UFDT | 23 / 200 | **26 / 200** | 3 | **0** | **0** |
| UFDTNIRA | 10 / 200 | 10 / 200 | 0 | **0** | **0** |
| **UF (control)** | 83 / 189 | 83 / 189 | 0 | **0** | **0** |

`UF` is the control: an established quantified division already on the parity
board, where letting more rungs run could only cost. Nothing moved either way.
`UFDTNIRA` is the honest null — this change does nothing for it.

All 70 new verdicts are `unsat`. Cross-checked three ways, and every check was
*comparable on every file* — no check was silently vacuous:

| check | comparable | disagreements |
|---|---:|---:|
| declared `:status` | 70 of 70 | **0** |
| z3 4.13.3, 24 s, same box | 70 of 70 | **0** |
| cvc5 1.3.4, 24 s, same box | 70 of 70 | **0** |

## 4. The corrected blocker census — the result worth more than the 70 files

`AUFDTLIRA`, the undecided files, before and after:

| refusal | before | after |
|---|---:|---:|
| eager Ackermann, array-valued function results | **174** | **3** |
| `datatype_native`: array/UF-sorted datatype FIELDS (ADR-0022) | 0 | **70** |
| UF applied to a datatype argument (ADR-1920) | 14 | **32** |
| `is`/`select` over a non-variable datatype term | 0 | **13** |
| quantified / e-matching budget | 0 | **12** |
| a datatype-sorted term survives tag/field expansion | 7 | 1 |
| parse: nested array element sort | 5 | **5** |
| watchdog | 0 | 2 |
| **decided** | **0** | **62** |

`UFDTLIRA`, after:

| refusal | files |
|---|---:|
| UF applied to a datatype argument | **54** |
| `datatype_native`: array/UF-sorted datatype fields | **29** |
| instantiation is satisfiable; the universal may still be violated | 27 |
| e-matching round budget | 8 |
| quantified budget after valid-universal elimination | 4 |
| uninterpreted sort at the pure-Rust BV backend | **1** |

Compare with the census this lane was dispatched on (40 files per division, 3 s,
`bench-results/dt-divisions-20260912/`), whose top two rows were *eager Ackermann
array-valued* (21 %) and *uninterpreted sort at the BV backend* (18 %). The first
was **87 %** of `AUFDTLIRA` before the guards and is **1.5 %** after; the second
is **1 of 200** in `UFDTLIRA`. Neither
was ever a capability boundary of these divisions. They were the rungs that
happened to refuse first.

`UFDTNIRA` is the one that looks different, and it is why it gains nothing here:
after the guards, **108 of 200** report `quantified solve time budget exhausted
after valid-universal elimination` and 69 the array/UF datatype-field refusal.
It is more than half CLOCK-bound at 10 s — the only one of the four that is —
and letting more rungs run spends clock. The 24 s board gives it 5 of 200, so
budget alone does not rescue it either; it needs the same datatype capability
plus a cheaper validity rung, and it is not evidence for or against this ADR.

**The rule this teaches.** *A blocker census taken through a ladder that stops
at its first refusal measures the ORDER OF THE LADDER.* It is reproducible,
stable across samples, and confidently wrong — which is the shape this
repository keeps finding. `attempts=` in `--trace` is the check: a ladder that
stopped early did not tell you what the query needs, it told you what it tried.

## 5. What to build next, named twice independently

The corrected census's top two blockers, across the three divisions where the
ladder now runs to the end (`UFDTNIRA` is excluded — it is unchanged by this
work and its blockers are elsewhere):

| capability | AUFDTLIRA | UFDTLIRA | UFDT | of 600 |
|---|---:|---:|---:|---:|
| UF applied to a datatype argument | 32 | 54 | 57 | **143** |
| array/UF-sorted datatype FIELDS in `datatype_native` | 70 | 29 | 53 | **152** |
| `is`/`select` over a non-variable datatype term | 13 | 1 | 23 | 37 |
| e-matching / quantified budget | 12 | 12 | 41 | 65 |

The first is exactly what ADR-1920 named as BUILD NEXT — "Ackermann congruence
over expanded datatype arguments … restricted to datatypes whose fields are all
scalar, and that restriction has to be a checked precondition in the scan, not a
comment". The second is the complementary half: the datatypes these divisions
actually use (`(Array Int Int)`-valued record fields, SPARK/Ada verification
conditions and the Barrett/Reynolds codatatype family) are precisely the ones
that restriction excludes. **Doing only the ADR-1920 slice leaves 152 of 600
sampled files exactly where they are.** Price both together or neither.

## 6. Caveats

- The 10 s A/B and the 24 s board are different budgets; the A/B's 62 is not the
  board row. The post-change board is a separate run against the same pinned
  lists and the same protocol.
- **The guards cost wall clock.** A query refused in 1 ms now runs all twenty
  rungs and may spend its whole budget. The A/B measured 0 verdicts lost to that
  at 10 s, but a sweep over these divisions is much slower than it was, and the
  old speed was the speed of being wrong.
- The guards buy `UFDTNIRA` **nothing** (10 of 200 both ways) and `UFDT` three
  files. The effect is concentrated in `AUFDTLIRA`, and the headline should say
  so rather than average it across four divisions.
- A FOURTH guard was written for `checked_quantified_fast_path`, which has the
  same defect by construction, then **removed**: scanned over 800 corpus files
  with the route trail inspected for its own decline label, it fired **0** times.
  A guard with no reachable trigger is the un-failable checker this repository
  keeps deleting.
