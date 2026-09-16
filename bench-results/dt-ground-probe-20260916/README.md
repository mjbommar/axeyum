# DT-GROUND-PROBE: the naive "strip every quantifier" ground part is not z3's ground part

ADR-2114 measured that z3 refutes 44 of 55 `AUFDTLIRA` reference-minimal cores
and 39 of 79 undecided originals with **both quantifier engines off**
(`smt.ematching=false smt.mbqi=false`) — its own attribution `GROUND`. This
lane's one question: on that same 83-file population, does OUR
quantifier-free ladder refute the ground part, and if not, what typed reason
does it give?

**The premise does not survive measurement, the same way ADR-2114's own did
not.** Stripping every `(assert ...)` that contains a `forall`/`exists`
binder (`scripts/strip-quantified-assertions.py`) and checking the result
with plain z3 gives **0 of 83 confirmed unsat — 83 of 83 are `sat`.** ADR-2114's
`GROUND` does not mean "there is a separate set of ground assertions
sufficient for unsat"; it means z3's own preprocessing (Skolemizing a negated
universal goal, and folding definitional `forall`-equalities into ground
macros) turns the quantified content into ground content **before** the two
quantifier ENGINES the ADR toggled ever run. Both SPARK conventions are
visible directly in this corpus: the VC's goal is written
`(assert (not (forall (...) body)))` (negating a universal — this is what
Skolemizes to a ground witness), and the datatype/array "helper" axioms are
written as `forall`-quantified equalities (this is what z3's macro-finder
folds). Literally deleting both removes exactly the content z3's own ground
reasoning depends on, so the remainder is generically satisfiable. This holds
on **both** populations and in **both** the minimized-core and full-original
shape (a 27-assert original with 9 ground / 18 quantified asserts is `sat`
after stripping exactly like a 2-assert, all-quantified core is).

**Consequence for the rest of this measurement.** There is no valid
"our-ladder-vs-z3's-ground-unsat" population to test here: the reference's
own confirmation excludes 83 of 83. What follows instead is descriptive: how
does OUR ground ladder perform on these 83 quantifier-stripped, SPARK
datatype/array-heavy SAT queries (reference verdict: `sat`), and what typed
reason does it give on the files it does not decide. That is still useful —
it exercises the same datatype/array ground machinery ADR-2114 examined, on a
population ADR-2114 never ran it against — but it answers a different
question than the one posed, and the difference is the finding.

## Method

1. Two file lists, read from ADR-2114's own artifacts
   (`bench-results/dt-quant-trace-20260915/census/reftrace-{cores-55,originals-79}.tsv`,
   column `attribution == GROUND`): **44 of 55 cores**, **39 of 79 undecided
   originals** — reproducing ADR-2114's own counts exactly.
   (`lists/ground-cores-44.list`, `lists/ground-originals-39.list`.)
2. `scripts/strip-quantified-assertions.py` on each of the 83 files: drop
   every top-level `assert` containing a `forall`/`exists` at any depth, keep
   everything else byte-verbatim, leave `(set-logic ...)` untouched (neither
   `axeyum-solver`'s dispatcher nor `smtcomp_cli` branches on the declared
   logic string). `census/strip-stats.tsv`: 813 asserts kept, 1021 dropped,
   across 83 files; 38 of 83 strip to an empty ground part (every assert in
   that file was quantified).
3. Plain z3 (`z3 -T:24`, no options) on each of the 83 stripped files, pinned
   `1,9`/`3,11` on an idle s7. `census/z3verify.tsv`: **83 of 83 `sat`, 0
   `unsat`, 0 `unknown`.**
4. Release `smtcomp_cli` (`10aff7750`, sha256
   `c9575e98d00662bb8010b9ddc0526f239ad4a73b4b48e13b8a2f81ed7973177e`)
   `--trace` on each of the 83 stripped files, 24 s / 8 GiB, pinned `1,9`/`3,11`
   on s7, through `scripts/ledger-run-one.sh`, `sweep_id=dt-ground-probe`.
5. Repeated step 4 under `AXEYUM_DATATYPE_NATIVE_REFUSAL=propagate` (ADR-1980's
   historical arm) beside the shipped `decline` default (`arm=default`).
6. Read every capture with `scripts/route_trace_reader.py` (JSON `route-trail`,
   never prose) for the terminal (last) attempt's typed `detail`.

## z3 confirmation counts

| | n | z3 verdict on the stripped file |
|---|---:|---|
| cores (44) | 44 | 100% `sat` |
| undecided originals (39) | 39 | 100% `sat` |
| **all 83** | **83** | **0 `unsat`, 83 `sat` (0 excluded for any other reason — the exclusion is total)** |

No file needed excluding "for a reason" in the sense step 3 anticipated
(a partial flip) — every one flipped, which is itself the reason, given
above.

## Decided / undecided, per list (our ladder, on the SAT-per-z3 stripped files)

| arm | population | n | `sat` (agrees w/ z3) | `unknown` (undecided) |
|---|---|---:|---:|---:|
| default (shipped) | cores | 44 | 39 | 5 |
| default (shipped) | originals | 39 | 30 | 9 |
| default (shipped) | **all** | **83** | **69 (83%)** | **14 (17%)** |
| propagate (ADR-1980 historical) | cores | 44 | 41 | 3 |
| propagate (ADR-1980 historical) | originals | 39 | 32 | 7 |
| propagate (ADR-1980 historical) | **all** | **83** | **73 (88%)** | **10 (12%)** |

**0 `unsat` anywhere, both arms, all 166 rows** — no soundness incident;
every miss is a safe `unknown`. All 166 runs exited 0, max elapsed 412 ms
against a 24 000 ms budget, so every `unknown` is genuine ladder exhaustion,
not a timeout (`bench-results/ledger/dt-ground-probe.tsv`).

**The refusal-policy arms disagree on 4 files, all one direction**
(`unknown` under `decline` → `sat` under `propagate`): both core+original
copies of `why_b5aa01` and `why_ec30e5` (`R509-011__higher_order_proof`).
Both are `auto.rs:8527`-bucket files (below) under `decline`; `propagate`
reaches a different, successful route on exactly these four instead. This is
not a timeout artifact (elapsed times are single-digit milliseconds under
both arms) — it is a genuine case where letting the ladder try every rung
after the datatype-native decline (the shipped `decline` policy) reaches a
worse outcome than aborting immediately (`propagate`) on this narrow,
datatype+non-BV-array population. ADR-1980's broader measurement is not
challenged by 4 files; this is flagged as a population-specific
counter-example worth knowing, not a re-litigation of that ADR.

## Terminal-reason histogram, the 14 undecided files (default/shipped arm)

| n | typed reason | file:line |
|---:|---|---|
| 8 | `register_datatype` refuses a field sort `field_sort_expands` rejects | `crates/axeyum-solver/src/datatype_native.rs:1511-1518` |
| 5 | a non-bit-vector array (domain/range mentions an uninterpreted sort) falls outside the lazy Bool/Int array route | `crates/axeyum-solver/src/auto.rs:8521-8528` |
| 1 | a `Datatype`-sorted term reaches the pure-Rust BV backend directly and cannot be bit-blasted | `crates/axeyum-solver/src/sat_bv_backend.rs:120-123` |

Full per-file detail: `census/terminal-reasons.tsv` (both arms).

## The largest bucket, and where it points

**8 of 14 (57%) of the shipped-default undecided files terminate at the same
site ADR-2114 §4 already named and sized: `register_datatype`
(`crates/axeyum-solver/src/datatype_native.rs:1491-1524`), which refuses any
constructor field sort `field_sort_expands` (`:1549` in ADR-2114's numbering,
now the same predicate) does not accept — the message is
`"a datatype field sort with no expansion variable (native datatype solving
expands Bool/BitVec/Int/Real, uninterpreted sorts, and arrays whose
component sorts mention no datatype)"`, carried verbatim out through every
lower rung's decline until the ladder's final `dispatch-error` attempt.**
This is a **cross-check, not a new finding**: ADR-2114 traced this exact
refusal on the *original, quantified* files and declined to build a lever for
it (at most 1 of 79 undecided originals convertible, by z3's own both-off
arm); this lane finds the identical site dominating the undecided remainder
of a completely different, quantifier-stripped population, which is the kind
of agreement that makes a blocker census believable. ADR-2114 §4 already
names and sizes the representation that would close it (recursive tag/field
expansion of a datatype-typed field to its own nesting depth, reusing the
`links` child slots `unfold_traversals` already creates, terminating because
0 of 134 files in that lane's population declares a recursive datatype and
the deepest nest is 5) — the next build lane's target is that representation,
still, now cross-confirmed from a second, independent population built by
this lane rather than re-derived from the same 134 files.

The second bucket (`auto.rs:8521-8528`, non-BV array outside the lazy
Bool/Int route) is a **different, smaller** gap: none of ADR-2114's own
sizing covers it, because it is an array-theory limitation (domain or range
sort is `Uninterpreted`, not `Datatype`), not a datatype one — `features`
shows `NonBvArray|NonBoolBvArray` on all 5 files, all copies of the same 3
underlying `why_*` VCs (`R509-011__higher_order_proof`). Naming and sizing
that representation is out of this lane's scope (one question, ground-only,
no ADR), but it is the second-largest bucket here and is not the same gap as
the datatype one — a future census should not fold the two.

## Artifacts

- `scripts/strip-quantified-assertions.py` (+ 18 unit tests) — commit
  `10aff7750`.
- `lists/ground-cores-44.list`, `lists/ground-originals-39.list` — the exact
  83 basenames, reproducing ADR-2114's `GROUND` attribution counts.
- `census/strip-stats.tsv` — per-file kept/dropped assert counts.
- `census/z3verify.tsv` — per-file plain-z3 verdict on the stripped file.
- `census/terminal-reasons.tsv` — per-file typed terminal reason, both arms.
- `bench-results/ledger/dt-ground-probe.tsv` (166 rows, registered in
  `bench-results/ledger/INDEX.tsv`) — the full `--trace` capture-derived
  ledger rows, both arms, both pinned cores.
