# Lane: dt-ground-probe — does our ground ladder decide ADR-2114's z3-GROUND files, and if not, what typed reason

<!-- plan-section: lane-status -->

**The premise does not survive measurement, the way ADR-2114's own did not**
(`DONE`, dt-ground-probe, 2026-09-16, `bench-results/dt-ground-probe-20260916/`).
ADR-2114 found z3 refutes 44 of 55 `AUFDTLIRA` cores and 39 of 79 undecided
originals with **both** quantifier engines off (`GROUND`). This lane's
question: does OUR quantifier-free ladder refute the same ground part, and if
not, what typed reason does it give.

Wrote `scripts/strip-quantified-assertions.py` (18 unit tests, byte-verbatim
except for dropped top-level `assert`s containing a `forall`/`exists` at any
depth) and ran it on the exact 83 files (44 cores + 39 originals) ADR-2114
attributed `GROUND`. **Plain z3 on the 83 stripped files: 0 `unsat`, 83
`sat`.** ADR-2114's `GROUND` does not mean "a separate set of ground
assertions suffices" — it means z3's own preprocessing (Skolemizing a negated
universal GOAL, folding definitional `forall`-equalities into ground macros)
produces ground content from the quantified assertions *before* the two
quantifier engines ADR-2114 toggled ever run. Literal deletion removes both
mechanisms' input, so the remainder is generically satisfiable — measured on
both populations, both the minimized-core and full-original shape.

So there is no `our-ladder-vs-z3's-ground-unsat` population to test; what the
lane instead measured is descriptive: our ground ladder against the same 83
files with reference verdict `sat`. Shipped-default arm: **69 of 83 (83%)
`sat`, agreeing with z3; 14 `unknown`, 0 `unsat` (no soundness incident)**.
`AXEYUM_DATATYPE_NATIVE_REFUSAL=propagate` (ADR-1980's historical arm): 73 of
83 (88%) `sat`, 10 `unknown` — 4 files flip `unknown`→`sat` under `propagate`
(both copies each of `why_b5aa01`/`why_ec30e5`), not a timeout (max elapsed
412 ms of a 24 000 ms budget across all 166 runs).

Terminal-reason histogram, 14 shipped-default `unknown` files (read from
`route-trail` JSON, never prose): **8 at `register_datatype`
(`datatype_native.rs:1511-1518`)** — the exact site ADR-2114 §4 already named
and sized on the *quantified* files, now cross-confirmed as the dominant
undecided bucket on an independent, quantifier-stripped population; **5 at
`auto.rs:8521-8528`** (a non-BV array whose domain/range mentions an
uninterpreted sort falls outside the lazy Bool/Int array route — a different,
smaller, un-sized gap, all 5 rows the same 3 underlying `R509-011
higher_order_proof` VCs); **1 at `sat_bv_backend.rs:120-123`** (a
`Datatype`-sorted term reaches the pure-Rust BV backend directly).

Full detail, tables and both arms: `bench-results/dt-ground-probe-20260916/README.md`.

<!-- plan-section: landed-changes -->

| 2026-09-16 | `10aff7750` | `scripts/strip-quantified-assertions.py` + 18 unit tests: byte-verbatim quantifier-assert stripping, iterative tokenizer/parser (no recursive `let` expansion). |
