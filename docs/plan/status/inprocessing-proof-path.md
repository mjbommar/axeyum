# Lane: inprocessing-proof-path — inprocessing inside the proof-producing core

<!-- plan-section: lane-status -->

**`WIP`, inprocessing-proof-path, 2026-09-07.** The one hypothesis the
[boolean-core lane](bench-boolean-core.md) left standing for the measured
propagations-per-conflict gap is **confirmed, and it was under-predicted**.
[ADR-1750](../../research/09-decisions/adr-1750-a-reducing-pass-must-record-what-it-derived-not-what-it-deleted.md);
working record, including where the pre-registered expectations were wrong:
[`docs/research/12-performance/inprocessing-proof-path-2026-09-07.md`](../../research/12-performance/inprocessing-proof-path-2026-09-07.md).

**The measurement.** s5 idle, one binary (sha256 pinned), 20,000-conflict
budget, arms interleaved, 64 cells, 0 failures, counters bit-identical across
repeats, worst wall-time spread 1.025x. Over the six p4dfa instances where every
arm exhausts the budget, **BVE cuts propagations per conflict to a median
0.426** and **conflicts per second to 1.875x**. Against the 2.56x median deficit
measured on the same eight files on the same host, `2.56 x 0.426 = 1.09` — on
this metric one-shot BVE closes essentially the whole gap to Kissat. Subsumption
alone moves the median 7% and is worse on three of eight files; the effect is
entirely BVE, the only pass that removes variables. Unpredicted mechanism: the
reduced formula has 24-28% fewer clauses but **17-21% more literal occurrences**, so
propagations per *second* falls 13% — a change aimed at volume moved rate the
other way.

**The cost, as a break-even rather than a wall time.** At this budget BVE loses
on total time on every file (1.2-88 s of pass against a 0.35-35 s search). The
break-even is **59k-131k conflicts, median ~92k, on every file across a 100x
range of instance size** — 4.6 s of unreduced search on the smallest instance,
177 s on the largest. The sweep ran ~4.6x below it, which is why the default
stays `OFF`: turning it on is a scheduling decision to be made against that
table and a real solve budget.

**The certificate survives it.** `axeyum_cnf::inprocess` streams each pass's
DRAT into the same sink the search writes to, so the concatenation is one proof
of the **original** formula. Every step is plain RUP — no RAT, no extension
variable — including BVE's. Measured obligation: **only the clause-adding half of
a pass is soundness-critical to record.** Making the passes silent about every
clause they derived is rejected 38 of 38 times; dropping every deletion leaves
all 38 proofs valid, because deletion only shrinks the checker's active set. The
pre-registered negative test ("over-strengthening must be rejected") was
**inverted** and the first run said so — `check_drat` accepts RAT, which is
satisfiability-preserving, so a DRAT proof does not certify that an added clause
was entailed. Replaced with the end-to-end form: 521 corrupted passes produced a
wrong `unsat` and the checker rejected all 521.

**A checker bug the inprocessed proof found.** Pointing `check_drat_backward` at
the same proofs — because six of the suite's tests reach their verdict through
one `check_drat` call — produced a disagreement on the first run: forward
accepts, backward rejects at step 41. `drat_backward.rs` said which of several
set-equal live clauses a deletion removes is "immaterial"; that is false for the
pair every normalization prelude creates on purpose, since `(b)` is a unit to a
verbatim propagator and `(b ∨ b)` is not. All three deletion lookups
(`drat.rs`, `drat_backward.rs`, `lrat.rs`) now prefer the **multiset** match.
A completeness fix, never an unsound acceptance; mutation control kills exactly
one test per reverted half.

**Not run, not ruled out.** *In-search* inprocessing — everything here is one
pre-pass. It needs `Cdcl` to rebuild arena/headers/watches at level zero while
preserving VSIDS activity and phases; the ~92k break-even is what makes it
interesting. Also open: `sat_bv_backend` still checks its `unsat` against the
*reduced* formula (`sat_bv_backend.rs:297`), so with `cnf_inprocessing` on the
BVE link is trusted rather than checked — the machinery to close it now exists,
the obstacle is that backend's `compact()` renumbering. And no p4dfa instance in
the <=25 MB slice is decided `unsat` at 20,000 conflicts, so the corpus-scale
proof check ran on a near-threshold random 3-SAT instead (backward checking 231x
faster than forward over 203,528 steps).

**Attribution note for whoever merges this.** The first five commits of this
lane are stamped `Agent: retire-generic-1`, not `inprocessing-proof-path`. The
shell running `lane-commit.sh` had no `AXEYUM_AGENT` (it does not survive
between tool invocations here), so `hooks/commit-msg` took its repo-local
fallback — which git worktrees **share**, so it carried another lane's name.
This is the exact incident the hook's own comment records (38 commits over four
days from at least four lanes). The five are `f8b9927d1`, `f7321fcc0`,
`8f24e7f23`, `40fe71b3d`, `3ba12a718`; no history was rewritten to correct them.

<!-- plan-section: landed-changes -->

| 2026-09-07 | `3ba12a718` | A deletion names a literal MULTISET: `check_drat` and `check_drat_backward` disagreed on an inprocessed proof because all three deletion lookups matched only the literal SET, and the normalization prelude puts `(b)` and `(b OR b)` live at the same moment. Fixed in `drat.rs`, `drat_backward.rs` and `lrat.rs`; a completeness fix, mutation-controlled. |
| 2026-09-07 | `8f24e7f23` | The measurement (ADR-1750) plus `examples/inprocess_profile.rs` and `examples/inprocess_proof_check.rs`. |
| 2026-09-07 | `f7321fcc0` | `axeyum_cnf::inprocess` + `solve_with_drat_proof_inprocessed`: the passes now say what they did. `simplify`/`bve` gained recorders threaded through their fixpoint loops (a diff of input against output has no ordering guaranteed to verify). `tests/inprocess_proof_path.rs`, 8 tests over 19 instances x 6 arms. |
| 2026-09-07 | `f8b9927d1` | Lane opened: five expectations pre-registered, plus the correction that `sat_bv_backend` already runs these passes — off by default, as preprocessing, with the certificate covering only the reduced formula. |
