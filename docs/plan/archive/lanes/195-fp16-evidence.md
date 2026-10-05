# Lane: fp16-evidence — settle F:fp16-add-monotone-rne's evidence row (ADR-0613)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, fp16-evidence, 2026-08-28).** `F:fp16-add-monotone-rne`
is now `epistemic_status: proved`. Rebuilt `smtcomp_cli --release` from
scratch in this worktree and ran it end to end against the fact's own pinned
negation file TWICE: both `unsat`/`certified=1`/`recheck=ok`/`arena=ok`.
Wall clock 339.01s (load ~2.8/16) and 353s (load ~20.7/16) -- **not** the
~125s ADR-0613's prose calls "end to end": that figure is a sub-stage timer
captured before `UnsatProof::recheck()` and the `arena` fresh-parse check
run (both inside `evidence_report_line`, after the timer stops). Wrote one
`unsat-certificate` evidence row whose `checker_command` greps the real
process output for three independently-tested, discriminating substrings
(`^unsat$`, `certified=1 `, `recheck=ok`) via `test`-chained `&&`, verified
against both a captured real positive transcript and two synthetic
negative-control transcripts before being written. `checker_seconds: 400`
(budget 800s under the replay gate's 2x rule) to absorb contention.
`validate-facts.py` passes: 0 errors, `smt-clausal=10` (was 9), `open=155`
(was 156). No exhaustive enumeration exists or was attempted at this width
(2^48 triples); this fact rests on the symbolic CNF/DRAT/LRAT route alone,
unlike its fp8 sibling which has two independent routes.

<!-- plan-section: landed-changes -->

| 2026-08-28 | fp16-evidence | `F:fp16-add-monotone-rne` flipped open -> proved; attached `unsat-certificate` evidence row with discriminating `checker_command` (ADR-0613 LRAT route), reproduced end-to-end twice (339s, 353s wall clock) |
