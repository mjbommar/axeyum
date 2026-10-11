# Lane: wide-real-smtlib-writer — exact input and source evidence

<!-- plan-section: lane-status -->

**LIB-5/6 / EVD-5 / P0 (`WIP`, wide-real-smtlib-writer, 2026-10-11).**
Current Rust cc65885a3 (last change is Python documentation); generated stub
6c11a0008. [Detailed receipts](../notes/28-wide-real-smtlib-writer.md).
Overall feedback goal remains active; implementation has not landed on main.

Earlier exact Real intake/writer, wide NRA/FP safety, datatype source export
and source-bound SAT/ref-miter replay are in ancestry. SMT396 and required
parser frontdoors158 pass; MSRV/default Wasm pass; facts2971 validated on ancestor.
Private decimal/FP/NRA guards each kill one intended test. Full-feature solver
2033pass/0fail/0ignore826.10s on9fd9721d0 predates nested CAS additions.

Reference-miter replay binds final CNF and independently reconstructed miter
CNF to original Bool/BV terms. Private v2:7baseline; each of two guard removals
6pass/one intended failure; both files independently match9fd9721d0 bytewise.
Parent native focused49/census15 and existing consumers1154 pass0 skips.
General theory correspondence and kernel admission are explicit separate gaps.

Nested conditional composition checks source/path/context/congruence/continuity,
partial domains, local guarded-v2 witnesses and bounded transport/work.
Six Rust controls and13Python controls cover wide coefficients and partial declines.
Private congruence guard:6baseline ->5pass/one intended failure; restored bytewise.
Full CAS on lint-fixed0b829e980:2154pass/0fail/11ignored85.25s. CAS lint passes.
Fresh native99af1a4c preserved:34trace tests pass0skip0.32s;25consumer files
1166pass/1external-checker skip65.53s. No partial evidence on unsupported steps.

Python lint final rerun49809 passes after cc65885a3 doc fix; generator62778
passes27modules/667items/5qualified integer annotations. Generated stubs committed.
Sealed typed52388 passes drift27/1888, type95.4%, runtime44/0skip22.84s including configured guarded LRAT exports.
Current CAS registry6894 passes:1310public/153certified/116checker/1041uncertified;
no logging credit. Plan/link gates45795 pass. Merge hygiene36970 exits0 with
shape duplicate/projection scopes explicitly skipped, not full population credit.

Current facts60449 passes2971/0errors with0missing derived edges. Final workspace11433 remains live, uncredited. All-targets
check22417 waits for confirmed workspace Cargo3092650 to finish. Read-only main
merge preview has no conflicts; keep main untouched until green. Older parent
workspace handles need independent collection and cannot qualify this child.
ADR3200/3300/3400/3500/7200 accepted as bounded contracts; validator20pass.
Final native costs/statute replay and5shipped examples pass; fmt2294files passes.
ADR6700 accepted:release controls3pass, source bytes identical. Next: collect workspace/all-targets and
queued completeClippy12036 and CLI43772 (missing skipped comparisons),
archive lanes, integrate and audit.
