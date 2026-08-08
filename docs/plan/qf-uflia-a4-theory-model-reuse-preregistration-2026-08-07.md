# QF_UFLIA A4 theory-model reuse preregistration

Date: 2026-08-07

## Trigger and diagnosis

The v3 exact-commit Axeyum restart produced 93/200 instead of the required
94/200. Exactly one file drifted:
`mathsat/Wisa/xs-18-09-1-5-4-4.smt2` was SAT in the v2 pass and `unknown` in
v3. Three isolated runs of the unchanged v3 binary produced SAT in 19.41 s,
`unknown` at 24.33 s, and SAT in 19.92 s. All outcomes are sound, but retrying
the census until the retained aggregate passes would be invalid selection.

The route trace localizes the cost to `dpll_lia::try_finish_sat`. The preceding
theory-conflict scan has already run the selected conjunctive theory oracle.
When that oracle returns `Sat(model)`, the scan discards the model and reports
only an empty conflict set; SAT finishing then runs the identical theory
conjunction again to reconstruct a model. The duplicate solve races the shared
24-second deadline.

## Authorized repair

Preserve a `Sat(model)` returned by the existing integer or real conflict scan
and pass it to SAT finishing for the same literal indices. Keep conflict cores
unchanged. If the probe returns `Unknown`, preserve the current behavior:
reconstruction may retry under the remaining shared deadline and must degrade
to `unknown` on failure. Opaque-integer applications continue to use the
opaque-tolerant oracle and cannot receive unchecked SAT model credit.

Every final SAT result still builds an original-symbol assignment and replays
every original assertion. No timeout, node cap, route ordering, abstraction,
lemma, or evidence rule changes. A focused unit test must prove cached theory
models bypass a second oracle call; existing replay-rejection and inconsistent
reconstruction tests remain controls.

## Acceptance and stop rules

1. Focused solver tests and warning-denied Clippy pass.
2. Five isolated 24-second repetitions of the drifting file are SAT and replay
   cleanly; any `unknown`, wrong verdict, or replay failure stops the repair.
3. A three-file near-miss control selected from adjacent Wisa rows preserves its
   prior verdict vector under the same binary and budget.
4. Commit and push before restarting A4 v4 capture from row one. The complete
   frozen list must restore at least all 94 historical decisions, reproduce the
   94/180/94/0/86/0 matrix exactly, and retain zero disagreements.

Do not raise caps, special-case a filename, reuse a failed stream, or infer
reference outcomes from history.
