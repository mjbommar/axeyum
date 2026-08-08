# QF_UFLIA A4 reference-timeout v3 preregistration

Date: 2026-08-07

## Why v2 stopped

The v2 Axeyum stream completed all 200 rows at commit `79ad4af7b`, but the
fresh reference stream stopped at row one. With the preregistered
`cvc5 --tlimit=24000 FILE` command, pinned cvc5 1.3.4 exhausted its internal
limit after 26.2 seconds, emitted no stdout, aborted with exit `-6`, and wrote
exactly `cvc5 interrupted by timeout.` to stderr. The fail-closed adapter
correctly refused to guess that a signal was a timeout. The retained
uncredited failure record is
`/tmp/axeyum-qf-uflia-a4-reference-v2.failure.json`.

A controlled rerun of the same first file with cvc5's documented per-query
form, `--tlimit-per=24000`, completed in 24.13 seconds with exit 0, one
standalone `unknown`, and no cvc5 stderr. This removes the ambiguous signal
instead of teaching the adapter to reinterpret one.

## Sole amendment

V3 changes the reference invocation from `--tlimit=24000` to
`--tlimit-per=24000`. The 29-second outer wall guard, 8 GiB memory guard,
pinned binary, frozen list, complete-record predicate, exact aggregate,
failure retention, selection rules, and all v1/v2 constraints remain
unchanged. A focused test must freeze the per-query spelling and continue to
prove that nonzero exits, signals, malformed output, and verdict-bearing outer
timeouts fail closed.

Commit and push this amendment before capture. Because both streams must name
one exact commit/upstream, discard the otherwise valid v2 Axeyum stream for
credit and rerun Axeyum and reference from row one. No solver edit, timeout
increase, historical-outcome substitution, or partial-stream reuse is
authorized.
