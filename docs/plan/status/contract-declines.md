# Lane: contract-declines

## Status

**Open.** Investigating why every autogenesis contract dispatch declined.

## The question

On 2026-08-27 the autogenesis loop dispatched 27 facts through its two producer
contracts (`artifacts/autogenesis/producer-contracts/nat-coprime-family-v1.json`
and `int-modeq-family-v1.json`). All 27 declined: 15 `TrustedDeclaration`,
12 `TerminalNotClosed`, every one emitted from
`crates/axeyum-lean-import/examples/modeq_family_operation.rs`. Since then the
loop has produced nothing; `scripts/fact-frontier.py --json` reports 217
dependency-ready open facts, 0 admissible via any operation, 1 via a contract,
and 209 of the 217 as `proof-route-only` with no producer that could ever
match them.

Is it

- (a) the two contracts are aimed at the wrong shape,
- (b) one specific capability is missing that every dispatch hits, or
- (c) something else?

And: what is the minimum change that would make at least one of those 27
dispatches NOT decline?

## Landed changes

_(none yet)_
