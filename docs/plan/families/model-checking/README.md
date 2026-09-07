# Family: hardware model checking

**State:** not entered. **Rank among cheap targets: 4** — and the best
architectural fit in the whole survey, independently picked by two of the four
research passes.

## Why it fits

| | |
|---|---|
| Input format | AIGER 1.9 — `axeyum-aig` already exports AIGER |
| Mandatory certificate | **is itself an AIG** |
| Checking a certificate | five SAT calls |
| Certificates required since | 2024 |

When certificates became mandatory, participation went from three entrants to
nine, and the winner beat the previous uncertified champion with every
certificate verified. That is direct evidence against the assumption that
requiring certificates suppresses a field.

## What entering requires

A model-checking front end. The certificate half — emit an AIG, check it with
our own SAT core — is the part closest to done, which is the opposite of the
usual ratio and the reason this ranks above larger SMT divisions.

## What it would prove

It is the only arena where the artifact we are best at producing *is the
required output*, so a result there is not a claim about our architecture; it
is the architecture working in someone else's harness.

## Owning document

[The survey](../../../research/02-ecosystems/competition-landscape-2026-09/adjacent-reasoning-arenas.md)
