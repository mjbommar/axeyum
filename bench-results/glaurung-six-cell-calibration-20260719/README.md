# Glaurung deterministic six-cell calibration — 2026-07-19

This directory records the compact, repository-retained result of ADR-0273's
preregistered first-20 `tcpip.sys` calibration. The complete raw campaign is
retained outside Git at
`/nas4/data/workspace-infosec/.axeyum-six-cell-calibration-20260719.IYMKcA`.

The campaign completed all 42 tier-major, repetition-minor processes. Every
process exited successfully, produced one validator-clean v4 trace, analyzed the
same registered 20/338 function boundary for its tier, reproduced its complete
ordered outcome/finding/work vectors across all three repetitions, and recorded
zero wall-timeout or outer deadline stops.

Calibration is **rejected**. Z3 first qualifies at `rlimit=100000` (tier 9),
and Bitwuzla first qualifies at 4 termination polls (tier 2), but no registered
Axeyum progress-check limit makes both cold and warm cells decide at least 95%
of the tier's ordered checks. At the largest registered Axeyum limit, 8192,
cold decides 4233/4846 (87.35%) and warm decides 3280/4846 (67.68%); all 613
and 1566 remaining outcomes respectively are typed `resource-limit`.

Consequently ADR-0273 selects no triplet and authorizes no 338-function census.
The result is also a design warning for any follow-up: because cold Z3 is the
exploration authority, changing its limit changes the ordered check population.
Backend limits observed at different tiers must not be combined as though they
had been tested on one common stream. Any extension must first freeze the
qualifying Z3 authority limit and then calibrate shadow limits on that fixed
stream under a new zero-row protocol.

Identities:

- campaign SHA-256: `118e90a4d3577f9e4636d45e37391024851ecf4f169276c63aef7814912ec2ec`
- full analysis SHA-256: `46e8e29fee0d3293531c4e5743e861d9f8eb22163e056dbd74f82e86bb8d5e0c`
- executable SHA-256: `d96520a04d5dd4825957dc3e07e1fd11a24bad220c55baae539ec9f8a10db5f7`
- driver SHA-256: `ff965206a37f2c258b7199bc87b49ee12c834e5fc50f58dae2f3de66a57022ea`

[`result-summary.json`](result-summary.json) retains the tier counts needed to
audit the rejection without treating timing or incomparable work units as a
cross-solver result.
