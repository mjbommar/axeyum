# QF linear A5 IDL extended DL slice v1 result — 2026-08-11

## Outcome

The [preregistered structural candidate](qf-linear-a5-idl-extended-dl-slice-v1-preregistration-2026-08-11.md)
failed its first target observation and stopped. BubbleSort remained typed
`unknown`; the trace was byte-identical to the unchanged-binary replay. The
candidate was reverted before any other target, control, retained-decision, or
census run. No production solver diff remains.

## Exact observation

Candidate source was the clean local commit
`72a41ef432f5375f556d5e09699ac1cdc2520f73`, based on exact pushed
preregistration `713022df51a08891e03e5dd04cce0bfe826cb382`. Its 11,857,256-byte
release binary had SHA-256
`79253a15652c68e6545550be0ebb5c140c350d6b65f6e14282636bbdd3e58606`.
The group started at `2026-08-11T22:13:34Z` with one-, five-, and
fifteen-minute loads 6.04, 5.86, and 6.14.

The single 24,000 ms / 8 GiB worker exited 0 with zero stderr. It returned
`unknown` after the standard `dl-online` budget decline and the fallback's
construction timeout at 4,705 atoms / zero CNF variables. Wall time was 42.97
seconds and peak RSS was 179,604 KiB. JSONL SHA-256 was
`938b078ea545662a114043e68d88ac57d56621e5bd686bea28d61c79162107e1`,
identical to the earlier unchanged-binary BubbleSort replay.

The files remain outside the repository under
`/home/mjbommar/.cache/axeyum/a5-idl-dl-slice-v1-matrix`.

## Interpretation

The proposed predicate used the fallback's observed scale as a proxy for the
DL scan: more than 1,024 difference atoms and fewer than 128 numeric equality
gates. Its failure to change the route boundary proves that proxy is invalid
for BubbleSort. It does not contradict D2's 3/3 DL decisions with a larger
unchanged timeout; it shows that the actual DL scan shape must be measured
before choosing a production predicate.

Proceed only with the separately preregistered scan-telemetry increment. Do not
retry a threshold, global 21/3 split, pre-SAT change, or fallback optimization
from this result.
