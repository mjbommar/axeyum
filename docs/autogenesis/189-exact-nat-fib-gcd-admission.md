# Exact `Nat.fib_gcd` admission

Date: 2026-08-21

Registration prestate: `d357b330705c8b1817260bfb3e14618d52de9643`

## Result

The flywheel converted the twice-reconstructed, byte-identical, empty-footprint
capsule for exact Mathlib 4.30 `Nat.fib_gcd` into durable ledger knowledge. The
frontier selected `F:ml430-nat-fib-gcd-d1d98407`; the caller supplied no fact,
route, checker, status, footprint, or evidence row.

The registered operation binds the exact capsule, goal, declaration, result
manifest, five direct theorem dependencies, four fresh imports, and two fixed
reconstructions. The capsule checker also binds the surface proposition by its
SHA-256 identity. No Mathlib proof body or tactic trace was consulted.

## Crash-safe admission

The first application stopped after durable intent with exit status 75 and
left the fact byte-identical to its open prestate. Same-filesystem recovery then
performed exactly one authoritative ledger write and produced durable event
`25fa3ff173975871fca0633a71db276a5bf6208f0558095c37e318856bff1f7a`.

The immutable primary archive is
`/nas3/data/axeyum/autogenesis/admissions/d357b3307-mathlib-nat-fib-gcd-v1/`.

## Measured readiness delta

The authoritative DAG delta made exactly one descendant newly ready:

- `F:ml430-nat-fib-dvd-f80f3de1`

The preregistration projected two direct unlocks from theorem-level adjacency.
The second, `F:ml430-int-gcd-fib-73bdafc2`, correctly remains unready because it
also requires open premise `F:ml430-int-fib-neg-b4021d37`. The measured delta,
not the projection, controls the next action.

## Independent replay

Commit `e242b72b303884ed192243df8ed19895848976a8` reproduced the episode in a
detached clean worktree. It reconstructed the historical open fact, generated
fresh execution and transaction identities, injected the same crash, recovered,
and reproduced the same one-child readiness delta. The replay semantic digest
is `b376dc0d2143d276516ac0506845ef254e60bac6579170a76c837326359f4043`.

The immutable replay archive is
`/nas3/data/axeyum/autogenesis/replays/e242b72b3-nat-fib-gcd-v1/`.

## Reproduction

```sh
python3 scripts/check-autogenesis-statement-reflexivity-admission.py \
  --manifest artifacts/autogenesis/mathlib-nat-fib-gcd-admission-v1.json
python3 scripts/check-autogenesis-fact-operation.py \
  --fact artifacts/facts/F-ml430-nat-fib-gcd-d1d98407.json
```

This grants one theorem admission and no held-out evaluation credit. The next
mathematical target is the newly ready `Nat.fib_dvd`; `Int.gcd_fib` remains over
the horizon behind `Int.fib_neg`.
