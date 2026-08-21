# Exact `Nat.fib_dvd` construction and admission

Date: 2026-08-21

Registration prestate: `e8861458ebf0438518018f2a8bf5186bd92d21fd`

## Result

The newly ready Mathlib 4.30 proposition `Nat.fib_dvd` was reconstructed without
consulting its proof body. From `m ∣ n`, the target-owned divisibility laws show
`gcd m n = m`; congruence through Fibonacci plus the admitted `Nat.fib_gcd`
identifies `fib m` with `gcd (fib m) (fib n)`; the checked right-GCD divisor then
transports to the exact conclusion.

Two complete invocations produced the same 1,057,656-byte capsule, the same
observation, two target submissions, four fresh imports, and an empty kernel
axiom footprint. The exact direct dependencies are `Nat.fib_gcd` plus five
target-owned GCD/divisibility theorems. No `Iff`, `propext`, `Quot.sound`, proof
search, evaluation, or ledger write entered construction.

## Crash-safe admission and replay

The registered frontier selected exactly `F:ml430-nat-fib-dvd-f80f3de1`.
Application stopped after durable intent with exit 75, left the fact unchanged,
then recovery made exactly one authoritative write. Event identity:
`23d0be9a5e0ffcbaa488b76dd6f29dcf31c82342f1b1e044e2483d40d041e359`.

The immutable primary archive is
`/nas3/data/axeyum/autogenesis/admissions/e8861458e-mathlib-nat-fib-dvd-v1/`.

Commit `733126c0f351f0931f7eaf0b4f5f9f569f3aef44` independently reproduced the
entire episode in a detached clean worktree. Its semantic replay digest is
`37f2b39e4a00aab587ecd161f5d81da9eb7f323ea35c5a284c7de593d8728daf`,
retained at
`/nas3/data/axeyum/autogenesis/replays/733126c0f-nat-fib-dvd-v1/`.

The fact is an honest DAG leaf, so the measured newly-ready set is empty. The
next strategic move is not to manufacture an unlock: qualify `Int.fib_neg`, the
remaining real premise of `Int.gcd_fib`.

## Reproduction

```sh
python3 scripts/check-autogenesis-statement-reflexivity-admission.py \
  --manifest artifacts/autogenesis/mathlib-nat-fib-dvd-admission-v1.json
python3 scripts/check-autogenesis-fact-operation.py \
  --fact artifacts/facts/F-ml430-nat-fib-dvd-f80f3de1.json
```
