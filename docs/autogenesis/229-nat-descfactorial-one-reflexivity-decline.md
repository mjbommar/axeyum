# `Nat.descFactorial_one` declines bare reflexivity — a family-shaped finding

Date: 2026-08-22

Plan context: [`226`](226-production-measurement-and-general-producer-plan.md) ·
[`228`](228-capsule-lane-retrospective.md)

## Fact

`F:ml430-nat-descfactorial-one-d4856d4a` — Mathlib's `Nat.descFactorial_one`:

```text
∀ (n : ℕ), n.descFactorial 1 = n
```

`train` partition, family `natural-factorial`, `depends_on: []` (dependency-ready),
`epistemic_status: open`, not named by any operation in
`artifacts/autogenesis/operations.json`.

## Result: decline

Attempted the one general, already-registered producer in this repository whose
`applicability.fact_ids` is plainly reusable in shape —
`bounded-pi-equality-reflexivity-v1`
(`crates/axeyum-lean-import/examples/statement_reflexivity_support/mod.rs`) —
against this fact's already-captured, hash-pinned Lean export
(`streams/r068.ndjson` under the frozen
`26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1` coverage root).

**Stage reached:** kernel typecheck of the constructed candidate declaration.
**Error:** `KernelError::DeclarationValueMismatch`.
**Outcome class:** `kernel-rejection:candidate-typecheck-failed`.

The full decline record, including hashes and reproduction commands, is
[`../../artifacts/autogenesis/mathlib-nat-descfactorial-one-reflexivity-decline-v1.json`](../../artifacts/autogenesis/mathlib-nat-descfactorial-one-reflexivity-decline-v1.json).

## Why, precisely

The producer is three lines of substance: strip the goal's binders, check the
terminal is an exact `Eq` application, and build
`fun binders => Eq.refl (lhs)`. It never inspects whether `lhs` and `rhs` are
actually equal — it relies entirely on the kernel to accept or reject that
proof, which is this repository's stated division of labour ("untrusted fast
search, trusted small checking").

Unfolding `Nat.descFactorial n 1` by iota alone:

```text
descFactorial n 1
  = (n - 0) * descFactorial n 0        -- recursive case
  = (n - 0) * 1                        -- base case of descFactorial
  = n * 1                              -- base case of subtraction
  = 0 + n                              -- Nat.mul recurses on its 2nd argument
```

`Nat.add` also recurses on its second argument. With `n` a free variable
(not a literal successor chain), `0 + n` cannot iota-reduce further — it is
stuck, and stuck terms are not definitionally equal to `n` for a symbolic `n`.
Closing that last step is `Nat.zero_add`, which Mathlib proves by induction,
not by `rfl`. So the kernel's rejection here is correct and expected: the goal
is externally **true** but not **definitional**, and the reflexivity producer's
only move is definitional equality.

This is not an adapter bug. The statement adapter (`import_statement_ndjson`)
succeeded — the fact reached the reflexivity producer at all, which 114 of 138
train/development rows never do (rejected earlier for referencing a trusted
declaration). It is also not a kernel bug: `DeclarationValueMismatch` is the
kernel correctly refusing a forged `rfl`.

## This generalizes — it is a cluster, not a one-off

The 2026-08-19 census (`artifacts/autogenesis/mathlib-reflexivity-coverage-v1.json`)
already classified the **same** outcome for 7 of 138 rows. Re-running the
row classifier fresh in this session against today's HEAD reproduced identical
`goal_sha256`/`proof_sha256`/outcome for all 7 (see the decline JSON's
`reproduction` block); the only per-row difference was an internal debug arena
index (`ExprId(N)`), which is not stable across builds and carries no semantic
weight.

All 7 share the same shape: a `Nat.descFactorial` / `Nat.ascFactorial` / `Nat.fib`
recursive identity whose base-case unfolding lands on a stuck
`0 + n` / `n + 0`-shaped term:

```text
F:ml430-nat-descfactorial-of-lt-fbcf5d26
F:ml430-nat-descfactorial-one-d4856d4a      <- this fact
F:ml430-nat-descfactorial-self-899fc0e0
F:ml430-nat-one-ascfactorial-8bacb017
F:ml430-nat-zero-ascfactorial-af4fcdca
F:ml430-nat-fib-add-two-b86e0c82            <- already proved, via a different capsule
F:ml430-mutation-7afa5ec620720a1501bf349d   <- a mutation fixture, not a real target
```

`F:ml430-nat-fib-add-two-b86e0c82` is useful independent confirmation: it is
already `proved` in this ledger through a bespoke, non-reflexivity capsule
operation, so the cluster is not mathematically closed to Axeyum — it is closed
to *this one producer*.

**What would move the cluster, not just this fact:** a producer one step more
capable than bare `Eq.refl` — for instance, one that may additionally apply
`Nat.zero_add` / `Nat.add_zero` / `Nat.mul_one` (already proved, axiom-free, in
this ledger as `F:nat-zero-add` and `F:nat-mul-one`) before falling back to
`rfl` on what remains. Registered against the 5 non-mutation, unproved siblings
above at once, that operation's `applicability.fact_ids` would have length 5,
not 1 — which is the generality this repository's provenance ledger currently
measures as zero across all 24 registered operations
([`228`](228-capsule-lane-retrospective.md)). This decline is deliberately
scoped to naming that gap, not to building the producer: doc 16's ask is to
aggregate typed declines by family and statement shape before choosing what to
build next, and this is one such aggregation, not a capsule.

## An unrelated but real finding along the way

`python3 scripts/check-autogenesis-reflexivity-coverage.py` **currently exits 1**
on this HEAD:

```text
autogenesis-reflexivity-coverage: proof-free coverage input no longer regenerates
```

Root cause: `artifacts/autogenesis/nursery-v1.json`'s train+development
population grew 138 → 157 under the ADR-0542 held-out repair
([`227`](227-held-out-partition-breach-result.md)), but the frozen reflexivity
census (`mathlib-reflexivity-coverage-v1.json`) was computed against the
138-row population and pins that count. The Python checker regenerates the
mapping from the **current** `nursery-v1.json` and compares it byte-for-byte
against the frozen one, so it now mismatches on population size alone — this
is retrospective item 4 in `228` ("regenerate every artifact downstream of the
population in the same commit") having actually happened, not merely being a
risk.

This does **not** put the fact-level finding above in doubt: the failing
Python check only verifies that the *aggregate* input still regenerates from
the live nursery manifest. The row-level Rust classifier
(`--example statement_reflexivity_coverage`) was run directly against the
still-intact, hash-pinned external artifact in this session and reproduced the
frozen result exactly (see the decline JSON). This is now a real red step in
`just check` / `./scripts/check.sh` (`autogenesis-reflexivity-coverage`,
`check.sh:95`) that this session did not introduce and did not fix — flagged
here rather than silently left for the next lane to discover as "my gate is
red and I don't know why."

## Verification

```sh
scripts/cargo-serialized.sh build -p axeyum-lean-import --example statement_reflexivity_coverage
cargo run -q -p axeyum-lean-import --example statement_reflexivity_coverage -- \
  /nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams \
  /nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/mapping.json \
  | python3 -c 'import json,sys; d=json.load(sys.stdin); print([r for r in d["rows"] if r["fact_id"]=="F:ml430-nat-descfactorial-one-d4856d4a"][0])'
```
