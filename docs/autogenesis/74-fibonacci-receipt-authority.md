# Fibonacci receipt authority

Date: 2026-08-20

## Result

The exact direct library basis for `Nat.fib_coprime_fib_succ` is now
preregistered before semantic receipt issuance. Two fresh complete
reconstructions produced byte-identical authority observations with SHA-256
`739d9a4c6ce38576d6573547f1c98e052d6df80dca5334be36154026ebd01954`.
Neither run issued a receipt or changed the fact ledger.

The sorted dependency authority is:

| Direct theorem | Canonical declaration SHA-256 |
|---|---|
| `Axeyum.Autogenesis.fibAddTwo` | `982c676b0656664e807c5e195bbdbd43376d78dec029bb3c409df661de39edb4` |
| `Nat.add_comm` | `c05e6d0986251392c9b1bc9fcc2bd5d66de22c856b9669cdd993e9993d94f4f9` |
| `Nat.dvd_add_iff_right` | `4bc8146aabb20e59aa1b0a19f80588ac80656320031f12b61f96da3f94802cf0` |
| `Nat.dvd_gcd` | `325197e87bf46cc929ad03177c49e73de7054b446ec22f132c605af4d3c35e94` |
| `Nat.eq_one_of_dvd_one` | `bc5301b4f9dbd08785db127ca6512283d2125321be596b362129d339c80ffa37` |
| `Nat.gcd_dvd_left` | `7fa32fac2240feebdb94d6259f2bbab2dbb83059227286303efd7c306e5ad399` |
| `Nat.gcd_dvd_right` | `d3214bf5b657f399baa82c9e2817996b64ae26d688308dfa0641a6ed376fdef4` |
| `Nat.gcd_zero_left` | `f81aee8a1d8528ddf8b7be6007efbee190f2208cdef3dcfda9fa03a1f200175d` |

The canonical compact dependency-set digest is
`d407340befc681d6d9abd187bbfead1f6ca1a7395c7dcf908950fd9c4d02e4d5`.

## Receipt format boundary

The earlier checked semantic receipt intentionally accepts only proofs with no
direct theorem dependencies. That remains the correct contract for the
zero-premise Fibonacci recurrence and is unchanged.

ADR-0534 adds a separate dependency-bound format for ordinary library
theorems. Its authority must contain a nonempty, strictly sorted, unique list
of direct theorem names and canonical declaration identities. Issuance still
requires the exact preregistered target, goal, proof, theorem declaration,
operation and budget, plus an empty complete kernel-derived axiom footprint.
Any premise proof change therefore rejects even if its name is unchanged.

Transitive theorem rows are recorded and replayed as diagnostics, not expanded
premise authority. The canonical declaration identities already recursively
bind their dependency content under ADR-0350.

## Immutable evidence

The read-only authority pack is:

`/nas3/data/axeyum/autogenesis/reference-packs/b55bc977e-fibonacci-receipt-authority-v1/manifest.json`

Its manifest SHA-256 is
`b9eb358d0928be257084150998f4f57c87cbbe01040f2c43ac1a306810093b6b`.
The directory is mode `0555`; all three files are mode `0444`. The tracked
checker binds both identical runs, the implementation blob, exact candidate
pack, target stream, theorem identities, complete dependency rows and zero
receipt/evaluation/ledger counters.

## Reproduction

```sh
cargo run -q -p axeyum-lean-import \
  --example nat_gcd_succ_specialization -- \
  /path/to/nat-mod-invariant.ndjson \
  /path/to/r082.ndjson \
  /path/to/nat-gcd-bridge.ndjson \
  --exact-authority /path/to/fib-recurrence.ndjson

python3 scripts/check-autogenesis-nat-fib-coprime-premise-plan.py
```

## Next

Use exactly this dependency set with the sealed candidate identities to issue
the dependency-bound semantic theorem receipt in one fresh reconstruction and
reissue it identically in another. Only the resulting checked receipt may be
registered as evidence for the separate crash-safe fact transaction.
