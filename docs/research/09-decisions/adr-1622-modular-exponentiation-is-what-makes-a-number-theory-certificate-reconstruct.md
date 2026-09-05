# ADR-1622: Modular exponentiation, not a bigger numeral budget, is what makes a number-theory certificate reconstruct

Status: accepted
Date: 2026-09-04
Lane: `cas-reconstruct`
Roadmap: W1-13 (the ADR-0601 SS2 `cas-internal` residue) — the "drive it down" half of ADR-1617's measurement

Index-summary: The `cas-internal` residue falls 46 → 45 (76.7% → 73.8%) by
reconstructing the CRT family in full and the Pratt family up to a measured
prime ceiling; the enabling move is rebuilding the CAS checker's own `pow_mod`
out of `Int.modEq_mul_general`, so the kernel never forms `a^(n-1)`.
Index-status: Accepted

**Supersedes:** nothing. **Extends:** ADR-0601 §2, ADR-1617.

## Context

ADR-1617 and `artifacts/measurements/cas-internal-residue-2026-09-04.md`
measured the ADR-0601 §2 residue: **60 `cas-certificate` facts, 14
`kernel-reconstructed`, 46 `cas-internal` (76.7%)**, concentrated in number
theory, hypergeometric/binomial identities, GF(2) and sum-of-squares. That
measurement was explicitly measurement-only and named the four number-theory
certificates (Pratt, CRT, factorization, compositeness) as one of the four
cheapest bridges. This lane builds it.

## The cost comparison that chose the families

The brief nominated Pratt as the strongest candidate. Measuring first changed
the answer to *both* Pratt **and** CRT, for a reason that is not about proof
difficulty at all.

Every `Nat` numeral in this kernel is unary, so the cost of a reconstruction
is set by the **largest numeral the kernel is made to form**, not by how many
lemmas the argument uses. Measured against each candidate family's own ledger
fact:

| family | fact's instances | largest numeral a naive reconstruction forms | verdict |
|---|---|---|---|
| `cas-ntheory-crt-certificate` | six systems, every numeral ≤ 105 | 105 | **reconstructs in full** |
| `cas-ntheory-pratt-certificate` | headline `2^89 − 1` (27 digits) | `a^(n−1)`, astronomically large | reconstructs only below a measured ceiling |
| `cas-ntheory-factorization-certificate` | includes `2147483647` and `1999966` | 2 147 483 647 | out of reach for two of eight instances |
| `cas-ntheory-composite-certificate` | includes `1000000` | 1 000 000 | out of reach for one of five instances |
| hypergeometric (9 facts) | binomial identities | needs `Nat.choose` identities that do not exist | not costed here |
| GF(2) (6), SOS (3) | — | need carriers that do not exist | not costed here |

So CRT is the only one of the four whose **every** claimed instance the kernel
can reach, which is what lets its ledger fact flip honestly rather than being
split. Pratt is the one whose *engine* is worth building, because the same
engine is what any future modular-arithmetic certificate will need.

## The decision

**A number-theory certificate reconstructs by rebuilding the CAS checker's own
modular arithmetic out of kernel congruence lemmas — never by asking the kernel
to reduce the certificate's exponentiation.**

The naive route states `ModEq (ofNat n) (pow (ofNat a) (n−1)) one` and closes
it with `Eq.refl`, letting the kernel compute. That forms `a^(n−1)` as a
literal unary numeral. `int_prelude/mult_order_tests.rs` already calls
`3^6 = 729` "the one expensive case" and confines it to a battery that builds
no proof terms. This is exactly the trap the existing Pratt fact's own notes
predicted ("it would hit the measured unary-numeral cost wall").

The route in `int_prelude/cas_pratt_bridge_tests.rs` is **square-and-multiply
with reduction at every step** — structurally the same algorithm as the CAS
checker's `pow_mod`, rebuilt from:

- `Int.pow_add a t t : a^(t+t) = a^t · a^t` and `Int.pow_succ a t : a^(t+1) = a^t · a`
  to split the exponent;
- `Int.modEq_mul_general : ModEq n a b → ModEq n c e → ModEq n (a·c) (b·e)` —
  chosen over the positivity-scoped `Int.modEq_mul` precisely because it is
  **unconditional in the modulus**, so no `0 < n` obligation threads through
  every one of the `O(log n)` steps;
- one `Eq.refl` on `emod` per step to renormalise the residue;
- `Int.modEq_trans` to chain.

The largest numeral the kernel ever forms is bounded by `n²`.

The CRT inconsistency direction (`int_prelude/cas_crt_bridge_tests.rs`) is not
an evaluation at all: `∀ x : Int, ModEq mₗ x aₗ → ModEq m_r x a_r → False` is
universally quantified, so no reduction can close it. It goes through
`Int.modEq_of_mul_left` at `g = gcd(mₗ, m_r)`, then `modEq_symm`/`modEq_trans`
to `ModEq g aₗ a_r`, which unfolds to a false equation between two distinct
numerals.

## Where it stops — the measured ceiling

`the_cost_ladder_is_measured` walks a ladder of primes, proving
`a^(n−1) ≡ 1 (mod n)` at the CAS's own witness for each, and prints the
wall-clock cost. Measured 2026-09-04 on the shared dev box (`--release`,
`--test-threads=4`, other lanes active — so these are upper bounds, not a
clean-room benchmark):

| `n` | witness | exponent | wall clock |
|---|---|---|---|
| 47 | 5 | 46 | 0.83 s |
| 101 | 2 | 100 | 7.8 s |
| 251 | 6 | 250 | **398 s** |
| 509 | — | — | killed, not waited out |

The `251` rung is 51x the `101` rung for 2.5x the modulus, so the cost is
superlinear in `n` well past the `n^2` numeral size — `Nat.mod` on a unary
numeral is itself superlinear. `509` was killed rather than measured, because
it holds the host-wide cargo lock every other lane needs; that is a deliberate
non-measurement and is recorded as one rather than extrapolated into a number.

So: **`251` is the last prime this route certifies at all, and `101` is the
last one a gate can carry.** The shipping `RECONSTRUCTED` set stops at 47 (the
whole set, trees included, is well inside a second) and `COST_LADDER` at 101.

For contrast, the naive route's wall sits **below `n = 20`**: `2^18 = 262144`
as a unary numeral, where the reducing route at `n = 251` never forms anything
above `251² = 63001`. So the engine buys roughly an order of magnitude in the
modulus, not an unbounded win — the ceiling is real, it has just moved.

**`2^89 − 1` remains out of reach and the ledger says so.** Its fact
(`F:cas-ntheory-pratt-primality-mersenne89`) stays `cas-internal` — flipping it
on the strength of small-prime evidence would be exactly the overstatement
ADR-0622's substance gate exists to catch. The kernel-reconstructed Pratt
instances are registered as a **separate** fact, per ADR-0603's graded
statement family.

## What is reconstructed, and what is not

For Pratt, three theorem families per prime in the certificate tree, matching
`check_primality_certificate`'s guards one for one: `Check.pratt_factorization_<n>`
(G6, completeness), `Check.pratt_fermat_<n>` (G8) and
`Check.pratt_order_<n>_q<q>` (G9, one per factor base). For CRT:
`Check.crt_congruence_<id>_<i>` (R3), `Check.crt_least_modulus_<id>` (R4),
`Check.crt_canonical_<id>` (R2) and `Check.crt_inconsistent_<id>` (R6).

**Neither route proves the theorem the certificate is a certificate for.**
Pratt reconstructs the certificate's *arithmetic conditions*; the step from
those conditions to primality is Lucas's theorem and is not derived. This is
the same boundary `rat_prelude::cas_geometry_pair_bridge_tests` draws — it
proves the cofactor identity and not the geometric conditional — and both
modules' doc comments state it in full.

### What the missing Lucas half would cost

`Int.IsOrder`, `Int.order_exists` and `Int.pow_modeq_one_iff_order_dvd`
(ADR-1598) already supply the first half: the order `k` exists, and G8 gives
`k ∣ (n−1)` while G9 gives `k ∤ (n−1)/q` for each factor base. The missing
step is

> `k ∣ m`, and `k ∤ m/q` for every prime `q ∣ m`, implies `k = m`.

For a *concrete* `m` this is a bounded case analysis over the divisors of `m`,
each of which needs a `Nat.dvd` refutation — `m+1` cases for `m = n−1`, so
`O(n)` term-building work per prime, which is the cost the Pratt certificate
exists to avoid. For a *general* `m` it needs divisor enumeration this prelude
does not have. Getting from there to primality needs additionally
`totient n = n − 1 ↔ n prime`, of which `int_prelude/euler_totient.rs` has
only one direction. That is the shape of the next increment, and it is a
prelude-development task, not a bridge task.

## The residue, before and after

`python3 scripts/check-cas-internal-residue.py --report`:

```
before (ADR-1617, 2026-09-04):
cas-certificate: 60 total -- kernel-reconstructed 14, cas-internal 46, unrecognized 0
  cas-internal residue share: 76.7%

after (this lane):
cas-certificate: 61 total -- kernel-reconstructed 16, cas-internal 45, unrecognized 0
  cas-internal residue share: 73.8%
```

Per fragment, the three rows that moved:

| fragment | before | after |
|---|---|---|
| `cas-ntheory-crt-certificate` | 0 reconstructed / 1 cas-internal | **1 / 0** |
| `cas-ntheory-pratt-certificate` | 0 / 1 | 0 / 1 (unchanged: `2^89 - 1` is out of reach) |
| `cas-ntheory-pratt-certificate-kernel-reconstructed` | did not exist | **1 / 0** (new fact) |

`scripts/check-cas-internal-residue.ratchet` regenerated with `--update`, so
both new `kernel-reconstructed` rows are now a floor; the gate reports
`OK: 16 kernel-reconstructed ... (floor 14, all held)`.
`scripts/check-cas-substance.py` reports
`OK: 16 ... carry a checked cas_substance block (ratchet floor 14, all held)`.
Both new facts declare shape `evaluation` with `certificate: null` and a
`derivation_declined_reason`, which is the self-reported standing ADR-0622
already records for 8 of the previous 14.

## The next-cheapest family

Per the cost table above, in order:

1. **`cas-ntheory-factorization-certificate` (1 fact).** The product identity
   `∏ qᵢ^eᵢ = |n|` is an evaluation the engine here does not even need, and
   per-base primality is exactly this lane's Pratt route. Blocked only by the
   two large instances (`2147483647`, `1999966`) the fact currently claims;
   landing it means splitting the fact per ADR-0603, the same way Pratt was
   split here.
2. **`cas-ntheory-composite-certificate` (1 fact).** One `Eq Nat (mul d c) n`
   per instance; four of the five instances are already reachable and the
   fifth (`1000000`) is not.
3. **Hypergeometric (9 facts, the largest single family).** Needs
   `Nat.choose` identities — Pascal, symmetry, and the absorption law — which
   this prelude does not carry. That is prelude work of a different kind and
   should be scoped as such, not as a bridge.
4. **GF(2) (6) and SOS (3).** Both need carriers that do not exist. Unchanged
   from ADR-1617's reading.

## Consequences

- One new engine (`pow_modeq`) that any future modular-arithmetic
  reconstruction can reuse; it is the reason the ceiling is a few hundred
  rather than under twenty.
- Two ledger facts changed and one added; `scripts/check-cas-internal-residue.ratchet`
  regenerated so both new `kernel-reconstructed` rows become a floor.
- The residue is now a number that has been made to move once, by a route
  another lane can copy, rather than only measured.
- **A caution for whoever reads the counter next:** the residue's *absolute*
  count falls by one here while *two* reconstruction routes landed, because
  Pratt's headline instance is genuinely unreachable and its reconstruction is
  registered as a new fact rather than a flip. Reading the counter alone
  understates what landed; reading the per-fragment table does not.
