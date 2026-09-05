# Lane: cas-reconstruct — drive the ADR-0601 §2 `cas-internal` residue down (W1-13)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, cas-reconstruct, 2026-09-04).** ADR-1617 measured
the residue at **60 `cas-certificate` facts, 14 kernel-reconstructed, 46
`cas-internal` (76.7%)** and stopped there. This lane made it move:
**61 total, 16 kernel-reconstructed, 45 `cas-internal` (73.8%)**, with
`scripts/check-cas-internal-residue.ratchet` regenerated so both new rows are
a floor. ADR-1622 carries the reasoning.

**The enabling move, for whoever bridges the next family.** The reason number
theory sat in the residue is not proof difficulty; it is that every `Nat`
numeral here is unary, so stating `ModEq (ofNat n) (pow (ofNat a) (n−1)) one`
and closing it by `Eq.refl` makes the kernel form `a^(n−1)` as a literal
numeral. That walls **below `n = 20`**. `int_prelude/cas_pratt_bridge_tests.rs`
instead rebuilds the CAS checker's own `pow_mod` — square-and-multiply with
reduction at every step — out of `Int.pow_add`, `Int.pow_succ`,
`Int.modEq_mul_general` (**unconditional in the modulus**, which is why it and
not the positivity-scoped `Int.modEq_mul`: no `0 < n` obligation threads
through the `O(log n)` steps) and `Int.modEq_trans`. Largest numeral formed:
`n²`. Reuse `pow_modeq` for any future modular-arithmetic certificate.

**Where it stops, measured, not assumed** (`--release`, shared box, other lanes
active): `n = 47` 0.83 s, `n = 101` 7.8 s, `n = 251` **398 s**, `n = 509`
killed rather than waited out (it holds the host-wide cargo lock). So `251` is
the last prime the route certifies at all and `101` the last a gate can carry;
the shipping set stops at 47 and the ladder at 101. The cost is superlinear in
`n` well past the `n²` numeral size — `Nat.mod` on a unary numeral is itself
superlinear — so the engine buys about an order of magnitude in the modulus,
not an unbounded win.

**Two facts moved, and the two counters do not tell the same story.**
`F:cas-ntheory-crt-certificate` flipped whole: every numeral in all six of its
systems is ≤ 105, so the kernel reaches **every instance it claims**, which is
the only one of the four number-theory families that is true of.
`F:cas-ntheory-pratt-primality-mersenne89` did **not** flip and must not — its
headline is `2^89 − 1`, which no numeral budget reaches, so the reconstruction
is a **new** fact (`F:cas-ntheory-pratt-certificate-kernel-reconstructed`) per
ADR-0603's graded statement family. Net: `cas-internal` falls by one while two
routes landed. Read the per-fragment table, not the total.

**What neither route establishes, stated as precisely as what they do.**
Pratt reconstructs the certificate's *arithmetic conditions* (G6/G8/G9) and
**not** primality — the Lucas implication is absent. Both modules' doc comments
list that plus four more disclosures apiece, and both facts carry them in
`axiom_footprint`.

**The missing Lucas half, sized.** `Int.IsOrder`, `Int.order_exists` and
`Int.pow_modeq_one_iff_order_dvd` (ADR-1598) give `k ∣ (n−1)` and
`k ∤ (n−1)/q`. What is missing is "`k ∣ m` and `k ∤ m/q` for every prime
`q ∣ m` implies `k = m`" — a bounded divisor case analysis (`O(n)` cases at
concrete `m`, which is the cost the certificate exists to avoid; general `m`
needs divisor enumeration this prelude lacks) plus the reverse direction of
`totient n = n − 1 ↔ n prime`, of which `int_prelude/euler_totient.rs` has one
direction only. That is prelude work, not bridge work.

**Next-cheapest families, in order** (ADR-1622 §"The next-cheapest family"):
factorization (blocked only by its two large instances — split the fact the way
Pratt was split), compositeness (four of five instances already reachable),
then hypergeometric (9 facts, the largest family, needs `Nat.choose`
identities that do not exist), then GF(2)/SOS (need carriers that do not
exist).

<!-- plan-section: landed-changes -->

| 2026-09-04 | cas-reconstruct | ADR-1622: CAS Pratt + CRT certificates reconstruct into kernel terms; `cas-internal` residue 46 → 45 (76.7% → 73.8%), ratchet floor 14 → 16 |
