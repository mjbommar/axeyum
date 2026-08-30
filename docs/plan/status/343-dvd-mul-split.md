# Lane: dvd-mul-split — the divisor-splitting iff (Mathlib's `Nat.dvd_mul`/`Int.dvd_mul`)

<!-- plan-section: lane-status -->

**Done (`dvd-mul-split`, 2026-08-30).** `F:ml430-nat-dvd-mul-ebd102e2` closed.
`F:ml430-int-dvd-mul-3a7b94cd` stays open — precise blocker below, not a
re-derivation of the "no short route" verdict two prior lanes already gave it.

## `Nat.dvd_mul_split` — closed

Two prior lanes called `k ∣ m*n ↔ ∃ k1 k2, k1∣m ∧ k2∣n ∧ k1*k2=k` a
factorization-existence statement with no short route. Both sized it before
`Nat.gcd_mul_right` existed (landed the same day, lane `gcd-mul-right`) and
neither reports having tried the gcd construction. With `gcd_mul_right` in
hand it is not a factorization problem at all:

- **Forward.** `k1 := gcd(k,m)`, `k2 := k/gcd(k,m)`. `k1 ∣ m` is
  `gcd_dvd_right` directly. `k1*k2=k` comes from eliminating `gcd_dvd_left`'s
  witness. The one piece of real content, `k2 ∣ n`: `k ∣ k*n` (`dvd_mul`) and
  `k ∣ m*n` (hypothesis) combine via `dvd_gcd` into `k ∣ gcd(k*n,m*n)`;
  `gcd_mul_right` rewrites the gcd to `k1*n`, giving `k ∣ k1*n`; substituting
  `k = k1*k2` gives `k1*k2 ∣ k1*n`; cancelling the positive common factor
  `k1` (`one_le_of_dvd_pos` + `mul_left_cancel_of_pos`, no case split on `k1`
  needed since `k1 ∣ k` and `k > 0` already force it) gives `k2 ∣ n`.
- **Reverse.** Fully uniform: `m*n = (k1*q1)*(k2*q2) = (k1*k2)*(q1*q2) =
  k*(q1*q2)` (a four-factor regroup, `mul_assoc` + `mul_left_comm`), no case
  split, works even when `k1` or `k2` is `0`.
- **`k=0` degenerate case: handled by DIRECT case split, not the general
  formula.** `h : dvd 0 (m*n)` gives `m*n=0` (`mul_eq_zero`), splitting into
  `m=0` (witnesses `(0,n)`) or `n=0` (witnesses `(m,0)`). This is exactly the
  corner the dispatching brief warned "a slick argument silently breaks" on:
  the general formula's `k2 := k/gcd(k,m)` does NOT reproduce a valid witness
  pair when `n ≠ 0 = m` — `gcd(0,m)=m`, `0/m=0`, forcing `k2=0` and needing
  `0 ∣ n`, false in general.

New file `crates/axeyum-lean-kernel/src/nat_prelude/dvd_mul_split.rs`, wired
in via one `declare_dvd_mul_split` call after `declare_gcd_mul_right_mirrors`/
`declare_dvd_add_iff_left`. **Not named `Nat.dvd_mul`**: that kernel name is
already taken by the unrelated trivial lemma `∀ a q, dvd a (a*q)`
(`nat_prelude.rs`'s pre-existing `dvd_mul` field) — declaring under Mathlib's
literal name would hit `DeclarationExists`, the `Nat.inverseIndex` collision
class. Named `dvd_mul_split` (checked free in both preludes before writing).

Detail moved to [`../notes/343-dvd-mul-split.md`](../notes/343-dvd-mul-split.md).

