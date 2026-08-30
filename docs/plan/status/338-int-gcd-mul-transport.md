# Lane: int-gcd-mul-transport — the ℤ transport of `gcd_mul_right`'s mirrors, plus `Nat.dvd_add_iff_left`

<!-- plan-section: lane-status -->

**Done (`int-gcd-mul-transport`, 2026-08-30).** `docs/plan/status/335-int-dvd-mirrors.md`
left three `ml430` facts open, all blocked on `Nat.gcd_mul_right`.
`docs/plan/status/336-gcd-mul-right.md` built that lemma and its three `Nat`
mirrors within the hour. This lane merged both and did the ℤ transport.

**All four targets closed, no re-derivation needed at the `Int` layer:**

- `F:ml430-int-dvd-gcd-mul-iff-dvd-mul-12f61b99`
- `F:ml430-int-dvd-mul-gcd-iff-dvd-mul-22d6488e`
- `F:ml430-int-dvd-gcd-mul-gcd-iff-dvd-mul-8ea752a5`
- `F:ml430-nat-dvd-add-iff-left-332cbe04`

**The ℤ→ℕ transport held, and the mechanism is worth recording.** `Int.gcd a b
:= Nat.gcd (natAbs a) (natAbs b)` (`gcd.rs`), and `Int.dvd` is equivalent to
`Nat.dvd` on magnitudes in both directions
(`nat_abs_dvd_nat_abs_of_dvd`/`dvd_of_nat_abs_dvd`, `gcd.rs`), and `natAbs` is
multiplicative (`nat_abs_mul`, `gcd.rs`). Composing these three turns any
`k ∣ x*y` statement (`k, x, y : ℤ`) into `natAbs k ∣ natAbs x * natAbs y`, and
specializing `x := ofNat (k.gcd n)` lands on exactly the `Nat`-level
`dvd_gcd_mul_iff_dvd_mul` at `(natAbs k, natAbs n, natAbs m)` — the kernel
resolves `natAbs (ofNat c) ≡ c` and `Int.gcd k n ≡ Nat.gcd (natAbs k) (natAbs
n)` on its own via `def_eq` at `add_declaration` time (both are bare
delta/iota reductions), so no explicit bridging LEMMA is needed for either —
only the genuinely non-defeq step, `natAbs`'s multiplicativity, needs a real
proof term in the chain.

New file `int_prelude/gcd_scaled_mirrors.rs`:
`idvd_mul_iff_nat_dvd_mul(k,x,y) : Iff (idvd k (x*y)) (Nat.dvd (natAbs k)
(natAbs x * natAbs y))` is the general bridge; `int_dvd_gcd_scaled_iff(k,b,c) :
Iff (idvd k ((ofNat (k.gcd b))*c)) (idvd k (b*c))` specializes it and chains
against the `Nat`-level fact — this is `Int.dvd_gcd_mul_iff_dvd_mul` directly
at `(b,c) := (n,m)`. `Int.dvd_mul_gcd_iff_dvd_mul` commutes both sides of the
shape applied at `(b,c) := (m,n)` into place with `Int.mul_comm`, mirroring
`nat_prelude/gcd_mul_right_mirrors.rs`'s `dvd_mul_gcd_iff_dvd_mul` one layer
up. `Int.dvd_gcd_mul_gcd_iff_dvd_mul` applies the shape at
`c := ofNat (k.gcd m)` and chains one more `Iff.trans` against
`dvd_mul_gcd_iff_dvd_mul` — so that one had to be declared first, same
dependency order as the `Nat` file.

Detail moved to [`../notes/338-int-gcd-mul-transport.md`](../notes/338-int-gcd-mul-transport.md).

<!-- plan-section: landed-changes -->

| 2026-08-30 | `96dd8d93a` | wip: Int transport of gcd-scaled dvd mirrors, compiles but not yet run. |
| 2026-08-30 | `e75823399` | Close all 4 facts (3 Int gcd-scaled dvd + 1 Nat dvd_add_iff_left), evidence + depends_on. |
