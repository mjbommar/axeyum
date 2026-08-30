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

`Nat.dvd_add_iff_left` (new file `nat_prelude/dvd_add_iff_left.rs`) turned out
to be genuinely cheap, not merely "looks cheap": the existing
`dvd_add_iff_right(k,m,n,h : dvd k m) : Iff (dvd k n) (dvd k (m+n))`
instantiated with the summands swapped, `(k,n,m,h)`, gives
`Iff (dvd k m) (dvd k (n+m))` directly, and one `add_comm` transport turns
`n+m` into `m+n`. No new case split.

**Step 0 checks, before writing any code:** grepped for `dvd_add_iff_left`
across `nat_prelude/` (absent) and confirmed via `nat_theorem_inventory`
(exit 1, "no Nat theorem matches") before building it. The `int_prelude/gcd.rs`
module doc explicitly rules out its own `Int.gcd_mul_right` as a shortcut
(unrelated coprimality-descent proposition sharing the Mathlib name) — did not
reach for it.

**Verification, per the standing non-negotiable (concrete AND free-variable):**
every declaration here is proved directly over the `int_theorem`/`theorem`
combinators' genuinely free `k, n, m` (or `k, m, n`) fvars — there is no
concrete-instantiation shortcut in these proofs, so the kernel's acceptance
*is* the symbolic check. `int_theorem_inventory`/`nat_theorem_inventory`'s
rendered types were diffed character-for-character against each fact's
`formal.statement` (recorded per-fact in the evidence notes). Each
`checker_command` verified both directions: the anchored `grep -c` (`-ge 1`,
never piped through `grep -q`) requires the exact name followed by whitespace,
checked not to also match the closest substring-overlapping sibling
(`dvd_gcd_mul_iff_dvd_mul` vs `dvd_gcd_mul_gcd_iff_dvd_mul`,
`dvd_add_iff_left` vs the pre-existing `dvd_add_iff_right`), and a fabricated
name for each (`*_bogus_xyz`) makes the inventory tool exit 1, "no
Int/Nat declaration matches".

All four are axiom-free: `prelude_axiom_inventory --require-axiom-free
integer` -> `integer axiom=0`; `nat_axiom_inventory --require-axiom-free nat`
-> `nat axiom=0 opaque=0 quotient=0`. `int_prelude::` sweep: 49 passed, 0
failed (unchanged count — no new `#[test]`, only coverage-list entries).
`nat_prelude::` sweep: 183 passed, 0 failed (also unchanged). `derived_laws`
pin (`int_prelude_tests.rs`) 208 -> 211, a Rust array-length literal the
compiler itself enforces against the added entries (not hand-counted).
`the_build_is_deterministic` pin (`nat_prelude_tests.rs`) 93+602 -> 93+603,
recounted by running the test after adding one entry to `theorem_names`, not
by hand-incrementing.

`python3 scripts/check-fact-depends-derived.py --fix` regenerated
`depends_on` from each proof term (`F:int-dvd-of-nat-abs-dvd`,
`F:int-nat-abs-dvd-nat-abs-of-dvd`, `F:int-nat-abs-mul`,
`F:ml430-nat-dvd-gcd-mul-iff-dvd-mul-0afe640a`, `F:int-mul-comm` for the three
ℤ facts; `F:ml430-nat-add-comm-56a2d614`, `F:ml430-nat-dvd-add-iff-right-bf79c0cd`
for the ℕ fact). `python3 scripts/validate-facts.py`: 2220 facts checked, 0
errors, `missing_edges=0`.

Partition check before touching any fact: all four are `development` in
`artifacts/autogenesis/nursery-v2-extension.json` — none held-out.

`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`: clean.
`rustfmt --edition 2024 --check` on every touched/new file: clean.

**Nothing left open from this lane's scope.** The four dispatched targets are
all closed.

`bash scripts/check-merge-hygiene.sh`: see commit history for the exact line.

<!-- plan-section: landed-changes -->

| 2026-08-30 | `96dd8d93a` | wip: Int transport of gcd-scaled dvd mirrors, compiles but not yet run. |
| 2026-08-30 | `e75823399` | Close all 4 facts (3 Int gcd-scaled dvd + 1 Nat dvd_add_iff_left), evidence + depends_on. |
