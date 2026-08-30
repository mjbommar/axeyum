# Notes: 346-int-dvd-mul-split

Detail moved out of [`../status/346-int-dvd-mul-split.md`](../status/346-int-dvd-mul-split.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- **`c = 0`.** Handled by a DIRECT case split on `a = 0 ∨ b = 0`
  (`Int.mul_eq_zero`, applied after `zero_dvd_elim` turns
  `dvd 0 (a*b)` into `a*b = 0`) — exactly the corner the `Nat` proof hit and
  for the identical reason: the general `g1 := gcd(c,a)` construction needs
  `g1 ≠ 0` from `c ≠ 0`, so it cannot fire at `c = 0` at all. Witnesses
  `(0, b)` or `(a, 0)` respectively.
- **Sign, the axis `ℕ` does not have.** The witnesses are built so sign is
  never guessed or reconstructed. `c1 := ofNat(Nat.gcd(natAbs c, natAbs a))`
  is manifestly nonnegative. `c2 := w` comes from an **`Int`-level**
  `dvd_elim` applied to `gcd_dvd_left c a : dvd c1 c` — the witness `w`
  already satisfies `c = c1*w` as a genuine `Int` equation, so whatever sign
  it needs to carry (e.g. `c=-6, a=4` gives `c1=2, w=-3`) falls out of that
  equation directly. The route the handoff correctly warned off — solving
  the `Nat` existential first and then guessing which of `±k1, ±k2` are the
  right signs via an `eq_or_eq_neg_of_nat_abs_eq`-style lemma — is never
  needed, because the `Int` witness is never reconstructed from a `Nat` one.

## Verification

- `scripts/cargo-serialized.sh test -p axeyum-lean-kernel --lib int_prelude::`
  — **50 passed, 0 failed** (up from 49; new coverage-inventory entry
  `derived_laws` caught immediately when the declaration was added without
  it, per `every_int_declaration_is_checked_and_axiom_free`).
- New test
  `dvd_mul_split_applies_at_a_discriminating_negative_and_free_degenerate_instance`
  exercises: `Iff.mpr` at a discriminating instance where `c` shares a
  factor with BOTH `a` and `b` (`c=6,a=4,b=9,c1=2,c2=3`, producing a real
  proof of `Int.dvd 6 36`, and confirming `a*b` actually computes to `36`);
  `Iff.mp` at a **negative** divisor (`c=-6,a=4,b=9`, witness `-6`,
  `36 = -6 * -6`); `Iff.mp` at the `c=0` degenerate branch with a genuinely
  **free** `b` (pushed into an explicit `LocalContext` as an
  axiom-declared variable, not a numeral).
- The whole theorem is additionally checked against a genuinely free
  variable by construction: `int_theorem`'s arity-3 declaration builds the
  ENTIRE proof (both directions, the full case split) over fresh bound
  `fvar`s for `c, a, b`, so `add_declaration`'s own kernel check IS the
  free-variable check — the concrete/negative/degenerate tests above are
  in addition to that, not a substitute for it.
- `cargo run --release -p axeyum-lean-kernel --example int_theorem_inventory -- dvd_mul_split`
  renders `Int.dvd_mul_split`'s type byte-for-byte matching the fact's
  `formal.statement` (`x0..x4 = c,a,b,c1,c2`); the same command with a
  fabricated name (`dvd_mul_split_bogus_xyz`) exits 1 with
  `error: no Int declaration matches ...`. Both directions run through
  `/usr/bin/grep -cE` explicitly (`[[:space:]]`, not a literal tab).
- `cargo run --release -p axeyum-lean-kernel --example prelude_axiom_inventory -- --require-axiom-free integer`
  → `integer: axiom=0`, exit 0 (the same run's `axreal: axiom=30` is the
  unrelated legacy axiomatized-reals package).
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` clean
  (one `doc_markdown` fix: `` `def_eq` `` needed backticks).
  `rustfmt --edition 2024 --check` clean on all three touched files.
- `F:ml430-int-dvd-mul-3a7b94cd` flipped to `proved`, `depends_on` expanded
  by `scripts/check-fact-depends-derived.py --fix` (18 edges — every base
  lemma the proof term actually calls, spanning both the `Int` and `Nat`
  preludes). `validate-facts.py` clean (0 errors, `missing_edges=0`).
  Partition confirmed `development` in
  `artifacts/autogenesis/nursery-v2-extension.json` (not held-out).

New file `crates/axeyum-lean-kernel/src/int_prelude/dvd_mul_split.rs`
(~650 lines — mostly local per-file-copy term-building helpers this
codebase's convention already uses throughout `int_prelude/gcd.rs`,
`euclid.rs`, `crt.rs`, etc.: `idvd_predicate`/`idvd_intro`/`idvd_elim`,
`int_exists_elim`, `zero_dvd_elim`, `nat_abs_zero_implies_int_zero`,
`imul_left_comm`/`imul_mul_mul_comm`, and Nat-level
`nat_dvd_elim`/`nat_dvd_intro`/`dvd_cancel_left_of_ne_zero` typed for an
`IntDev` context via `NatOps`'s default methods). Wired in via one
`dvd_mul_split::declare_dvd_mul_split(&mut d)?;` call placed LAST in
`int_prelude.rs`'s build (after `gcd_scaled_mirrors::declare_all`), since it
needs `gcd.rs`, `ring.rs`'s `Int.mul_eq_zero`, and the whole `Nat` prelude.
`split_exists_ty`/`split_exists_intro` marked `pub(super)` so the test file
can reuse them rather than duplicating the two-layer `Exists`/`And`
construction a third time.
