# Lane: modeq-div-gcd — the modular-cancellation-by-gcd family

<!-- plan-section: lane-status -->

**Done (`modeq-div-gcd`, 2026-08-30).** All five facts closed:

- `F:ml430-nat-modeq-cancel-left-div-gcd-57ef8287`
- `F:ml430-nat-modeq-cancel-right-div-gcd-22a4f40d`
- `F:ml430-nat-modeq-cancel-left-div-gcd-cfca1225`
- `F:ml430-int-modeq-cancel-left-div-gcd-b2d407e8`
- `F:ml430-int-modeq-cancel-right-div-gcd-00cd73fa`

Two prior lanes (`nat-modeq-mirrors`, `docs/plan/status/329-nat-modeq-mirrors.md`;
`int-dvd-mirrors`, `docs/plan/status/335-int-dvd-mirrors.md`) had sized this
whole family as needing a new "divide-by-gcd factorization" slice, built
around `Nat.gcd_mul_right` (which landed for a sibling family within the
hour before this lane started). **`gcd_mul_right` turned out NOT to be what
unlocks this family, on either carrier.** What actually closes it:

- **Nat side**: `Nat.gcd_cofactors_coprime` (`bezout.rs`, pre-existing,
  neither prior lane had searched for it) plus `Nat.div_mul_cancel_of_dvd`.
  With `g := gcd(m,c)`, substituting `m=g*(m/g)`, `c=g*(c/g)` into
  `gcd c m = gcd m c = g` (`gcd_comm`) gives `gcd(g*(c/g))(g*(m/g)) = g`
  directly, and `gcd_cofactors_coprime` turns that into coprimality of the
  quotients with **no** need for `gcd_mul_right`. Zero new low-level
  arithmetic — this file is pure composition.
- **Int side**: `Int.gcd_div_gcd_div_gcd` already existed (`gcd.rs`) by the
  time this lane started, contrary to the `int-dvd-mirrors` handoff's
  framing of it as the missing piece. What was genuinely missing — and
  is new here — is a way to **cancel a shared nonzero factor from an
  `Int.dvd` statement**: this development had no `Int`-level multiplicative
  cancellation lemma under any name (every prior use of
  `mul_left_cancel_of_pos` routed through the `Nat` version on `natAbs`
  quantities instead). Built `imul_left_cancel_of_ne` from `Int.mul_eq_zero`
  (ℤ has no zero divisors) plus basic `add`/`neg`/`sub` algebra — no case
  split needed — then `idvd_cancel_scale` (existential-unpacking) on top of
  it.

**Verification, per the standing non-negotiable (concrete DISCRIMINATING
instance AND a genuinely free variable, not either alone):**

- Both carriers tested at `(m,c,a,b) = (6,4,1,4)`: `gcd(6,4) = 2`, not
  coprime — a coprime instance could not distinguish this family from the
  pre-existing coprime-only cancellation lemma (`Nat.mod_eq_cancel`; no Int
  analogue exists at all). Both sides also verified symbolically via a
  fresh restating theorem at genuinely free arguments.
- Nat negative control: the SAME proof rejected against the transposed
  conclusion (`4 ≡ 1 [MOD 3]`) — genuinely different from `1 ≡ 4 [MOD 3]`
  for the witness-based `ModEq` encoding.
- **Int negative control needed a different shape, and the first attempt
  was silently vacuous**: `Int.ModEq n a b := emod a n = emod b n` reduces
  `ModEq 3 1 4` and `ModEq 3 4 1` to the IDENTICAL closed proposition
  `Eq 1 1` once `emod` computes — transposing `a`/`b` is defeq-symmetric
  for any true concrete instance of this encoding, so it is not a real
  negative control here (unlike the Nat side's witness form). Caught
  because the test failed the WRONG way (accepted the transposed
  conclusion) — replaced with a wrong-MODULUS control (`ModEq 2 1 4`
  reduces to the genuinely false-shaped `Eq 1 0`), which correctly rejects.

**One genuine bug found and fixed, via `Kernel::render_lean` on both sides
of the `TypeMismatch`** (the standing technique for an opaque mismatch):
`mul_assoc(scale, modulus, u)` gives `Eq du scale_mod_u` directly — NOT
`Eq scale_mod_u du` — and a stray `symm()` in the Nat side's
`mod_eq_cancel_scale` helper had it backwards. The Int side's analogous
`mul_assoc` calls were built correctly on the first attempt (48/50 tests
passed immediately, only the registration-list failure), likely because
the bug was found and internalized on the Nat side first.

**Axiom-freedom confirmed on both carriers**: `nat_axiom_inventory
--require-axiom-free nat` → `axiom=0 opaque=0 quotient=0`;
`prelude_axiom_inventory --require-axiom-free integer` → `integer: axiom=0`
(the only nonzero row anywhere is the unrelated legacy `axreal: axiom=30`).

Full `nat_prelude::` sweep: 184 passed, 0 failed. Full `int_prelude::`
sweep: 50 passed, 0 failed. `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` clean. `rustfmt --edition 2024` clean on
every touched file.

Registered in `theorem_names` (Nat) / `derived_laws` (Int, pin recounted
by `scripts/recount-pinned-inventory.py`, 208 → 210, matches +2) and the
`the_build_is_deterministic` pin (Nat, recounted by running the test:
695 → 698, matches +3, never hand-incremented).

Every fact's `checker_command` run directly, both directions:
`nat_theorem_inventory`/`int_theorem_inventory` anchored `grep -cE`
against `^Nat\.<name>[[:space:]]` / `^theorem[[:space:]]+Int\.<name>[[:space:]]`
gives count 1 for the real name and 0 for a bogus one on every one of the
five, with the two `cancel_left_div_gcd`/`cancel_left_div_gcd_general`
Nat names cross-checked for substring overlap (none). `python3
scripts/check-fact-depends-derived.py --fix` added 15 edges (Nat) + 26
edges (Int) derived from the proof terms, including
`F:ml430-int-gcd-div-gcd-div-gcd-2db608dc`. `python3
scripts/validate-facts.py`: 2220 facts, 0 errors, `missing_edges=0`.

Partition check before touching any fact: the three Nat facts are `train`,
the two Int facts are `development`, in `nursery-v2-extension.json` —
none held-out.

**Nothing left open from this lane's scope.** `bash
scripts/check-merge-hygiene.sh`: see below.

<!-- plan-section: landed-changes -->

| 2026-08-30 | `932812b9c` | wip: `modeq_cancel_div_gcd.rs` Nat family (3 mirrors), not yet compiled. |
| 2026-08-30 | `82752e56e` | Nat family admitted, axiom-free, registered, tested (concrete discriminating + symbolic); fixed a `mul_assoc` direction bug found via `Kernel::render_lean`. |
| 2026-08-30 | `590477e33` | Flip the three Nat facts + `depends_on` cascade fix (3 files). |
| 2026-08-30 | `6ec2edf6f` | wip: `modeq_cancel_div_gcd.rs` Int family (2 mirrors), compiles. |
| 2026-08-30 | `30cb26f7a` | Int family admitted, axiom-free, registered, tested; new `Int.mul` cancellation-by-nonzero lemma (first in this development). |
| 2026-08-30 | `523e45393` | Flip the two Int facts + `depends_on` cascade fix (2 files). |
