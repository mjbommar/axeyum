# Lane: gcd-mul-right — `Nat.gcd_mul_right` and its three ml430 mirrors

<!-- plan-section: lane-status -->

**Done (`gcd-mul-right`, 2026-08-30).** `docs/plan/status/331-nat-gcd-dvd-mirrors.md`
left three `ml430` facts open, all blocked on one missing distributive lemma:
`Nat.gcd_mul_right : ∀ a b c, gcd (a*c) (b*c) = gcd a b * c`.

**Verified the lemma was genuinely absent, not a naming miss**, before writing
any induction: grepped `nat_prelude/gcd.rs` and `nat_prelude/lcm_gcd_lemmas.rs`
in full for any `gcd_mul_*` spelling (nothing), and `int_prelude/gcd.rs`'s own
module doc (around its `Int.gcd_div` construction) states explicitly that
neither `Nat.gcd_mul_left` nor `gcd_mul_right` exists in this development and
that building either needs a fresh strong-induction principle over `gcd`'s
well-founded recursion. (`Int.gcd_mul_right`, in that same file, is an
unrelated coprimality-descent proposition sharing the Mathlib name — checked
and ruled out as a transportable shortcut.)

**Built it**: `crates/axeyum-lean-kernel/src/nat_prelude/gcd_mul_right.rs`,
well-founded induction on the first argument mirroring `declare_gcd_bezout`'s
WF-fix scaffolding (`bezout.rs`) exactly — same relation (`lt_well_founded`),
same `family`/`step_motive`/`step` pattern. Two supporting pieces, both new:

- `mul_mod_mul_right_eq : mod(n*c, m*c) = (mod n m)*c` for positive `m` (built
  via `div_mod_reconstructed` + `div_mod_unique`, mirroring `mod_mul_eq`'s
  proof shape in `mod_mul_lemmas.rs`).
- `gcd_unfold_pos : gcd x y = gcd (mod y x) x` for arbitrary positive `x`,
  generalizing `gcd_succ` (which needs its first argument literally of shape
  `succ _`) the same way `div_mod_reconstructed` generalizes `div_mod_exec`.

Wired in as the LAST `declare_*` call in `build_nat_prelude`.

**Then closed all three mirrors**: `crates/axeyum-lean-kernel/src/nat_prelude/gcd_mul_right_mirrors.rs`.
All three reduce to one shared argument (`dvd_gcd_scaled_iff`): rewrite
`gcd(a,b)*c` to `gcd(a*c,b*c)` via `gcd_mul_right`, unpack via `dvd_gcd_iff`
into `(k∣a*c) ∧ (k∣b*c)`, and drop the first conjunct since `k∣a*c` always
holds (`dvd_mul`). `dvd_mul_gcd_iff_dvd_mul` needs `mul_comm` to move the
scaling factor from right to left; `dvd_gcd_mul_gcd_iff_dvd_mul` applies the
shape with `c := gcd(k,m)` and chains one more `iff_trans` against the
already-proved `dvd_mul_gcd_iff_dvd_mul` (declared second, for this reason).

- `F:ml430-nat-dvd-gcd-mul-iff-dvd-mul-0afe640a` — proved.
- `F:ml430-nat-dvd-mul-gcd-iff-dvd-mul-f9517e6b` — proved.
- `F:ml430-nat-dvd-gcd-mul-gcd-iff-dvd-mul-07fec722` — proved (depends on the
  fact above).

**Verification, per the standing non-negotiable (concrete AND free-variable,
not either):**

- `gcd_mul_right_holds_at_concrete_and_symbolic_instances`: concrete
  discriminating triple `(4,6,5)` with a negative-numeral control, the base
  case `(0,7,3)`, and a symbolic restatement via a fresh `f.theorem` at a
  genuinely free `(a,b,c)`.
- `gcd_mul_right_mirrors_apply_at_concrete_and_symbolic_instances`: for each
  of the three mirrors, the statement shape at a concrete triple
  (independently-built expected `Iff`, catching a swapped argument), the
  LOGICAL CONTENT by applying `Iff.mp` to a real `dvd_refl` proof witness and
  confirming the target type comes out right (not just that the shape
  type-checks), and the symbolic restatement at a free `(k,n,m)`.

All four new declarations are axiom-free (`nat: axiom=0 opaque=0 quotient=0`),
registered in `theorem_names`, and the `the_build_is_deterministic` pin was
recounted by RUNNING the test and reading the reported value (93 + 602 = 695),
not by adding the delta by hand. Full `nat_prelude::` sweep: **183 passed, 0
failed**. `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`
clean. `rustfmt --edition 2024 --check` clean on every touched file.

Every fact's `checker_command` was run directly, both directions: the
anchored `nat_theorem_inventory` grep gives count 1 for the real name and
exits non-zero (fails closed, `0 theorems` on stdout) for a bogus one; cross-
checked for substring overlap against the two sibling names in one combined
inventory (no false match). `nat_axiom_inventory --require-axiom-free nat`
confirmed `axiom=0 opaque=0 quotient=0` after the batch.

`python3 scripts/check-fact-depends-derived.py --fix` was run after flipping
the three facts (each proof term uses `Nat.dvd_gcd_iff`/`Nat.dvd_mul`/
`Nat.mul_comm`/the sibling mirror, none originally recorded — added from the
proof term, not hand-transcribed). `python3 scripts/validate-facts.py`: 2220
facts checked, 0 errors, `missing_edges=0`.

Partition check before touching any fact: all three are `train` in
`artifacts/autogenesis/nursery-v2-extension.json` — none held-out.

**Nothing left open from this lane's scope.** The prior lane's third open
target, `F:ml430-nat-dvd-mul-ebd102e2` (`k ∣ m*n ↔ ∃ k₁ k₂, k₁∣m ∧ k₂∣n ∧
k₁*k₂ = k`), is a genuinely different kind of statement (a factorization
existence claim closer to unique factorization than to gcd algebra) and was
not attempted here — it does not depend on `gcd_mul_right`.

`bash scripts/check-merge-hygiene.sh`: see commit history for the exact line.

<!-- plan-section: landed-changes -->

| 2026-08-30 | `9a773bac4` | wip: `Nat.gcd_mul_right` proof term, not yet registered in coverage list. |
| 2026-08-30 | `dcd876d2c` | `Nat.gcd_mul_right` admitted, axiom-free, registered, tested (concrete + symbolic). |
| 2026-08-30 | `4b9d27239` | New `nat_prelude/gcd_mul_right_mirrors.rs`: all three ml430 mirrors, registered, tested. |
| 2026-08-30 | `52dbe8dad` | Flip the three facts to `proved` + `depends_on` cascade fix (3 files). |
