# Lane: nat-gcd-dvd-mirrors — ℕ gcd/divisibility `ml430` mirrors

<!-- plan-section: lane-status -->

**Eleven mirrors closed (`WIP` -> mostly done, nat-gcd-dvd-mirrors,
2026-08-30).** Of the nineteen dispatchable in this area, closed:

- **Two pure flips, no new proof.** `F:ml430-nat-dvd-gcd-e5184fc5` and
  `F:ml430-nat-dvd-gcd-iff-b8485987` are `Nat.dvd_gcd`/`Nat.dvd_gcd_iff`,
  which predate this session (`declare_gcd_semantics`, `nat_prelude/gcd.rs`).
  The rendered type matches `formal.statement` exactly; closed by evidence
  only.
- **Nine new proofs**, all in the new file
  `crates/axeyum-lean-kernel/src/nat_prelude/gcd_dvd_mirrors.rs`, wired in
  with one `declare_gcd_dvd_mirrors` call:
  `Nat.dvd_mul_left`, `Nat.dvd_mul_left_of_dvd` (not in the original
  nineteen-item list but dispatchable in the same shape-search sweep and
  equally cheap — `dvd_mul_right_of_dvd` + `mul_comm`),
  `Nat.eq_zero_of_gcd_eq_zero_{left,right}`, `Nat.dvd_mod_iff_gen`,
  `Nat.div_mul_cancel`, `Nat.dvd_iff_mod_eq_zero`, and
  `Nat.div_gcd_pos_of_pos_{left,right}`.

All nine new declarations are axiom-free (`nat: axiom=0 opaque=0
quotient=0`), registered in `theorem_names`/`the_build_is_deterministic`'s
pin (669 -> 676 after the first seven, -> 678 (`93 + 585`) after the two
`div_gcd_pos_of_pos_*` theorems), and covered by the environment-derived
`every_nat_declaration_is_checked_and_axiom_free` assertion. Full
`nat_prelude::` sweep: 181 passed, 0 failed.

Every fact's `checker_command` was run directly (not just written): the
exact-name `grep -Ec '^Nat\.<name>[[:space:]]'` was checked to discriminate
against the substring-overlapping sibling in each case that has one
(`dvd_gcd` vs `dvd_gcd_iff`, `div_mul_cancel` vs `div_mul_cancel_of_dvd`,
`div_gcd_pos_of_pos_left` vs `_right`), and `nat_axiom_inventory
--require-axiom-free nat` was run and confirmed `nat: axiom=0 opaque=0
quotient=0` after every batch.

Partition check before touching any fact: all eleven are `train`/
`development` in `artifacts/autogenesis/nursery-v2-extension.json` — none
held-out.

`python3 scripts/check-fact-depends-derived.py --fix` was run after each
batch (flipping `Nat.dvd_gcd`'s status made every fact whose proof term
already used it newly require the edge — the dependency was always in the
proof term, only the ledger edge was missing). `validate-facts.py`: 2219
facts checked, 0 errors throughout.

**Three targets remain open, genuinely harder — not mis-sized, checked
against the actual proof strategy needed:**

- `F:ml430-nat-dvd-gcd-mul-iff-dvd-mul-0afe640a`
  (`k ∣ k.gcd n * m ↔ k ∣ n * m`) and
  `F:ml430-nat-dvd-gcd-mul-gcd-iff-dvd-mul-07fec722`
  (`k ∣ k.gcd n * k.gcd m ↔ k ∣ n * m`) both reduce cleanly to a
  distributive law the prelude does **not** have:
  `gcd (a*c) (b*c) = (gcd a b) * c` (`Nat.gcd_mul_right` in Mathlib). With
  that lemma, `0afe640a` is `k ∣ gcd(k,n)*m ↔ k ∣ gcd(k*m,n*m) ↔ (via
  dvd_gcd_iff) k∣k*m ∧ k∣n*m ↔ (k∣k*m trivial via dvd_mul) k∣n*m`. I
  verified this route numerically (a handful of cases) but did **not**
  attempt the distributive lemma itself — it is a real induction (not a
  case split), most naturally via strong/well-founded induction mirroring
  `declare_executable_gcd`'s own recursion, and sizing it honestly needs
  more than the time this lane had left. `nat_prelude/lcm_gcd_lemmas.rs`
  and `nat_prelude/gcd.rs` have no `gcd_mul_*` distributive lemma under any
  spelling (checked both files in full, not just grep).
- `F:ml430-nat-dvd-mul-ebd102e2`
  (`k ∣ m*n ↔ ∃ k₁ k₂, k₁∣m ∧ k₂∣n ∧ k₁*k₂ = k`) is a genuinely different
  kind of statement — an existence claim over a factorization of `k`
  compatible with `m*n`'s own factor structure, closer to unique
  factorization than to gcd algebra. I did not find a short route through
  existing prelude lemmas and did not attempt a from-scratch construction.
- `F:ml430-nat-dvd-mul-gcd-iff-dvd-mul-f9517e6b` (`k ∣ n*gcd(k,m) ↔ k∣n*m`,
  found via the frontier script, not in the original nineteen) has the
  same `gcd_mul_right`-shaped blocker as the two above.

**Next step for whoever picks this up:** build
`Nat.gcd_mul_right : ∀ a b c, gcd(a*c, b*c) = gcd(a,b)*c` in
`nat_prelude/lcm_gcd_lemmas.rs` (or a new file) via well-founded induction
mirroring `declare_executable_gcd`'s Euclidean descent (`gcd(a*c,b*c)`
reduces via `mod(a*c,b*c) = mod(a,b)*c`, which itself needs a
multiplicative-distributes-over-mod lemma — check `mod_mul_lemmas.rs`
first, it may already have the piece). That one lemma unlocks three facts
at once (`0afe640a`, `07fec722`, `f9517e6b`).

`bash scripts/check-merge-hygiene.sh`: see commit history for the exact
line; ran clean (no conflict markers, ADR index fresh — this lane touched
no ADRs, generated-file freshness ok).

<!-- plan-section: landed-changes -->

| 2026-08-30 | `b410fb749` | New `nat_prelude/gcd_dvd_mirrors.rs`: seven theorems, one `declare_*` call. |
| 2026-08-30 | `c20464d53` | Register the seven in `theorem_names`, recount `the_build_is_deterministic` pin. |
| 2026-08-30 | `935dde5e2` | Close nine ml430 facts (two flips, seven new) + depends_on cascade fix (24 files). |
| 2026-08-30 | `d92fb202d` | `div_gcd_pos_of_pos_{left,right}` — two more theorems, shared helper. |
| 2026-08-30 | `126aee313` | Close the two `div_gcd_pos_of_pos_*` facts + depends_on fix. |
| 2026-08-30 | `d255ef6e2` | rustfmt fix. |
