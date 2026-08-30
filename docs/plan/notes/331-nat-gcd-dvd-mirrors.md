# Notes: 331-nat-gcd-dvd-mirrors

Detail moved out of [`../status/331-nat-gcd-dvd-mirrors.md`](../status/331-nat-gcd-dvd-mirrors.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
