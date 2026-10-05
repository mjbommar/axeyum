# Lane: pow-add-prime — odd-factor divisibility toward the Fermat-prime lemma

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, pow-add-prime, 2026-08-30).**

`F:ml430-nat-pow-of-pow-add-prime-ab61d0d3` (`Nat.Prime (a^n+1) -> exists m, n
= 2^m`, the classical fact behind Fermat primes) stays `open`. The classical
proof needs an alternating-sum cofactor (`x^d+1 = (x+1)*(x^{d-1}-x^{d-2}+...+1)`
for odd `d`), and this kernel has no signed sum over ℕ — so rather than build
one (pairing terms, or transporting through `Int`), I sidestepped it entirely.

**What landed** (`crates/axeyum-lean-kernel/src/nat_prelude/pow_add_prime.rs`,
new file, wired into `nat_prelude.rs` as the last `declare_*` call):

- `Nat.pow_mul : forall a e k, pow a (mul e k) = pow (pow a e) k` — mirrors
  `Int.pow_mul`'s proof shape (`int_prelude/algebra.rs`).
- `Nat.dvd_pow_add_one_of_odd_exp : forall x t, dvd (add x 1) (add (pow x (succ
  (mul 2 t))) 1)` — `x+1 | x^{2t+1}+1` for every `x`, by an OUTER case split on
  `x` (0 is trivial: `dvd 1 _`) then an INNER induction on `t` for `x = succ
  xp`, using only `dvd_add`/`dvd_mul_left` plus one subtraction-free identity
  `x^2 = x'*(x+1)+1` (`x'` is the genuinely free predecessor standing in for
  `x-1`, so `Nat.sub` never appears).
- `Nat.dvd_pow_add_one_of_odd_mul_exp : forall a e t, dvd (add (pow a e) 1)
  (add (pow a (mul e (succ (mul 2 t)))) 1)` — `a^e+1 | a^{e*(2t+1)}+1`, the
  reusable "odd-factor divisibility" step named in the fact's own brief as a
  good outcome on its own (`d := 2t+1`; combines `pow_mul` with the lemma
  above at `x := a^e`).

All three are genuinely axiom-free theorems (checked via
`Kernel::axiom_footprint`), admitted on the FIRST attempt against a real
kernel (no debugging round-trips needed once the algebra chains were worked
out on paper first). Verified both at a free `(a,e,t)` (the theorem's own
`forall` IS the free-variable check, plus one `infer_in` application at fresh
fvars) and at the concrete discriminating instance `a=2, e=1, t=1`: `3 | 9`
(`2^3+1=9=3*3`, exactly the smallest instance the classical argument would
use to show a prime `a^n+1` cannot have an odd exponent factor). Largest
numeral formed anywhere in the proofs or tests: `9` (`2^3+1`) — everything
else is symbolic, since this is a proof about free variables, not a
computation.

Registered in `nat_prelude_tests.rs`'s environment-derived coverage list
(`theorem_names`) and confirmed via
`every_nat_declaration_is_checked_and_axiom_free`. Full `nat_prelude::` sweep:
**208 passed, 0 failed** (was 204 before this lane; +3 theorems +1 new test).
`cargo fmt --all --check` and `clippy -p axeyum-lean-kernel --all-targets -D
warnings` both clean.

**What did NOT land, and why**: the fact itself. Two pieces are still needed
and neither is attempted here:

1. "`n` is not a power of two ⟹ `n` has an odd factor `d > 1`" — a 2-adic
   valuation argument (extract the odd part of `n` via strong/well-founded
   recursion). Nothing in this session builds it; `Nat.even_or_odd`
   (`powsq.rs`) is the closest existing primitive but stops at one bit, not
   an iterated valuation.
2. The final contradiction: given `d*e = n`, `d` odd `> 1`, show
   `dvd_pow_add_one_of_odd_mul_exp` exhibits a divisor `a^e+1` that is
   neither `1` nor `a^n+1` (needs `e < n` from `d > 1`, and `a^e+1 > 1` from
   `a > 1`, both easy order facts — not done here), then plug into
   `prime_condition`'s `∀ c, c ∣ x → c = 1 ∨ c = x` to derive `False`.

Bridging `dvd_pow_add_one_of_odd_exp`'s `succ (mul 2 t)` exponent shape to
`Nat.Odd`'s own witness shape (`succ (add t t)`) needs only
`two_mul_eq_add_self` (`powsq.rs`, module-private today) — cheap, not done
here since nothing downstream needs it yet.

**For the next lane**: piece 1 above is the harder of the two remaining
pieces and is a genuine well-founded-recursion undertaking (`Nat.gcd`,
`Nat.bezout_witnesses`, `Nat.modeq`, `Nat.wilson` all already use
`WellFounded.fix` in this kernel — see CLAUDE.md's "NO FUEL ENCODING CAN BE A
DEPENDENT RECURSOR" entry for why a fuel encoding here is the wrong tool).
Piece 2 is comparatively short standard order-theory bookkeeping once piece 1
exists.

<!-- plan-section: landed-changes -->

| 2026-08-30 | pow-add-prime | `Nat.pow_mul`, `Nat.dvd_pow_add_one_of_odd_exp`, `Nat.dvd_pow_add_one_of_odd_mul_exp` — the odd-factor divisibility step toward `F:ml430-nat-pow-of-pow-add-prime-ab61d0d3`, subtraction-free (no alternating sum, no `Int` transport); fact stays `open`, full lemma not assembled |
