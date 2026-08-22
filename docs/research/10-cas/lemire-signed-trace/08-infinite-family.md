# A proven infinite family: Lemire holds for n = 2*3^k

Status: research note, 2026-08-22. The theorem below is proved and
independently machine-checked (flint, `k = 0..6`). It is input type (2) of
note 05 -- a class-specific construction that reads the identity class's own
description -- the one route neither barrier blocks, and it is the first
proven infinite family of degrees for the Kaser--Lemire conjecture. The
irreducibility itself is classical cyclotomic theory; the contribution is the
observation that it lands in the half-degree window, resolving the conjecture
for infinitely many `n`.

## Theorem

For every `k >= 0`, Lemire's conjecture holds at `n = 2*3^k`:
`f_k(x) = x^{2*3^k} + x^{3^k} + 1 = Phi_{3^{k+1}}(x)` is irreducible over `F_2`
of degree `n`, and `deg(f_k - x^n) = 3^k = floor(n/2)`, so it is a half-degree
witness. Hence `I_n(1) >= 1` for the infinite set
`n in {2, 6, 18, 54, 162, 486, 1458, ...}`.

## Proof (three textbook facts)

1. `f_k = Phi_{3^{k+1}}`. The prime-power cyclotomic identity
   `Phi_{p^m}(x) = Phi_p(x^{p^{m-1}})` (Lidl--Niederreiter, *Finite Fields*,
   Thm 2.47 f.) gives
   `Phi_{3^{k+1}}(x) = Phi_3(x^{3^k}) = x^{2*3^k} + x^{3^k} + 1`.
2. For `p` not dividing `m`, `Phi_m mod p` is irreducible over `F_p` iff `p`
   is a primitive root mod `m` (it splits into `phi(m)/ord_m(p)` factors of
   degree `ord_m(p)`; Lidl--Niederreiter Thm 2.47). Here `p = 2`,
   `m = 3^{k+1}`.
3. `2` is a primitive root mod `3^{k+1}` for all `k >= 0`: `ord_3(2) = 2 =
   phi(3)`, `2` is a primitive root mod `9` (order `6 = phi(9)`), and a
   primitive root mod `p^2` is a primitive root mod `p^m` for all `m`. So
   `ord_{3^{k+1}}(2) = phi(3^{k+1}) = 2*3^k` and `f_k` is irreducible of
   degree `2*3^k`. Since `f_k - x^n = x^{3^k} + 1` has degree
   `3^k = floor(n/2)`, `f_k` is a half-degree witness.  QED

Machine-checked (`scripts` reproduction, flint): `f_k` irreducible and
`ord_{3^{k+1}}(2) = 2*3^k` for `k = 0..6` (`n` up to `1458`); and
`x^{2k} + x^k + 1` is `F_2`-irreducible for `1 <= k <= 81` **exactly** when
`k in {1,3,9,27,81}` = the powers of `3`.

## Scope and why it is the unique cyclotomic family

The family has density zero (`n = 2*3^k`) and gives only even `n` (every
cyclotomic degree `phi(m)` is even), so it does not touch the odd endpoint.
It is the *unique* cyclotomic window family: for `Phi_{p^a}` to be
`F_2`-irreducible needs `m = p^a` odd with `2` a primitive root, and its
second-highest term sits at degree `(p-2)p^{a-1}`, which is `<= phi/2` iff
`p <= 3`; `p = 2` gives the reducible `(1+x)^{2^{a-1}}`, so `p = 3` is forced
(scan of odd prime powers `m <= 400` confirms `m in {3,9,27,81,243}` are the
only `F_2`-irreducible in-window cyclotomics). The classical trinomial fact
`x^{2k}+x^k+1` irreducible over `F_2` iff `k` a power of `3` is
Fredricksen--Wisniewski (Inform. Control 1981) and Golomb--Lee; the novelty
here is only that it resolves Lemire for an explicit infinite set of degrees.

## Why it does not extend to a denser or provable general family

- **Trinomials `x^n + x^k + 1`, `k <= n/2`, general `n`:** whether infinitely
  many are irreducible is *open* (Brent--Zimmermann arXiv:2105.06013 treat it
  heuristically). The `n = 2*3^k` case is the only provable one.
- **Provable-irreducible degree-raising transforms leave the window.** Meyn's
  `R`-transform `f -> x^{deg f} f(x + x^{-1})` doubles degree preserving
  irreducibility but its coefficient count grows `3 -> 7 -> 13 -> 19` and is
  never in-window (4 iterations tested); the `Q`-transform `f(x^2+x)` is
  in-window only for the seed `x^2+x+1` (giving `x^4+x+1`) and leaves
  immediately; monomial composition `f(x^k)` is in-window only for degree-2
  seeds -- the cyclotomic family again. This is the branch ledger's
  construction closure (note 02 section 5C: constructions produce primes of
  degree `~2^ell deg F`, overshooting or filling the top half).
- **Swan/parity (input C) fails as a lower bound:** Swan's theorem gives only
  the parity of the factor count. Swan-odd yet reducible (`>= 3` factors)
  trinomials are abundant in-window -- first instances `(n,k,#factors) =
  (10,5,3), (12,1,3), (13,2,3), (14,1,3), ...` -- and separating `r = 1` from
  odd `r >= 3` needs a smallest-factor bound that does not hold (`x^2+x+1`
  divides many `x^n+x^k+1`). Swan proves only *negative* results: for
  `n = 0 mod 8` there is **no** irreducible trinomial at all (verified
  `n = 8..128`), so those `n` require pentanomial-or-denser witnesses -- which
  is why the committed witness set is about half pentanomials (of
  `n in [2,200]`, 80 have no half-degree irreducible trinomial, 25 of them
  `= 0 mod 8`).
- **The sieve route (input A) reduces to the open estimate:** the window is
  the short interval `{x^n + g : deg g <= floor(n/2)}` of length `~ 2 sqrt X`,
  `X = 2^n`, with *exact* Type-I information to level `X^{1/2}` -- but that is
  the parity barrier. The window is dominated by products of two half-degree
  irreducibles (census irreducible : 2-factor `~ 1 : 2.5`), which a level-`sqrt
  X` sieve cannot separate from primes; crossing parity needs the
  Friedlander--Iwaniec asymptotic-sieve Type-II input, which transplants
  exactly to `(REL)`/`(HWO)` (a factor `4 ell` saving over Weil on the same
  bilinear forms). Sawin--Shusterman fails at `q = 2` (Betti constants
  exponential in `n` swamp `q^{n/4}`; needs squarefree modulus, `x^j` is
  maximally non-squarefree). So the sieve does not bypass the open estimate.

## Status

This is a genuine partial theorem -- Lemire for infinitely many `n`, by an
explicit witness, not blocked by either barrier -- and the first such recorded
for the conjecture. It does not approach the general (all-`n`) statement,
which still needs the phase-aware estimate of the roadmap. Both barriers plus
the almost-all theorem plus this family now bound the problem from every side
we can reach: averaging (note 05), symmetry (note 06), phase correlation
(note 07), and explicit construction (here) each go exactly as far as they can
and stop at the same wall.
