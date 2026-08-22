# Backward chains: diary of the five angles (Opus agents, sequential)

Status: running diary, started 2026-08-22. Method: work backwards from either a
full proof of Kaser--Lemire over `F_2` or a *proved* statement that blocks a
route (an equivalence or a strict obstruction). One Opus agent per angle, run
one at a time; each agent receives every earlier entry here as guidance.
Nothing in this file is a claim of proof unless a section says "proved" and
names the script that checks it.

## Ground truth the agents start from (coordinator, 2026-08-22)

- The lane's own notes 00--10 are the map; note 00 is the synthesis, note 10
  the specialist statement of the missing estimate `(HWO)`.
- **Correction to notes 08/09 (verified by coordinator, Rabin test in pure
  Python):** monomial composition `f(x^t)` preserves the half-degree window
  for EVERY in-window seed (tail and degree both scale by `t`), and
  Lidl--Niederreiter Thm 3.35 gives irreducibility iff `rad(t) | ord(f)`,
  `gcd(t, (2^m-1)/ord f) = 1` (and `4 nmid t`, automatic at `q=2`). So
  `n = 2*3^k` is NOT the unique provable family and NOT the only cyclotomic
  one in effect: `x^21+x^7+1`, `x^147+x^49+1`, `x^1029+x^343+1` (seed
  `x^3+x+1`, order 7, `n = 3*7^k`, ODD `n`) and `x^{4t}+x^t+1` for
  `t in {3,5,9,15,25,27,45,75}` (seed `x^4+x+1`, order 15, `n = 4*3^a*5^b`)
  are all irreducible and in-window. Note 09's sentence "monomial composition
  `f(x^k)` is in-window only for degree-2 seeds" is false; note 08's "unique
  cyclotomic window family" and "gives only even `n`" are false as stated.
  Barrier III's CONCLUSION (degree-multiplicative => density zero) is
  probably still right but its proof and density count must be redone for
  the union over all seeds.
- **Angle 5's empirical question is already answered in note 05 sec. 4:**
  the exceptional set is EMPTY at every `(ell, n)` computed (`ell <= 24`,
  `n <= 50`); `min_g N_ell(g)/mean -> 1` (0.9971 at `(24,50)`). So the data
  say "every top half is realized" -- the identity class is not
  distinguished in the data, only in its description. Angle 5 is therefore
  re-aimed at the uniform conjecture (below), not at a computation.
- **Averaging over `n` does not help** (coordinator, large-sieve count): the
  family has `R ~ ell 2^ell` Frobenius angles and the useful range of `n` has
  `~ell` members; `sum_n |sum_r e(n theta_r)|^2 <= (N + delta^{-1}) R` is
  trivial when `R >> N`. Any averaging the problem offers is over a set
  exponentially smaller than the family. To be written as a lemma (angle 1).
- **Tooling rule (owner, 2026-08-22): the Rust GF(2) CAS is the PRIMARY
  engine; python-flint is the independent cross-check only.** The CAS
  (`axeyum-cas`, ~33k lines, unmerged branch `agent/gf2/lemire-proof` at
  `47fd7b440`) is built in the snapshot
  `/data0/axeyum/scratch/snap-lemire-signed-trace-47fd7b440/target/release/`:
  `axeyum-gf2-check`, `-certify`, `-search`, `-dump-populations`,
  `-composition-tower`, `-hayes-*`; sources in that snapshot's
  `crates/axeyum-cas/src/`. Run them from the snapshot; never cargo in the
  shared checkout. If the Rust layer lacks an operation, say so explicitly.
- Cross-check venv: `/data0/axeyum/scratch/lemire-signed-trace-lemire-venv`
  (python 3.12, python-flint 0.9.0, sympy, numpy); branch CAS binaries in
  `/data0/axeyum/scratch/snap-lemire-signed-trace-47fd7b440/target/release/`
  (`axeyum-gf2-dump-populations <ell> <degree>` etc.); certified witnesses
  `scripts/lemire-signed-trace/data/witnesses-401-3000.txt`; layer dumps in
  `scripts/lemire-signed-trace/data/`.

## The five angles (order of execution: 3, 4, 2, 1, 5)

1. Frobenius-angle reformulation: Lemire <=> mean of `cos(n theta)` over the
   `~ell 2^ell` angles `>= -kappa/ell`; `q > n^2/4` makes it a one-line
   theorem; write the "no averaging over n or chi suffices" lemma.
2. Sieve / Legendre in `F_2[t]`: construct the Selberg parity example with
   exact Type-I data to level `sqrt X` and no primes in the window.
3. Construction / Galois: the corrected Thm-3.35 family from every certified
   seed; compute the provable-degree set and its coverage; prove the
   prime-`n` blocker; rewrite notes 08/09 and the ledger fact.
4. Geometry: settle Katz's Betti question at `p=2` for the layer
   representation -- either a poly bound (=> Lemire for large `ell`) or a
   proof that the Betti sum is exponential in `j` (closes Q1 negatively).
5. Uniformize: the data say every top half occurs; state the uniform
   conjecture (Hansen--Mullen for the whole top half) and ask whether any
   proof shape separates Lemire from it.

## Literature check (peer session, 2026-08-22; secondary sources unless marked)

- **LN Thm 3.35** (Lidl--Niederreiter 2nd ed. 1997) confirmed by two concordant
  quotations (Tuxanidy--Wang arXiv:1109.4693 Lemma 3.4; Handbook of Finite
  Fields Thm 3.2.6): the book's form is the *exhaustive* one -- `f_1(x^t), ...,
  f_N(x^t)` are ALL the irreducibles of degree `mt` and order `et`. The iff
  single-polynomial form is Handbook Thm 3.2.5 (Menezes et al. 1993).
- **Pollack FFA 22 (2013)** (primary read): `floor((1-eps) sqrt n)` coefficients
  in ARBITRARY positions, uniformly in `q`. Prop. 10 (Hayes 1965 + Weil):
  any `s + t <= (1/2 - eps) n` LOW+HIGH coefficients, all `q`. So "top
  `(1/2 - eps) n` coefficients" IS a theorem at `q = 2`; the whole problem is
  the `log n`. Garefalakis 2008: `(1/3 - eps) n` CONSECUTIVE coefficients set
  to ZERO, any position.
- **Ha FFA 40 (2016)** (arXiv v1 read): `(1/4 - eps) n` arbitrary positions
  needs `q >= q_0(eps)`; at arbitrary `q`: `r <= n/10` for `n >= 52` (Thm 1.3),
  so `delta = 1/10` at `F_2`. Note 09's "sqrt n ceiling" sentence: Pollack's
  sqrt n is correct for arbitrary positions at fixed q, but the relevant
  ceiling for the TOP positions is Hayes/Weil `n/2 - log_2 n`, and for
  arbitrary positions at `q=2` it is `n/10` (Ha). Rewrite accordingly.
- **Sharp explicit form** (Hsu 1996 Thm 2.4 = Cohen 2005 Thm 2.1, via Gao
  arXiv:2109.14154 Cor. 2): `#{irreducible, top l coefficients prescribed}
  >= q^{n-l}/n - (l+1) q^{n/2}/n`, positive iff `l < n/2 - log_q(l+1)`; Gao
  remarks the bound is negative at `l >= ceil(n/2)` -- Weil structurally stops
  there. Shortfall at `q=2`: `n = 64: 27/31`, `1024: 503/511`, `4096:
  2037/2047`. Corollary: Kaser--Lemire is a THEOREM for `q > n/2` (even `n`)
  / `q > (n+1)^2/4` (odd `n`) -- matches angle 1's `q > n^2/4` remark.
- **Barrier not broken at fixed q:** Bank--Bary-Soroker--Rosenzweig (Duke 2015)
  is `q -> infinity` at fixed degree; Sawin--Shusterman (Ann. Math. 2022)
  needs odd `p`, `q > 685090 p^2`. Keating--Rudnick IMRN 2014 Lemma 4.2 is the
  reversal duality (top coefficients <-> AP mod `T^{n-h}`).
- **The conjecture's source:** Kaser--Lemire, "Strongly universal string
  hashing is fast", Comput. J. 57(11) 2014, arXiv:1202.4961 sec. "GF
  Multilinear": "(There are such irreducible polynomials for L in {1..400}
  [Arndt's table] and we conjecture that such a polynomial can be found for
  any L)". Motivation: Barrett reduction. Arndt's `lowbit-irredpoly.txt`:
  minimal subdegree is `<= 10` for all `n <= 400` (tracks `~log_2 n`), so the
  truth is far stronger than the conjecture asks.
- arXiv:2105.06013 (Brent--Zimmermann) is about almost-irreducible trinomials
  at Mersenne exponents, NOT the in-window trinomial question; note 08's
  citation of it for "infinitely many irreducible trinomials is open" is
  misattributed -- cite it only for what it is, or drop it.

## Entries

## Entry 1 -- angle 3 (construction family, prime-`n` blocker)

Lane `lemire-signed-trace`, 2026-08-22. Producer: Rust `GF(2)` CAS (new snapshot bin
`axeyum-gf2-monomial-family` over `monomial_prime_eligibility` + `certify_irreducible`;
10--300x python-flint). Cross-check: python-flint. Script
`scripts/lemire-signed-trace/lemire_composition_family.py` -- exits nonzero, four mutation
controls, asserts the engines agree.

- **Theorem A (note 08, rewritten).** `f` in-window irreducible of degree `m`, order `e`;
  `t >= 2` with `rad(t)|e`, `gcd(t,(2^m-1)/e)=1` `=>` `f(x^t)` in-window irreducible of
  degree `mt`. LN Thm 3.35 / Handbook 3.2.5. **The window is free:**
  `deg(f(x^t)-x^{mt}) = t*deg(f-x^m) <= floor(mt/2)` for every `t >= 1`, so monomial
  substitution can never leave the window. `m=2` is the old cyclotomic family; `m=3`
  (`x^3+x+1`, `e=7`) gives the ODD family `n = 3*7^k`.
- **Operational form -- cheap, use it.** Both hypotheses say: for every prime `p|t`,
  `v_p(e) = v_p(2^m-1) >= 1`, i.e. `p | 2^m-1` and `x^{(2^m-1)/p} != 1 mod f`. **No
  factorization of `2^m-1`.** And `p | 2^m-1 <=> ord_p(2) | m`. The CAS already has this.
- **Coverage, exact at `N=10^5`** (certified ledger `m <= 3000` + bounded per-degree
  search): `|S|` = 22 / 243 / 2086 / 8394 at `N = 10^2..10^5`; composites covered
  0.297 / 0.292 / 0.238 / 0.093. `W = max|A(f)| = 16` (at `m=360`), so
  `#S = O((log N)^16)`: density zero **proved asymptotically, not observed** -- that bound
  is `6.5e7` at `N=10^5`, vacuous. The fall past `N > 6000` is the ledger cap binding.
  Smallest composite NOT in `S`: **4**; smallest odd: **9**. No prime, no power of two.
- **Prime-`n` blocker (note 09 B1), proved for the toolbox** (monomial/general composition,
  Meyn `R`/`Q`, composed products, Cohen/Kyuregyan, cyclotomic, Carlitz, norm from
  `F_{2^k}`): every degree is `m*k` (`k>=2`), or `2m`, or degree-preserving, or
  `phi(M)`/`ord_M(2)`. At prime `n` all are silent. Scope: this toolbox only.
- **The norm from `F_{2^k}` destroys the window** (checked): second layer at
  `n(k-1)+deg g`, so in-window forces `deg g <= 0`, and that case gives back
  `x^{2n}+x^n+1` -- the `m=2` family again.
- **Two note-09 lemmas were FALSE, corrected in place.** (a) "monomial composition
  in-window only for degree-2 seeds" -- false for every seed. (b) "non-monomial
  `f(x^d+r)` has tail `>= d(n-1)`" -- false; exact tail `km-(k-s)lsb(m)`, in-window iff
  `(k-s)lsb(m) >= ceil(km/2)`, forcing `m` a POWER OF TWO (checked: exactly `{2,4,8,16}`).
  **The lane's own CAS had both right** (`composition_shape_criterion`); only the prose was
  wrong. Read `crates/axeyum-cas/src/gf2.rs` before trusting a note.
- **Literature ceiling was wrong by a power.** Top-position ceiling at `q=2` is
  `n/2 - log_2 n` (Hayes/Weil; Hsu 1996 = Cohen 2005), not `sqrt n`: Kaser--Lemire is
  `~log_2 n` past Weil, a log gap. That argues FOR the analytic side, not against it.
- **Landed:** notes 08, 09 rewritten; note 00 item 2 + Barrier III corrected; new fact
  `F:gf2-lemire-monomial-composition-family`, cyclotomic fact kept as its `m=2` case with
  its false scope sentences fixed; scripts README. **Next agent:** the construction angle
  is closed and *located* -- structurally silent at prime `n`. Do not re-open it.
