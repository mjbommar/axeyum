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
- **MathOverflow, 23 Nov 2011 (owner supplied the thread; the peer sweep had
  wrongly reported "no MO thread found"):** "Can we always find such an
  irreducible polynomial of degree n where degree(p(x)-x^n) <= n/2?", asked by
  `lemire` -- the conjecture's actual origin, three years before the 2014
  paper. Elkies / Zaimi: expected subdegree `O(log n)`. Rivin's answer cites
  Cohen 2004 (`q^{n/2-m} > m W(q^n-1)`) as possibly proving it "for many
  degrees"; Voloch and quid object that it gives only `m < n/2 + O(log n)`.
  **Verified (coordinator, sympy):** the largest `m` Cohen's criterion allows
  at `q=2` falls short of `ceil(n/2)-1` by `~log_2 n + omega(2^n-1)`
  (3 at n=9, 8 at n=32, 17 at n=100) -- the same log gap as Hayes/Weil;
  it reaches the window for NO `n >= 6`. **Emil Jerabek's comment gives
  `x^{2*3^k}+x^{3^k}+1`** (Lahtonen: an exercise in Lidl--Niederreiter), so the
  lane's "first proven infinite family" was wrong on priority as well as on
  uniqueness; cite Jerabek for the `m=2` case. **Ellenberg's answer** states
  the Legendre / Cramer-under-RH framing (`n/2 + log n`): angle 2 was posed in
  2011. Voloch links MO question 39100 (not fetched; MO is unreachable from
  this host).
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

## Entry 2 -- angle 4 (horizontal Deligne budget; Katz's Betti question re-posed)

Lane `lemire-signed-trace`, 2026-08-22. Note
[12-horizontal-deligne-budget.md](12-horizontal-deligne-budget.md); script
`lemire_horizontal_weights.py` (six controls, five mutation controls, exits
nonzero). Bulk producer: new Rust bin `axeyum-lemire-horizontal` (mirrored as
`axeyum-lemire-horizontal.rs.txt`); cross-checked against python-flint and an
exact Witt/Walsh--Hadamard engine that solves `j = 2` in closed form.

- **Budget VERIFIED, one correction:** `#Prim_j(F_2) = 2^{j-1}`, not `2^j`, so
  the trivial bound is `2^{j-1}(j-1)2^{n/2}` and `k >= 2 log2(8 ell C/(j-1))`
  top degrees must vanish, not `2 log2(4 sqrt2 ...)`. **Note 10's Q1 was
  mis-posed; it is now (Q1').** A Betti bound ALONE cannot give `(HWO)`: with
  `i_max in {2j, 2j-1, 2j-2}` the budget forces `C < 1/4`, impossible for
  nonzero cohomology however good the bound. The question is the PAIR
  `(i_max, C)`; do not re-open "is `C(2,j,Xi)` polynomial" on its own.
- **Middle concentration is impossible here (new).** Katz's `Prim_j` is
  literally `G_m x A^{j-1}`, and the trace function of `Xi_n(L_univ)` is
  `G_m`-invariant (`F(T) -> t^n F(T/t)` preserves degree and `Lambda`). A full
  `q-1` never cancels, so `i_max >= j+1`; the sharp target is `i_max = j+1`
  with `C <= (j-1)2^{(j-1)/2}/(8 ell)`. Derived control, true on every row:
  `(2^r - 1) | A_r(n,j)`.
- **`j = 2` is completely solved** (Prop. 3, exact, `r <= 16`): `C = 2`,
  `i_max = 2j-1` (odd `n`), `2j` (`n = 0 mod 4`), `H^*_c = 0` (`n = 2 mod 4`).
  Careful: at `j = 2`, `2j-1 = j+1`, so only the `n = 0 mod 4` rows separate the
  shapes -- and they are the worst case, `H^{2j}_c != 0`.
- **Three in-range rows resolve AND separate the shapes; all three are bad:**
  `(8,2)`, `(12,2)` (`i_max = 2j`) and `(7,3)` -- the one such row on the
  critical line `n = 2j+1` -- where `A_r = 64^r - 32^r` exactly for `r <= 6`,
  so `C = 2` and `i_max >= 2j-1 = 5 > j+1`. Their size is exactly
  `q^{j-1}(q-1)q^{(n-1)/2}`: one square root over the whole `j`-dimensional
  family, none of the Weil factor `(j-1)`. `j >= 4` is **not resolved** (cost
  `q^{j+2}` caps `r <= 33/(j+2)`; several eigenvalues with nontrivial phases --
  cube roots of unity already at `(7,4)`). `(9,3)` goes the other way and is
  exact: `N_3(1) = q^{n-3}` on the nose, top weight only `n+j`.
  Reading `i_max`, `C` off in `r` is legitimate (both are geometric); the
  `q`-aspect SIZE does not extrapolate to `q = 2` -- the `G_m` factor has one
  `F_2`-point, and at `q = 2` the saving is the random value of notes 05/07.
- **A tool lied; control C5 caught it.** The Rust `r = 8` row was wrong: the
  modulus was irreducible but NOT primitive (AES polynomial, `ord(x) = 51`), so
  most of the log table was zero. `assert(a == 1)` after `q-1` steps does not
  detect this.
- **To resolve `j >= 4` you need a different algorithm.** The window scan costs
  `q^{j+2}` on the critical line (`r <= 33/(j+2)`). Instead use
  `L(chi,T) = sum_{m<j} c_m(chi)T^m`, `c_m = sum_{g in V_m} chi(g)` over the
  image `V_m` of the monic degree-`m` polynomials: one Fourier transform over
  `E_j` per `m`, `~(j-1)q^j log q`, independent of `n`. `lemire_anchor.py` has
  the group structure and characters at `q = 2`; generalize them to `F_q`.
- **Next agents (2, 1, 5):** the route is relocated, not closed. It needs a
  DEGREE theorem, and the literature has none for this family: middle
  concentration in print comes from forget-supports being an isomorphism
  (Katz--Laumon 5.4, generic in the parameter), genericity in a twisting
  character, or a singular-locus bound -- never from big monodromy, which only
  kills `H^{2d}_c`; nothing found controls `H^{2d-1}_c`. Katz's own Thm 8.2 is
  the `i_max = 2dim-1` shape, hence `~8.5x` short even where it applies.

### Entry 2 addendum (coordinator)

- The resolved rows `j <= 3` are in a finite-monodromy regime (8th / 24th
  roots of unity as eigenvalue angles), which forces exactly the top-degree
  (co)invariant classes seen; they do not extrapolate.
- Summing the `ell = 24` layer dumps to conductor sums: `|A_j|/2^{n/2} =
  2^{(j+1)/2} x O(1..3)` for `j = 18..24` -- the `i_max = j+1`, small-`C`
  size; (H) over-predicts `30..100x`. **(H) is false at large `j`; the `F_2`
  data are consistent with the ALIVE case of (Q1').** Note 12 sec. 9.
- Angle 4b (priority follow-up after the five angles, or sooner if the owner
  prefers): `L`-function-route resolution of `(2j+1, j)`, `j = 4..6`, and the
  monodromy transition of `L_univ` at `p = 2`.
- MO question 39100 (Voloch, 2010; owner supplied): the Carlitz-cyclotomic
  curve formulation, `q^n/n + O(g q^{n/2})`, genus `g ~ m q^m`, nothing at
  `m ~ n/2` -- identical to note 01's setup. No new content.

## Entry 3 -- angle 2 (sieve face: exact Type I, P_3 theorem, parity population, Type II transplant)

Lane `lemire-signed-trace`, 2026-08-22. Note
[13-sieve-face.md](13-sieve-face.md); script `lemire_sieve_face.py` (six mutation
controls, exits nonzero). Producer: new Rust CAS bin `axeyum-lemire-sieve`
(mirrored as `axeyum-lemire-sieve.rs.txt`; its factorisation agrees with
`certify_irreducible` on all 32766 monics of degree `<= 14`); cross-check
python-flint; LPs scipy/HiGHS, every LP-value-zero row re-certified over `Q`.

- **Type I is EXACT, remainder identically zero, to `D = |W_n| = 2^h`,
  `h = floor(n/2)+1`** (reversal: `d*m* = 1 mod x^{ell+1}` fixes the top `ell`
  coefficients of `m` unitriangularly). Verified `n <= 34`, `k <= h+3`, **zero
  exceptions** in 454 rows. Above `h`, `A_d in {0,1}`, exactly `2^h` of the `2^k`
  divisors occur, and `sum_{deg d=k}|r_d| = 2|W_n|` for EVERY `k > h`: there is no
  averaged (Bombieri--Vinogradov) level past `2^h` either. `s = h/(n/2) -> 1`.
- **The brief was off by one.** `s > 2` at `y = (1/4-eps)n` gives `P_4`, not
  `P_3`. `P_3` needs Kuhn weights (`y_1 = alpha n`, `y_2 = n/3`, `lambda = 1/2`)
  and then only for `alpha < 1/6`, margin `G(alpha) = 2e^gamma alpha
  log((1-2alpha)/(4alpha))`, `G(1/8) = 0.1805`; `n_0 = max(300, 2825 K^3)` with
  `K` the (unpublished) Jurkat--Richert constant. Fully explicit fallback with no
  black box: Brun's pure sieve, exact because every Bonferroni term has
  `deg d <= (2r+1)y <= h` -- no factor of degree `<= 3` for `n >= 28`, `<= 10`
  for `n >= 138`, but only `P_{O(log n)}`.
- **`P_3` with factors `> n/4` is TRUE and abundant** (5% of `W_44`, CAS census
  `n <= 44`) **and provably unreachable by the linear sieve**: `y = n/4` gives
  `s = 2 + 4/n`, main term `4e^gamma/n`, sieve error `O(n^{-1/3})`. The sieve
  face reproduces the lane's `1/n` deficit exactly, from a different direction.
- **Exact Brun--Titchmarsh, no error term** (Selberg, weights `deg d <= h/2`, so
  every entry of the quadratic form is exact): `#irred <= |W_n|/G_{floor(h/2)}`,
  measured `3.0--3.3x` the truth, `-> 4x`.
- **Parity barrier is a theorem with an exact witness.** For `10 <= n <= 15`
  there is an explicit nonnegative rational `w` on ALL degree-`n` monics,
  vanishing on every irreducible, matching `W_n`'s Type-I data exactly to level
  `2^h`; so by LP duality no lower-bound sieve at the window's own level proves a
  prime. `k_max(n) = h+1` for `10 <= n <= 15`, `>= h+2` at `n = 16`; for
  `n <= 9` there is NO barrier (small `n` is misleading here). The support must
  meet `Omega` odd -- pure Liouville `1+lambda` is infeasible against exact data.
- **For angles 1 and 5, the load-bearing item:** every window
  `{A_0 + g : deg g <= floor(n/2)}` has the SAME exact Type-I data, so any sieve
  bound at level `2^h` positive for `W_n` is positive for all `2^ell` of them.
  **A sieve proof of Lemire at level `X^{1/2}` IS a proof of angle 5's uniform
  conjecture** (Legendre for `F_2[t]`); conversely one prime-free window at any
  `n` would kill the route. None exists for `n <= 16` (checked). Angle 5 should
  treat this as the equivalence it asks for, not look for a separation here.
- **Type II does not bypass `(HWO)`** (Prop. 13): `1[ml in W_n] = 2^{-ell}
  sum_chi chi(<m>)chi(<l>)`, so every bilinear form is a reweighting of the same
  Hayes family, `A_M(chi)B_L(chi)` for `S_n(chi)`; angle 4's horizontal sums are
  the `alpha = beta = 1` case. Converse: `(HWO)` gives the count only.

## Literature check 2 (sub-agent of angle 4b, 2026-08-22; primary texts read)

- **Katz IMRN 2013 covers `p = 2` for conductor `j >= 4`.** Thm 5.1 (= 7.1):
  "`G_geom` contains `SL(n-1)` except `(p=5,n=3)` and `(p=2,n=3)`"; `p=2`
  handled via `NFT_3` (sec. 6, Lemma 6.8, Cor 7.4); Thm 1.2/8.1 is
  equidistribution in `PU(n-1)#` for `n >= 4` in ANY characteristic. The
  `p > 2n-1` hypothesis lives ONLY in Thm 8.2 (uniform Betti constant). The
  lane's notes 10/12 said Katz's big-monodromy result excluded `p = 2`; that
  was wrong -- only the uniform Betti constant does.
- **`(p=2, j=3)` is finite monodromy, settled:** Gorodetsky FFA 56 (2019),
  arXiv:1805.07105, Lemma 3.5 -- normalized roots are 24th roots of unity
  (`Theta_chi^24 = I_2`), confirming Katz Rem 5.2 and the coordinator's hand
  computation in note 12 sec. 9. So **`j_0 = 4`**: the resolved rows of note
  12 (`j <= 3`) are exactly the finite-monodromy exceptions.
- Sawin arXiv:1805.04330 Cor 5.3: `d >= 4 => G_geom` contains `SL_N`, no
  characteristic hypothesis (unpublished; `q -> infinity` over a fixed
  `F_{q0}`). Gorodetsky--Sawin Math. Ann. 376 (2019) Thm 9: for small `p`
  they do the geometry on `Prim_ell` directly, top cohomology vanishes by
  Katz 5.1; Thm 8: uniform-in-`p` Betti bound `3(4m deg M + ell + 2)^{2m+ell}`
  (Katz FFA 2001 Thm 12 type) -- exponential `(O(j))^{O(j)}`, far above the
  `~2^{j/2}` that (T2) needs. Sawin ANT 2020 (1810.01303) excludes `p=2` at
  `n in {4,5}` for a determinant-order reason, not monodromy.
- Still char-2-open in the literature: super-even/symplectic family at
  `n = 3, 5` (Katz, Rudnick--Waxman paper; `n >= 7` covered); integral
  monodromy (Perret-Gentil, odd `p` only); squarefree-conductor family
  (Hall--Keating--Roditty-Gershon, odd `q`).
- Consequence for (Q1'): with `G_geom` containing `SL(j-1)` for `j >= 4`, the
  Adams/power-sum virtual representation `Xi_n` has a trivial constituent
  only through `Lambda^{j-1}` (i.e. `n = j-1`), so for `n > j-1` there are
  no geometric coinvariants and `H^{2j}_c = 0` -- the `i_max = 2j` rows of
  note 12 are small-`j` artefacts. What big monodromy does NOT control is
  `H^{2j-1}_c ... H^{j+2}_c` (dually `H^1 ... H^{j-2}` of the quotient `B`
  with coefficients in `G^vee`); that is (T1), and it has no literature.

## Entry 4b -- angle 4b (is the horizontal route unblocked?)

Lane `lemire-signed-trace`, 2026-08-22. Note
[14-horizontal-unblocked.md](14-horizontal-unblocked.md); script
`lemire_horizontal_quotient.py` (controls C1--C9, mutation controls, exit 0);
Rust bin `axeyum-lemire-lfunc` (exact `L`-function engine in `Z[zeta_8]`,
cost `~ j q^j log q`, independent of `n`). The agent was terminated by a
spend limit while finalising; this entry is the coordinator's digest of its
note, which was complete through the verdict.

- **Verdict: ALIVE** (moderate-to-high on "not dead"; low-to-moderate on
  "provable"). Note 12's proposed obstruction (H) is refuted; the top-degree
  classes of its resolved rows are the finite-monodromy artefact of `j <= 3`.
- **Target corrected downward.** In the range `(HWO)` uses (`a <= j <= ell`,
  `ell/(j-1) -> 1`) the budget reads `k >= 6.15 + 2 log2 C` uniformly in
  `ell`: the top SIX OR SEVEN degrees must vanish, not "concentration in
  degree `j+1`". What the data measure is `delta` = top weight minus `n`;
  the estimate follows from `delta <= 2j - 6.15 - 2 log2 C` (T1w).
- **Transition at `j_0 = 4` is a theorem** (Katz IMRN 2013 Thm 5.1 at `p=2`,
  `j >= 4`; Gorodetsky FFA 2019 Lemma 3.5 for `(2,3)`), confirmed
  mechanically by an exact Frobenius-torsion identity (orders `| 8`, `| 24`,
  none `<= 100` at `j = 4`). **Lemma D (new, unconditional):** `H^{2j}_c = 0`
  for all `j >= 4`, `n != j-1` (big monodromy + hook decomposition of the
  Adams operation), so the worst case of note 12 cannot recur.
- **Past the transition the top classes do not persist:** all nine exactly
  resolved cells with `j >= 4` have `delta in {j, j+1}` (the `G_m`-forced
  optimum); note 12's `(7,4)` is `delta = j+1`, `C = 6`; critical-line slope
  of `delta` in `j` is `1.30 +- 0.19` (slope 1 within 1.5 sigma, slope 2 at
  3.6 sigma). `q = 2` layer sums: `delta_1 = (1.00 +- 0.14) j + 2.3` over
  `14 <= j <= 24` (supporting, not decisive).
- **`G_m`-action is free iff `gcd(j, q-1) = 1`** (corrects note 12's guess);
  non-free locus has `dim <= j/3`, invisible in degrees `>= j+1`, so the
  Leray reduction to `B = Prim_j/G_m` survives: `C = 2C'`, `i_max = i'_max+2`.
- **What remains is two named open statements.** (T1)/(T1w): the
  `w = j - 7` case of Sawin's Hypothesis `H(n,r,r~,w)` (arXiv:1810.01303);
  his only unconditional input (Lemma 5.3) is VACUOUS at `p = 2` for every
  `r` and already sufficient at `p >= 3` -- the lane's obstruction is exactly
  the characteristic-two case of that lemma. (T2): best uniform-in-`p` Betti
  bound is `2^{O(j log j)}` (Sawin Lemma 2.11) against the allowed `~2^{j/2}`.
- **Most decisive next computation:** extend the engine from `Z[zeta_8]` to
  `Z[zeta_16]` (`j <= 15`) and measure `delta(2j+1, j)`, `delta(2j+2, j)` for
  `j = 8, 9, 10` at `r = 4, 3, 3` (`q^j <= 2^{32}`, already-run size).
- **Guidance for angles 1 and 5:** the family has big monodromy from `j = 4`;
  the identity-class question is now (T1w)+(T2) on the quotient `B`; do not
  re-derive Betti-size or shape arguments -- they are settled here.

### Entry 4b addendum (coordinator): the `(5,7)` run

- The agent's last job (`axeyum-lemire-lfunc 5 7 14`, `2^35` elements,
  17,401 s, 6 GB) finished after the agent was terminated; dump committed,
  weights table regenerated, script still `ALL CONTROLS PASS`.
- It resolves `(12,5)` to `delta = 8 = j+3 = 2j-2` (six modes, one spare --
  weak) and leaves `(11,5)` unresolved (`delta_7 ~ 7.4`). First resolved
  `j >= 4` cell above the `G_m`-forced optimum `{j, j+1}`; it is the
  `n = 0 mod 4` endpoint, the class that was worst at `j = 2`. Regression
  unchanged (its `r = 6` value was already `7.99`); Lemma D still excludes
  `2j`. Verdict stays "alive, not closed", with the caveat sharpened: at
  `j = 5` the critical line is not yet in the `j + O(1)` shape, and the
  `j = 8..10` computation of note 14 sec. 10 is the only thing that decides.
