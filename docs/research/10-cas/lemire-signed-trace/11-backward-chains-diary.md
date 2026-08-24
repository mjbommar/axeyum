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

## Entry 5 -- arXiv techniques sweep 2023-2026

- 84 arXiv API queries (math.NT/math.AG, 2022-01..2026-08), 1262 distinct ids,
  437 post-2022, 20 sources pulled and read. Full note:
  [15-arxiv-techniques-2023-2026.md](15-arxiv-techniques-2023-2026.md).
- **New lever (rank 1).** Gorodetsky--Kovaleva arXiv:2307.01344, `lem:sym` +
  `cor:sym`: for `chi_{k,psi}(f) = psi(p_{-k}(f))`, a *primitive Dirichlet
  character mod `T^{k+1}`*, the `Lambda`-weighted sum over degree `n` equals the
  same sum for `k' = gcd(k, q^n - 1)`, hence `|sum Lambda chi| <= q^{n/2}
  gcd(k, q^n-1)` against Weil's `q^{n/2} k`. Exact, fixed `q`, no geometry.
  Proof uses ONLY that the summand is a function of `x^{-k}` on `F_{q^n}^x`,
  which is also true of a Witt-level-`s` character supported at a single odd
  position (Teichmuller is multiplicative). At `q = 2` the stated family is
  order 2 (`s = 1`, the Kerdock layer). **Arithmetic: at `gcd = 1` the saving is
  `(j-1)`; `(HWO)` needs `4 ell`; in the `(HWO)` range `j/ell -> 1`, so the
  shortfall is the absolute constant 4** -- every mechanism in notes 03--09 is
  short by `ell`. Next action: count single-position characters in `X_{j,s}`.
- **Reframing.** Bagshaw arXiv:2401.10399 `cor:vonmangoldt`: level of
  distribution `omega < 1/2 + 1/62` for **arbitrary** modulus (Sawin and
  Sawin--Shusterman need squarefree; ours `x^{ell+1}` is maximally not), under
  `q > p^2 e^2 ((16-omega)/(16-31omega))^2`. Reversal duality => **Kaser--Lemire
  over `F_q` holds for all large `n` once `q > 7101 p^2`; at `p = 2`,
  `q >= 2^15`.** Note 09's threshold `q > n/2` grows with `n`; this one does
  not. The open set is small `q`, not large `n`.
- **Note 14 sec. 11.4 answered, negatively.** Hu--Teyssier arXiv:2502.11060
  Thm. 2 gives `h^i(A^n,L) <= b_i(lc) rk` with `b_i` explicit, uniform in `p`
  and `l`, graded by degree, linear in rank -- all four properties (T2) wants.
  Evaluated their recursion: `b_n(1) = 2^{Theta(n log n)}` (same as Sawin
  Lemma 2.11), and the graded budget `sum_k b_k(1) 2^{-k/2}` diverges (partial
  sums `1, 1.71, 10.2, 75, 690, 7621`) against a budget of `1/4`. Retarget: the
  *coefficients* of `fd_k`, `k <= 7`, not "a polynomial Betti bound".
- **Disproof template.** Sawin arXiv:2209.02170: at fixed `q`, prime-power
  modulus, wild `p | k`, the Kloosterman sum vanishes off a sparse locus, and
  Plancherel then forces one value to be huge -- so certain short-interval sums
  and moments provably have NO square-root cancellation. Same computation runs
  on note 07's `A_psi`: if `A_psi = 0` off a `2^{-c}` fraction then
  `max |A_psi| >= 2^{c/2}(mean square)^{1/2}`, and `(CYL)` is false if that
  exceeds `2^{ell-1}`. The vanishing locus is already in the note-07 dumps,
  uncounted.
- **Char-2 negative datum.** Klurman--Mangerel--Teravainen arXiv:2202.10370: the
  functions with bounded short-interval discrepancy are exactly the Dirichlet
  characters to prime-power modulus -- our family -- and "over `F_q[t]` with `q`
  even ... the set of characters with bounded discrepancy is somewhat larger
  than in the case of `q` odd".
- **The fixed-`q` wall is one wall.** Sawin--Shusterman arXiv:2512.24080 bound
  short trace-function sums by `X^{1/2} |g|^{log_q(2r+c)}`; that factor is `< 1`
  only for `q > 2r + c`, and it is the same threshold reappearing in Bagshaw's
  `q`-condition and in Sawin's `omega < 1`. Also: Sawin's Waring paper
  arXiv:2412.14053 needs `k < p`, i.e. it dies at `p = 2` in the *same* lemma
  (arXiv:1809.05137 Prop. 2.5) that makes his Lemma 5.3 vacuous -- two
  independent papers, one `p = 2` wall.

### Entry 5 addendum (coordinator, 2026-08-23): the lever does not lift

- Verified `lem:sym`/`cor:sym` of arXiv:2307.01344 verbatim in the source. Then
  closed the note's own open check, negatively, two ways (note 15 sec. 4):
  (i) **counting** -- single-position characters number `~2 j ln j` against
  `2^j` in the dual (`2^{-1011}` of it at `j = 1024`), so bounding them
  perfectly does not move a layer sum `T_{j,s}` at all; (ii) **mechanism** --
  the lemma's proof reindexes by the power map `x -> x^k`, which IS the
  Adams action of note 06, whose orbit of the identity class is `<= 2`. The
  unbounded saving in their setting comes from the phase being a SINGLE
  monomial; our exact-conductor characters are tuples and the power map moves
  the whole tuple.
- So "a constant factor 4 from (HWO)" is withdrawn: true per character,
  vacuous per layer. **Do not re-open this.** What survives: the existence of
  a fixed-`q` improvement over Weil for a complete family (worth knowing), and
  their `lem:Blk` as a tool for the monomial sub-family.
- Unaffected and still open leads: the Bagshaw reframing (`q >= 2^15` at
  `p = 2` would make the residual problem small `q`, not large `n` -- verify
  independently before quoting) and Sawin's sparsity+Plancherel disproof
  template applied to note 07's `A_psi` (cheap: one uncounted statistic in
  dumps we already have).

## Entry 7 -- the large-q threshold claim, verified/refuted

Lane `lemire-signed-trace`, 2026-08-23. Note 16; checker
`scripts/lemire-signed-trace/lemire_largeq.py` (17 checks, 5 positive controls,
exits nonzero; data `largeq-*.txt`). Primary LaTeX: arXiv:2401.10399 (Can. J.
Math. 78 (2026) 302--327), arXiv:1808.04001, arXiv:1204.0708.

- **Individual, not averaged -- the structure survives.** Bagshaw
  `cor:vonmangoldt` (Cor. 2.5) is single-modulus, ARBITRARY `F`, `r <= omega n`,
  `omega < 1/2+1/62`. The Bombieri--Vinogradov form is a separate theorem
  (Thm 2.6), better exponent, not used. `F = T^r` is legitimate; Sawin and
  Sawin--Shusterman need squarefree and do not apply.
- **Constant re-derives.** `g(omega) = e^2((16-omega)/(16-31omega))^2` is
  increasing; `g(1/2) = 961 e^2 = 7100.8829`, so `7101 p^2` is right.
- **REFUTED at `p = 2`.** The paper fixes `q` an ODD prime power, and its one
  indispensable input -- SS `LinearFormsMobThm` (Thm 4.5) -- sits in a section
  opening "we will assume that the characteristic `p` of `F_q` is odd. Because
  of this, `F_q^x` admits a unique quadratic character". The Mobius cancellation
  IS quadratic reciprocity (Jacobi symbol of a resultant). Note 15's "at
  `p = 2`, every `q >= 2^15`" is a theorem that does not exist.
- **REFUTED a second way.** `q > 7100.88 p^2` is `p^{l-2} > 7100.88`, forcing
  `l >= 3`: NO prime field, NO `q = p^2`, ever. Admissible set is `O(X^{1/3})`
  below `X`; smallest member `3^11 = 177147`. External control: the rule
  reproduces Bagshaw's own list `3^14, 5^10, 13^7, 23^6, 59^5, ...` exactly.
- **Reversal duality verified**, index `r = ceil(n/2)` (KR sec. 5.2), bijection
  onto the `f(0) = 1` part of the window; 89 `(q,n)` pairs, 24,090 polynomials.
  The brief's `floor(n/2)+1` is off by one at even `n`: over `F_3` at `n = 4` it
  reports an EMPTY progression where the window holds 6 irreducibles.
- **Step nobody wrote down:** at the endpoint `Lambda` also counts prime powers,
  and `#{proper powers of degree n} ~ q^{n/2}` = the class size. They die because
  `x = P^k = 1 mod T^r` forces `P = zeta mod T^{ceil(r/p^A)}`, leaving
  `O(q^{n/2p})` -- a saving only by `1/p`.
- **Next:** note 15 sec. 2.2, 3(i), 3(iii), 3(iv) and headline answer 2 need
  note 16 sec. 8's corrections (note-15 owner / coordinator). Do NOT propagate
  to notes 00/09 as written. Effective `n_0(q)` is a bounded follow-up.

## Entry 6 -- the Plancherel forcing test on A_psi

- Applied Sawin's sparsity+Plancherel DISPROOF template (arXiv:2209.02170, note
  15 sec. 2.3) to note 07's `A_psi`, which Entry 5 carried as "one uncounted
  statistic". Counted; nothing is refuted. [17-cylinder-plancherel.md](17-cylinder-plancherel.md).
- **It CANNOT refute (CYL), and the reason needs no data.** Plancherel here runs
  over `K = ker(E_ell -> E_{a-1})`, `|K| = 2^{ceil(log2 ell)+2} < 8 ell`. The
  forcing gains at most `sqrt(|K|-1)` over the rms, and the rms is
  `Theta(ell 2^{-ell/2})` times the `(CYL)` threshold. Exact reach
  `sqrt(NTM)/2^{ell-1}` lies in `[8,32] ell^{3/2} 2^{-ell/2}` (asserted in code
  for `11 <= ell <= 400`): `< 1` from `ell ~ 21`, `3.2e-26` at `ell = 200`.
  Sawin's group has `q^{n-1}` characters with `q^{-cn}`-sparse support; ours has
  `< 8 ell`, and `a` is chosen by the Haar telescope precisely to make it that
  small. COMPARE THOSE TWO SIZES BEFORE TRANSPLANTING SUCH A TEMPLATE.
- **Both hypotheses fail independently.** Sparsity: `Z = #{psi != 1 : A_psi = 0}
  = 0` at ALL 26 endpoints `12 <= ell <= 24`, both `n`; the near-zero set is not
  a coset either. Mass: `NTM = sum_{psi!=1} A_psi^2 = |K| SSD_id < 2^{2ell-2}`
  from `ell = 22` (odd) / `23` (even) on, so NO vanishing pattern whatever can
  force `max |A_psi| >= 2^{ell-1}`. `Z_needed` runs `0` (at `(12,25)`,`(12,26)`,
  `(13,28)` Plancherel ALONE refutes `(CYL)`) -> `126/127` -> impossible.
- Exact data for all 26 endpoints, incl. `ell = 12` and the odd `ell = 13..21`
  never computed here. CONFIRMS the roadmap paper verbatim: `(CYL)` true from
  `ell=16` (n odd), `ell=18` (n even) on. Nothing to retract; `(REL)` untouched.
- Random model made exact: `E|A_psi|^2 = (cond psi - 1) 2^{n-a+1}`, with
  `cond(psi_u) = max_{k in supp u} k 2^{e_k(ell)-1} in [a, ell]`; measured/model
  in `[0.90,1.22]` at every endpoint. Parity: `A_psi = A_1 (mod 2)`, so `A_1`
  odd => NO zeros; `A_1` IS odd at `(23,47)`, where `Z = 0` is thus a proof.
- Part D: the Plancherel identity DOES exist for the TWISTED families
  `T_{j,s}(g0)` and `A_j(g0) = 2^{j-1} H_j(g0)`, and both are exact controls.
  But `(HWO)` is a claim at `g0 = 1` and forcing yields SOME `g0`, so it cannot
  refute `(HWO)`. Measured anyway: required surviving fraction falls like
  `2^{-ell}` (median `4.4e-3` at `(22,45)`) against a measured `0.9997`, and the
  identity's rank among the `2^j` twists is generic -- no position anomaly.
- Byproduct: `|K| SSD_id < 2^{2ell-2} => (CYL) => (REL)`, one second-moment
  inequality, true at `ell = 22`(odd), `23`, `24`. Does NOT evade Barrier I:
  note 03 sec. 5's `F` has `A_psi(F) = -c ~ 2^{ell+1}`, violating `(CYL)` by 4-8.
- TOOL TRAP: `axeyum-gf2-dump-populations 24 49` needs its third argument
  (`1300000000` table cells); without it the binary PANICS, the shell loop keeps
  going, and you get a ZERO-BYTE dump that analyses as an empty group.

## Entry 8 -- savings as a dial: the (HWO_k) ladder

- The chain states its open estimate as a THRESHOLD ("prove `4 ell`"). It is a
  DIAL. Exact dictionary (note 18, `lemire_savings_scale.py`, 11 checks, 7
  controls): a uniform saving `F` over Weil for the whole non-trivial family of
  `E_l` gives an irreducible with `deg(f-x^n) <= floor(n/2)+k`, `k = ell-l`, iff
  `F > F_req(n,l) = D(l)/(2^{n/2} - 2^{l-n/2} Theta^+)`, `D(l)=(l-2)2^l+2`.
- BOTH ENDS CHECK OUT. `F = 1` is not an analogue of Hayes/Weil, it IS the
  published inequality: Gao arXiv:2109.14154 Thm 1(b), sharpening Hsu 1996 =
  Cohen 2005 Thm 2.1 (ours is one coefficient better at `(16,33),(20,42),
  (50,101)`). `k = 0` is Kaser--Lemire, needing `F > (ell-2)/kappa`.
- **THE ROADMAP'S `4 ell` IS `4 kappa` STRONGER THAN NEEDED** (`kappa =
  2^{n/2-ell}`): `5.714x` odd `n`, `8.081x` even, at `ell=200`; honest constants
  `140.007`/`99.000`. Decomposition (asserted): `800 -> 625.198` (the chain's
  own exact requirement) `-> 108.905` (`B=2^{2ell}-W` is the wrong target; the
  true one is `2^n - 2^ell Theta - W`) `-> 99.000` (split `a=191 -> 4`).
- Proper powers exactly: **odd `n`, `l>=n/3`: `Theta_l(1)=1`, only `x^n`**. Even
  `n`: `E_l[2^v] = ker(E_l -> E_{floor(l/2^v)})`, so `2^l` times the `r=2` term
  is `2^{n/2}|E_l[2]|` -- literally Gao's `|{eps^{1/2}}|`, same argument.
- **B1--B5 FOUND NO UNCONDITIONAL `F > 1`.** B1 low orders: `Y_j = 0` if `Q|j`,
  else `2^{j-1-j/Q}`; a `2^{-23}` share at `ell=200`, so free even at infinite
  saving = `1 + 3.0e-8`. B2 the `W` term: `Phi(a)` is strictly INCREASING in `a`,
  so the split only costs (`1.10x`-`1.33x`) and `a>=4` is forced. B3:
  Cauchy--Schwarz on the unconditional 2nd moment gives `(ell-2)/
  sqrt(ell^2-4ell+6) < 1`, WORSE than the triangle inequality (Weil saturates
  the moment it is fed); on Sato--Tate it gives `sqrt(ell-2)=14.07`, i.e. `k=4/3`,
  half the Weil `k`, but KR is `q -> oo`. B5: the trivial bound needs
  `j-1 >= 2^{n/2}` (short by `2^{193.4}`) and the population route loses to Weil
  by `>= 3` at EVERY layer -- every unconditional upper bound on a population
  carries its own full Weil error.
- NEW EXACT FACT (why `a >= 4`): `E_2 = Z/4`, `deg L = 1`, `alpha = -(1+i^{+-1})`,
  so `|T_{2,2}(n)| = 2^{n/2+1}|cos(pi n/4)|` -- **conductor 2 SATURATES Weil when
  `4|n`**, `1/sqrt2` of it at odd `n`, vanishing at `n=2 mod 4` (conductor 3 then
  takes over at exactly `1/2`); all 22 endpoints. So a PER-PAIR `(HWO_k)` with
  any constant `>1` is false at `j<=3`; the aggregate form needs no repair and
  clears `F_req(0)` by 26x-565x at `ell<=18`, growing like `2^{ell/2}`.
- **THE NEGATIVE IS FORCED.** Note 03 sec. 5's fake population, optimised over
  its own split, exists at level `l` iff `2^{n/2-l} <= A*(l) = max_a (a-1)
  (1-2^{a-1-l})`; that boundary EQUALS the Weil boundary at 22 of 26 endpoints
  (gap of one at `(12,26),(24,50),(100,201),(30,61)`). B1--B5 are all
  moduli-only, so no `k < k_Weil` was ever available.
- SMALLEST `k` PROVED: unchanged, 8 at `(200,401)`, 7 at `(200,402)`,
  `= log_2 n - 1 + O(1)`, i.e. Hayes 1965. NO NEW RUNG; what is added is the
  calibration, the `5.7x`/`8.1x` constant, and the ceiling proof.

## Entry 10 -- almost all degrees

Lane `lemire-signed-trace`, 2026-08-23. Note 20; checker
`lemire_almost_all_degrees.py` (11 checks, 10 mutation controls each tripping
exactly one, ~4 s; data `aad-*.txt`).

- TARGET (AAD) `#{n<=N : W_n holds no irreducible} = o(N)`. NOT proved, and it
  gives NO prime degree and NO power of two -- where Barrier III is also silent.
- REDUCTION (Thm 1-2). Split `d_n=(N_ell(1)-2^h)/2^h` at `a=ell-ceil(log2 ell)-1`.
  Low block `< 2^{-5/2}` (n odd) / `< 2^{-3}` (n even) UNIFORMLY and SHARPLY
  (sup 0.17672/0.12496 over `5<=ell<=10^6`). Then `|d^top|<=0.34 => I_n>=1` for
  `n>=26`: AAD follows from `sum_{n<=N}|d^top_n|^2 = o(N)`.
- NULL RESULT (Thm 4), the point. For ANY angle multiset `delta^{-1}>=D` and
  `Sigma_2>=Sigma_1^2/D`, so the Montgomery-Vaughan bound
  `(T+delta^{-1})Sigma_2/lambda^2` is ALWAYS `>= Sigma_1^2/lambda^2`: the large
  sieve's own error term contains the trivial bound and never says anything at a
  PRESCRIBED point. At the KL threshold the floor is `4.32(ell-1)^2` exceptional
  degrees against the `<=2ceil(log2 j)+4` degrees whose TOP block holds
  conductor `j` (Thm 3) -- vacuous by 8565x at `ell=200`. What survives is the
  off-diagonal at `T=O(log ell)`: fixed-`q` PAIR CORRELATION, note 00's wall.
- SLACK (Thm 8). Hsu/Cohen `k*(n)~log_2 n-1` for ALL n; the large-sieve slack
  is `k*+1` or `k*+2`, NEVER less. Averaging buys ZERO coefficients, so
  `k=O(1)` and `k=c log n`, `c<1`, are both out of reach. `k*(401)=8`,
  `k*(402)=7`: independent concordance with Entry 8, now gated in CHECK F.
- Cand. 2: under the ONLY canonical comparison of different `ell` (the tower
  projections) the identity is a FIXED POINT, so "the exceptional set moves" is
  contentless without a measure on `{X_ell}`, and the sole structure-preserving
  source of one is a group action = Barrier II (Prop 6). Not the same statement.
- MEASURED, 46 endpoints, every `ell` in 2..24: an INDEPENDENT python L-function
  engine reproduces all 18 endpoints `ell<=10` EXACTLY, two CAS producers agree
  at 13 more. `z=D_n/sd` rms 1.400, max 3.328 (identity is a TYPICAL class);
  consecutive-`ell` r=-0.066/-0.056, nothing to average. NEW, no mechanism: the
  two degrees of ONE group are ANTI-correlated, r=-0.657 (Spearman -0.617, perm
  p=2.6e-4, jackknife [-0.70,-0.54]) -- but a PERFECT one gives density 1/2.
  Angles repeat EXACTLY (j=9,10,11: 252/488/994 distinct L-polys), so `delta=0`.
- MARGIN, flint search over 479 degrees: `s_min <= 10` for all `n<=410`
  (reproduces Arndt), `<=13` to 3000; equality `s_min=floor(n/2)` ONLY at 2,3,5,8.
- TRAP: `pkill -f "<pat>"` matched THIS shell (the pattern sits in the wrapper's
  own cmdline), killing the invocation mid-heredoc: the script it was writing
  never existed and the relaunch silently did nothing.

## Entry 11 -- the probabilistic face

Note 21; `lemire_probabilistic.py` (23 checks, 8 controls, ~7 s); `data/prob-*.txt`.
An embedded Hayes-character engine (pure python, no CAS) reproduces `D_n` EXACTLY
at all 20 endpoints `ell<=11`, `N_5(1)=45`, `N_7(1)=472`, and Entry 8's 11 flint
`Theta_ell(1)` (extended to `ell=19..24`).

- (A) VARIANCE STATEMENT: `Sigma_j <= C 2^{j-1}(j-1)2^n`, Weil over `(j-1)`. The
  saving MUST be `j`-dependent -- `Sigma_2 = 2^{n+1}` EXACTLY at every endpoint,
  so a uniform proportional saving over Weil is FALSE. 242 rows, `12<=ell<=22`:
  `mean C_j = 1.000` at EVERY `j`, `sup_j = 2.179`, `sup_{j>=14} = 1.047`,
  aggregate `1.0274`. NEW: Barrier I's fake population satisfies `(VAR)` iff
  `k <~ k_Weil/2`, so `(VAR)` opens exactly `[k_Weil/2, k_Weil)` -- Entry 8's
  `F=sqrt(ell-2)` rung, by a different computation.
- (B) FOUR TOOLS, FOUR OBSTRUCTIONS, ONE CONSTANT `(ell-1)/(2 kappa)`. Negative
  association: `sum_g N = 2^n` forces EXACTLY `sum_{t!=0}(R(t)-2^{2n-ell}) = -V`,
  but Barrier I's `F` has a SMALLER second moment, hence MORE negative
  correlation and an empty identity class -- it runs backwards. Doob martingale
  along the tower: increments ARE the `H_j`, `b_ell/2^{n-ell} = (ell-1)/(2 kappa)`
  exactly, no concentration inequality beats the largest increment bound,
  Freedman dies on the same term, `max_g|D_2(g)|/b_2 = 1` at even `n`.
  Chen--Stein: `d_TV` to Poisson has a REAL floor `~1/n`, short of resolving one
  class in `2^ell` by `2^{18}/2^{191}/2^{1013}` at `n=50/402/2050`, its `b_2`
  term being the fixed-`q` pair correlation -- clean impossibility. Extreme
  value: `max_g|D|/sd` is `0.76-1.19` x Gumbel, but NEW, the identity's RANK
  among the `2^ell` classes has quantile mean `0.311` vs uniform `0.500` (3.08
  sigma low) and hits the top 5% at 6 of 22 endpoints vs 1.10 expected
  (`p=9.7e-4`): **the identity is NOT typical**, and Entry 10's `rms z = 1.400`
  was that same signal read as agreement.
- (C) THE ANTI-CORRELATION IS SOLVED. Not normalisation: `z_n =
  -2^{-ell/2}G_ell(n)/sqrt(ell-2+2^{1-ell})`, so the `2^{ceil(n/2)}` convention
  is not in `z` at all. Not proper powers: `-0.661 -> -0.622` after removing the
  square mass exactly. It is EXACT ANGLE REPEATS: `76-85%` of `sum m_theta^2`
  sits at `theta in (1/8)Z`, dominated by `3/8, 5/8` = the conductor-2 Kerdock
  roots `-(1 -+ i)`, `cos = -1/sqrt2`. The weight is `m^2`, NOT `m` -- exactly
  why Entry 10's `g_j(1)` was two orders too small; `rho_k = (sum m^2 cos 2pi k
  theta - m_0^2)/(sum m^2 - m_0^2)` matches the measured autocorrelation to
  `0.008` at every `ell`. SHARPER: the 8-periodic atom phase gives a `mod 8` SIGN
  LAW for `z_n`, right at 42 of 45 endpoints (`p=4.3e-10`); 3 of 4 residue
  classes get opposite signs, so `r ~ -1/2` and `-0.657` is 1.41 sigma from it.
- (D) MODEL: right WITHIN a character (2nd/3rd/4th moments, the max), wrong
  ACROSS characters (`Sigma_2^A/Sigma_1^A = 18` at `ell=13`; block corr mean
  `+0.452`; `Var(G) = 2.32 sum_j Var(g_j)`). Still finitely many bad `n`, exponent
  `2^{ell} -> 2^{0.33 ell}`. OPEN and new: the atom term is `~2^{-0.07 ell}` in
  `d_n` while `|z|` stays `O(1)`, so the non-atomic part must cancel it ever more
  precisely; a lower bound on that residual would be a new handle.

## Entry 9 -- effectivising the large-q theorem (coordinator, from note 19)

Strategy 2. The agent was killed by the coordinator before it wrote this entry
(see the incident at the end); its note, script and data are complete and its
checker passes, so this entry is written from
[note 19](19-effective-large-q.md).

- **No Siegel mechanism anywhere in the chain.** Every `L`-function is a
  polynomial, every bound is Weil/Deligne plus elementary counting, every
  "sufficiently large" is a limit with an explicit rate. The ineffectivity in
  Bagshaw Cor. 2.5 is **pure bookkeeping**, as the prior predicted.
- **But the bookkeeping, done honestly on the argument as written, gives
  `n_0(3^11) ~ 10^{344.5}`.** ONE step is responsible: both Bagshaw and
  Sawin--Shusterman invoke the POINTWISE divisor bound
  `tau(x) = O_eps(q^{eps deg x})` at an `eps` their own proof drives down to
  `8.63e-4`, where the extremal constant is `q^{10^{341.2}}`. Nothing else in
  the chain is worse than `q^{O(1)}` times a polynomial in `n`.
- **The fix is known and exact, not conjectural.** Over `F_q[T]` the AVERAGED
  divisor identity `sum_{deg x = m} tau(x) = (m+1) q^m` is an identity with no
  `eps` at all, and every pointwise `q^{eps n}` in Bagshaw sec. 4--5 and
  Sawin--Shusterman sec. 4 sits inside a sum over the variable it bounds. That
  rewrite is routine and **it is not done**; it is the whole remaining task.
- **Two of the coordinator's briefing assumptions were WRONG.** (i) The
  `omega` trade-off is inverted: constants do NOT blow up as `omega -> 1/2`;
  `omega = 1/2` is optimal in both directions. What degrades near the endpoint
  is only the odd-`n` requirement `omega >= 1/2 + 1/(2n)`, already satisfied at
  `q = 3^11` for every odd `n >= 78`. **The window is not the blocker; the
  implied constant is.** (ii) Coefficient slack is not a lever either: with
  `k = 1` the Hsu/Cohen range jumps from odd `n <= 839` to `n <= 1.49e8`, and
  `k = 2` to `2.6e13`. **The gap exists ONLY at the exact half-degree
  endpoint** -- the lane's standing diagnosis, reached from a new direction.
- **`3^11` is the smallest admissible `q` but not the best target.** Under a
  polynomial-constant hypothesis the Bagshaw and Hsu/Cohen ranges first meet
  with no gap at `q = 3^14`, and robustly (any `C <= q^10 n^6`) at `3^17`.
- **Closed unconditionally today over `F_{3^11}`:** every even `n <= 354292`
  and every odd `n <= 839` (Hsu/Cohen), plus 363 certified witnesses --- every
  odd `n` in `[841, 1199]`, and odd `n` in `[1201, 1601]` with `11 nmid n`
  (the sparse tier uses an `F_3`-carrier trick that fails when `11 | n`, so
  the 18 odd multiples of 11 in that range are EXCLUDED BY CONSTRUCTION, not
  unresolved). Solid to odd 1199; sparse to 1601 with 18 holes. Do not quote
  this as "certified to 1601".

**Incident (coordinator, 2026-08-23).** This agent's witness search spawned
**729 concurrent worker processes** (`search.py 841 3001`, one python per
degree-block, each at ~65% CPU) and ran for nearly three hours, driving the
shared box to load 39 and starving the session that launched it. It was killed
by process group -- `kill -- -$PGID` after checking `PGID != $(ps -o pgid= -p
$$)`, NOT by `pkill -f`, which this diary already records as matching the
invoking shell itself. Lessons: (i) a subagent given a compute budget in prose
will not enforce it; if a brief permits a parallel search, it must also state a
worker cap; (ii) the results the agent actually needed (through 1601) were
written 20 minutes in -- the remaining 2h40m was an unrequested extension to
`n = 3001` that produced nothing that landed.
