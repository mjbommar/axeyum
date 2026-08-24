# AC-Bridge phase 2, workstream D -- the rank/Arf split: falsifying `(GR-2)`,
# and what replaces `(E2')` and `(S)` once the fibres are looked at directly

Workstream: AC-Bridge (`docs/research/10-cas/ac-bridge-2026-08/00-charter.md`),
phase-2 board `10-angles-board.md`, workstream **D**.
Opened: 2026-08-20.
Scope: ad hoc research, outside roadmap/gates/fact-ledger.  Nothing here changes
lane state.

Epistemic law (charter rule 3): finite computation is EVIDENCE, never a theorem.
Every claim below is labelled **PROVED** (with the argument written out) /
**REFUTED** (with a witness) / **OPEN** / **EVIDENCE**.  Literature is fetched,
never recalled.

New code, all of it new files (charter rule 1 -- no existing source touched):

```text
crates/axeyum-cas/examples/acb_gr_fibre_census.rs   independent fibre census
crates/axeyum-cas/examples/acb_gr_orbit_profile.rs  twist orbits + completion
```

Both share **no code** with `gf2_hayes`: the Moebius sign is recomputed from a
smallest-irreducible-factor sieve over `GF(2)[x]`, the principal-unit inverse
from its own recursion, the fibres from their own grouping.  Each then
cross-checks its aggregates against the in-tree
`binary_dyadic_autocorrelation_fibre_report` and **exits nonzero** on any
disagreement or failed structural invariant, so a green run is a finding and
not merely a completion (CLAUDE.md's rule on self-checking evidence).

Notation is the charter's, plus: `eps(m) = mu(f_m) mu(f_(m+h))` the fibre sign,
`c_F = sum_(m in F) eps(m)`, `n_F = dim F`, `N_points = sum_F |F|`,
`N_sf = #{points with eps != 0}` (both members squarefree),
`Delta = sum_F c_F`.

---

## Log

### [t0] 2026-08-20 -- orientation, and an object mismatch found on the first read

Read in order: the charter; `10-angles-board.md`; `03-lit-galois-ring-fourier.md`
**in full**; `adhoc-blocker-sweep-2026-08-20/08-boolean-complexity.md`;
`04-weak-target-verification.md` (the `(E2')` section and the `(WK)` derivation);
the lane ledger `docs/plan/status/52-gf2-lemire.md` for the proved
Artin--Schreier kernel dimension and the proved parallelogram identity; the
`(E2')` accumulator `crates/axeyum-cas/examples/acb_wt_e2prime.rs`; and the
report struct `BinaryDyadicAutocorrelationFibreReport` in `gf2_hayes.rs`.

**Label collision to record before anything else.**  Diary 03 numbers its own
candidates twice.  In `[t6]` the rank-count reformulation of `(E2')` is called
`(GR-4)` and the Arf-sign statement `(GR-5)`; in the `(d)` list they are
`(GR-3)` and `(GR-4)`, with `(GR-5)` the incomplete-orbit reframing.  **I adopt
the `(d)` list as canonical** (it is the one written as falsifiable candidate
statements) and say so wherever a number is used.

**The object mismatch.**  Sweep-08's Problem T and diary 03 both write the fibre
quantity as a Gauss sum

```text
G(p) = sum_(x in A_p) chi_8(q_p(x))  in {0} union {+- 2^j},
```

and diary 03 then treats it under Brown/Taylor/Schmidt as
`sum_x zeta_8^(Q(x))` for a `Z/4`-valued Brown form `Q`.  These are not the same
object, and reading the shipped code settles which one the lane computes.
`accumulate_binary_dyadic_shift_fibres` forms
`phase = (residues[m] * residues[m ^ shift]) % 8` and accumulates
`kronecker_two_mod_eight(phase)`, i.e. the **dyadic character** `chi_8`, whose
values are `{0, +-1}` -- not `zeta_8`.  Because `chi_8` is multiplicative and the
lane has PROVED `mu(f) = (-1)^deg chi_8(Disc F)`, the two degree signs cancel and

```text
   eps(m) = chi_8(Disc(f_m) Disc(f_(m+h))) = mu(f_m) mu(f_(m+h)).
```

So `c_F` is a **restricted Moebius autocorrelation**, a sum of `2^(n_F)` terms
each in `{0, +1, -1}`, and its zeros are Moebius zeros (squareful inputs), not
degenerate Gauss sums.

This matters immediately for `(GR-2)`.  Diary 03 states the hypothesis with an
"equivalently" clause: *"the fibre phase is `2 x (a Brown Z/4 form)` -- linear
`Z/8`-ANF coefficients even, quadratic ones in `4Z/8`, none above degree 2."*
By diary 03's own `[t3]`, `psi = 2Q'` takes values in `2Z/8 = {0,2,4,6}`, i.e.
**even everywhere**, and `chi_8` vanishes on every even residue.  So a fibre
satisfying the "equivalently" clause has `c_F = 0` identically, and the clause is
incompatible with the "`c_F != 0`" hypothesis of the same sentence.  Taken
literally `(GR-2)` is self-contradictory.

That is a cheap refutation resting on a mis-transcription, so I did **not** stop
there.  The charitable and correct reading -- the one the lane's own proved
Arf/second-trace realization of `mu` supports -- is the classical `F_2`
statement:

> **`(GR-2)` (charitable form).**  On a fibre with `eps` nowhere zero, write
> `eps = (-1)^(q_F)` with `q_F : F -> F_2`.  Then `q_F` is quadratic, and with
> `r_F` the rank of its (automatically alternating) bilinear form,
> `c_F = (-1)^(Arf(q_F^red)) 2^(n_F - r_F/2)` when tame and `0` otherwise.

Everything below tests **this** form.  It is the strongest version that can be
true, and the `+-2^(n - r/2)` value set and the Arf sign are exactly the
classical `F_2` quadratic-form Gauss sum, so nothing is lost by dropping the
`Z/8` framing -- which diary 03's own `[t3]` had already proved to be empty.

### [t1] Lemma D1: the fibres are shift-stable, and half the second moment is forced

**Lemma D1.  PROVED.**  Every exact affine fibre `F` at parameters
`(ell, k, d)` is stable under `m -> m xor s`, and `eps(m xor s) = eps(m)`.

*Proof.*  The report enumerates shifts `s in [1, 2^d)` and keys fibres by
`(m / 2^d, inv[m] xor inv[m xor s])`.  Since `s < 2^d`, `m` and `m xor s` differ
only in the low `d` bits, so `m / 2^d = (m xor s) / 2^d`: same input coset.  The
inverse difference `inv[m] xor inv[m xor s]` is symmetric in the pair, so `m` and
`m xor s` carry the same key.  Hence `m in F => m xor s in F`.  And
`eps(m) = mu(f_m) mu(f_(m+h))` is symmetric in `f_m <-> f_(m+h)`, i.e. invariant
under `m -> m xor s`.  QED

**Corollary D1a.  PROVED.**  `c_F` is even for every fibre, `n_F >= 1`, and

```text
   sum_F c_F^2  =  2 N_sf  +  Theta,
   Theta := sum_F sum_(y not in {x, x xor s}) eps(x) eps(y).
```

*Proof.*  `sum_F c_F^2 = sum_F sum_(x,y in F) eps(x)eps(y)`.  The terms `y = x`
give `eps(x)^2 = 1[eps(x) != 0]`; the terms `y = x xor s` give
`eps(x)eps(x xor s) = eps(x)^2` by D1, and `x xor s != x`.  Together they
contribute `2 N_sf`.  QED

**This corrects sweep-08's `(E2')` identity and the in-tree doc comment.**
Sweep-08 `[t8]` writes `sum_F c_F^2 = N_points + sum_(x != y) eps(x)eps(y)` and
concludes that `(E2')` "is exactly *the within-fibre off-diagonal correlation is
non-positive*"; `BinaryDyadicAutocorrelationFibreReport::within_fibre_off_diagonal_correlation`
carries the same claim in its doc comment ("Subtracting `total_fibre_points`
gives the exact within-fibre off-diagonal dyadic correlation").  Both are wrong
whenever `eps` vanishes anywhere, i.e. on essentially every fibre: the diagonal
is `N_sf`, not `N_points`, and the `s`-partner term is also forced.  The honest
identity is Corollary D1a.  (Recorded per CLAUDE.md's standing warning that in
this repository the *tools and comments* have lied more often than the solver.)

### [t2] The corrected `(E2')`: the plateau at 0.889 is a forced diagonal

`acb_gr_fibre_census.rs`, 22 rows, both endpoint parities, `ell = 4..14`.  Every
row cross-checks `fibre_count`, `points`, `sum c^2`, `Delta`, `sum|c|`,
`nonzero_fibres` and `power_of_two_fibres` against the in-tree report; a
mismatch aborts with a nonzero exit.

```sh
cargo build --release -p axeyum-cas --example acb_gr_fibre_census
./target/release/examples/acb_gr_fibre_census 4 12    #  22.6 s
./target/release/examples/acb_gr_fibre_census 13 13   #  47.3 s
./target/release/examples/acb_gr_fibre_census 14 14   # 169.6 s, well inside budget
```

```text
 ell   k   d      points        N_sf      sum c^2      Theta  Theta/pts  2N_sf/pts  c2/pts   Delta
   4   6   3         128          50           68        -32  -0.250000   0.781250 0.531250      -2
   4   7   3         256         106          196        -16  -0.062500   0.828125 0.765625     -14
   5   7   4         576         256          408       -104  -0.180556   0.888889 0.708333     -28
   5   8   4        1152         478          884        -72  -0.062500   0.829861 0.767361       6
   6   8   5        1920         820         1472       -168  -0.087500   0.854167 0.766667     -32
   6   9   5        3840        1670         3572        232  +0.060417   0.869792 0.930208     138
   7   9   6        8448        3712         7904        480  +0.056818   0.878788 0.935606      16
   7  10   6       16896        7460        14520       -400  -0.023674   0.883049 0.859375     -96
   8  10   7       32256       14200        27904       -496  -0.015377   0.880456 0.865079    -128
   8  11   7       64512       28496        57968        976  +0.015129   0.883433 0.898562    -188
   9  11   8      130048       57660       120680       5360  +0.041216   0.886750 0.927965     -68
   9  12   8      260096      115196       233576       3184  +0.012242   0.885796 0.898038    -236
  10  12   9      522240      231642       461204      -2080  -0.003983   0.887109 0.883127    1170
  10  13   9     1044480      463538       919588      -7488  -0.007169   0.887596 0.880427    -314
  11  13  10     2125824      948172      1877080     -19264  -0.009062   0.892051 0.882989   -1592
  11  14  10     4251648     1888868      3754360     -23376  -0.005498   0.888535 0.883036     452
  12  14  11     8380416     3729610      7450844      -8376  -0.000999   0.890078 0.889078    -894
  12  15  11    16760832     7460780     14905072     -16488  -0.000984   0.890264 0.889280    -108
  13  15  12    33669120    14961868     29953880      30144  +0.000895   0.888759 0.889654    -948
  13  16  12    67338240    29919980     60074488     234528  +0.003483   0.888648 0.892130    8356
  14  16  13   134184960    59628850    119676844     419144  +0.003124   0.888756 0.891880   -8670
  14  17  13   268369920   119263628    238505120     -22136  -0.000082   0.888800 0.888718    -136
```

**Result D-1 (EVIDENCE, 22 rows).  Diary 04's "`(E2')` plateaus at 0.889" is
entirely the forced diagonal.**  `2 N_sf / N_points` sits at
`0.8888 +- 0.0002` from `ell = 12` on, and `sum c^2 / N_points` tracks it to
within `0.003`.  The *genuine* off-diagonal `Theta` -- the part not forced by
Lemma D1 -- is `o(N_points)`: `|Theta| / N_points` falls from `0.25` at
`ell = 4` to `<= 0.0035` for `ell >= 12`, and it changes sign.

**Result D-2 (REFUTED, with witnesses).  Sweep-08's reading of `(E2')` as
"the within-fibre off-diagonal correlation is non-positive" is false.**  The
reported quantity `sum c^2 - N_points` is negative on all 22 rows, but the
quantity it is *called* -- the true off-diagonal `Theta` -- is **positive** on
7 of 22 rows: `(6,9,5): +232`, `(7,9,6): +480`, `(8,11,7): +976`,
`(9,11,8): +5360`, `(9,12,8): +3184`, `(13,16,12): +234528`,
`(14,16,13): +419144`.  Positivity of the within-fibre off-diagonal correlation
is not available as a hypothesis.

### [t3] `(GR-2)`: REFUTED, three independent ways, with witnesses

The census classifies each fibre.  A fibre is **zero-free** when `eps` never
vanishes on it -- the only case in which a sign function `q_F` exists at all.

```text
 ell   k      pow2   pow2_not_zero_free   |c|>=6   pow2 among |c|>=6   zero-free   zf points/fibre   ranks
   9  11     12456                11114      648                 189        2518             4.000     0:2518
  10  12     49283                44211     2445                 691       10148             4.000    0:10148
  11  13    197916               177164     9388                2606       41166             4.000    0:41166
  12  14    783702               701592    35330               10082      163810             4.000   0:163810
  13  15   3142701              2818875   140411               39139      648160             4.000   0:648160
  14  16  12567001             11269863   555786              156638     2593622             4.000  0:2593622
  14  17  25129678             22539268  1107620              311356     5185840             4.000  0:5185840
```

**(GR-2) REFUTED, witness class 1 -- the hypothesis class is empty on 89% of the
very fibres it is about.**  At the pinned witness `(9,11,8)`, `11,114` of the
`12,456` power-of-two fibres are **not** zero-free, i.e. carry a Moebius zero, so
`eps` cannot be written as `(-1)^(q_F)` and no rank, no Arf and no
`+- 2^(n - r/2)` is defined for them.  The fraction is stable and rising:
`89.2%` at `ell = 9`, `89.7%` at `ell = 14`.  The census prints a concrete
witness on every row, e.g.

```text
ACB_GR_CENSUS|witness|ell=9,k=11,d=8,shift=2,origin=0,dim=4,points=16,nonzero_points=8,c_F=-8
```

a `16`-point fibre with `8` Moebius zeros and `c_F = -8`, an exact power of two
produced with no quadratic form anywhere in sight.

**(GR-2) REFUTED, witness class 2 -- on the sub-family where it *is* well posed,
it is true but vacuous.**  Every zero-free fibre, at every one of the 22 rows,
has `zero_free_points / zero_free_fibres = 4.000` exactly: **all zero-free fibres
have dimension exactly 2**, and every one has bilinear rank `0`
(`ranks = 0:N` on every row, `zero_free_nonquadratic = 0` on every row).  A
rank-`0` quadratic function is affine; by Lemma D1 it is constant on the
`2`-element `s`-orbits, so on a dimension-2 fibre affineness is *forced* and
carries no information.  The rank/Arf stratification of this family therefore has
exactly one nonempty stratum, the degenerate one, and the Arf invariant never
does any work.  Diary 03's `[t6]` dictionary (`c_F = 0` or
`(-1)^(Arf) 2^(n - r/2)`, with all even ranks available) describes a family that
does not exist here.

**(GR-2) REFUTED, witness class 3 -- the powers-of-two measurement it rests on is
nearly forced.**  By Corollary D1a every `c_F` is even, so "`|c_F|` is a power of
two" means `|c_F|/2 in {1,2,4,8,...}`, and the magnitude histogram is dominated
by `|c_F| = 2`.  Conditioning on `|c_F| >= 6` removes the forced part:
`189` of `648` (`29%`) at `ell = 9`, `156638` of `555786` (`28%`) at `ell = 14`.
Diary 03 and sweep-08 read `96.4%` as evidence of Gauss-sum structure; the
structural content is a factor of two from Lemma D1, and past that the
power-of-two rate is `28%`, i.e. **the Gauss-sum picture is absent exactly where
it would matter**.  (A true quadratic Gauss-sum family would be `100%` powers of
two, with no `6`, `10`, `12`, `14` at all.)

### [t4] Lemma D3: why no fibre above dimension two can be zero-free -- PROVED

Class 2 above is not a probabilistic accident and I can prove it.  Under a naive
independence model, a dimension-4 fibre is zero-free with probability
`(2/3)^16 ~ 1.5e-3`, so the `262,144` dimension-4 fibres at `(12,15,11)` should
produce roughly `400` zero-free ones.  Observed: `0`.  The census also reports
the deficit histogram, and at `(9,11,8)`:

```text
dim=2  fibres=16384  max_nonzero=4    deficits=0:2518,2:9537,4:4329
dim=4  fibres=2048   max_nonzero=12   deficits=4:110,6:205,8:731,10:695,12:288,14:19
dim=6  fibres=416    max_nonzero=42   deficits=22:1,24:17,26:52,...
```

The dimension-4 deficit **never** falls below `4 = 2^(4-2)`.  That is the theorem:

**Lemma D3.  PROVED.**  Let `F` be a fibre of dimension `n` whose direction space
`T_h` is such that the two `F_2`-linear functionals `lambda_1(f) = f(1)` and
`lambda_2(f) = f'(1)` are independent on `T_h`.  Then `F` contains exactly
`2^(n-2)` polynomials divisible by `(x+1)^2`, each of which has `mu = 0`.  In
particular `F` is not zero-free and `|c_F| <= (3/4) 2^n`.

*Proof.*  Over `F_2`, `(x+1)^2 = x^2 + 1`, and `(x+1)^2 | f` iff `(x+1) | f` and
`(x+1) | f/(x+1)`, i.e. iff `f(1) = 0` and `f'(1) = 0`.  Both are `F_2`-linear
in the coefficient vector: `f(1)` is the parity of the number of nonzero
coefficients and `f'(1)` the parity of the number of nonzero odd-index
coefficients.  `F` is an affine subspace `f_0 + T_h`, so
`(lambda_1, lambda_2) : F -> F_2^2` is affine; if the linear part is surjective
its fibres all have size `2^(n-2)`, and one of them is the set in question.  A
polynomial divisible by a square has `mu = 0`.  QED

**Lemma D4.  PROVED.**  For every shift with `v(h) >= 2`, `lambda_1` and
`lambda_2` are independent on `T_h`.

*Proof.*  By Theorem D2 `[t6]`, `T_h = {tau : v(tau) + v(tau + h) >= ell + 1 - v}`
inside `span{x, ..., x^d}`.  For `v(tau) > v` we have `v(tau + h) = v`, so the
condition reads `v(tau) >= ell + 1 - 2v`; hence
`T_h` contains `span{ x^j : max(1, ell+1-2v) <= j <= d }`, of dimension
`min(2v - 1, d)`, which is `>= 3` for `v >= 2` and `ell >= 4`.  Three consecutive
powers contain two consecutive powers `x^j, x^(j+1)`; on them
`lambda_1 = (1,1)` while `lambda_2 = (1,0)` or `(0,1)`.  Two independent
functionals.  QED

**Corollary.  PROVED.**  Combining with Theorem D2's dimension formula
(`n = 2` exactly when `v(h) = 1`, `n >= 4` when `v(h) >= 2`): **no fibre of
dimension `>= 4` is zero-free**, and every such fibre satisfies
`|c_F| <= (3/4) 2^(n_F)` -- so a Gauss-sum value `+- 2^(n_F)` is impossible above
dimension two.  This is exactly the measured class 2, and it closes `(GR-2)`,
`(GR-3)` and `(GR-4)` as a program rather than as three separate data points.

The census checks Lemma D3 as an assertion (`square_forced_violations`) on every
fibre of dimension `>= 4`: **0 violations on all 22 rows**.  It also reports the
global count, which is exactly `N_points / 4` on every single row -- the
codimension-2 condition is exactly equidistributed over the admissible set.

### [t5] `(GR-3)`/`(GR-4)`: REFUTED, by a factor that converges to exactly 3

Diary 03's `(d)`-list `(GR-3)` asserts

```text
   (E2')  <==>  sum_(F tame) 2^(n_F) (2^(n_F - r_F) - 1)  <=  sum_(F not tame) 2^(n_F).
```

On the only stratum where its terms are defined (the zero-free fibres) the census
evaluates both sides exactly:

```text
 ell   k   tame rank-defect mass   non-tame point mass   ratio
   9  11                   16104                  4704    3.42
  10  12                   60864                 20304    3.00
  11  13                  249024                 81656    3.05
  12  14                  985320                326800    3.02
  13  15                 3885912               1297336    3.00
  14  16                15565656               5185936    3.00
  14  17                31084920              10381720    2.99
```

**REFUTED on every row, with the failure ratio converging to exactly `3`.**  The
reason is structural, not numerical: by `[t3]` class 2 all zero-free fibres have
`r_F = 0` and `n_F = 2`, so a tame one contributes
`2^2 (2^2 - 1) = 12` and a non-tame one `2^2 = 4`.  The inequality would need at
least three times as many non-tame as tame dimension-2 fibres, and the observed
ratio is `~1 : 1`.  The degenerate mass that makes `(E2')` true does **not** come
from vanishing Gauss sums; it comes from **Moebius zeros**, which the `(GR-3)`
bookkeeping does not contain a slot for.

### [t6] Theorem D2: the twist-orbit structure, in closed form -- PROVED

`acb_gr_orbit_profile.rs`.  Charge item 3 asks for the group, the orbit sizes and
the exact complete-orbit statement.  All three come out of the lane's own proved
inputs.

**Theorem D2.  PROVED.**  Fix a shift `h` (`h = s << 1`, `v = v(h) >= 1`), and
let `r = ell + 1`, `d` the interval degree.  Then:

1. `delta_h(f) = delta_h(f + tau)` iff `h tau (tau + h) = 0` in
   `GF(2)[x]/x^r`, i.e. iff `v(tau) + v(tau + h) >= r - v`, i.e. iff
   `tau^2 + h tau = 0` in `GF(2)[x]/x^(r-v)`.  (The lane's proved parallelogram
   identity; `tau -> h(tau^2 + h tau)` is `F_2`-linear by Frobenius, so the level
   sets of `delta_h` are cosets of a **group** `T_h`.)
2. Put `T_h := ker(tau -> tau^2 + h tau  mod x^(r-v))  intersect  span{x, ..., x^d}`,
   the intersection of that kernel with the input-coset direction space.  Then
   the level sets of `delta_h` inside one input coset are exactly the cosets of
   `T_h`, so **every exact affine fibre is a complete coset of `T_h`**, and
   ```text
      dim T_h = dim ker(z -> z^2 + h z  mod x^(r-v))  +  max(0, d - (r - v) + 1)
              = [ v + 1        if 2v < r - v ]  +  max(0, d - r + v + 1),
                [ floor((r-v)/2)  otherwise  ]
   ```
   using the lane's PROVED truncated Artin--Schreier kernel dimension.
3. The number of shifts with `v(h) = v` is `2^(d - v)`, `1 <= v <= d`.

*Proof of 2.*  The kernel condition is modulo `x^(r-v)`, so directions of
valuation `>= r - v` lie in it automatically, contributing
`max(0, d - (r-v) + 1)` dimensions; every kernel element has positive valuation
(a constant term would give valuation `0` in `tau^2 + h tau`), so the constraint
`v(tau) >= 1` is free and the truncation map from `span{x,...,x^d}` onto the
positive-valuation classes mod `x^(r-v)` is onto.  QED

`acb_gr_orbit_profile` computes the stabiliser by brute force and **asserts** the
closed form on every shift of every row, aborting with the offending shift if it
fails.  At `d = ell - 1` the measured dimension histograms are reproduced
exactly, e.g. `ell = 9`: `2:128, 4:64, 6:56, 7:6, 8:1`; `ell = 13`:
`2:2048, 4:1024, 6:512, 8:384, 9:96, 10:24, 11:6, 12:1`.  **0 mismatches on all
20 rows** (`ell = 4..13`).

**Consequence, and it contradicts diary 03's picture of the geometry.**  Diary 03
`[t6]`/`(GR-1)` concluded "the Lemire fibre family is emphatically NOT a union of
complete twist orbits; all of its cancellation comes from the orbits being
incomplete."  For the actual acting group the opposite holds: **every fibre is a
complete `T_h`-orbit, exactly.**  The incompleteness lives one level up, in
*which* orbits are admitted, and that selection is by the linear condition
`deg delta_h <= d`.  Diary 03's `(GR-1)` corollary ("complete orbits all
contribute the same sign, so `Delta / l2 -> sqrt(M)`") does not transfer, because
its orbit sums are Brown-form Gauss sums with a fixed Arf sign, whereas a
`T_h`-orbit sum here is a Moebius correlation with no forced sign at all -- as
`[t3]`--`[t5]` establish.

### [t7] The amplification inequality: a Burgess-style completion that is an exact identity

With the charter's pinned `d = ell - 1`, the admissibility condition
`delta_h >> (d+1) == 0` says precisely that the coefficient of `x^ell` in
`delta_h` vanishes -- an `F_2`-linear condition of **index two**.  So the
indicator expands into exactly two additive characters and the Burgess-style
completion loses nothing:

**Theorem D6 (the completion identity).  PROVED.**

```text
   2 Delta = A + B,
   A = sum_(h != 0, deg h <= d) sum_(f) mu(f) mu(f + h)                (complete orbits)
   B = sum_(h != 0, deg h <= d) sum_(f) (-1)^(delta_h(f)_ell) mu(f) mu(f + h).
```

*Proof.*  `1[b = 0] = (1 + (-1)^b)/2` applied to `b = ` the `x^ell` coefficient
of `delta_h(f)`, summed against `mu(f)mu(f+h)` over the full domain and all
nonzero shifts of degree `<= d`.  `delta_h` is constant on `T_h`-orbits
(Theorem D2), so the two characters are constant on orbits and the identity is
simultaneously an orbit-level and a point-level statement.  QED

`A` is the **complete-orbit term**: the *unrestricted* binary Moebius
autocorrelation summed over the whole shift range.  `B` is its twist by the single
nontrivial character of the quotient.  `acb_gr_orbit_profile` asserts
`2 Delta = A + B` and `sum(admissible orbits) = report fibre count` on every row.

```text
 ell   k   d      orbits  admissible  completeness      A       B   Delta   sum|A_h|  2^((k+d+1)/2)
   9  11   8       37812       18884      0.499418   -260     124     -68       5536           1024
   9  12   8       75624       37768      0.499418    380    -852    -236       7780           1448
  10  12   9      150964       75460      0.499854   -558    2898    1170      14798           2048
  10  13   9      301928      150920      0.499854   -314    -314    -314      20930           2896
  11  13  10      601524      300932      0.500283  -1092   -2092   -1592      43868           4096
  11  14  10     1203048      601864      0.500283  -1956    2860     452      66172           5793
  12  14  11     2399668     1199748      0.499963  -2158     370    -894     135686           8192
  12  15  11     4799336     2399496      0.499963   -122     -94    -108     187806          11585
  13  15  12     9596340     4798340      0.500018  -4420    2524    -948     382236          16384
  13  16  12    19192680     9596680      0.500018  -1316   18028    8356     553008          23170
```

**Result D-3 (EVIDENCE + PROVED identity).  The orbit-completeness profile is
exactly `1/2`, and the completion is lossless.**  `admissible / total` is
`0.500018` at `ell = 13` and never leaves `[0.49, 0.556]`, as the index-two
selection requires.  `(|A| + |B|) / (2|Delta|)` lies in `[1.0, 5.4]` over 20 rows
-- there is no exponential loss anywhere in the completion.  The `(10,13,9)` row
even has `A = B = Delta = -314`.

**Result D-4 (a stopping result, EVIDENCE with a clean exponent).  A per-shift
Chowla theorem, however strong, cannot deliver the connected target.**  The
boundary mass a naive Burgess argument would pay is enormous
(`boundary_absolute = 33,316` against `Delta = -68` at the pinned witness), but
that is not the operative obstruction, because Theorem D6 pays no boundary at
all.  The operative obstruction is one level in: taking absolute values
**shift by shift** already overshoots.  Mean `|A_h|` is at square-root scale
(`135686 / 2047 = 66` against `2^(k/2) = 128` at `(12,14,11)`, i.e. `0.52
* 2^(k/2)`), so per-shift square-root cancellation is empirically *true* -- and
still

```text
   sum_h |A_h| / 2^((k+d+1)/2)  =  5.4, 7.2, 10.7, 16.6, 23.3   (ell = 9..13, odd family)
```

growing exactly like `2^((d-3)/2) = 2^((ell-4)/2)`.  **Cancellation across shifts
is mandatory and carries a full `2^(ell/2)`.**

**Literature check (fetched 2026-08-20, not recalled).**  The complete-orbit term
`A` is the binary Moebius autocorrelation, so the relevant theorem is
Chowla-for-function-fields.

- **D. Carmon, "The autocorrelation of the Moebius function and Chowla's
  conjecture for the rational function field in characteristic 2",
  arXiv:1409.3694** (<https://arxiv.org/abs/1409.3694>, abstract and ar5iv full
  text opened).  Abstract verbatim: *"We prove a function field version of
  Chowla's conjecture on the autocorrelation of the Moebius function in the limit
  of a large finite field of characteristic 2."*  Theorem 1.1 verbatim:
  *"Fix `r>1` and assume that `n>2` and that `q` is even.  Then for any choice of
  distinct polynomials `alpha_1,...,alpha_r in F_q[x]` with `max deg alpha_j < n`,
  and `eps_i in {1,2}`, not all even,
  `|C(alpha_1,...,alpha_r;n)| <= r n q^(n-1/2) + (3/4)(r+3) n^2 q^(n-1)`."*
  **This is exactly the theorem for `A`, and at `q = 2` it is vacuous**: the
  bound exceeds the trivial `q^n` once `q < (rn)^2`, and our regime is `q = 2`
  fixed with `n = k -> infinity`.  The fetch confirms the limit is `q ->
  infinity` with `n` fixed, i.e. the opposite corner of the parameter space.
  **PROVED (by citation) that the published characteristic-2 Chowla theorem does
  not reach this family.**
- **Carmon--Rudnick, arXiv:1205.1599** (large `q`, any characteristic) -- same
  corner.
- **Sawin--Shusterman, "On the Chowla and twin primes conjectures over
  `F_q[T]`", arXiv:1808.04001** -- abstract fetched; it states the results hold
  "for finite fields satisfying a simple condition", and **the condition is not
  in the abstract**.  Whether it admits `q = 2` is **UNVERIFIED**; do not cite
  this from here in either direction.
- **Kurlberg--Rosenzweig, "Prime and Moebius correlations for very short
  intervals in `F_q[x]`", arXiv:1802.01215** -- abstract fetched.  Two regimes:
  `q = p` with `p -> infinity`, and the harder fixed-`p`, `q = p^l -> infinity`
  case with "slightly weaker" results.  They also *"construct counterexamples
  showing intervals where the heuristic 'primes are independent' fails badly"*
  and exhibit cases with **no cancellation at all** in Moebius/Chowla-type sums.
  Again `q -> infinity`; and the counterexamples are a warning that short-interval
  Chowla statements can be false, which is directly relevant since our `A` is a
  short-interval-shaped sum (`deg h <= d = ell - 1` against `deg f = k`).

**Verdict on the `(S)` half via incomplete orbits.**  The Burgess opening diary 03
identified is real and I have made it exact: the completion costs nothing
(Theorem D6, index two).  But the object it completes to -- `A` -- is a fixed-`F_2`
Chowla sum over a short shift range, which the literature reaches only in the
large-`q` limit, and which needs cross-shift cancellation worth `2^(ell/2)` on
top of per-shift square-root cancellation.  **`(S)` is not obtained by
amplification; amplification converts it, at zero cost, into a fixed-field
Chowla-with-shift-averaging statement.**  That is a strictly better place to
stand than "square-root cancellation of a family of Arf signs", because the target
is now a named open problem in a well-populated literature rather than an
invented one.

### [t8] The other `(GR)` candidates, processed cheapest first

- **`(GR-1)` [diary 03: PROVED, L1].**  The identity for a full Brown twist orbit
  is correct as stated and I do not dispute it.  Its **corollary** ("a disjoint
  union of `M` complete twist orbits gives `Delta/l2 -> sqrt(M)`, so `(S)` cannot
  be obtained by completing orbits") is **inapplicable here**: by Theorem D2 the
  fibres *are* complete orbits of the genuine acting group `T_h`, and by
  `[t3]`--`[t5]` their sums are not Gauss sums with a fixed Arf sign.  The
  measured `Delta / l2` (mean `-0.317`, sd `0.953`, sweep-08) is therefore not
  evidence of orbit incompleteness; it is what the identity of Corollary D1a
  predicts once the diagonal is removed.
- **`(GR-2)`** -- **REFUTED**, `[t3]`, three witness classes, with the mechanism
  proved in `[t4]`.
- **`(GR-3)`** (the rank count) -- **REFUTED**, `[t5]`, failure ratio `-> 3`.
- **`(GR-4)`** (the Arf Moebius statement) -- **REFUTED as a reformulation**: it
  is equivalent to `(S)` only under `(GR-2)`, whose hypothesis class is empty on
  `>= 89%` of the nonzero fibres and degenerate on the rest.  The weighted
  Arf-sign sum it names is not the object `Delta`.
- **`(GR-5)`** (incomplete twist orbits) -- **REPLACED, and improved**: the
  correct group is `T_h`, the fibres are complete orbits, the incompleteness is an
  index-2 linear selection, and the completion is the exact Theorem D6 rather
  than a Burgess inequality.  This is the one candidate that survives in
  strengthened form.
- **`(GR-6)`** (is `sign(c_F)` multiplicative in `h_0/w_0`?)  -- **not tested
  here**; but its premise ("the Arf-shift formula predicts `sign(c_F)` is a
  quadratic function of the twist") is void, since `[t3]` shows `sign(c_F)` is not
  an Arf sign.  Recorded so the experiment is not run against a dead prediction.
- **`(GR-7)`** (exact fourth moment of a complete twist family) -- **true and
  irrelevant to this family**: it is a statement about `sum_u chi_Q(u)^4` for a
  Brown form, and `[t3]` shows the fibre sums are not `chi_Q`.  It remains a
  correct benchmark for the model problem.

---

## FINDINGS

### (a) `(GR)` verdicts

| Candidate | Verdict | Evidence |
|---|---|---|
| `(GR-1)` identity | stands, but **inapplicable** | fibres *are* complete orbits (Thm D2), and their sums are not Gauss sums |
| **`(GR-2)`** | **REFUTED** | 89.2%--89.7% of power-of-two fibres carry Moebius zeros (no sign function exists); all zero-free fibres have `dim = 2, r = 0`; conditional on `\|c_F\| >= 6` only 28% are powers of two |
| `(GR-3)` rank count | **REFUTED** | tame rank-defect mass exceeds non-tame point mass by a factor converging to exactly `3`, on all 22 rows |
| `(GR-4)` Arf Moebius | **REFUTED as a reformulation** | equivalent to `(S)` only under `(GR-2)` |
| `(GR-5)` incomplete orbits | **REPLACED and STRENGTHENED** | Theorem D2 + Theorem D6: exact index-2 completion |
| `(GR-6)` | premise void | `sign(c_F)` is not an Arf sign |
| `(GR-7)` | correct, not about this family | model-problem benchmark only |

The kill-shot the board asked for lands, and it lands harder than expected: it is
not that some power-of-two fibre fails to be alternating, it is that **the
alternating stratum of this family consists entirely of dimension-2 rank-0
fibres, and Lemma D3/D4 prove it must.**

### (b) Proved rungs

- **Lemma D1 (L1).**  Every fibre is `xor s`-stable and `eps` is `xor s`-invariant.
  Hence `c_F` is even and `n_F >= 1`.
- **Corollary D1a (L1) -- the corrected `(E2')` identity.**
  `sum_F c_F^2 = 2 N_sf + Theta`, `Theta` the correlation over pairs that are
  neither equal nor `s`-partners.  **This replaces the identity in sweep-08
  `[t8]` and the doc comment on
  `BinaryDyadicAutocorrelationFibreReport::within_fibre_off_diagonal_correlation`,
  both of which use `N_points` where the truth is `N_sf`.**
- **Lemma D3 + Lemma D4 (L3).**  Every fibre with `v(h) >= 2` -- equivalently every
  fibre of dimension `>= 4` -- contains exactly `2^(n-2)` polynomials divisible by
  `(x+1)^2`, hence at least that many Moebius zeros; so `|c_F| <= (3/4) 2^(n_F)`
  and no such fibre is zero-free.  Checked as an assertion on every fibre of all
  22 rows: **0 violations**.  Globally the count is exactly `N_points / 4` on
  every row.
- **Theorem D2 (L3).**  Closed form for the acting group and every fibre
  dimension, from the lane's proved parallelogram identity and proved truncated
  Artin--Schreier kernel dimension:
  `dim T_h = [v+1 if 3v < ell+1 else floor((ell+1-v)/2)] + max(0, d - ell + v)`,
  with `2^(d-v)` shifts of valuation `v`.  Asserted on every shift of 20 rows:
  **0 mismatches**.  Every fibre is a complete `T_h`-orbit.
- **Theorem D6 (L1, and the amplification statement).**  `2 Delta = A + B`
  exactly, with `A` the unrestricted binary Moebius autocorrelation over the shift
  range and `B` its twist by the single nontrivial character of the index-2
  selection.  Asserted on 20 rows.

### (c) The amplification inequality and its test results

**Statement.**  Because the fibre family is a union of *complete* orbits selected
by an `F_2`-subspace condition of index `2^(ell-d)`, the incomplete sum completes
with **no error term**, at a cost of `2^(ell-d)` additive characters.  At the
charter's `d = ell - 1` that is two characters:
`|Delta| <= (|A| + |B|)/2`, an identity in disguise.

**Test results (20 rows, `ell = 4..13`, both parities).**
- Orbit completeness is `1/2` to five decimals from `ell = 10` on.
- `(|A| + |B|) / (2|Delta|) in [1.0, 5.4]`: the completion is lossless.
- The naive boundary mass is useless (`33,316` vs `Delta = -68` at the pinned
  witness) -- but Theorem D6 never pays it.
- **The real cost is one level in:** `sum_h |A_h| / 2^((k+d+1)/2)` grows like
  `2^((ell-4)/2)` (`5.4, 7.2, 10.7, 16.6, 23.3` for `ell = 9..13`), even though
  the individual `|A_h|` already sit at `~0.5 * 2^(k/2)`.  So **per-shift Chowla
  is not enough by an exponential factor; cross-shift cancellation is the content.**

### (d) The residual lemmas, and their relation to `(WK)` / `(CAB)`

**Residual lemma R1 (the counting half; replaces `(E2')`).**

```text
   (E2')  <==>  2 N_sf + Theta <= N_points,
```
so it splits into
```text
   (R1a)  N_sf <= (4/9 + o(1)) N_points        [doubly-squarefree density]
   (R1b)  Theta <= (1/9 - o(1)) N_points       [genuine off-diagonal]
```

*Status of (R1a): partially proved, and the constant is identified.*  For each
irreducible `p != x`, `{p^2 | f}` and `{p^2 | f + h}` are affine subspaces of
codimension `2 deg p`, and they are **disjoint** when `p^2` does not divide `h` and **equal** when
`p^2 | h`.  Hence the doubly-squarefree density for shift `h` is at most
`prod_p b_p(h)` with `b_p = 1 - 2|p|^(-2)` or `1 - |p|^(-2)`; averaging over `h`
(density `|p|^(-2)` for `p^2 | h`) gives the bound
`prod_(p != x) (1 - |p|^(-2))^2 = (2/3)^2 = 4/9`, since
`prod_p (1 - |p|^(-2)) = 1/zeta_A(2) = 1/2` over `F_2[T]` and removing `p = x`
divides by `3/4`.  **`8/9 = 0.8889` is therefore the predicted plateau, and the
measurement gives `2 N_sf / N_points = 0.8888 +- 0.0002` for `ell >= 12`.**  The
proof is complete on the full polynomial domain; what remains is the
equidistribution sub-lemma

> **(EQ)**: each of the square-divisibility conditions has its full density on
> the *admissible* set of each shift,

which is measured **exactly** (not approximately) for `p = x + 1` on all 22 rows:
`square_divisible_total = N_points / 4`, identically.

*Reproduction.*  `acb_gr_orbit_profile` prints `clean_points`, `clean_pairs`,
`dirty_points`, `dirty_pairs`, `clean_density`, `dirty_density` per row:

```sh
cargo build --release -p axeyum-cas --example acb_gr_orbit_profile
./target/release/examples/acb_gr_orbit_profile 4 12    # 23 s
./target/release/examples/acb_gr_orbit_profile 13 13   # 49 s
```

*A sharp negative that comes with it (EVIDENCE, `ell = 4..12`).*  `(E2')` is
**not** provable shift-stratum by shift-stratum.  Splitting shifts by whether
`(x+1)^2 | h`:

```text
   (x+1)^2 does NOT divide h (3/4 of shifts): density -> 0.3951  [<= 1/2 proved, given (EQ)]
   (x+1)^2 DOES divide h    (1/4 of shifts): density -> 0.5923  [> 1/2, so no per-stratum proof]
```

The "dirty" stratum exceeds the `1/2` threshold that `(E2')` needs per stratum,
and `(E2')` survives only in aggregate, because that stratum carries a quarter of
the points.  Any proof must therefore average over shift classes.

*Status of (R1b): OPEN, with a factor-31 measured margin.*  `|Theta| / N_points
<= 0.0035` for `ell >= 12` against an allowance of `1/9 = 0.111`.

**Residual lemma R2 (the sign half; replaces `(S)`).**  By Theorem D6,

```text
   (S)  <==  |A| + |B| <= 2 C (sum_F c_F^2)^(1/2),
```

i.e. **square-root cancellation, with an absolute constant, of the binary
Moebius autocorrelation `A = sum_(1<=deg h<=d) sum_f mu(f) mu(f+h)` and of its
single character twist `B`, over `F_2` with `q` fixed and `deg f -> infinity`.**
No Arf invariants, no Gauss sums, no `Z/8` remain.  Carmon's characteristic-2
Chowla theorem is exactly this object and is vacuous at `q = 2`; cross-shift
cancellation worth `2^((ell-4)/2)` is required beyond any per-shift result.

**Exact implication chain, and the honest comparison with `(WK)` and `(CAB)`.**

```text
  (R1a)+(R1b)  =>  sum_F c_F^2 <= (8/9 + o(1)) N_points          [stronger than (E2')]
  with N_points = (1 + o(1)) 2^(k+d-2)                            [measured: 0.992 at the pinned row]
  and (S) at constant C
        =>  Delta^2 <= C^2 (8/9) 2^(k+d-2)
        =>  Delta^2 <= 2^(k+d+1)                 provided  C <= 3.
```

Two things change against sweep-08's version of the split.  First, the counting
half is **stronger** by a factor `9/8`, so the sign half is allowed
`C <= 3.00` instead of `C <= 2.83`; against the observed maximum `C = 2.31` the
margin goes from `23%` to `30%`.  Sweep-08's "zero-slack" characterisation is
therefore too pessimistic, but only mildly.  Second, the counting half is no
longer a four-point correlation statement at all -- it is a squarefree-density
statement, `(R1a)`, of which the dominant part is proved.

Where the chain lands, exactly:

```text
   (E2') + (S)  =>  Delta(k,d)^2 <= 2^(k+d+1)     (the lane's connected target)
                =>  E(k,d) = Q_k + Delta <= 2^k    (Q_k = (2^k - (-1)^k)/3, proved diagonal)
```

using `d = ell - 1`: at the odd endpoint `k = ell + 2`,
`Q_k + 2^(ell+1) = 1.33 * 2^ell + 2 * 2^ell = 3.33 * 2^ell < 4 * 2^ell = 2^k`; at
the even endpoint `k = ell + 3`, `2.67 * 2^ell + 2.83 * 2^ell = 5.5 * 2^ell
< 8 * 2^ell`.  It does **not** reach the stronger `E <= 2^(k-1)` target, which
would need `|Delta| <= 2^k/6`, i.e. `C <= 1.0`.

**Relation to `(WK)` (diary 04) and `(CAB)` (workstream A): parallel, not
nested, and the split is the weaker of the two.**  `(WK)` is a statement about
the connected fourth cumulant `K_4` of the Mangoldt populations, and diary 04
**proved** that it suffices for the endpoint (Lemmas A/B/C + `(W4-exact)`).
`(CAB)` is the cellwise absolute form of the same fourth-moment route.  The
`(E2')+(S)` split lives in the *other* route -- the annihilator-average/Cauchy
route -- and its output is the connected target `Delta^2 <= 2^(k+d+1)`, i.e. the
energy bound `E(k,d) <= 2^k`.  The lane's own ledger records repeatedly that this
"still does not control the complementary signed cross-order convolution block".
So:

- `(E2') + (S)` **does not imply** `(WK)`, and `(WK)` does not imply them.
- `(E2') + (S)` is **strictly weaker as a closing statement**: `(WK)` closes the
  endpoint by a proved implication, `E <= 2^k` closes a lemma inside a route whose
  remaining block is unproved.
- The right way to read the split is therefore as **the cheapest available
  falsification instrument**, not as a route to the target: both halves are now
  reduced to named objects (a squarefree-pair density and a fixed-field Chowla
  sum), and both are measurable to `ell = 14` in minutes.

### Cross-checks performed (charter rule 1)

1. **Independent Rust reimplementation vs the in-tree report.**  `acb_gr_fibre_census`
   recomputes `mu` by `GF(2)` factorization (smallest-irreducible-factor sieve),
   the principal-unit inverse by its own recursion, and the fibre partition by its
   own grouping, then asserts agreement with
   `binary_dyadic_autocorrelation_fibre_report` on seven aggregates.  **22 rows,
   0 disagreements**, including the pinned `(9,11,8)` sextuple
   `18884 / 130048 / 120680 / -68 / 33680 / 12915 / 12456`.
2. **From-scratch sympy cross-check** (`xcheck.py`, session scratchpad; runs in
   0.2 s).  Uses `sympy.discriminant` of the integer lift reduced mod 8 and the
   Kronecker symbol `(2/.)` -- a completely different route to `mu` -- plus its own
   `GF(2)`-free Python fibre grouping.  Reproduces, for `(4,6,3)`, `(4,7,3)`,
   `(5,7,4)`, `(6,8,5)`: `fibres`, `points`, `N_sf`, `sum c^2`, `Delta`,
   `sum |c|`, the `(x+1)^2` count, the complete-orbit sum `A`, `Theta`, and the
   zero-free-by-dimension histogram `{2: N}` -- **every value identical**.  Three
   independent implementations now agree on this family.
3. **Structural assertions as gates.**  `acb_gr_fibre_census` aborts if any fibre
   is not an affine subspace or if Lemma D3 fails on a fibre of dimension `>= 4`.
   `acb_gr_orbit_profile` aborts if the stabiliser is not a subspace, if the
   inverse difference is not constant on an orbit, if the closed-form dimension of
   Theorem D2 fails on any shift, if the admissible orbit count misses the report
   fibre count, or if `2 Delta != A + B`.  All green over `ell = 4..14`.

### Compute

All runs inside the charter's bounds and on `/data0`-free paths (no `/tmp`
snapshots): census `ell = 4..12` in `22.6 s`, `ell = 13` in `47.3 s`, `ell = 14`
in `169.6 s`; orbit profile `ell = 4..13` in `82.6 s`.  Peak memory well under
1 GB (the largest arrays are `2^(k-1)` entries).

### What I did not do

- No attempt on `(WK)`, `(CAB)`, `(W4)` or the cross-order convolution block.
- No proof of `(R1b)` (the genuine off-diagonal), and no proof of the
  equidistribution sub-lemma `(EQ)` beyond the exact 22-row measurement.
- No verification of Sawin--Shusterman's field condition; whether their Chowla
  theorem admits `q = 2` is **UNVERIFIED** here.
- No row above `ell = 14` for the census or `ell = 13` for the orbit profile.
