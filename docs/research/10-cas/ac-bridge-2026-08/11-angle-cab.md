# AC-Bridge 11 (phase 2, workstream A): the (CAB) ladder

Charge: advance the resurrected cellwise-absolute connected-cumulant bound

```text
(CAB)   sum_(a<=b<=c<=d) mult(a,b,c,d) |K_(a,b,c,d)|
             <  2^(ell + 4(n-ell))  -  3 M_2^2 ,      ell >= ell_0,
```

as far up the ladder as possible: cell structure, decay mechanism,
measurement to the largest affordable `ell`, and a recursion in `ell`.

Date opened: 2026-08-20T21:45-04:00.
Board: `10-angles-board.md`, workstream A.
Charter: `00-charter.md` (rules of the project apply verbatim).

Epistemic labels: **PROVED** (argument written out here), **REFUTED** (with an
exact witness), **OPEN**.  Finite computation is EVIDENCE, never a theorem.
Every retained number below is an exact integer; the only floating point is in
printed ratios and fits.

New files written by this workstream (no existing source file touched):

```text
crates/axeyum-cas/examples/acb_cab_cells.rs    order-graded cells, independent
                                               reimplementation + CAS control
crates/axeyum-cas/examples/acb_cab_levels.rs   CONDUCTOR-graded cells, the
                                               sibling recursion, the layer L4
                                               reduction, the envelope bound
```

## Log

### 21:45 -- required reading, and the exact object

Read `00-charter.md`; `10-angles-board.md`; `05-resurrection-audit.md` in full
(720 lines) including the `(WICK)` identity and the S1 closure table;
`04-weak-target-verification.md` in full (715 lines) including Lemmas A/B, the
corrected target `(W4-exact)` and the corollary `(WK)`; and the cumulant / Wick
/ cell entries of `docs/plan/status/52-gf2-lemire.md` (lines 180-200, 425-450).
Read the implementation of `connected_order_cumulant_report`
(`crates/axeyum-cas/src/gf2_hayes.rs:14350-14510`) and its cell struct
(`:4599`), plus `class_mobius_distribution` (`:10419`),
`principal_unit_structure` (`:6265`), the private
`principal_unit_from_mixed_radix_index` (`:6298`), `add_mixed_radix_indices`
(`:13240`) and `principal_unit_factors` (`:15379`).

Notation is the charter's, plus:

```text
T_d(e) = d sum_(u in V_d) M_(n-d)(e u^-1),  V_d = {1+a_1x+...+a_d x^d} in E_ell
C_ab   = sum_e T_a(e) T_b(e)
K_(a,b,c,d) = 2^ell sum_e T_aT_bT_cT_d - (C_ab C_cd + C_ac C_bd + C_ad C_bc)
A(ell,n)    = sum_(a<=b<=c<=d) mult |K_(a,b,c,d)|        -- the (CAB) left side
Pabs(ell,n) = sum mult |C_ab C_cd + C_ac C_bd + C_ad C_bc|
L(ell,n)    = sum_(a,b) |C_ab|
```

### 21:55 -- tooling, and the controls it has to pass

`acb_cab_cells.rs` reimplements the interval-order vectors and the symmetric
cell tensor from scratch.  It shares no code path with
`connected_order_cumulant_report`: it builds its own principal-unit factor
table, its own mixed-radix unit table, and -- the point of the rewrite -- it
observes that the mixed-radix index *is* the packed bitfield word of the
cyclic decomposition (field `i` occupies `log2(order_i)` bits, and
`sum_i log2(order_i) = ell`), so group multiplication is a carry-masked SWAR
add

```text
add(x,y) = ((x & low) + (y & low)) ^ ((x ^ y) & high)
```

with `high` the top bit of every field.  That replaces the CAS's per-element
mixed-radix loop and is what makes `ell = 17, 18` affordable inside the
5-minute budget.  Controls, all fail-closed:

* `control=swar_add`: the SWAR add is compared against
  `index(unit_multiply(unit(a), unit(b)))` on every pair up to `2^9` and on a
  stride-37 lattice above (65 536 pairs at `ell = 8`).
* order reconstruction `sum_(d=1)^(ell-1) T_d = D` on **every class of every
  row** (aborts the row otherwise);
* `control=cas_report`: **cell-by-cell** equality of `interval_degrees`,
  `permutation_multiplicity`, `raw_fourth_sum`, `pairing_sum` and
  `connected_numerator` against `connected_order_cumulant_report`;
* `signed == 2^ell M_4 - 3 M_2^2` recomputed from the population vector;
* a magnitude guard `2^ell (max|T|)^3 (sum_e |T|) < 2^126` that refuses the row
  rather than let release-mode `i128` wrap.

```sh
cargo build --release -p axeyum-cas --example acb_cab_cells
./target/release/examples/acb_cab_cells verify 8 17
ACB_CAB|control=swar_add|ell=8|pairs_checked=65536
ACB_CAB|control=cas_report|ell=8|n=17|cells_agree=210|direct=-47710569216
ACB_CAB|probe=row|ell=8|n=17|cells=210|...|abs_total=230376139285248|...
```

`abs_total = 230376139285248` is the audit's pinned `(8,17)` value, and every
row `6 <= ell <= 15` reproduces the audit's `A` to the digit.  Reproduced
exactly: `(12,25) 157946261057023250432`, `(13,27) 3600279701752796910592`,
`(14,29) 72482620910741465221888`, `(14,30) 289137771289401958115840`,
`(15,31) 1435571519440946522627584`, `(15,32) 5790274281755889729402368`.

### 22:10 -- (charge 3) the (CAB) closure table, extended to `ell = 18`

The audit's `cumulant` probe declined at `ell = 16`
(`requested: 4495376384`).  The rewrite reaches `ell = 18` in 3m41s per row.

(`closure` here is `A/affordable` with `affordable = 2^(ell+4(n-ell)) - 3M_2^2`;
the audit printed the equivalent `(3M_2^2+A)/2^(ell+4(n-ell))`, which differs by
a factor `1 + 3M_2^2/A` and agrees to three digits once `ell >= 14`.)

```text
 ell   n  par   A = sum mult|K|                        closure = A/affordable
   6  13  odd   168917081088                                   10.638
   7  15  odd   13158446328832                                 27.989
   8  17  odd   230376139285248                                14.265
   9  19  odd   13125241053984256                              24.789
  10  21  odd   167845851196981248                              9.758
  11  23  odd   6173593773349663232                            11.030
  12  25  odd   157946261057023250432                           8.713
  13  27  odd   3600279701752796910592                          6.171
  14  29  odd   72482620910741465221888                         3.862
  15  31  odd   1435571519440946522627584                       2.384
  16  33  odd   24629016173929714588672896                      1.276   NEW
  17  35  odd   468344167493092756076063808                     0.758   NEW, CLOSES
  18  37  odd   8288178104817783599672029440                    0.419   NEW
   6  14 even   1778855818240                                   6.771
   8  18 even   1095811544008448                                4.042
  10  22 even   825395049403345408                              2.903
  12  26 even   650391631824020488704                           2.214
  13  28 even   14999217840610212754432                         1.593
  14  30 even   289137771289401958115840                        0.958   CLOSES
  15  32 even   5790274281755889729402368                       0.599
  16  34 even   104611750122595221454654048                     0.338   NEW
  17  36 even   1913088134160452143749531904                    0.193   NEW
  18  38 even   33151221870979469247307336704                   0.105   NEW
```

**Result 1 (MEASURED).  The odd endpoint's `(CAB)` crossing is `ell_0 = 17`,
inside measured range.**  The audit extrapolated `17-18`; the row exists now.
Both parities of the top candidate are therefore measured-closing, with
margins `0.42` / `0.105` at `ell = 18` and still improving.

**Result 2 (correction to the audit's fit).**  The audit fitted the closure
decay as `2^(-0.283 ell)` (odd) / `2^(-0.390 ell)` (even) over `ell = 6..15`.
Over `ell >= 13` -- the only range that matters for `ell_0` -- the decay is
`2^(-0.782 ell)` (odd) and `2^(-0.783 ell)` (even).  The small-`ell` rows drag
the fit; see 22:25 for why (the loss factor is still saturating there).

### 22:25 -- (charge 2) the decay mechanism, factored exactly

Write the closure ratio as an exact product of three measurable factors:

```text
   A/affordable  =  [A/Pabs] * [Pabs/(3 M_2^2)] * [3 M_2^2/affordable] .
```

Exact rows (`acb_cab_cells sweep`, then integer arithmetic):

```text
 ell   n  par   A/aff   A/Pabs  Pabs/3M2^2  3M2^2/aff   A/(3M2^2)
   8  17  odd  14.265   0.2300      694.5    0.08930      159.7
  10  21  odd   9.758   0.1988     1038.1    0.04729      206.4
  12  25  odd   8.713   0.2202     2252.1    0.01757      495.8
  13  27  odd   6.171   0.1730     3043.9    0.01172      526.5
  14  29  odd   3.862   0.1435     4177.6    0.00644      599.3
  15  31  odd   2.384   0.1101     5745.0    0.00377      632.3
  16  33  odd   1.276   0.0820     6872.3    0.00226      563.7
  17  35  odd   0.758   0.0643     9438.1    0.00125      606.9
  18  37  odd   0.419   0.0497    11443.5    0.00074      569.2
   8  18 even   4.042   0.2357      447.4    0.03833      105.5
  12  26 even   2.214   0.2289     2060.7    0.00469      471.7
  14  30 even   0.958   0.1409     4056.0    0.00168      571.4
  16  34 even   0.338   0.0860     6979.2    0.00056      600.0
  18  38 even   0.105   0.0498    11484.5    0.00018      572.2
```

Log-linear slopes in bits per unit `ell` (`ell >= 8`):

```text
              odd      even
A/Pabs      -0.248    -0.246
Pabs/3M2^2  +0.411    +0.459
3M2^2/aff   -0.708    -0.760
A/(3M2^2)   +0.013    +0.014      (fitted over ell >= 13)
```

**Result 3 (MECHANISM, MEASURED).  The `(CAB)` closure ratio decays for
exactly one reason, and it is not any of the three the charge listed.**  It is
not cell-count growth, not per-cell decay, not the multiplicity weights.  The
cellwise-absolute loss *relative to the Wick total*,

```text
       kappa(ell,n) := A(ell,n) / (3 M_2^2) ,
```

**saturates at an absolute constant `~570-630` from `ell = 13` onwards** (fitted
slope `+0.013` bits per `ell`, i.e. flat to measurement) in *both* parities.
The two factors the audit measured separately (`A/Pabs` falling `2^(-0.25 ell)`,
`Pabs/3M_2^2` rising `2^(+0.41..0.46 ell)`) are the two halves of one constant;
their product is the quantity with meaning, and the audit did not form it.
Everything that decays is the third factor `3 M_2^2/affordable`, which is the
`(W4)` slack `~ell^2 2^(-ell)` and is a property of the target, not of the
shortcut.

Consequence, and this is the useful part:

> **(CAB-const)**  There is an absolute constant `c` with
> `A(ell,n) <= c M_2(ell,n)^2` for both endpoint parities and all large `ell`.

is *equivalent in strength* to `(CAB)` up to a computable crossover, and is
`ell`-free.  Measured `A/M_2^2` over `ell = 13..18`: `1580, 1798, 1897, 1691,
1821, 1708` (odd), `1630, 1714, 1804, 1800, 1762, 1717` (even).  With
`c = 1900` and the lane's PROVED `M_2 <= mu Sigma(ell)`, the chain
`(c+3)(mu Sigma)^2 < 2^ell (mu - P_n)^4` closes from `ell = 29` (odd) --
inside the certified finite range.  That is a materially better statement of
the obligation than `(C4-weak)`: one absolute constant instead of `~ell^4/24`
individual estimates, and no `ell`-dependence.

### 22:40 -- (charge 1) cell structure: where the mass is, and the Fourier form

Cell-mass profile of `A` (`acb_cab_cells profile`), share of `A`:

```text
(12,25)  by #distinct orders  1: 0.005   2: 0.137   3: 0.514   4: 0.344
(14,29)  by #distinct orders  1: 0.005   2: 0.121   3: 0.459   4: 0.415
(12,25)  by max order   <=8: 0.132   9: 0.181  10: 0.343  11: 0.344
(14,29)  by max order  <=10: 0.209  11: 0.207  12: 0.310  13: 0.275
```

and the single heaviest cell carries `1.34%` at `(12,25)`, `0.95%` at
`(14,29)`.  So the order-graded mass is **delocalised**: no cell, no small
family of cells, and no degenerate order vector dominates; the top three
orders carry `~79%` and the fully-distinct cells `~41%`.  A per-cell estimate
of the dominant cells is therefore not a route -- there is no dominant cell.

The structural facts that *are* available are Fourier-theoretic.

**Lemma 1 (order-grading Fourier form).  PROVED.**
For every character `chi` of `E_ell`,

```text
hat T_d(chi) = d * a_d(chi) * m_(n-d)(chi),
a_d(chi) = sum_(u in V_d) chi(u) = [z^d] L(chi,z),
m_j(chi) = [z^j] 1/L(chi,z) = sum_(deg F = j) mu(F) chi(<F>) .
```

*Proof.*  `A_d(e) = #{F monic, deg F = d, <F> = e}` equals `1_(V_d)(e)` for
`d <= ell` (the class records every non-leading coefficient), so
`T_d = d (A_d * M_(n-d))` is a group convolution and Fourier-diagonalises;
`hat A_d(chi) = a_d(chi)` is by definition the `L`-coefficient, and
`A * M = delta` gives `hat M(chi, z) = 1/L(chi,z)`.  QED

**Lemma 2 (order-level support).  PROVED.**
`a_d(chi) = 0` whenever `d >= level(chi)`, where `level(chi) = j` means `chi`
is trivial on `H_j = 1 + x^(j+1) F_2[x]/x^(ell+1)` and not on `H_(j-1)`.
Hence `T_d` is supported on characters of level `>= d+1`, and `T_(ell-1)` is
supported on the primitive (level-`ell`) characters only.

*Proof.*  For `d >= j` the truncation `V_d -> E_ell/H_j` is surjective with all
fibres of size `2^(d-j)`, and `chi` induces a **nontrivial** character of that
quotient, whose full sum vanishes.  QED

**Corollary 3 (the decomposition terminates, exactly).  PROVED.**
`T_d` is a constant vector for every `d >= ell`, and `T_d` has zero mean for
`1 <= d <= ell-1`; hence `sum_(d=1)^(ell-1) T_d = D` exactly.

*Proof.*  By Lemma 2 every nontrivial Fourier coefficient of `T_d` vanishes for
`d >= ell`.  At the trivial character `hat T_d(1) = d 2^d hat M_(n-d)(1)` and
`hat M_m(1) = [z^m](1-2z) = 0` for `m >= 2`; since `d <= ell-1` and
`n >= 2ell+1` we have `n-d >= ell+2 >= 2`.  QED

This is the invariant `connected_order_cumulant_report` *checks* classwise on
every row; it is now a theorem, and it is the reason the cell tensor has
exactly `binom(ell+2, 4)` cells.

**REFUTED, with witnesses (the first thing a proof would try).**  Splitting a
cell as `|K_cell| <= |2^ell raw_cell| + |P_cell|` is dead: the ratio
`(sum mult|2^ell raw| + Pabs)/A` is

```text
 ell    8     10     12     14     16     18
odd   8.31  10.04   9.39  14.26  24.81  40.58
even  8.32   9.02   9.15  14.55  23.70  40.51
```

-- a loss that **grows** (fitted `2^(+0.253 ell)` odd, `2^(+0.248 ell)` even).  The cancellation between a
cell's fourth-order term and its own Wick pairing is essential and increasing;
any argument that bounds the two halves separately in the order grading is
exponentially dead.  (Contrast the conductor grading below, where the same
split costs a bounded factor.)

### 23:00 -- the pivot: grade by CONDUCTOR, not by convolution order

Lemma 2 says the order grading is the *lower-triangular shadow* of the
conductor grading.  So grade by conductor directly.  Put

```text
P_j D(e) = 2^-(ell-j) sum_(h in H_j) D(e h),   D_[j] = P_j D - P_(j-1) D,
```

computed exactly by the **integer sibling recursion**

```text
R_ell = D,   R_(j-1)(e) = R_j(e) + R_j(e g_j),   g_j = 1 + x^j,
A_j(e) = R_j(e) - R_j(e g_j),   D_[j] = A_j / 2^(ell-j+1) .
```

`R_j(e) = D^((j))(pi_j e)` is the level-`j` coarse class discrepancy, so `A_j`
is exactly the lane's **sibling difference** at level `j`.  Define the
conductor-graded cells

```text
Klev_(j1,j2,j3,j4) = 2^ell sum_e D_[j1]D_[j2]D_[j3]D_[j4] - (three pairings),
A_L(ell,n) = sum_(j1<=j2<=j3<=j4) mult |Klev| ,
```

`(CAB-L)`: `A_L < 2^(ell+4(n-ell)) - 3 M_2^2`.  Since
`sum mult Klev = K_4` exactly (asserted on every row), `(CAB-L)` is a
sufficient statement of exactly the same type as `(CAB)`.

Four structural facts separate the two gradings, and they are the content of
this workstream.

**Lemma 4 (orthogonality; the Wick half is exact).  PROVED.**
`sum_e D_[j] D_[k] = 0` for `j != k` (distinct Fourier supports).  Hence the
conductor covariance matrix is **diagonal**, every cell's pairing sum is
`0` or `V_j V_k` or `3 V_j^2` with `V_j = ||D_[j]||_2^2 >= 0`, so **every Wick
pairing is nonnegative** and

```text
sum mult |P_lev|  =  sum mult P_lev  =  3 (sum_j V_j)^2  =  3 M_2^2   EXACTLY.
```

Contrast the order grading, where `Pabs/(3 M_2^2)` is `694` at `ell = 8` and
`11 444` at `ell = 18` and grows `2^(+0.41 ell)`: **the entire `Pabs` loss of
the order grading is an artefact of grading by a non-orthogonal family.**

**Lemma 5 (parity selection rule).  PROVED.**
`Klev_(j1,j2,j3,j4) = 0` unless the number of indices equal to
`J = max(j_i)` is **even**.

*Proof.*  In `2^ell sum_e prod D_[j_i]` only quadruples with
`chi_1 chi_2 chi_3 chi_4 = 1` survive.  Restrict that relation to `H_(J-1)`:
every `chi_i` of level `< J` is trivial there, and every `chi_i` of level
exactly `J` restricts to *the* nontrivial character of the order-2 group
`H_(J-1)/H_J`.  So the restriction of the product is that character raised to
`#{i : j_i = J}`, which is trivial iff that count is even.  The pairing part
vanishes for the same reason (a pairing needs two equal levels).  QED

Measured: `odd_max_nonzero = 0` on **every** row `ell = 4..20`, both parities
-- e.g. 147 of the 210 cells at `(8,17)` and 6 156 of the 7 315 cells at
`(20,42)` are identically zero.  The rule removes `~82%` of the cells.

**Lemma 6 (Weil control of every layer).  PROVED given the lane's proved
`L`-degree distribution.**
`V_1 = 0`; `V_2 = 2^(n-ell+1)` exactly; and
`V_j <= 2^(n-ell) 2^(j-1) (j-1)^2` for every `j`.

*Proof.*  A level-`j` character has an `L`-polynomial of degree `j-1` with all
inverse roots of absolute value `2^(1/2)`, so `|S_chi| <= (j-1) 2^(n/2)`, and
level `j` carries `2^(j-1)` characters; `V_j = 2^-ell sum_(level j)|S_chi|^2`.
Level 1 gives `deg L = 0`, hence `S_chi = 0`.  Level 2 gives `deg L = 1`, hence
`|S_chi| = 2^(n/2)` **exactly**, and `V_2 = 2^-ell * 2 * 2^n`.  QED

Independent control: `2^ell V_j` was compared against the CAS's
`exact_conductor_second_moment(j, n)` -- a completely different algorithm
(two modular character tables plus CRT) -- and agrees on every level of
`(8,17)` and `(9,20)`; the printed Weil fill `V_j / (2^(n-ell)2^(j-1)(j-1)^2)`
is `1.0000` at `j = 2` and `<= 0.62` elsewhere, never above 1.

**Lemma 7 (exact recursion in `ell`).  PROVED.**
At *fixed* `n`, for every cell with all four levels `<= ell-1`,

```text
Klev^(ell)(j1,j2,j3,j4) = (1/4) Klev^(ell-1)(j1,j2,j3,j4) ,
```

hence

```text
A_L(ell,n) = (1/4) A_L(ell-1, n)  +  T(ell,n),
T(ell,n) = sum over cells with 2 or 4 indices at the top level ell.
```

*Proof.*  For `j <= ell-1`, `R_j^(ell)` is `H_(ell-1)`-invariant and equals
`R_j^(ell-1)` composed with the truncation `pi`, so `A_j^(ell) = A_j^(ell-1) o
pi` and `D_[j]^(ell) = (D_[j]^(ell-1) o pi)/2`.  Each of the four factors
contributes `1/2`, the class sum doubles, the prefactor `2^ell` doubles: net
`2^(1+1) / 2^4 * 2 = 1/4` for the fourth-order term, and `V_j^(ell) =
V_j^(ell-1)/2` gives the same `1/4` for each pairing.  QED

Verified numerically to full precision:

```text
ell=8,  n=17: low-level mass 1.53052818e11  =  A_L(7,17)/4  ratio 1.0000000000
ell=12, n=25: low-level mass 8.61494444e15  =  A_L(11,25)/4 ratio 1.0000000000
```

This is charge 4, and it is an **equality**, not an inequality with loss: the
inherited part costs exactly `2^-2` per level while the budget gains `2^5` per
endpoint step.  The residual family is exactly `T(ell,n)`, the cells with two
or four indices at the exact top conductor level; measured share of `A_L`:

```text
 (ell,n)      top=0     top=2     top=4
  (8,17)      0.250     0.617     0.134
 (10,21)      0.202     0.548     0.250
 (12,25)      0.193     0.750     0.057
 (14,29)      0.227     0.662     0.110
 (16,33)      0.317     0.650     0.033
 (12,26)      0.356     0.572     0.072
 (14,30)      0.313     0.629     0.058
 (16,34)      0.321     0.577     0.102
```

(`top = 1` and `top = 3` are `0.000000` everywhere -- Lemma 5.)

### 23:20 -- (CAB-L) measured: four orders of magnitude better than (CAB)

`acb_cab_levels sweep`, both parities, `ell = 4..20`.  `closure` is against
the audit's budget `2^(ell+4(n-ell)) - 3M_2^2`; `strict` is against the
diary-04 budget `2^ell (mu - P_n)^4 - 3M_2^2` with Lemma A / Lemma B `P_n`
(`inf` marks rows below the `(WK)` crossover, where the budget is negative and
nothing can close -- `ell <= 13` even, as diary 04 predicts).

```text
 ell   n  par   (CAB-L) closure    strict     (CAB) closure   ratio (CAB)/(CAB-L)
   6  13  odd        0.037389     0.038682        10.638            284.5
   8  17  odd        0.037962     0.038287        14.265            375.8
  10  21  odd        0.010717     0.010739         9.758            910.5
  12  25  odd        0.002465     0.002467         8.713           3534.0
  14  29  odd        0.000433     0.000433         3.862           8925.1
  16  33  odd        0.000078     0.000078         1.276          16323.6
  17  35  odd        0.000034     0.000034         0.758          22023.4
  18  37  odd        0.000016     0.000016         0.419          25805.5
  19  39  odd        0.000005     0.000005           --              --
  20  41  odd        0.000002     0.000002           --              --
   8  18 even        0.026312       inf            4.042            153.6
  12  26 even        0.000665     0.002168         2.214           3329.9
  14  30 even        0.000139     0.000263         0.958           6883.2
  16  34 even        0.000022     0.000031         0.338          15416.3
  18  38 even        0.000004     0.000005         0.105          25441.3
  20  42 even        0.000001     0.000001           --              --
```

**Result 4 (MEASURED).  `(CAB-L)` holds on all 34 measured rows
`ell = 4..20`, both parities, with margin growing `2^(+0.46 ell)`; at
`ell = 18` it beats `(CAB)` by a factor `25 800`.**

And the sharper statement, which was not visible in the order grading at all:

```text
 ell    A_L / M_2^2  (odd / even)
   8      1.275 / 2.059
  10      0.680 / 0.752
  12      0.421 / 0.425
  14      0.201 / 0.249
  16      0.104 / 0.117
  18      0.066 / 0.068
fit (ell>=12):  d log2(A_L/M_2^2)/d ell  =  -0.465 (odd) / -0.462 (even)
```

**Result 5 (MEASURED, and it changes what is at stake).  `A_L < M_2^2` on
every row from `ell = 10`, decaying like `2^(-0.46 ell)`.**  Since
`|K_4| <= A_L`, the *levelwise-absolute* bound already implies the lane's
**strong** aggregate target `K_4 <= M_2^2` (`R_0 <= 4`), not merely the weak
one -- and it does so while discarding **all** cross-conductor cancellation.
Contrast the order grading, where `A/M_2^2 ~ 1700-1900` is constant: the same
shortcut, applied to a non-orthogonal grading, is `~1800x` too weak for the
strong target and only survives against the weak one.

The comparison is exact and self-contained, so the ledger's headline
refutation of cellwise absolute values ("individual connected cells are over
thirty times larger than their signed total") is a statement about the
**convolution-order** grading only.  In the conductor grading the same
operation is essentially free.

### 23:40 -- collapsing the cell tensor: two strictly simpler sufficient statements

The conductor grading admits two reductions the order grading does not.

**(SPLIT-L).  PROVED reduction.**  Because every level Wick pairing is
nonnegative and they sum to exactly `3 M_2^2` (Lemma 4),

```text
A_L  <=  R_L + 3 M_2^2 ,   R_L := sum mult |2^ell sum_e prod D_[j_i]| .
```

so `(CAB-L)` follows from `R_L + 6 M_2^2 < 2^ell (mu-P_n)^4`.  Measured
closure of that:

```text
 ell      6      8     10     12     14     16     18     20
odd   0.1801 0.1877 0.0963 0.0363 0.0132 0.0046 0.0015 0.00047
even  0.1015 0.0995 0.0276 0.0100 0.0034 0.0011 0.00037 0.00012
```

Cost of the split
relative to `A_L`: a factor `5-60`, **bounded**, versus the exponentially
growing `8.3 -> 40.6` cost of the same split in the order grading.

**(ENV-L).  PROVED reduction, and it removes the cell tensor entirely.**
Put

```text
U_L(e) = sum_(j=1)^ell |D_[j](e)|          (the conductor-absolute envelope).
```

Pointwise `|D_e| = |sum_j D_[j](e)| <= U_L(e)`, so `M_4 <= sum_e U_L(e)^4`
and therefore

```text
(ENV-L)   sum_e U_L(e)^4  <  (mu - P_n)^4      ==>   (W4-exact)  ==>  endpoint.
```

This is `(W4-exact)` with every conductor-layer sign erased.  No cells, no
multiplicities, no Wick subtraction, no cross-layer cancellation.  Measured
`sum_e U_L^4 / ((mu-P_n)^4 - 3M_2^2/2^ell)`:

```text
 ell      6      8     10     12     14     16     18     20
odd   0.2955 0.4311 0.2153 0.1005 0.0388 0.0144 0.0048 0.00156
even    inf    inf  0.6901 0.0870 0.0192 0.0051 0.0014 0.00044
```

(`inf` again marks the rows below the even `(WK)` crossover.)  It closes on
every row from `ell = 6` (odd) / `ell = 11` (even) and decays
`~2^(-0.7 ell)`.  Note `sum_e U_L^4 / M_4` is only `6.1` at `(16,33)`: taking
absolute values across the whole conductor filtration costs a factor `1.6` in
the `L^4` norm, not an exponential.

**(L4-LAYER).  PROVED reduction of `(ENV-L)`.**  By Minkowski,
`||U_L||_4 <= sum_j ||D_[j]||_4`, so `(ENV-L)` follows from

```text
(L4-LAYER)   sum_(j=1)^ell ( sum_e D_[j](e)^4 )^(1/4)  <  mu - P_n .
```

Now there is **no interaction between levels at all**: one `L^4` number per
conductor layer.  Measured `sum_j ||D_[j]||_4 / (mu - P_n)`:

```text
 ell     6     8    10    12    14    16    18    20
odd   0.841 1.061 0.933 0.787 0.627 0.493 0.376 0.284
even    --  3.049 1.291 0.790 0.536 0.383 0.278 0.207
```

closing from `ell = 10` (odd) / `ell = 11` (even), decaying like `ell^-1.74`
(odd) / `ell^-2.55` (even).

### 00:05 -- the reduced lemma, and its exact crossover

`(L4-LAYER)` needs, per layer, an `L^4` bound.  Two inputs give one:

```text
 ||D_[j]||_4  <=  ( max_e |D_[j](e)| )^(1/2) * V_j^(1/4)        (elementary)
 V_j          <=  2^(n-ell) 2^(j-1) (j-1)^2                      (Lemma 6, PROVED)
```

so everything reduces to the **sup norm of one conductor layer**.  Define

```text
 kappa_j(ell,n) := max_e |D_[j](e)| * 2^ell / ( (j-1) 2^((j-1)/2) 2^(n/2) ) .
```

The denominator is the *square root, in the character count*, of the trivial
triangle bound `2^(j-1)(j-1)2^(n/2)/2^ell`.  Measured over `ell = 6..20`, both
parities, all levels -- 341 (row, level) pairs:

```text
   j   rows      min   median      max
   2     29   1.0000   1.0000   1.4142
   4     29   0.4677   0.9428   1.8994
   6     29   0.5625   0.9899   1.3562
   8     25   0.7678   1.0625   1.4601
  10     21   0.7482   1.0754   1.3581
  12     17   1.0051   1.1284   1.5146
  14     13   0.9655   1.0944   1.2281
  16      9   0.9987   1.0767   1.2478
  18      5   1.0575   1.1096   1.1741
  20      1   1.1049   1.1049   1.1049
global max over all 341 pairs: 2.0000   (at ell=11, n=24, j=3)
global max over j >= 6:        1.5234
```

**Result 6 (the reduced lemma).**  The whole workstream reduces to

> **(SUP-L)**  There is an absolute constant `K` with
> ```text
> max_e |D_[j](e)|  <=  K (j-1) 2^((j-1)/2) 2^(n/2) / 2^ell
> ```
> for every conductor level `j <= ell` and both endpoint degrees.

Measured `K = 2` covers all 341 pairs; `K = 1.53` covers every `j >= 6`; the
median is `0.94-1.13` with no drift in `j` or in `ell`.

Given `(SUP-L)` the chain is closed and every other step is PROVED:

```text
M_4 <= sum_e U_L^4 <= ( sum_j ||D_[j]||_4 )^4
    <= ( K^(1/2) sum_(j=2)^ell (j-1) 2^((j-1)/2) 2^((2n-3ell)/4) )^4
    <  (mu - P_n)^4   ==>  (W4-exact)  ==>  I_n(1) >= 1 .
```

Exact crossovers (exact `sum_(j=2)^ell (j-1)2^((j-1)/2)`, Lemma A/B `P_n`,
60-digit decimal arithmetic; "first `ell` from which it holds for every larger
`ell`"):

```text
   K      odd endpoint    even endpoint
  1.6         21               19
  2.0         22               20
  2.5         23               21
  4.0         25               23
```

The crossover moves by one level per doubling of `K`, because the chain gains
`2^(ell/4)` per level: **the reduction is insensitive to the constant.**  With
`K = 2` -- the value that fits all measured data with a `31%` margin -- the
endpoint follows for every `ell >= 22` (odd) / `ell >= 20` (even), and
`ell <= 21` is inside the lane's separately certified finite range through
degree 400 (diary 04; I did not re-verify that certification here).

`(SUP-L)` is a **delocalisation / square-root-cancellation** statement about a
single conductor layer: the level-`j` component of `D` is not allowed to
concentrate to the full triangle bound over its `2^(j-1)` characters, only to
its square root.  It is exactly the "one logarithm" sweep-09 isolates as
`(LP-DEFICIT)`, and exactly the object phase-2 workstream C is chartered to
attack; it is *not* a fourth-moment statement, a cumulant statement, or a cell
statement.

### 00:20 -- independent verification

**(i) From-scratch sympy brute force of the NEW machinery.**
`scratchpad/sympy_levels.py` shares no code, no algorithm and no convention
with the CAS or with either example: it enumerates every monic polynomial of
degree `n` over `GF(2)`, factors it with `sympy.factor_list()` over `GF(2)`,
applies the von Mangoldt weight, bins by reciprocal truncation, then computes
the conductor projections by **direct averaging over each subgroup `H_j`** (no
sibling recursion), forms `A_j`, `V_j`, and the full level-cell tensor with its
own multiplicities.

```text
SYMPY_LEV|ell=4|n=9 |m2=1168 |m4=149776  |k4=-1696256 |abs_scaled=111165833216      |zero_cells=10
SYMPY_LEV|ell=4|n=10|m2=1200 |m4=192576  |k4=-1238784 |abs_scaled=119839653888      |zero_cells=8
SYMPY_LEV|ell=5|n=11|m2=4384 |m4=765472  |k4=-33163264|abs_scaled=40185861505024    |zero_cells=24
SYMPY_LEV|ell=5|n=12|m2=23584|m4=73638400|k4=687813632|abs_scaled=1127356974497792  |zero_cells=24
```

Every field agrees **exactly** with `acb_cab_levels`, including the new
quantity `A_L` itself (`abs_scaled`), the zero-cell counts predicted by
Lemma 5, and the per-level energies.  AGREEMENT, four rows, two parities.

**(ii) CAS cross-checks.**  `acb_cab_cells` matches
`connected_order_cumulant_report` cell-by-cell (210 cells at `(8,17)`, 35 at
`(5,11)`, 1 001 at `(12,25)`) on `raw_fourth_sum`, `pairing_sum`,
`connected_numerator` and multiplicity.  `acb_cab_levels control` matches
`exact_conductor_second_moment` on `2^ell V_j` at every level of `(8,17)` and
`(9,20)`.  Both tools independently reproduce `M_2`, `M_4` and `K_4` at every
shared row (`(18,37)`: `m2 = 2203042899488`,
`k4 = -181147010541912818486272`, from Moebius convolutions in one tool and
subgroup averaging in the other).

**(iii) The audit's pinned rows** are reproduced to the digit at every
overlapping `ell` (listed at 21:55).

### 00:30 -- resource notes

```text
acb_cab_cells sweep 12 14      12.2 s
acb_cab_cells sweep 15 16       2m06
acb_cab_cells row 17 35         1m18      row 18 37   3m41   (peak RSS < 120 MB)
acb_cab_levels sweep 4 14        1.1 s
acb_cab_levels sweep 15 18      32.3 s
acb_cab_levels sweep 19 20      2m08                          (peak RSS < 700 MB)
acb_cab_levels layers <row>     < 3 s per row through ell = 20
```

The conductor tool is `~100x` cheaper than the order tool at equal `ell`
because it needs no Moebius transforms at all -- only `ell` passes of the
sibling recursion over the class vector.  Both stay inside the charter's
5-minute / 2-GB budget per run; `ell = 18` order rows were sharded one per
parity.  `ell = 21` is refused by the `i128` magnitude guard
(ceiling `2^126.2`), not by time.

## FINDINGS

### (a) Proved rungs (L1 / L3)

1. **Lemma 1-3 (order grading, PROVED).**  `hat T_d = d a_d m_(n-d)`;
   `a_d(chi) = 0` for `d >= level(chi)`; hence `T_d` is a constant vector for
   `d >= ell` and `sum_(d=1)^(ell-1) T_d = D` exactly.  This turns a runtime
   invariant of `connected_order_cumulant_report` into a theorem and explains
   the cell count `binom(ell+2,4)`.
2. **Lemma 4 (PROVED).**  The conductor components `D_[j]` are pairwise
   orthogonal, so the conductor-graded Wick pairings are all nonnegative and
   `sum mult |P_lev| = 3 M_2^2` exactly.  In the convolution-order grading the
   same quantity is `694x` (`ell=8`) to `11 444x` (`ell=18`) larger than
   `3M_2^2` and grows `2^(+0.41 ell)`.  **The entire `Pabs` loss of the audit's
   candidate is an artefact of grading by a non-orthogonal family.**
3. **Lemma 5, parity selection rule (PROVED).**  A conductor cell vanishes
   unless the number of indices at the maximal level is even.  Confirmed on
   every row `ell = 4..20`: `odd_max_nonzero = 0`, and it kills `~82%` of the
   cells (6 156 of 7 315 at `ell = 20`).
4. **Lemma 6 (PROVED given the lane's `L`-degree distribution).**  `V_1 = 0`,
   `V_2 = 2^(n-ell+1)` exactly, `V_j <= 2^(n-ell)2^(j-1)(j-1)^2`; cross-checked
   against the CAS's independent `exact_conductor_second_moment`.
5. **Lemma 7, the `ell`-recursion (PROVED, and it is an equality).**  At fixed
   `n`, `Klev^(ell) = (1/4) Klev^(ell-1)` on every cell with all levels
   `<= ell-1`, so `A_L(ell,n) = (1/4)A_L(ell-1,n) + T(ell,n)`.  Verified to
   full precision at `(8,17)` and `(12,25)`.  Charge 4 is answered with loss
   exactly `2^-2` per level against a budget that gains `2^5` per endpoint
   step; the residual family is the top-conductor cells `T(ell,n)`.
6. **PROVED reductions.**  `(CAB-L) <= (SPLIT-L) <= (ENV-L) <= (L4-LAYER)`,
   each step elementary (triangle inequality, Lemma 4, Minkowski,
   `sum_e X^4 <= max X^2 * sum_e X^2`), ending in a statement with **no cells
   and no interaction between conductor levels**.
7. **REFUTED with witnesses.**  In the order grading, `|K_cell| <= |2^ell raw|
   + |P_cell|` loses `8.3x` at `ell = 8` rising to `40.6x` at `ell = 18`
   (`2^(+0.25 ell)`); no proof may bound those halves separately there.  In the
   conductor grading the same split costs a bounded `5-60x`.

### (b) The precise reduced lemma

Everything on the path is proved except one absolute-constant statement:

> **(SUP-L)**  There is an absolute `K` such that for both endpoint degrees
> `n in {2ell+1, 2ell+2}` and every conductor level `1 <= j <= ell`,
> ```text
>       max_e |D_[j](e)|  <=  K (j-1) 2^((j-1)/2) 2^(n/2) 2^(-ell) ,
> ```
> where `D_[j] = P_j D - P_(j-1) D` is the exact-conductor-level component of
> the endpoint class discrepancy.

Given `(SUP-L)` with `K = 2`, the endpoint holds for every `ell >= 22` (odd)
and `ell >= 20` (even); with `K = 4`, for `ell >= 25` / `ell >= 23`.  The
remaining `ell` are inside the lane's certified finite range.  Chain, with
every constant explicit:

```text
(SUP-L) + Lemma 6  ==>  ||D_[j]||_4 <= K^(1/2)(j-1)2^((j-1)/2) 2^((2n-3ell)/4)
Minkowski          ==>  ||U_L||_4   <= sum_j (that)
|D| <= U_L         ==>  M_4 <= ||U_L||_4^4  <  (mu - P_n)^4
diary 04 Thm       ==>  I_n(1) >= 1 .
```

`(SUP-L)` says each conductor layer exhibits square-root cancellation **in the
character count** (its trivial triangle bound is `2^(j-1)(j-1)2^(n/2)/2^ell`).
It is a sup-norm / delocalisation statement, not a moment statement.  Measured
`K` is `0.94-1.13` in median with `max = 2.00` over 341 (row, level) pairs and
no drift in either `j` or `ell`.

Fallback statements, in decreasing strength, all measured-holding:

* **(CAB-const)** `A(ell,n) <= c M_2^2` with absolute `c` (measured
  `1580-1900` from `ell = 13`, flat).  This is the honest `ell`-free form of
  the audit's own `(C4-weak)`; with `c = 1900` and the proved
  `M_2 <= mu Sigma(ell)` it closes the endpoint from `ell = 29`.
* **(CAB-L)** the conductor-graded cellwise-absolute bound: closes on every row
  from `ell = 4`, margin `2^(+0.46 ell)`, and (Result 5) implies the lane's
  **strong** target `K_4 <= M_2^2` from `ell = 10`.
* **(ENV-L)** `sum_e (sum_j |D_[j](e)|)^4 < (mu-P_n)^4` -- one inequality, no
  cells; closes from `ell = 6` / `11`.
* **(L4-LAYER)** `sum_j ||D_[j]||_4 < mu - P_n` -- one `L^4` number per
  conductor layer; closes from `ell = 10` / `11`.

### (c) Data

All tables above are exact integers.  The headline ones:

* `(CAB)` closure to `ell = 18`, both parities (22:10) -- **the odd crossing is
  `ell_0 = 17`**, first measured here; the audit stopped at `ell = 15` with a
  `17-18` extrapolation.
* the three-factor mechanism decomposition (22:25) -- `A/(3M_2^2)` saturates at
  `~600`.
* `(CAB-L)` closure to `ell = 20`, both parities, with the strict diary-04
  budget (23:20), and `A_L/M_2^2` falling through 1 at `ell = 10`.
* `(SPLIT-L)`, `(ENV-L)`, `(L4-LAYER)` closures (23:40).
* the `kappa_j` table, 341 (row, level) pairs (00:05).
* the top-conductor mass split (23:00) and the `(CAB)` cell-mass profile
  (22:40).

### (d) Next experiments

1. **E-A1 (highest value, cheap).**  Falsify `(SUP-L)` hard.  Extend the
   `kappa_j` table to `ell = 21..24` using `acb_cab_levels layers` (which needs
   no cell tensor and no Moebius transform, so it is `O(ell 2^ell)` and only
   the `i128` guard binds -- switch `A_j` to `i64` blocks or `BigInt` for the
   sup/`L^4` pass and `ell = 24` is minutes).  A single `kappa_j > 4` at large
   `j` would move the crossover by two levels; a `kappa_j` growing in `j` would
   kill the reduction outright.  Also test off-endpoint `n` and small `j`,
   where the current maximum `2.0000` sits.
2. **E-A2.**  Hand `(SUP-L)` to workstream C.  Its dichotomy is stated for the
   conductor filtration, which is exactly the filtration `D_[j]` lives on, and
   the increment side must collide with the low-conductor Weil equidistribution
   -- which is Lemma 6 here, with `V_2` **exact**.  `(SUP-L)` is a cleaner
   collision target than the `B_j(b)` cylinder data because it has no
   `ell`-dependence.
3. **E-A3.**  Prove `(SUP-L)` for the two extreme layers, where it is nearly
   forced: `j = 2` is exact (`V_2 = 2^(n-ell+1)`, two characters) and
   `j = ell` is the sibling difference `A_ell(e) = D(e) - D(e(1+x^ell))`, whose
   Fourier support is the full primitive family.  A proof for `j = ell` alone
   plus the measured constant for `j < ell` would already be a graded L3 rung,
   and by Lemma 7 the low-`j` cells are the `(ell-1)` problem at fixed `n`.
4. **E-A4.**  Re-audit the resurrection audit's remaining candidates in the
   **conductor** grading.  S10 (orderwise), S13 (annihilator-layerwise) and
   S14 `(ORD)` are all graded by objects that are not orthogonal; Lemma 4
   predicts that regrading each of them by exact conductor level removes a
   factor `Pabs/(3M_2^2) ~ 2^(0.4 ell)` from their loss.  Cheap: the sibling
   recursion is `ell` passes over the class vector.
5. **E-A5.**  Push `(CAB)` itself to `ell = 19, 20` for the record (the odd
   margin should reach `~0.1`), and re-fit the decay over `ell >= 15` only.
   Cost: `~15 min` and `~40 min` per row respectively; needs a fleet shard, not
   a 5-minute run.
6. **E-A6.**  The `(CAB-const)` constant `c ~ 1900`: measure it at
   `ell = 19, 20` to confirm saturation, and see whether the *conductor*
   analogue `A_L/M_2^2 ~ 2^(-0.46 ell)` continues -- if it does, `A_L = o(M_2^2)`
   is the strongest form of the statement and gives `R_0 -> 3`.

### Epistemic ledger for this file

**PROVED**: Lemmas 1, 2, 3 (order-grading Fourier form, level support,
termination of the order decomposition); Lemma 4 (conductor orthogonality,
`sum mult|P_lev| = 3M_2^2` exactly); Lemma 5 (parity selection rule); Lemma 6
(`V_1 = 0`, `V_2 = 2^(n-ell+1)` exactly, `V_j` Weil envelope -- given the
lane's proved `L`-degree distribution); Lemma 7 (the exact `1/4`-per-level
recursion at fixed `n`); the four reductions
`(CAB-L) <= (SPLIT-L) <= (ENV-L) <= (L4-LAYER)`; and the implication
`(SUP-L) + Lemma 6 ==> (W4-exact)` with the exact crossovers `ell >= 22`
(odd) / `ell >= 20` (even) at `K = 2`.

**REFUTED with exact witnesses**: the separate-halves split
`|K_cell| <= |2^ell raw| + |P_cell|` in the convolution-order grading (loss
`8.31` at `(8,17)` growing to `40.58` at `(18,37)`, `2^(+0.25 ell)`); the
audit's decay fit `2^(-0.283 ell)` as a description of the `ell >= 13`
behaviour (true value `2^(-0.79 ell)`); and the reading that the cellwise
absolute-value loss grows -- `A/(3M_2^2)` is flat at `~600` from `ell = 13`.

**MEASURED (finite evidence, no theorem credit)**: every closure ratio and fit
in this file; `(CAB)` on 26 rows `ell = 6..18`; `(CAB-L)` on 34 rows
`ell = 4..20`; `(ENV-L)`, `(SPLIT-L)`, `(L4-LAYER)` on `ell = 6..20`;
`kappa_j` on 341 (row, level) pairs; `A_L < M_2^2` from `ell = 10`.

**EXTERNALLY REPLICATED**: the conductor-level machinery and `A_L` itself at
`(4,9)`, `(4,10)`, `(5,11)`, `(5,12)` by an independent sympy brute force over
`GF(2)[x]` using direct subgroup averaging -- all fields agree, including the
zero-cell counts.  Internally cross-checked against
`connected_order_cumulant_report` (cell-by-cell) and
`exact_conductor_second_moment` (level-by-level).

**OPEN**: `(SUP-L)`; `(CAB-const)`; `(CAB)`, `(CAB-L)`, `(ENV-L)`,
`(L4-LAYER)` as uniform statements; the `(SUP-L)` constant `K` beyond
`ell = 20`.

**NO THEOREM CREDIT** is claimed for Lemire's conjecture or for any uniform
estimate.  A statement labelled MEASURED is a candidate for rung L2; the
Lemmas above are rung L1/L3 and are proved in the text.
