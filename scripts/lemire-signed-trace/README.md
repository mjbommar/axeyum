# Lemire signed-trace lane: Python anchors

Independent, exact re-implementations of the objects in
[`docs/research/10-cas/lemire-signed-trace/01-target-and-toolkit.md`](../../docs/research/10-cas/lemire-signed-trace/01-target-and-toolkit.md).
They exist so that every number this lane quotes can be regenerated without
the unmerged branch CAS, and so that the two agree.

Both scripts exit nonzero when a cross-check fails; an exit status of 0 means
every assertion in the file held, not merely that the file ran.

## Environment

The system Python (3.14) has `sympy` and `numpy` but no `pip`. Use `uv`:

```sh
uv venv /data0/axeyum/scratch/$AXEYUM_AGENT-lemire-venv --python 3.12
. /data0/axeyum/scratch/$AXEYUM_AGENT-lemire-venv/bin/activate
uv pip install python-flint sympy numpy
```

`python-flint` supplies `nmod_poly.factor` over `GF(2)` (about 8 us per
degree-20 polynomial); without it the scripts fall back to a pure-Python Rabin
test, roughly 100x slower. Nothing else is required.

## Scripts

- `lemire_anchor.py` -- `GF(2)[x]` as ints; irreducibles by degree (multiprocess);
  Mangoldt populations `N_j(g)` for every class of `E_j`; the group structure
  `E_j = prod_{k odd} Z/2^{e_k}` with explicit discrete logarithms; all
  characters with conductor and exact order; `L`-polynomials from degree-ball
  Fourier transforms; `H_j`, `P_{j,s}`, the four-population `T_{j,s}`,
  `C_{ell,n}`, `B_{ell,n}`. Running it reproduces the branch's pinned
  `C_{5,11} = -608` and `C_{7,16} = -4608`, the odd-endpoint identity
  `N_ell(1) = 1 + n I_n(1)`, checks every primitive `L`-polynomial at
  `(5,11)` has inverse roots of modulus `sqrt 2` whose `n`-th power sums equal
  the direct character sums, and checks the four-population identity against
  direct layer sums.

  ```sh
  cd scripts/lemire-signed-trace && python lemire_anchor.py
  ```

- `lemire_witt.py` -- Galois rings `GR(2^s, n)`, Teichmueller tables, traces of
  odd powers of Teichmueller lifts, and the check that the class of `alpha` in
  `E_j` and the vector `(Tr(teich(alpha)^k) mod 2^{e_k})_{k odd}` determine each
  other bijectively.

  ```sh
  cd scripts/lemire-signed-trace && python lemire_witt.py 13 6
  ```

- `lemire_layers.py <dump>` -- exact-order / exact-conductor layer analysis from a
  class-population dump (`axeyum-gf2-dump-populations <ell> <degree>`, built from
  `axeyum-gf2-dump-populations.rs.txt` dropped into `crates/axeyum-cas/src/bin/` of a
  snapshot of branch `agent/gf2/lemire-proof`): `P_{j,s}`, `Delta_{j,s}`, `T_{j,s}`,
  `#X_{j,s}`, the ratio against the `(HWO)` threshold `1/(4 ell)`; asserts the
  three-case reduction of `T_{j,s}` on every row.
- `lemire_cylinders.py <dump...>` -- the one-sided `(ICV)` object: per-cylinder sums of
  squared deviations, identity-cylinder rank, Sato--Tate prediction, `2^{2ell-2}` threshold.
- `lemire_twists.py <dump...>` -- twisted cylinder sums `A_psi^{(h)}` for every cylinder
  and character of `K` by exact Walsh transforms; identity and all-cylinder sups against
  `2^{ell-1}` (the open fact `F:gf2-lemire-cylinder-twist-sup-bound`).
- `lemire_parity.py <nmax>` -- counts irreducible `x^n + g`, `deg g <= floor(n/2)`, with
  parity and residues (kills the parity shortcut).
- `lemire_typeI_check.py` -- checks the exact Type-I / Moebius second-difference identity
  of note 02 section 2.1; exits nonzero on failure.
- `lemire_adams_check.py` -- checks directly from prime powers the exact
  Adams/Liouville identity
  `S_m(chi lambda) + S_m(chi) = 1_{2|m} 2 S_{m/2}(chi^2)`.  It records why
  degree-doubling through `chi -> chi^2` supplies no bound: the new
  Liouville-weighted term is not a Hayes character sum.

- `lemire_composition_family.py` -- **Theorem A** of note 08 (monomial composition
  transports Kaser--Lemire from an in-window seed of degree `m` to every degree
  `m*t` with `rad(t) | ord(f)` and `gcd(t, (2^m-1)/ord f) = 1`; Lidl--Niederreiter
  Thm 3.35 plus the one-line window computation), the exact coverage set
  `S(L,N)` over the certified seed ledger, the density trend against the proved
  `O((log N)^W)` lacunarity bound, the smallest uncovered composite, and the
  prime-`n` / power-of-two blockers of note 09.

  Two engines, never sharing an implementation. **Primary: the lane's Rust
  `GF(2)` CAS** -- `axeyum-gf2-monomial-family`, a batch driver over
  `axeyum_cas::gf2::{monomial_prime_eligibility, certify_irreducible,
  check_irreducible_certificate}` (source in the snapshot at
  `crates/axeyum-cas/src/bin/axeyum-gf2-monomial-family.rs`; build with
  `AXEYUM_CARGO_LOCK=... scripts/cargo-serialized.sh build --release -p axeyum-cas
  --bin axeyum-gf2-monomial-family` from the snapshot root). It is 10--300x
  faster than python-flint here, being bit-packed with a sparsity-aware
  reduction, so degree `10^5` compositions are seconds rather than minutes.
  **Cross-check: python-flint**, which re-derives a sample of the same verdicts
  by an independent Rabin test; the script asserts the two engines agree and
  exits nonzero if they do not. Point `AXEYUM_GF2_MONOMIAL_FAMILY` at the binary,
  or pass `--rust-binary`; `--engine flint` runs the whole computation on flint
  alone. It refuses to fall back silently when the binary is missing.

  Five mutation controls, each of which dies when one hypothesis of Theorem A is
  dropped: (1) `rad(t) | e` violated (`x^10+x^5+1` reducible) with its positive
  twin `x^6+x^3+1`; (2) `gcd(t,(2^m-1)/e) = 1` violated at the degree-6 seed of
  order 21 (`f(x^3)` of degree 18 reducible); (3) the window inequality
  `t*floor(m/2) <= floor(mt/2)` and (3b) the exact non-monomial tail formula
  `k*m - (k-s)*lsb(m)`, whose in-window solutions are exactly the power-of-two
  seed degrees; (4) the norm map from `F_4[x]` leaves the window except at a
  constant tail, where it reproduces the `m = 2` family; (5) the admissible
  prime set derived a third way -- `ord(f)` from a sympy factorization of
  `2^m-1` -- agrees with the powmod test in both engines on every degree
  `2..20`.

  ```sh
  python lemire_composition_family.py --nmax 100000 --sample 400 \
      --flint-crosscheck 220 --procs 24 --out data/composition-coverage.txt
  ```

  Generated table: `data/composition-coverage.txt`.  Ledger fact:
  `F:gf2-lemire-monomial-composition-family`.

- `lemire_horizontal_weights.py` -- the **horizontal (conductor-aspect) sums**
  of [note 12](../../docs/research/10-cas/lemire-signed-trace/12-horizontal-deligne-budget.md).
  Computes, exactly, `A_r(n,j) = sum_{chi in Prim_j(F_{2^r})} S_n(chi)
  = q^j N_j(1) - q^{j-1} N_{j-1}(1)`, and reads the largest Frobenius weight
  present off its growth in `r` at fixed `(n,j)` -- which is a lower bound on
  the top cohomological degree `i_max` of `H^*_c(Prim_j, Xi_n L_univ)`, the
  quantity the corrected question (Q1') of note 10 turns on.

  Three engines, no shared implementation. **`witt`** (exact, `j = 2`, every
  `n`, `r <= 16`): the Artin--Hasse identification `E_2 = W_2(F_q)`, the
  explicit order-4 character `chi_c(w) = i^{tr_W(c.w)}`, the reduction of the
  `L`-polynomial root to `alpha_d = -sum_u i^{Tr u} (-1)^{Tr(d u^2) + e_2(u)}`
  with `d = c_1/c_0^2` the `G_m`-invariant, and one Walsh--Hadamard transform.
  **`flint`**: direct window enumeration through `is_irreducible` plus a
  separate exact pass over the proper prime powers. **`rust`**: the lane's bulk
  engine `axeyum-lemire-horizontal` (source mirrored here as
  `axeyum-lemire-horizontal.rs.txt`; drop it into `crates/axeyum-cas/src/bin/`
  of a snapshot of branch `agent/gf2/lemire-proof` and build with
  `AXEYUM_CARGO_LOCK=... scripts/cargo-serialized.sh build --release -p
  axeyum-cas --bin axeyum-lemire-horizontal`), 24-threaded, own `F_{2^r}` log
  tables and Rabin/distinct-degree test, `~4e7` polynomials/s -- about `10x`
  python-flint and the only way to reach `r = 8`. Point
  `AXEYUM_LEMIRE_HORIZONTAL` at the binary or pass `--rust-binary`; the script
  refuses a silent fallback when `--grid` is requested without it.

  Six controls: (C1) `A_r(n,1) = 0` identically, with `N_1(1)` **computed** over
  the full `a_{n-1} = 0` window rather than assumed; (C2) Weil,
  `|alpha_d|^2 = q` exactly for every `d` and `r`; (C3) `witt` == `flint` on
  `A_r(n,2)`; (C4) `rust` == `flint` on every `N_j` in the overlap; (C5)
  `(2^r - 1) | A_r(n,j)` on every row (the `G_m` factor of note 12 Prop. 2);
  (C6) at `q = 2`, `I_n(1) = (N_j(1) - Theta(1))/n` with `j = ceil(n/2)-1`
  reproduces `data/irreducible-counts-n2-38.txt` for 20 degrees. C5 caught a
  real engine bug on its first run -- a merely *irreducible* (not primitive)
  field modulus at `r = 8`, which left most of the log table zero; the Rust
  engine now checks primitivity at startup.

  Five mutation controls, each killing the run through a *named* check:
  `--mutate 1` drops the Witt carry `e_2` (dies on C2), `2` sums over `q`
  instead of `q-1` characters per `G_m`-orbit (dies on the two-term Frobenius
  structure and C3), `3` drops the proper prime powers (dies on C1), `4` uses
  `q^j N_{j-1}` for `q^{j-1} N_{j-1}` (dies on C1), `5` shifts the window depth
  by one (dies on C3 and C6).

  ```sh
  python lemire_horizontal_weights.py
  AXEYUM_LEMIRE_HORIZONTAL=<snapshot>/target/release/axeyum-lemire-horizontal \
      python lemire_horizontal_weights.py --grid 9:5:3,11:4:4 \
      --out data/horizontal-weights.txt
  ```

  Generated table: `data/horizontal-weights.txt`; the Rust dumps it is read
  from are `data/horizontal-grid.txt` (pass `--grid-file` to regenerate
  without re-running the engine). `data/horizontal-grid-primitivity-bug.txt` is
  a **deliberately kept bad dump** -- the wrong `r = 8` rows from the
  non-primitive modulus -- and running the script against it must exit 1 with
  `control C5: (q-1) does not divide A_8(7,4) = 190017374764662784`. Do not use
  it as data.

- `lemire_horizontal_quotient.py` -- checker for
  [note 14](../../docs/research/10-cas/lemire-signed-trace/14-horizontal-unblocked.md)
  (angle 4b: is the horizontal route unblocked?). Exact `L`-function engine over
  `F_{2^r}` in `Z[zeta_8]` via an explicit basis of `E_j` (producer: Rust bin
  `axeyum-lemire-lfunc`, mirrored as `axeyum-lemire-lfunc.rs.txt`, built in the
  lane snapshot; dumps in `data/lfunc-dumps/`, weights table
  `data/horizontal-lfunc-weights.txt`). Reproduces the note-12 window-scan grid
  on 136 overlapping cells and every note-12 closed form; reaches
  `(j, r_max) = (4,8), (5,6), (6,5), (7,4)`. Controls C1--C9 (integrality,
  `(q-1) | A_r`, the `G_m`-freeness criterion `gcd(j,q-1) = 1`, Frobenius
  torsion orders `8` / `24` at `j = 2, 3` and none at `j >= 4`), mutation
  controls via `--mutate k`; exits nonzero on any failure.

- `lemire_cylinder_plancherel.py` -- checker for
  [note 17](../../docs/research/10-cas/lemire-signed-trace/17-cylinder-plancherel.md)
  (the Plancherel forcing test on the cylinder sums `A_psi`). Needs population
  dumps: `--dumps <files>` (regenerate with
  `axeyum-gf2-dump-populations <ell> <degree> 1300000000` -- **the third
  argument is required**; without it the binary panics on its default table-cell
  cap and a shell loop leaves a ZERO-BYTE dump that analyses as an empty group).
  `--model-extrapolation` runs the closed-form reach out to `ell = 1024` with no
  dumps. `--mutation-controls` runs seven mutants, each tripping exactly one
  named check. Exits nonzero on any failed control. Data: `data/plancherel-*.txt`.

- `lemire_effective_largeq.py` -- checker for
  [note 19](../../docs/research/10-cas/lemire-signed-trace/19-effective-large-q.md)
  (effectivising the large-`q` theorem). Verifies the Hsu/Cohen reach at
  `q = 3^11` both parities, the divisor-bound audit that locates the single
  ineffective step, the `omega`/slack trade-off table, and all 363 in-window
  witnesses over `F_{3^11}` (each re-verified by two independent
  irreducibility routines). Exits nonzero on failure. Data: `data/effq-*.txt`.
  **Note:** the witness tiers are dense on odd `[841,1199]` and sparse on
  `[1201,1601]` (odd, `11` not dividing `n`); the 18 odd multiples of 11 there
  are excluded by construction, not unresolved.

- `lemire_largeq.py` -- checker for
  [note 16](../../docs/research/10-cas/lemire-signed-trace/16-large-q-threshold.md)
  (the large-`q` threshold claim). Verifies the reversal duality
  `f in W_n <-> f* = 1 mod T^{ceil(n/2)}` as a bijection with flint (89 `(q,n)`
  pairs, 24,090 polynomials), re-derives Bagshaw's constant
  `961 e^2 = 7100.88`, and reproduces his published newly-covered prime-power
  list as an external control. 17 checks, 5 positive controls; exits nonzero on
  failure. Data: `data/largeq-*.txt`.

- `lemire_sieve_face.py` -- checker for
  [note 13](../../docs/research/10-cas/lemire-signed-trace/13-sieve-face.md)
  (angle 2, the sieve face). Recomputes with python-flint, from scratch and
  exactly, everything the Rust engine produced, and asserts each theorem's finite
  content: the exact Type-I lemma `A_d = 2^{h-k}` for `deg d <= h` and
  `A_d in {0,1}` above it, including the reversal criterion on every monic `d` of
  degree `h < k <= h+3` (153 `(n,k)` pairs, `6 <= n <= 20`, plus 454 pinned CAS
  rows with zero exceptions); the exact Mertens theorem for `F_q[t]`,
  `log(1/V(y)) = H_y + O(q^{-y/2})`, hence constant exactly `e^{-gamma}`; the
  window census for `n <= 44` against flint (`n <= 22`) and against the lane's
  pinned `data/irreducible-counts-n2-38.txt`; that `mindeg > n/4` forces
  `omega <= 3` and is nonempty for every `n <= 44`; the exact Selberg
  Brun--Titchmarsh `#irreducible <= |W_n|/G_{floor(h/2)}`; the exact rational
  prime-free populations for `n = 10..15` (all `2^{h+1}-1` Type-I equalities
  verified over `Q` with `Fraction`, plus nonnegativity and vanishing on every
  irreducible); that every one of the `2^ell` windows of length `2^h` contains an
  irreducible for `n <= 16` (the transfer bound of note 13 Prop. 11); and the LP
  ledger's monotonicity and `k_max` rows.

  Six mutation controls, each shown to trip a *named* check: M1 corrupts one
  `A_d`; M2 moves a unit of mass onto an irreducible; M3 perturbs one population
  value by `1/7`; M4 lowers the `P_3` degree threshold from `n/4` to `n/5`, where
  the implication is false; M5 triples the Selberg level so the remainders no
  longer vanish and the "bound" falls below the truth; M6 doubles the Mertens
  constant. Runtime about 2 s.

  ```sh
  /data0/axeyum/scratch/lemire-signed-trace-lemire-venv/bin/python \
      scripts/lemire-signed-trace/lemire_sieve_face.py     # -> SIEVE-FACE OK
  ```

  Bulk producer: the Rust CAS binary `axeyum-lemire-sieve` (source mirrored here
  as `axeyum-lemire-sieve.rs.txt`; drop it into `crates/axeyum-cas/src/bin/` of a
  snapshot of branch `agent/gf2/lemire-proof` and build with
  `AXEYUM_CARGO_LOCK=... scripts/cargo-serialized.sh build --release -p
  axeyum-cas --bin axeyum-lemire-sieve`). Subcommands `typei <n> <kextra>`,
  `factor <n>`, `dump <n>`, `selfcheck <trials>`; the last checks the binary's
  local `u64` polynomial layer against the crate's `Gf2Poly`/`Gf2Context` and its
  factorisation against `certify_irreducible` on all 32766 monic polynomials of
  degree `<= 14`. `factor 44` (8.4M polynomials) takes 30 s (measured).

  Generated tables: `data/sieve-typeI-n2-34.txt`,
  `data/sieve-window-factorizations-n2-44.txt`, `data/sieve-lp-levels.txt`,
  `data/sieve-parity-population-n{10,11,12,13,14,15}.txt`. The LP rows were
  produced with scipy/HiGHS (`uv pip install scipy` in the lane venv); every row
  claiming an LP value of 0 is re-certified over `Q` by the corresponding
  population file, so no floating-point result is load-bearing.

- `lemire_witness_search.py <lo> <hi>` -- flint-based sparse witness search with
  independent pure-Python Rabin re-verification (cross-check for the Rust certifier).

`data/witnesses-401-3000-sha256.tsv` is the certified witness table (degree, tail exponents,
SHA-256 of the `axeyum-gf2-search` artifact, check status); artifacts at
`/data0/axeyum/scratch/lemire-signed-trace-witnesses-401-3000/`.
`data/` also holds the generated tables: worst layer ratios (`layer-ratios-*`), full layer
tables at `ell = 20..24`, cylinder variances, twisted sums, irreducible counts.

## Cross-validation performed 2026-08-21

| Quantity | Anchor | Independent source |
| --- | --- | --- |
| `C_{5,11}`, `C_{7,16}` | `-608`, `-4608` | branch status file pins (sign-boundary regression) |
| `N_12(1) - 2^{n-12}`, `n = 25, 26` | `359`, `335` | branch `axeyum-gf2-hayes-endpoint 12` prints `odd=359`, `even=335` |
| layer sums `T_{j,s}` at `(5,11)` | four-population integers | direct sums over characters of exact conductor and order |
| Witt dictionary | bijective | `(n,j)` in `(7,3) (9,4) (11,5) (13,6) (15,7) (16,8)` |
