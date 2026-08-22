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
