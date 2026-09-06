# `axeyum-arith` — the shared exact-arithmetic layer

Status: design, proposed (lane `arith-design`, 2026-09-05)
Decision record: [ADR-1710](../09-decisions/adr-1710-a-shared-exact-arithmetic-crate-not-eight-private-copies.md)
Interface sketch: [`crates/axeyum-arith/src/lib.rs`](../../../crates/axeyum-arith/src/lib.rs)

> Every file:line in §2 was read, not grepped. Every literature claim in §3
> carries a source. Every number is either from a command shown here or
> attributed to the document it came from — and where a source disagrees with
> what this repository has assumed, the disagreement is recorded rather than
> smoothed over (see §3.4).

## 1. Why

[`docs/math-department/13-computer-algebra.md`](../../math-department/13-computer-algebra.md)
ranks the arbitrary-precision core first of its Next Ten, and names the cause
of the duplication in one sentence: *"Every module that needed more precision
grew its own `BigRational` path beside the core, which is why eight modules
carry bignum code and the zero-test does not."*

[ADR-1670](../09-decisions/adr-1670-i128-fast-path-with-a-big-integer-overflow-fallback-for-the-cas-zero-test.md)
measured the wall (`(x+1)^131` is the last binomial power the bounded normal
form expands; the 69th Catalan number cannot be *spelled* as an input) and
priced the three obvious migrations.
[ADR-1702](../09-decisions/adr-1702-rational-i128-fast-path-bignum-slow-path.md)
then landed a widening for `axeyum_ir::Rational` and discovered that a global
widening **breaks the CAS**, because `axeyum-cas` uses `i128` exhaustion as a
termination argument: 25 unit tests failed and about seven stopped terminating.

Neither ADR proposes what this note proposes, and neither is superseded by it.
They are about the **coefficient type at the API boundary**. This is about the
**algorithms underneath it**, which are a different problem with a different
answer:

- ADR-1702's answer is *do not change what `Rational` means*, and it is right.
- ADR-1670's answer is *keep the bounded normal form and add an unbounded
  fallback*, and it is right.
- Neither stops the ninth lane from writing the ninth polynomial remainder
  sequence over `BigRational`. That is what this crate is for.

The specific waste, measured in §2: **eight separate univariate
polynomial-over-ℚ implementations**, five of them over `BigRational`; **five
copies of modular exponentiation**; **six exact Gauss–Jordan / null-space
routines**; **three extended Euclid algorithms over ℚ\[x\]** with two of them
sharing a function name and a signature and knowing nothing about each other.

## 2. Inventory of what exists

### 2.1 The polynomial layer, by implementation

Legend: ● re-derived here · ▲ delegated to another implementation · ○ absent.
`qe_bivariate.rs`'s ℚ\[x\]\[y\] and `qe_fibre.rs`'s K\[y\] are counted
separately because each re-derives its own divmod, gcd, derivative and Sturm
chain *at its own level* rather than reusing the one below it.

| op | `mvpoly/big.rs` `BigPoly` ℤ\[vars\] | `qe_big.rs` `Vec<BigRational>` | `numberfield.rs` `poly_*` | `fps_analytic.rs` `poly_*` | `qe_fibre.rs` ℚ\[x\] extras | `ir/poly_big.rs` `big_*` | `qe_bivariate.rs` | `qe_fibre.rs` K\[y\] | `ir/poly.rs` i128 | `ratint.rs` i128 |
|---|---|---|---|---|---|---|---|---|---|---|
| trim | ● `:299`,`:308` | ● `:74` | ● `:370` | ● `:617` | ▲ | ● `:87` | ▲ | ● `:571` | ● `:31` | ○ |
| degree | ● `:399` | ● `:83` | ● `:378` | ● `:625` | ▲ | ● `:95` | ● `:1172` | ● `:367` | ● `:40` | ○ |
| add | ● `:446` | ○ | ● `:389` | ● `:634` | ○ | ● `:282` | ● `:1194` | ● `:336` | ● `:426` | ○ |
| sub | ● `:455` | ○ | ● `:400` | ○ | ● `:277` | ○ | ● `:1206` | ● | ○ | ○ |
| neg | ● `:464` | ○ | ○ | ○ | ○ | ● `:260` | ● `:1189` | ● `:361` | ● `:328` | ○ |
| mul | ● `:472` | ● `:132` | ● `:411` | ● `:648` | ▲ | ● `:265` | ● `:1211` | ● `:587` | ● `:407` | ○ |
| scalar mul | ● `:485` | ○ | ● `:428` | ● `:664` | ● `:353` | ● `:714` | ● `:1211` | ● | ○ | ○ |
| pow | ● `:282` | ○ | ○ | ○ | ○ | ○ | ● `:1216` | ○ | ○ | ○ |
| divmod | ○ | ○ | ● `:434` | ● `:771` | ● `:253` | ○ | ● `:1237` | ● `:625` | ○ | ● `:37` |
| rem only | ○ | ● `:151` | ▲ | ▲ | ▲ | ● `:125` | ▲ | ● `:655` | ● `:70` | ▲ |
| exact div | ● `:503` | ● `:201` | ▲ | ▲ | ▲ | ● `:172` | ▲ | ○ | ● `:140` | ○ |
| monic | ○ | ● `:173` | ▲ | ● `:796` | ▲ | ● `:163` | ○ | ● `:660` | ● `:123` | ○ |
| gcd | ● `:584` | ● `:185` | ▲ | ● `:807` | ▲ | ● `:148` | ● `:1267` | ● `:670` | ● `:105` | ▲ |
| ext gcd | ○ | ○ | ● `:460` full | ● `:828` full | ● `:293` half | ○ | ○ | ○ | ○ | ○ |
| pseudo-division | ● `:669` | ○ | ○ | ○ | ○ | ○ | ● `:1237` | ○ | ○ | ○ |
| derivative | ○ | ● `:117` | ○ | ● `:760` | ○ | ● `:113` | ● `:1223` | ● `:615` | ● `:56` | ○ |
| eval | ○ | ● `:89` | ○ | ● `:668` | ▲ | ● `:251` | ○ | ● `:605` | ● `:307` | ○ |
| content / primitive | ● `:522`,`:539` | ○ | ○ | ● `:718` | ○ | ○ | ○ | ○ | ○ | ○ |
| squarefree part | ○ | ● `:227` | ○ | ● `:858` | ▲ | ● `:206` | ● `:1284` | ● `:682` | ● `:180` | ○ |
| Cauchy bound | ○ | ● `:240` | ○ | ● `:872`,`:891` | ○ | ○ | ○ | ● `:768` | ○ | ○ |
| **Sturm chain** | ○ | ● `:266` | ○ | ● `:1018` | ▲ | ● `:297` | ○ | ● `:703` | ● `:343` | ○ |
| sign variations | ○ | ● `:294` | ○ | ● `:1044` | ▲ | ● `:316` | ○ | ● `:729` | ● `:372` | ○ |
| root counting | ○ | ● `:312` | ○ | ● `:1065` | ▲ | ● `:335` | ○ | ● `:746` | ● `:399` | ○ |
| root isolation | ○ | ● `:370` | ○ | ▲ | ▲ | ▲ | ● `:1329` | ● `:781` | ▲ | ○ |
| sign at algebraic | ○ | ● `:512` | ○ | ○ | ▲ | ○ | ▲ | ● `:964` | ○ | ○ |
| resultant | ○ | ○ | ● ideals `:1824` | ● `:1140`,`:1204` | ○ | ● `:611` | ▲ | ○ | ● `:485` | ● `:219` |

**Six Sturm chains**, verified by a name search whose every hit was then read
(`crates/axeyum-cas/src/qe_big.rs:266`, `crates/axeyum-cas/src/qe_fibre.rs:703`,
`crates/axeyum-cas/src/fps_analytic.rs:1018`,
`crates/axeyum-cas/src/sturm.rs:22`,
`crates/axeyum-ir/src/poly.rs:343`,
`crates/axeyum-ir/src/poly_big.rs:297`).

**Three extended Euclid routines over ℚ\[x\]**, two of them with the same name
and signature and no relationship:
`crates/axeyum-cas/src/numberfield.rs:460` `poly_ext_gcd` (full `(g, s, t)`),
`crates/axeyum-cas/src/fps_analytic.rs:828` `poly_ext_gcd` (also full),
`crates/axeyum-cas/src/qe_fibre.rs:293` `xgcd` (half — returns `(g, s)`, and
uses a non-unit `g` as a *modulus splitting* signal, which is a genuinely
different contract and should survive the migration as its own operation).

**Five modular exponentiations**, all read:
`ntheory.rs:60` (`u128` engine), `ntheory.rs:374` (`i128` public wrapper),
`ntheory_certify.rs:77` (the certificate checker's own copy — deliberately
independent, and it should stay independent; see §6),
`gfp.rs:343` (𝔽ₚ\[x\]), `factor_int.rs:462` (𝔽ₚ\[x\] again, a second copy
because `factor_int.rs` re-derives the whole 𝔽ₚ\[x\] layer rather than using
`gfp.rs`).

**Six exact Gauss–Jordan / determinant / null-space routines**:
`enclosure_special.rs:859` (`BigRational`, for the Krawczyk preconditioner —
its doc says outright it does not reuse `crate::matrix` because that is
machine-width), `ratint.rs:48`/`:99` (i128 fast path + `BigRational`
fallback), `fps.rs:1328`, `numberfield.rs:531`, `gfp.rs:534`,
`factor_int.rs:550`, plus `crate::matrix::Matrix::rref`.

### 2.2 The scalar carriers

| carrier | file:line | representation | normalization | overflow |
|---|---|---|---|---|
| `axeyum_ir::Rational` | `crates/axeyum-ir/src/rational.rs:145` | `{ num: i128, den: i128 }`, `Copy`; `den == 0` tags a handle into a global dedup pool of `BigRational` (`:87`–`:137`, cap `1 << 20`) | **on every operation** — `small_new` `:164` divides out a Euclidean gcd (`:930`) on every construction; `small_mul` `:206` cross-cancels two gcds before multiplying | three families, deliberately: `new` panics `:368`; `checked_*` decline; `wide_*` promote `:403`ff (ADR-1702). Never saturates. `numerator()` `:439` / `denominator()` `:455` return `i128` and **panic** on a promoted value, at 416 call sites |
| `mvpoly/big.rs::BigPoly` | `crates/axeyum-cas/src/mvpoly/big.rs:73` | `BTreeMap<Monomial, BigInt>` — **integer** coefficients; rationals are handled by clearing denominators in `from_mvpoly` `:334`, correct up to a positive rational scale | zero-stripping always (`:299`, `:308`); content stripping **on demand** (`normalized` `:552`, called at `gcd` `:611` and inside the pseudo-remainder loop `:695`) | budgeted: `mul_within` `:258` charges cost *before* the work |
| `lib.rs::BigQPoly` | `crates/axeyum-cas/src/lib.rs:3007` | `{ num: BigPoly, den: BigInt }` — a shared positive integer denominator | `reduced()` `:3040`, **on demand** | budget |
| `lib.rs::BigRatFunc` | `crates/axeyum-cas/src/lib.rs:2892` | `{ num: BigPoly, den: BigPoly }` | cross-multiplied, no gcd | budget |
| `axeyum_ir::RealAlgebraic` | `crates/axeyum-ir/src/real_algebraic.rs:84` | boxed `{ poly: Vec<BigInt>, lo: BigRational, hi: BigRational }` | — | `MAX_REFINE_STEPS = 256` `:63`, declines rather than looping |
| `poly_big.rs::BigAlgebraic` | `crates/axeyum-ir/src/poly_big.rs:71` | the same triple, unboxed and public | — | dimension/degree/round caps `:51`–`:56` |
| `gfp.rs` | `crates/axeyum-cas/src/gfp.rs` | `Vec<i128>`, every coefficient reduced into `0..p`, `p` passed as an argument to every function | on every op | widening `u128` multiply `:49`, binary double-and-add above `u64::MAX` |
| `gf2.rs::Gf2Poly` | `crates/axeyum-cas/src/gf2.rs:16` | bit-packed `Vec<u64>` | trailing words trimmed in `from_words` `:32` | metered through `Gf2Context` `:1461` |

**Neither `gfp.rs` nor `factor_int.rs` uses Montgomery or Barrett form.**
Reduction is by explicit `div_rem` against a passed modulus.

### 2.3 Determinants: the good news

Both big-determinant routes are already **fraction-free Bareiss inside an
evaluation–interpolation outer loop**, not naive Gaussian elimination:
`crates/axeyum-ir/src/poly.rs:485` (`sylvester_determinant`, with
`bareiss_determinant` at `:542` and `newton_interpolate` at `:592`) and
`crates/axeyum-ir/src/poly_big.rs:498` (`big_determinant`, Bareiss at `:539`,
Newton at `:581`). Each keeps an `O(dim!)` Leibniz twin as a differential
oracle only (`poly.rs:456`, `poly_big.rs:451`). This is the pattern the new
crate should generalize, not replace.

### 2.4 The kernel side

- Exactly **one** library file in `axeyum-lean-kernel` touches `num-bigint`:
  `crates/axeyum-lean-kernel/src/expr.rs:22`. `NatLit` is a single `BigUint`
  (`expr.rs:63`); all bignum arithmetic is methods on it (`checked_add` `:108`,
  `truncated_sub` `:113`, `checked_mul` `:122`, `lean_div` `:127`,
  `lean_mod` `:136`, `gcd` `:145`, `bounded_pow` `:161`, shifts and bitwise
  `:170`–`:195`).
- The accelerated path is `reduce_nat_binop`
  (`crates/axeyum-lean-kernel/src/tc.rs:2648`), over the 14-entry `NatBinOp`
  table (`:2278`), each entry admitted only if the environment declares it with
  exactly Lean's type (`build_nat_binop_table` `:2507`).
- **Every prelude numeral is unary**, and no prelude file constructs a
  `Lit::Nat`. Construction sites read:
  `crates/axeyum-lean-kernel/src/fo_code.rs:184` (`Nat.succ^n Nat.zero`),
  `crates/axeyum-lean-kernel/src/linarith/generic.rs:115`,
  `crates/axeyum-lean-kernel/src/ipc_heyting.rs:353`,
  `crates/axeyum-lean-kernel/src/nat_prelude/polynomial_setoid.rs:3347`.
  The recognizers walk `App(Const Nat.succ, _)` chains and **do not accept a
  `Lit::Nat` at all** (`linarith/int.rs:153`, `ring/int.rs:141`).
- `reduce_nat_binop` requires **both** whnf'd operands to be `Lit::Nat` or
  `Nat.zero` (`tc.rs:2666`–`2669`). So on prelude-built numerals **the bignum
  fast path never fires**; the term reduces through `Nat.rec` instead. This is
  ADR-1617's finding, and §9 is what to do about it.
- The only bridge between the two representations lives *inside* the
  conversion checker — `nat_offset` `tc.rs:2383`, `def_eq_nat_offset` `:2414`,
  `nat_literal_to_constructor` `:2453`, `reduce_nat_succ` `:2435` — and each
  peels **one** `succ` per call, so any `Nat.rec` computation over a literal
  `n` is Θ(n) kernel steps. **There is no prelude-level theorem and no
  normalization function.** Absent, confirmed by search for `OfNat` / `natLit`
  / `nat_lit` in `prelude.rs` and `nat_prelude.rs`.

### 2.5 Dependency facts

```
$ grep -rn "num-bigint\|num-rational\|num-traits\|num-integer" --include=Cargo.toml .
crates/axeyum-fp/Cargo.toml:16:num-bigint = "0.4"
crates/axeyum-lean-kernel/Cargo.toml:15:num-bigint = "0.4"
crates/axeyum-ir/Cargo.toml:21:num-bigint = { version = "0.4" }
crates/axeyum-ir/Cargo.toml:22:num-rational = { version = "0.4", ... }
crates/axeyum-ir/Cargo.toml:23:num-integer = { version = "0.1" }
crates/axeyum-ir/Cargo.toml:24:num-traits = { version = "0.2" }
crates/axeyum-cas/Cargo.toml:25:num-bigint = { version = "0.4" }
crates/axeyum-cas/Cargo.toml:26:num-rational = { version = "0.4", ... }
crates/axeyum-cas/Cargo.toml:27:num-traits = { version = "0.2" }
```

**None of these is in the root `[workspace.dependencies]`.** Four crates pin
the same version literally, and `axeyum-ir` and `axeyum-cas` independently
repeat the identical `num-rational` feature incantation. Resolved versions
(from `Cargo.lock`): `num-bigint 0.4.6`, `num-rational 0.4.2`,
`num-integer 0.1.46`, `num-traits 0.2.19`. Moving these to
`[workspace.dependencies]` is a free, independently-valuable slice-0.

## 3. Ecosystem and literature

### 3.1 The Rust crates

| crate | mul | div | gcd | radix | `no_std` / wasm | license | latest | assurance |
|---|---|---|---|---|---|---|---|---|
| **`num-bigint` 0.4.6** (what we resolve today) | schoolbook ≤32 limbs, half-Karatsuba, Karatsuba ≤256, **Toom-3 ceiling** — `multiplication.rs:101,107,165,279` | **Knuth Alg. D only** — `division.rs:190,232,251`; no Burnikel–Ziegler symbol in 0.4.6 | **Stein's binary** — `biguint.rs:227` | bytes 2..=256, strings 2..=36 (`convert.rs:158,222`); no `divide_and_conquer` symbol in 0.4.6 | yes / yes | MIT OR Apache-2.0 | 0.4.6 in-tree | no `fuzz/`; quickcheck+arbitrary integrations, a `tests/fuzzed.rs` regression corpus; no differential oracle |
| `num-bigint` 0.5.1 (2026-07-05) | same ladder; **NTT merged on `master` only** ([PR #282](https://github.com/rust-num/num-bigint/pull/282), 2026-08-12), unreleased | + Burnikel–Ziegler (`BURNIKEL_ZIEGLER_THRESHOLD = 64`) | Stein | + D&C radix **output** above 32 limbs; input still quadratic | yes / yes | MIT OR Apache-2.0 | 0.5.1 | as above |
| **`dashu`** (`-int`/`-float`/`-ratio`) 0.6.0 | simple ≤24, Karatsuba ≤96, Toom-3, **NTT above 4 000 words** (`mul/mod.rs:16,23,28`) — released, since `dashu-int` 0.4.3 (2026-06-21) | Burnikel–Ziegler (`div/divide_conquer.rs:1` says so by name) | **Lehmer** (`gcd/lehmer.rs`); **no half-gcd** | strings 2..=36 D&C both ways; `to_digits`/`from_digits` base 2..=`Word::MAX` but **quadratic** | yes / yes (wasm32 is an explicit arch) | MIT OR Apache-2.0 | 0.6.0, 2026-08-09 | **`fuzz/` with a `rug`(GMP) differential oracle**, proptest in three crates, CI matrix at 16/32/64-bit words; ~102 `unsafe` sites |
| `ibig` 0.3.6 | simple 24, Karatsuba 192, Toom-3 ceiling; `ntt.rs` is dead scaffolding | D&C above 32 | binary | 2..=36, D&C both ways | yes / yes | MIT OR Apache-2.0 | 2022-09-17 | **weakest**: no fuzz, no proptest, no oracle. Superseded — `dashu` is the maintained fork (dashu's own NOTICE) |
| `malachite` 0.11.0 | Toom-2/3/4/6h/8h + **FFT at 450 limbs** | schoolbook → D&C → **Barrett/Newton** | **genuine subquadratic half-gcd** (`HGCD_THRESHOLD = 140`) | **arbitrary `&Natural` base, D&C** — the strongest in the field | yes / yes; `Limb = u64` even on wasm32 | **`LGPL-3.0-only`**, transliterated from GMP/FLINT/MPFR | 0.11.0, 2026-08-28 | 326 test files; `num` and `rug` differential oracles; `forbid(unsafe_code)`; but CI has no wasm and no `no_std` job |
| `crypto-bigint` 0.7.5 | Karatsuba only | Knuth D | Bernstein–Yang | 2..=36 quadratic | yes / yes | Apache-2.0 OR MIT | 2026-06-22 | differential proptests vs `num-bigint`. **Disqualified**: `BoxedUint` "is not arbitrary precision and will wrap at its fixed-precision" |
| `astro-float` 0.9.6 | schoolbook 32, Karatsuba 220, Toom-3 5400, **Schönhage–Strassen** | recursive D&C + Newton | **none** | **only 2, 8, 10, 16** | yes / yes | MIT | 2026-08-07 | MPFR differential tests, **inert off x86_64-linux** (`cfg(all(target_arch="x86_64", target_os="linux"))`). Float only — zero hits for `gcd`/`rational`/`BigInt` |
| `rust_decimal` 1.43.0 | fixed 96-bit | fixed | none | 2..=36 input only | yes / yes | MIT | 2026-09-02 | best fuzzing story here (`fuzz/` + proptest feature). A money type; scale ≤ 28 |
| `bigdecimal` 0.4.10 | inherits `num-bigint` 0.4 | inherits | inherits | inherits | yes | `MIT/Apache-2.0` (**not valid SPDX**) | 2025-12-27 | weakest: proptest suite double-gated off (`cfg(all(test, property_tests))` **and** the dep commented out) |
| `rug` 1.30.0 | GMP | GMP | GMP half-gcd | GMP | **no** — `gmp-mpfr-sys/build.rs:103` *panics* on any cross-compile | LGPL-3.0+ | 2026-04-27 | — |

Two findings that decide things:

**`malachite` fails our own gate, and I checked rather than assumed.**
`deny.toml`'s `[licenses] allow` list is `MIT`, `Apache-2.0`,
`Apache-2.0 WITH LLVM-exception`, `BSD-2-Clause`, `BSD-3-Clause`, `ISC`,
`Unicode-3.0`, `Unicode-DFS-2016`, `Zlib`, `bzip2-1.0.6`, `CC0-1.0`,
`CDLA-Permissive-2.0`. `LGPL-3.0-only` is absent, so `cargo deny check` — a
gate named in `CLAUDE.md` — goes red the moment malachite enters the graph.
Rust statically links, and LGPL-3.0 §4d1 (the shared-library escape) is not
available to an `rlib`, still less to a `wasm32-unknown-unknown` artifact.
Adopting it is an ADR plus a `deny.toml` change plus a redistribution
obligation, not a lane decision.

**We cannot simply move to `num-bigint` 0.5.** `num-rational`'s latest is
0.4.2 (2024-05-08) and it pins `num-bigint = "0.4.0"`, so a 0.5 upgrade puts
two `BigInt` types in the graph. Every `BigRational` in §2.1 is
`num_rational::Ratio<BigInt>`.

### 3.2 The algorithms

**Fraction-free elimination and PRS.** Bareiss, *"Sylvester's Identity and
Multistep Integer-Preserving Gaussian Elimination"*, Math. Comp. 22(103),
1968, [10.1090/S0025-5718-1968-0226829-0](https://www.ams.org/journals/mcom/1968-22-103/S0025-5718-1968-0226829-0/);
Collins, JACM 14(1), 1967, [10.1145/321371.321381](https://doi.org/10.1145/321371.321381);
Brown & Traub, JACM 18(4), 1971, [10.1145/321662.321665](https://doi.org/10.1145/321662.321665);
Brown, TOMS 4(3), 1978, [10.1145/355791.355795](https://doi.org/10.1145/355791.355795);
Ducos, JPAA 145(2), 2000, [10.1016/S0022-4049(98)00081-4](https://doi.org/10.1016/S0022-4049(98)00081-4).
*Buys:* both Bareiss and rational Gaussian elimination do Θ(n³) operations;
the whole difference is operand size. By Bareiss's Eq. (3) every intermediate
is *identically a minor of the input*, so it obeys the Hadamard bound of the
answer — you can preallocate and know you will never exceed it. Subresultant
PRS gets primitive-like coefficient growth with **zero content gcds**.
*Costs:* exact division is a precondition, not an invariant — Bareiss's §V
shows the two-step variant needs a strictly stronger pivot condition than the
one-step (`a^(k−1)_{k+1,k+1} ≠ 0` as well as `c^(k−2) ≠ 0`), which is the
classic source of two-step bugs. Memory is Θ(n³ log(n‖A‖)) bits of live state
and cannot be streamed. And exactness of the subresultant divisions is a deep
theorem, not a local check — the Isabelle/AFP authors say the major problem
was *proving all the performed divisions are exact*. Cheap mitigation, free:
`divmod` hands you the remainder, so assert `rem == 0` at every step.

**Lazy vs eager rational normalization.** *This is the item where the
literature contradicts the premise, and the in-tree measurement contradicts
the literature.* [GMP's Rational Internals](https://gmplib.org/manual/Rational-Internals)
argues **for** eager normalization: *"It's believed that casting out common
factors at each stage of a calculation is best in general. A GCD is an O(N^2)
operation so it's better to do a few small ones immediately than to delay and
have to do a big one later."* Its Efficiency chapter allows the exception
(*"when forming a big product it might be known that very little cancellation
will be possible"*). PARI documents the eager cost with a number: squaring a
degree-10³ polynomial with coefficients 1/i takes **1 392 ms** as rationals vs
**1 116 ms** with the content cleared once
([PARI/GP User's Guide ch. 2](https://pari.math.u-bordeaux.fr/dochtml/html-stable/usersch2.html)).
Bernstein's *"Fast multiplication and its applications"* §13 (MSRI Publ. 44,
2008, pp. 352–353) gives the structure that makes laziness win: `a/b + c/d` is
the matrix product `[[b,a],[0,b]]·…`, so a *balanced product tree* of t
fractions costs O(n (lg n)² lg lg n) with one normalization at the end.
*Buys:* one gcd instead of k, and above the fast-multiplication crossover a
gcd is strictly more expensive than the multiplication it is attached to
(Brent–Zimmermann, *Modern Computer Arithmetic*, §2.7). *Costs:* unreduced
denominators reach k·b bits, so every later multiply, compare and hash pays;
CGAL's naive lazy DAG burned **501 MB against 70 MB eager**
([Pion & Fabri, SCP 76(4), 2011](https://doi.org/10.1016/j.scico.2010.09.003)).
**And a left-to-right unreduced fold is Θ(k³b²), worse than eager — laziness
only wins as a balanced tree.** ADR-1670's measurement is the in-tree
confirmation: the integer ring beats `i128` rationals by 6% at degree 64 and
the gap is still opening, *"because every `Rational::checked_mul` runs a
Euclidean gcd to renormalize, on every coefficient, on every product; the
integer ring pays no gcd at all."*

**Dyadic and ball arithmetic.** Johansson, *"Arb: Efficient
Arbitrary-Precision Midpoint-Radius Interval Arithmetic"*, IEEE TC 66(8),
2017, [10.1109/TC.2017.2690633](https://doi.org/10.1109/TC.2017.2690633)
([arXiv:1611.02831](https://arxiv.org/abs/1611.02831));
Fousse et al., *"MPFR"*, ACM TOMS 33(2) art. 13, 2007,
[10.1145/1236463.1236468](https://doi.org/10.1145/1236463.1236468);
Muller et al., *Handbook of Floating-Point Arithmetic*, 2nd ed. 2018,
[10.1007/978-3-319-76526-6](https://doi.org/10.1007/978-3-319-76526-6),
interval arithmetic is **Ch. 12, pp. 453–477** (new in the 2nd edition);
Rump, BIT 39(3), 1999, [10.1023/A:1022374804152](https://doi.org/10.1023/A:1022374804152).
*Buys:* a ball `[m ± r]` tracks only `m` at full precision — Johansson: *"only
m needs to be tracked to full precision; a few digits suffice for r"*, and
*"At high precision, this costs (1+ε) as much as floating-point arithmetic,
saving a factor two over endpoint intervals."* Arb's radius is a 30-bit
`mag_t` with **automatic upward rounding**, which *"allows cleaner code by
making upward rounding automatic and removing the need for many sign checks"*
— that is exactly the defect class `enclosure_special.rs` guards by hand
today. Rump's theorem bounds the overestimate at a uniform factor 1.5.
Measured: 9.4× faster than MPFR at 1024 bits on a 10⁵-term recursive product.
*Costs:* Johansson scopes Arb to **narrow** intervals — *"we are more
concerned with bounding arithmetic error starting from precise input than
bracketing function images on 'wide' intervals, say sin(\[3,4\])"* — and
division is 1.72× MPFR at 64 bits, only winning (0.82×) at 4096. Correct
rounding carries a per-function termination obligation: MPFR's Ziv strategy
*"will not terminate"* unless you can identify every input whose output is
exactly representable. Dyadic exponents are unbounded, so repeated squaring
grows them with nothing to warn you — which is why `Dyadic` here carries an
explicit `MAX_EXPONENT`.

**Kronecker substitution and multiplication thresholds.** Harvey, *"Faster
polynomial multiplication via multipoint Kronecker substitution"*, JSC 44(10),
2009, [10.1016/j.jsc.2009.05.004](https://doi.org/10.1016/j.jsc.2009.05.004)
([arXiv:0712.4046](https://arxiv.org/abs/0712.4046));
Schönhage & Strassen, Computing 7, 1971, [10.1007/BF02242355](https://doi.org/10.1007/BF02242355);
Karatsuba & Ofman, Dokl. 145(2), 1962; Harvey & van der Hoeven, Annals 193(2),
2021, [10.4007/annals.2021.193.2.4](https://doi.org/10.4007/annals.2021.193.2.4).
*Buys:* KS turns one polynomial product into one integer product at `x = 2^N`,
so you inherit every tuned integer path for free — which for a pure-Rust layer
is the whole point. Harvey's observation is that standard packing wastes
*"about three-quarters of the digit-by-digit products"*; his four-point variant
is *"almost twice as fast as the standard Kronecker substitution"* between
degrees ~100 and ~5000. GMP's tuned thresholds (`mpn/x86_64/coreisbr/gmp-mparam.h`,
Sandy Bridge, limbs): `MUL_TOOM22 20`, `MUL_TOOM33 65`, `MUL_TOOM44 154`,
`MUL_TOOM6H 254`, `MUL_TOOM8H 333`, `MUL_FFT_MODF 396`, `MUL_FFT 4736`.
*Costs:* the multipoint variants lose below their crossover to packing
overhead, and Harvey never reaches the theoretical 4×. **A correctness
subtlety he states and does not resolve:** *"We assume that f and g have
non-negative coefficients… It should be possible to handle the case of signed
coefficients using essentially the same techniques, but we have not checked
the details."* Signed coefficients need an offset trick, and that is where a
from-scratch implementation goes wrong. *Checkability, unusually good:* a
claimed `h = f·g` is verified by the single evaluation identity
`h(2^N) = f(2^N)·g(2^N)` — one big-integer multiply, cheaper than redoing the
polynomial product and needing none of the multipoint machinery.

**Montgomery and Barrett.** Montgomery, Math. Comp. 44(170):519–521, 1985,
[10.1090/S0025-5718-1985-0777282-X](https://doi.org/10.1090/S0025-5718-1985-0777282-X);
Barrett, CRYPTO '86, LNCS 263:311–323,
[10.1007/3-540-47721-7_24](https://doi.org/10.1007/3-540-47721-7_24)
(conference 1986, volume dated 1987 — do not assert one year);
[HAC ch. 14](https://cacr.uwaterloo.ca/hac/about/chap14.pdf) Alg. 14.32/14.36/14.42;
Bosselaers et al., CRYPTO '93, [10.1007/3-540-48329-2_16](https://doi.org/10.1007/3-540-48329-2_16).
*Buys:* Montgomery replaces division by N with a mask and a shift, and REDC
yields `0 ≤ t < 2N` so exactly one conditional subtraction; the form is closed
under multiplication, and addition, negation, equality and gcd-with-N are
unchanged. HAC: 2n(n+1) single-precision multiplications, *"the classical
algorithm is superior for doing a single modular multiplication; however,
Montgomery multiplication is very effective for performing modular
exponentiation."* Barrett buys something different: **no constraint on the
modulus and no alternate representation** — Bosselaers lists "None" under both
argument transformation and postcalculation. *Costs:* the oddness constraint
is exact — REDC needs `gcd(N, 2^k) = 1`, i.e. `v₂(N) = 0`; one factor of 2 and
`N⁻¹ mod R` does not exist. **The representation invariant is the cost that
matters here:** a kernel looking at Montgomery-form limbs sees an integer that
is not the value it denotes, so `MontMul(a', b')` discharges nothing about
`a·b mod N`; the R-exponent has to be in the *type*. Bosselaers measures
Barrett within ~10% of Montgomery on reduction and ~6% on exponentiation.
**Conclusion for this crate: Barrett is the better default, because its output
is a true residue certified by `∃q. x = qm + c ∧ 0 ≤ c < m` with no
representation invariant crossing the kernel boundary.** Montgomery is reserved
for inner loops that have already paid for the tagged type.

**Subquadratic gcd.** Lehmer, Amer. Math. Monthly 45(4), 1938,
[10.1080/00029890.1938.11990797](https://doi.org/10.1080/00029890.1938.11990797);
Schönhage, Acta Inf. 1(2), 1971, [10.1007/BF00289520](https://doi.org/10.1007/BF00289520);
**Möller, *"On Schönhage's algorithm and subquadratic integer gcd
computation"*, Math. Comp. 77(261):589–607, 2008,
[10.1090/S0025-5718-07-02017-0](https://doi.org/10.1090/S0025-5718-07-02017-0)**.
*Buys:* Möller's one-sentence justification — *"even if the total length of
the remainders produced by Euclid's algorithm is quadratic, the total length
of the quotients is only O(n)"* — so carry a 2×2 matrix and never materialize
the remainders. O(M(n) log n). GMP's tuned thresholds today are far lower than
Möller's 2005 measurement: `HGCD_THRESHOLD` 96 (Sandy Bridge) / 64 (Skylake) /
109 (Zen) / 101 (arm64), `GCD_DC_THRESHOLD` 465 / 618 / 566 / 330. *Costs:*
implementation difficulty is the headline, and it is documented rather than
folklore — Möller: *"Both analysis and actual implementation are quite
difficult and error prone… it is seldom spelled out in detail in textbooks,
and when it is, it has been plagued by errors."* His line counts settle the
choice for a from-scratch Rust implementation: 1 967 lines / cyclomatic
complexity 292 for the Schönhage-1971 route against 733 / 133 for his own,
for the same runtime. *Checkability is the easy case, and half-gcd hands you
the certificate free:* the cofactor matrix **is** the algorithm's intermediate
state, so a Bézout pair falls out at the same complexity, and a wrong matrix
simply fails `ua + vb = g`. Pin `g ≥ 0`; Bézout certifies gcd only up to sign.

**Hensel lifting.** Zassenhaus, JNT 1(3), 1969,
[10.1016/0022-314X(69)90047-X](https://doi.org/10.1016/0022-314X(69)90047-X);
von zur Gathen & Gerhard, *Modern Computer Algebra*, 3rd ed. CUP 2013,
[10.1017/CBO9781139856065](https://doi.org/10.1017/CBO9781139856065) —
**Ch. 15, "Hensel lifting and factoring polynomials", pp. 433–472**;
van Hoeij, JNT 95(2), 2002, [10.1006/jnth.2001.2763](https://doi.org/10.1006/jnth.2001.2763).
*Buys:* Hensel is Newton iteration over a p-adic ring, so quadratic lifting
needs `⌈log₂ m⌉` steps against m, and the target precision is fixed in advance
by the Landau–Mignotte bound — which is exactly what
`crates/axeyum-cas/src/factor_int.rs:960` already does. *Costs, and this one
should change the design:* Monagan (ISSAC 2019) measured the constant —
*"when fast arithmetic is used, QHL… does the equivalent of 28
multiplications… fast QHL will not beat the quartic O(m²d²) LHL until fairly
high precision. Our data shows that Magma's fast QHL beats our quartic LHL
first at d = m = 200. For this reason, both LHL and QHL are in use in
practice."* **`factor_int.rs:713` is linear lifting, and for a schoolbook-mul
layer that is the right choice; the sketch's `HenselLift::lift` signature is
quadratic and should gain a linear sibling.** The worse cost is recombination:
van Hoeij, *"the complexity is not exponential in the degree N, it is only
exponential in the number of p-adic factors n"*, with Swinnerton–Dyer
polynomials as the standing witness. *Checkability:* a lifted factorization is
a witness — the kernel checks `f = g·h` by one polynomial multiplication.
**Irreducibility is the asymmetric half and is a search, not a witness.**
Prior formal art to borrow proof structure from: Divasón, Joosten, Thiemann &
Yamada, JAR 64(4), [10.1007/s10817-019-09526-y](https://doi.org/10.1007/s10817-019-09526-y),
AFP [`Berlekamp_Zassenhaus`](https://www.isa-afp.org/entries/Berlekamp_Zassenhaus.html)
(with separate `Hensel_Lifting` and `Reconstruction` theories — the same
two-phase split proposed here).

**Radix conversion.** Brent & Zimmermann, *Modern Computer Arithmetic*,
CUP 2010, **§1.7 Base conversion, §1.7.1 quadratic, §1.7.2 subquadratic,
pp. 37–39** ([free PDF](https://members.loria.fr/PZimmermann/mca/mca-cup-0.5.9.pdf));
[GMP §15.6.1 Binary to Radix](https://gmplib.org/manual/Binary-to-Radix) and
[§15.6.2 Radix to Binary](https://gmplib.org/manual/Radix-to-Binary);
Knuth TAOCP vol. 2 §4.4; Garner via HAC §14.5.2 Alg. 14.71.
*Buys:* naive conversion is O(n²) both ways; D&C gives **O(M(n) log n)**, by
the reassociation `A = A_hi·B^k + A_lo` — which is the same reassociation as
CRT reconstruction and as unreduced rational summation. *Costs:* the power
tree `B^{n·2^i}` must be built first (GMP has a *pair* of thresholds precisely
to separate "power available" from "power must be computed"); memory is ~lg n
powers of doubling size; and the crossover is **direction-asymmetric by ~50×**
— Sandy Bridge `GET_STR_DC_THRESHOLD 14` / `GET_STR_PRECOMPUTE_THRESHOLD 21`
limbs against `SET_STR_DC_THRESHOLD 1160` / `SET_STR_PRECOMPUTE_THRESHOLD
2043` digits, because *"`mpn_mul_1` is much faster than `mpn_divrem_1` (often
by a factor of 5, or more)"*. **The output recursion has a correctness
subtlety the input side does not**: MCA states the precondition —
*"it is assumed that `Output(A_lo,B)` has exactly k digits, after possibly
padding with leading zeros"* — and dropping the pad silently produces a wrong
number. GMP has the same class of hazard in sizing the output buffer: *"The
result is either correct or one too big"*, because distinguishing `99…9` from
`100…0` *"might well be almost as much as a full conversion."*
`RadixCertificate::verify` is immune to both, which is the point.

### 3.3 Lean 4 and Mathlib numerals — the kernel-bridge source material

Lean's kernel special-cases exactly **16 constants** for `Nat`
(`src/kernel/type_checker.cpp`, `reduce_nat` at line 672, table at 1286–1302):
`Nat.zero`, `Nat.succ`, and `add, sub, mul, pow, gcd, div, mod, beq, ble,
land, lor, xor, shiftLeft, shiftRight`. **`Nat.decEq` and `Nat.blt` are not in
the list** — `Nat.decEq` is a structure whose `decide` field *is* `Nat.beq`,
so it inherits acceleration without its own case. Numerals are bounded at
`LEAN_NAT_MAX_SIZE_DEFAULT = 128*1024*1024`. Lean's own source states the
trust boundary, e.g. for `Nat.add`: *"This function is overridden in both the
kernel and the compiler to efficiently evaluate using the arbitrary-precision
arithmetic library. The definition provided here is the logical model."*
`nat_lit_to_constructor` (`src/kernel/inductive.cpp:1359`) peels exactly one
`Nat.succ` per call, and `is_def_eq_offset` (`type_checker.cpp:1043`)
decrements one at a time — **so a `Nat.rec` computation over a literal `n` is
Θ(n) kernel steps in Lean too.** Our `tc.rs` is at full parity with this.

Mathlib carries the certified positional-notation triple, in
`Mathlib/Data/Nat/Digits/Defs.lean`:

- `def ofDigits (b : α) : List ℕ → α | [] => 0 | h :: t => h + b * ofDigits b t` (line 145) — Horner;
- `theorem ofDigits_digits (b n : ℕ) : ofDigits b (digits b n) = n` (line 242);
- `theorem ofDigits_append : ofDigits b (l1 ++ l2) = ofDigits b l1 + b ^ l1.length * ofDigits b l2` (line 168) — **the divide-and-conquer splitting lemma**.

**The gap, and it is the interesting one:** Mathlib 4 has no tactic to
discharge these for concrete numerals. The file's own TODO says *"A basic
`norm_digits` tactic for proving goals of the form `Nat.digits a b = l` where
`a` and `b` are numerals is not yet ported."* Mathlib 3 had it, and its lemma
shape is the one to copy:
`nat.norm_digits.digits_succ : r + b * m = n → r < b → digits b m = l → digits b n = r :: l`
— a chain of small steps, each one an arithmetic fact. Coq's answer was to
avoid the problem entirely with binary `positive`/`N`/`Z`
([Coq.Numbers.BinNums](https://rocq-prover.org/doc/v8.9/stdlib/Coq.Numbers.BinNums.html));
Grégoire & Théry, IJCAR 2006, LNCS 4130:423–437,
[10.1007/11814771_36](https://doi.org/10.1007/11814771_36), built
proved-correct bignum arithmetic *inside* Coq on a binary-tree word
representation so that divide-and-conquer applies, and certified primality for
13 000+ digit numbers. Their framing is ours: *"Even if generating a
certificate for a given n can be cpu-intensive, verifying conditions (1)-(5)
is an order of magnitude simpler… This is a direct application of the skeptic
approach"* — cf. Harrison & Théry, JAR 21:279–294, 1998,
[10.1023/A:1006023127567](https://doi.org/10.1023/A:1006023127567).

### 3.4 Four premises that were wrong

Recorded because each would otherwise have entered this document as fact.

1. **GMP does not argue for lazy rational normalization; it argues against
   it.** The pro-laziness sentence is in a different chapter and is scoped to
   "forming a big product". See §3.2.
2. **Bernstein has no note on converting between binary and decimal**, and
   *"Fast multiplication and its applications"* has **no section on radix
   conversion** — base conversion appears once, in the §12.7 *History*
   subsection, p. 350. Cite Brent–Zimmermann §1.7.2 and GMP §15.6 instead. The
   Bernstein material we *do* want is §13, the sum-of-fractions matrix product.
3. **`Nat.binaryRec` is not in Lean 4 core.** It is Mathlib,
   `Mathlib/Data/Nat/BinaryRec.lean:88`.
4. **A radix-conversion certificate is not cheaper to *run* than the
   conversion.** Horner is Θ(n²); a D&C producer is O(M(n) log n). What the
   certificate makes small is the **trusted code surface** — no division, no
   power tree, no digit-count pre-estimate, no zero-pad invariant — not the
   runtime. Say that, and not the other thing.

## 4. Where the crate slots in the DAG

The workspace's library edges today (dev-dependencies excluded — notably
`axeyum-lean-kernel`'s dep on `axeyum-cas` is **dev-only**, so there is no
cycle):

```
axeyum-arith          <- NEW: no axeyum dependency at all
    ^
axeyum-ir             <- currently the root; owns Rational, poly, poly_big, RealAlgebraic
    ^        ^
axeyum-cas   axeyum-fp   axeyum-query  axeyum-rewrite  axeyum-strings
    ^
axeyum-solver, axeyum-search, axeyum-py
```

`axeyum-lean-kernel` is a second root (library deps: `num-bigint` only).
`axeyum-arith` must sit **below `axeyum-ir`**, because `axeyum-ir` owns
`Rational`, `poly.rs`, `poly_big.rs` and `RealAlgebraic`, and `axeyum-ir` must
never depend on `axeyum-cas`. So the target edges are:

```
axeyum-arith  <-  axeyum-ir  <-  axeyum-cas
axeyum-arith  <-  axeyum-fp             (round_big_scaled_ratio, ieee_remainder_big)
axeyum-arith  <-  axeyum-lean-kernel    (NatLit; and the §9 radix bridge)
```

Against
[`foundational-dag.md`](../08-planning/foundational-dag.md)'s entry gates: this
crate adds no operator, no rewrite, no encoding, no backend and no logic
fragment. It adds a *carrier* below the IR. Its obligations under those gates
are therefore the representation contract (§5), the evidence story (§6) and
benchmark coverage (§7) — which is what the rest of this document is.

Against [ADR-0001](../09-decisions/adr-0001-vertical-slice-first.md)'s
"add crates only after a boundary is proven by use": the boundary is proven
eight times over by §2.1, and this is the first case in the repository where
the proof is *duplication already committed* rather than an anticipated need.

Against [ADR-0002](../09-decisions/adr-0002-ground-up-identity-oracle-bootstrap.md)
and [ADR-0017](../09-decisions/adr-0017-wasm-target-support.md): two
dependencies, both pure Rust, both already in the tree, no new registry
version, `wasm32` clean.

## 5. Module map

Implemented today in [`crates/axeyum-arith/src/lib.rs`](../../../crates/axeyum-arith/src/lib.rs):

**`Dyadic`** — exact `mantissa · 2^exponent` with a **canonical odd mantissa**,
so derived `Eq`/`Hash` agree with `Ord`. Five rounding directions
(`Round::{Down, Up, TowardZero, AwayFromZero, NearestTiesToEven}`), with
`round_outward(lower, upper, bits)` as the *only* interval-facing entry — a
single call, so a caller cannot round both endpoints the same way by accident,
which is the failure mode `enclosure_special.rs` guards against by hand at
`:237`/`:243`/`:251`. Exact `to_rational`, and `from_rational` that applies its
rounding mode **once, at the position the result needs**, so
`NearestTiesToEven` means nearest to the exact rational rather than nearest to
a wider intermediate. The **width contract** is explicit: `MAX_ALIGN_BITS`
(2³² bits), `align_cost_bits` to ask before paying, and `checked_add` /
`checked_sub` / `checked_mul` that decline rather than allocate. `MAX_EXPONENT`
bounds the exponent so repeated squaring cannot silently run away (§3.2).

**`Radix` / `RadixCertificate`, `MixedRadix` / `MixedRadixCertificate`** —
positional notation in **any base `b ≥ 2`** (a `BigUint`, so `2^32` and `10^9`
are as valid as `10`), digits little-endian and canonical. `verify` re-derives
the value by Horner and checks four independently-failable conditions:
base ≥ 2, every digit < base, no zero in the most significant place, and the
evaluation matches. `from_parts` exists precisely so a *forged* certificate can
be constructed and rejected. Mixed radix is what a CRT reconstruction, a
factorial number system and a bounded odometer all are.

**Status 2026-09-06: nothing in this crate is signature-only any more.** Every
trait has at least one implementation, every certificate has a `verify` that
re-derives its claim, and the crate contains no `todo!()`. The table below is
kept as the map from interface to implementation and to the copies each one is
there to replace — the third column is the migration debt, not the crate's.

| item | implemented by | still to replace |
|---|---|---|
| `Normalize` + `NormalizationReceipt` | `rational.rs`'s `RawRational`; `verify` re-derives the reduction and pins the sign, the coprimality and the bit counts | the policy question §3.2 leaves open. The receipt is how a benchmark answers it; no consumer has been migrated onto the lazy carrier yet |
| `UnivariatePoly` | `upoly.rs`, for both `ZPoly` and `QPoly` | the ten columns of §2.1 |
| `FractionFree` | `upoly.rs`, for `ZPoly` (fraction-free is a ℤ notion; `QPoly` has no impl and needs none) | `mvpoly/big.rs:669`, `qe_bivariate.rs:1237` |
| `BezoutCertificate` | `upoly.rs`'s `extended_gcd`. **Live, not superseded** by `PolyBezoutCertificate`: that one is the ℚ[x] object, this one the ℤ object | the three ext-gcds of §2.1 |
| `SturmCertificate` | `upoly.rs`'s `SturmChain::certificate`. Live for the same reason: `SturmChain` is the producer, this is its receipt | the six Sturm chains |
| `ModularRing` + `PowModCertificate` | `PlainModRing` (slice 2). Plain schoolbook reduction, a documented performance deviation from the Barrett/Montgomery plan, not a shape deviation | — (`ntheory.rs`'s two integer `pow_mod`s migrated) |
| `HenselLift` | `hensel.rs`'s `HenselRoot` + `lift_root`, quadratic lifting of a **simple root**, with a chain certificate | `factor_int.rs:713`, which is the *polynomial* half: linear two-factor lifting in 𝔽ₚ[x] on `i128` whose overflow is the termination argument. That is slice 7 and it is NOT done |
| `AlgebraicNumber` | `axeyum-ir`'s `algebraic_bridge.rs`, for **both** `RealAlgebraic` and `poly_big::BigAlgebraic` | `axeyum-cas`'s `algebraic::AlgebraicReal`, which is `i128`-backed and not yet on the trait |

Two signature changes the carriers forced, recorded rather than smoothed over:
`refine` returns a `bool` (an `i128`-backed endpoint can run out of room, and a
silent failure to refine makes `enclosure`'s width a claim nobody checks), and
`enclosure` returns an `Option` (a `Dyadic` conversion declines past
`MAX_EXPONENT`).

**The crate is also the workspace's single naming point for `num-bigint`,
`num-rational`, `num-integer` and `num-traits`** — `axeyum_arith::big`, plain
re-exports — and `scripts/check-arith-boundary.sh` enforces that no other crate
names them, in code or in a manifest. `axeyum-ir` and `axeyum-fp` are migrated;
`axeyum-cas` (31 files) and `axeyum-lean-kernel` (2 files) are on that gate's
allowlist with a per-file reason, and the allowlist itself fails the gate when
it goes stale.

**Two placement decisions, argued rather than assumed.**

*`Algebraic` / `RealAlgebraic` belongs in `axeyum-arith`, as a trait only.*
The carrier is already duplicated — `axeyum_ir::RealAlgebraic`
(`real_algebraic.rs:84`, boxed, private) and `poly_big::BigAlgebraic`
(`poly_big.rs:71`, unboxed, public) are the same triple. But `RealAlgebraic`
is a variant of `axeyum_ir::Value` (`value.rs:45`) and moving the *struct*
means moving a public IR type, which is exactly the churn ADR-1702 declined.
So: the **trait** lands here (giving `axeyum-cas`'s `real_algebraic.rs` and
`qe_fibre.rs` one interface to program against), and the two concrete carriers
stay where they are until a later ADR merges them.

*`NumberFieldElement` stays in `axeyum-cas`.* `qe_fibre.rs`'s on-demand
modulus splitting (`split_on` `:524`, `invert` `:533`, the `Inner::Split`
channel `:217`, `MAX_SPLITS` `:111`) is a *decision procedure's* control flow,
not arithmetic: a non-unit gcd is a signal to restart the enclosing
quantifier-elimination with a factored modulus. What belongs in `axeyum-arith`
is the half-extended Euclid `xgcd` underneath it, returning `(g, s)` with the
non-unit `g` as a first-class outcome rather than an error.

## 6. Certificate discipline

The rule, and the reason it is a rule: *a checker that cannot fail is worse
than no checker.* Every operation below either returns a receipt a caller can
re-derive **without any of the producer's machinery**, or is explicitly marked
as not carrying one.

| operation | receipt | re-derivation cost | what a forgery has to defeat |
|---|---|---|---|
| radix expansion | `RadixCertificate` | Θ(n²) Horner | four independent conditions; **implemented and tested**, including an out-of-range digit arranged so the value still re-derives |
| mixed-radix / CRT | `MixedRadixCertificate` | Θ(n²) | per-position base check plus the weighted sum |
| integer / polynomial gcd | `BezoutCertificate` | two multiplies + one add + two exact divisions | `ua + vb = g` and `g \| a`, `g \| b`. Pin `g ≥ 0`: Bézout certifies only up to sign (§3.2) |
| `pow_mod` | `PowModCertificate` — the square-and-multiply chain | one multiply + one reduction per bit | **never forms `base^exponent`.** This is ADR-1622's finding made reusable |
| Sturm root count | `SturmCertificate` | recompute the chain, recount the variations | the chain *and* the count, separately |
| Hensel factorization | the factors themselves | one polynomial multiply | `f = g·h`. **Irreducibility does not get a witness** — it is a search over 2^(n−1) recombinations, and must be labelled as such, not silently bundled |
| determinant | **none today** | — | see below |
| polynomial product | evaluation identity `h(2^N) = f(2^N)·g(2^N)` | one big-integer multiply | cheaper than redoing the product (§3.2) |

**The determinant is the open hole, and there is a known fix.** A Bareiss
determinant is one integer with no witness; rechecking costs as much as
computing. Zhou & Jeffrey, *Front. Comput. Sci. China* 2(1):67–80, 2008,
[10.1007/s11704-008-0005-z](https://doi.org/10.1007/s11704-008-0005-z)
([open PDF](https://www.uwo.ca/apmaths/faculty/jeffrey/pdfs/FFLUQR.pdf)) give
the fraction-free form **`PA = L D⁻¹ U`**; clear denominators and it is a pure
integral-domain matrix identity checkable by two matrix multiplications, with
`det A = ±∏pivots` falling out of the same object. It also does not need the
coefficient ring to support exact division, which is precisely the reason
`crates/axeyum-cas/src/matrix.rs:18` gives for *not* using Bareiss over
`CasExpr`. **This is the single most actionable item in this section.**

Three standing rules for the migration lanes:

1. **The certificate must carry every distinction the producer makes.** If
   `ModRing` picks Montgomery for an odd modulus and Barrett otherwise, the
   receipt says which — otherwise a differential test against the naive route
   cannot be written.
2. **`ntheory_certify.rs:77`'s private `pow_mod` stays private.** A checker
   that calls the producer's implementation is not a checker. That file's
   duplicate is the one copy in §2.1 that is *correct to keep*.
3. **When a lane touches a checker, delete one guard and require exactly one
   test to die.** `RadixCertificate::verify`'s four conditions are written so
   that this is possible: each has its own forgery test.

## 7. Performance plan

**What to measure before choosing anything.** ADR-1670's cost table is the
model: three columns that separate the coefficient ring from the algorithm
from the surrounding machinery, because *"the obvious comparison confounds two
effects"* — its "power" column mixes ring with binary-vs-repeated
exponentiation, and reporting it alone would have been wrong by 2.3×. Every
benchmark here must name which of the three it is.

**First benchmarks, in order:**

1. `Dyadic` round-trip and outward rounding against `enclosure_special.rs`'s
   `coarsen`/`dyadic_floor`/`dyadic_ceil` at 64 / 256 / 1024 / 4096 bits. This
   is the one place a `BigRational` endpoint pair is being used where a dyadic
   pair belongs, so it is the clearest before/after.
2. `RadixCertificate::expand` (repeated division) vs a divide-and-conquer
   expansion, at 32 / 128 / 512 / 2048 limbs, base 10 and base 2³². GMP's
   thresholds (§3.2) predict the crossover is **direction-asymmetric by ~50×**;
   confirm that on `num-bigint` 0.4.6, which has neither D&C direction.
3. Subresultant PRS vs the existing primitive PRS (`mvpoly/big.rs:707`), using
   its own `GcdCost` instrumentation (`mvpoly.rs:164`, `MvPoly::gcd_cost`
   `:565`) as the counter, so the comparison is operations rather than seconds.
4. `pow_mod` naive vs Barrett vs Montgomery at 64 / 256 / 2048-bit moduli,
   plus the certificate-checking cost separately.

**Algorithms in implementation order**, chosen by what the inventory says is
already load-bearing rather than by what is fastest:

1. Barrett `ModRing` with a certified `pow_mod` — replaces five copies, and
   the receipt is what ADR-1622's route needs.
2. `ZPoly` with pseudo-division and subresultant PRS — replaces the gcd column.
3. `QPoly` with Sturm and exact root isolation — replaces six Sturm chains.
4. Half-extended Euclid with `BezoutCertificate` — replaces three ext-gcds.
5. `PA = L D⁻¹ U` fraction-free elimination — closes the determinant hole.
6. Linear Hensel lifting with Miola–Yun error reuse; quadratic **only behind a
   measured crossover**, because Monagan's 28-multiplication constant means
   quadratic does not win until d = m ≈ 200 (§3.2).

**Thresholds we do not get to choose.** `num-bigint` 0.4.6's multiplication
ladder is fixed at schoolbook ≤32 limbs / half-Karatsuba / Karatsuba ≤256 /
Toom-3, with no FFT (`multiplication.rs:101,107,165,279`), its gcd is Stein's
binary (`biguint.rs:227`), and its division is Knuth Algorithm D with no
Burnikel–Ziegler (`division.rs:190,232,251`). So **do not spend a lane tuning a
Karatsuba threshold** — the leverage is entirely in (a) not calling the
underlying multiply as often, which is what fraction-free and lazy
normalization buy, and (b) whether we eventually move the base layer (§ADR-1710
option table). Kronecker substitution is the cheapest way to get Toom-3 to
apply to *polynomial* products; note Harvey's unresolved signed-coefficient
caveat before implementing it.

## 8. Migration plan

Each slice is one lane. Each lane's exit criterion is the same shape: **a
differential test against the copy it replaces, over that copy's own test
corpus, plus a measured before/after on the benchmark named above.** No slice
deletes the old copy in the same commit that adds the new one — the
differential test needs both.

| # | slice | replaces | risk | differential oracle |
|---|---|---|---|---|
| 0 | move `num-bigint`/`num-rational`/`num-integer`/`num-traits` into `[workspace.dependencies]` | four literal pins | none | `cargo tree -d` unchanged |
| 1 | `Dyadic` adopted by `enclosure.rs` / `enclosure_special.rs` for interval **endpoints** (values stay `BigRational` at the API) | `dyadic_floor` `:237`, `dyadic_ceil` `:243`, `coarsen` `:251` | low — the endpoint type is internal | the existing enclosure suite, plus: every `coarsen` result must still contain its input |
| 2 | `ModRing` + `PowModCertificate` | `ntheory.rs:60`, `ntheory.rs:374`, `gfp.rs:343`, `factor_int.rs:462` (**not** `ntheory_certify.rs:77`) | low | `ntheory_certify.rs`'s own independent checker is already the oracle |
| 3 | `ZPoly` + `FractionFree` | `mvpoly/big.rs`'s `pseudo_remainder` `:669` / `primitive_prs` `:707` / `gcd` `:584` | medium — `BigPoly`'s content-stripping-in-the-loop is load-bearing (`:695`) | `MvPoly::gcd_cost` `:565` runs the PRS twice already; run old and new |
| 4 | `QPoly` + Sturm + isolation | `qe_big.rs:266`, `fps_analytic.rs:1018`, `sturm.rs:22`, `ir/poly.rs:343`, `ir/poly_big.rs:297` | **high — five callers, and `fps_analytic.rs`'s chain normalizes members to primitive integer polynomials while `qe_big.rs`'s does not.** Land it as five sub-slices, not one | `fps_analytic.rs:2672` `bignum_and_machine_sturm_counts_agree` is an existing cross-width oracle; extend it |
| 5 | `BezoutCertificate` + half/full ext-gcd | `numberfield.rs:460`, `fps_analytic.rs:828`, `qe_fibre.rs:293` | medium — `qe_fibre`'s non-unit-`g` split contract must survive as an outcome, not an error | the `qe_fibre` split path has `MAX_SPLITS = 64`; assert the same split sequence |
| 6 | fraction-free `PA = L D⁻¹ U` | `enclosure_special.rs:859`, `ratint.rs:99`, `fps.rs:1328`, `numberfield.rs:531` | medium | the existing Leibniz oracles (`ir/poly.rs:456`, `ir/poly_big.rs:451`) |
| 7 | `HenselLift` (linear first) | `factor_int.rs:680`/`:713` and the local `fp_*` block `:336`–`:628` | medium | `gfp.rs` is the second implementation of the same 𝔽ₚ\[x\] ring — use it as the oracle before collapsing them |
| 8 | `AlgebraicNumber` trait adopted by `ir/real_algebraic.rs` and `cas/real_algebraic.rs` | interface only; carriers unchanged | low | existing suites |

**Sequencing constraint.** Slice 4 is the biggest win and the biggest risk, and
it must not go first: slices 2 and 3 are what establish the differential-test
pattern and the certificate shapes on lower-risk ground.

**A caution the inventory earns.** ADR-1702's finding — that `axeyum-cas`
uses `i128` exhaustion as a *termination argument* — applies to every slice
that touches a bounded route. `mvpoly/big.rs`'s `Cost` budget (`:89`) and
`qe_big.rs`'s `MAX_ISOLATION_STEPS`/`MAX_EXACTIFY_STEPS` (`:49`, `:54`) are the
unbounded ring's replacement for that argument. **A slice that removes a
bound must add one**, and its test must name the input that would otherwise
run away.

## 9. The kernel bridge

**The problem, restated exactly.** Our kernel has a bignum `NatLit`
(`expr.rs:63`) and a 14-op accelerated reduction (`tc.rs:2648`). Our preludes
build every numeral as `Nat.succ^n Nat.zero` (`fo_code.rs:184` and four other
sites), and the recognizers do not accept a `Lit::Nat` at all
(`linarith/int.rs:153`, `ring/int.rs:141`). So **the accelerator never fires on
prelude terms**, and ADR-1622's ceiling — the CRT family reconstructs in full
at numerals ≤ 105, the `101` rung costs 7.8 s, and the `251` rung is 51× that
for 2.5× the modulus, so 251 is the last prime the route certifies at all — is
a *representation* bound, not an arithmetic one.

**What a `RadixCertificate` buys, and what it does not.** It does not make
`Nat.rec` faster. What it does is let a large numeral arrive at the kernel as a
**limb chain in base 2^k** whose correctness is a chain of small arithmetic
facts, each one inside the accelerated 14-op set, rather than as one unary
term of length n. The shape is Mathlib's, and Mathlib has the theorem:

- `Nat.ofDigits b (l1 ++ l2) = ofDigits b l1 + b ^ l1.length * ofDigits b l2` — the D&C split;
- `Nat.ofDigits_digits b n : ofDigits b (digits b n) = n` — the round trip.

**The kernel-side theorem this needs.** A prelude `Nat.ofDigits` (Horner,
recursing on the list, so `Nat.rec` runs on the *digit count* and not on the
value) plus the two lemmas above, plus a step lemma in the Mathlib-3
`norm_digits` shape:

```
digits_succ : r + b * m = n → r < b → digits b m = l → digits b n = r :: l
```

Each hypothesis is a `Nat.add`/`Nat.mul`/`Nat.blt` fact on numerals that fit
one limb, i.e. exactly what `reduce_nat_binop` accelerates. The cost of
admitting an `n`-limb literal then goes from Θ(value) unary steps to Θ(limbs)
small accelerated steps.

**How this relates to the two ADRs.** ADR-1617 measured that the accelerated
path exists and does not fire; ADR-1622 measured what that costs a
number-theory certificate and worked around it by rebuilding modular
arithmetic out of congruence lemmas so the kernel never forms `a^(n-1)`. Those
are the same move at two levels: *never make the kernel materialize a large
object; hand it a chain of small facts instead.* The `PowModCertificate` in §6
is that move for exponentiation; the `RadixCertificate` is that move for the
numeral itself. **They compose:** with a base-2^k numeral bridge, ADR-1622's
modulus ceiling stops being about the size of `101` and starts being about the
number of chain steps.

**Honest scoping.** This is a prelude-and-tactic project, not an
`axeyum-arith` project. What this crate owes it is exactly one thing: a
`RadixCertificate` whose base is a `BigUint` (so `2^k` is expressible), whose
digits are canonical, and whose `verify` is the Rust twin of
`ofDigits_digits`. That is implemented. Everything after it belongs to a lane
that writes prelude declarations, and it should be briefed as one — with the
Mathlib-3 `norm_digits` lemma shape and the Grégoire–Théry precedent (§3.3) in
the brief.

## 10. The three open questions

1. **Do we stay on `num-bigint`, or move the base layer to `dashu`?** §3.1
   says `dashu` has released NTT multiplication, Burnikel–Ziegler division,
   Lehmer gcd, a GMP-differential fuzz suite, and the same license — against
   `num-bigint` 0.4.6's Toom-3 ceiling, Stein gcd and Knuth-D division. The
   cost is that `num_rational::BigRational` appears in ~18 files and does not
   follow. ADR-1710's recommendation is **not now, and re-open when a
   §7 benchmark shows the base layer is the bottleneck** — but the option
   table is priced there so the coordinator can decide otherwise.
2. **Does `RealAlgebraic` move?** §5 recommends the trait moves and the two
   concrete carriers stay, which leaves the `axeyum_ir` / `poly_big`
   duplication in place. The alternative — one carrier in `axeyum-arith`,
   `axeyum_ir::Value::RealAlgebraic` re-exporting it — is a public IR type
   change, i.e. the churn ADR-1702 declined for `Rational`.
3. **Is slice 4 one lane or five?** It touches five Sturm chains with
   *different* normalization conventions. This note says five sub-slices;
   the coordinator may prefer one lane with a longer leash.
