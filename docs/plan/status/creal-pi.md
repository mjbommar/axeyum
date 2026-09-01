# Lane: creal-pi — π as a constructed real

<!-- plan-section: lane-status -->

**`DONE`, creal-pi, 2026-08-31.** **`CReal.pi` is constructed and
`3 ≤ π ≤ 4` is proved, axiom-free.** Thirteen declarations in
`crates/axeyum-lean-kernel/src/creal/pi.rs`, admitted through
`Kernel::add_declaration`, covered by
`creal_tests::every_creal_declaration_is_checked_and_axiom_free` (which reads
the environment, not a list) with an empty axiom footprint each.

**The claim this retracts.** `docs/curriculum/foundational-books/spivak.md`'s
Ch 15–17 row said π was "downstream of a root of `cos` and therefore of the
exact-root construction `creal/ivt.rs` refutes". That is a statement about
**one definition of π**, presented as a statement about π. Corrected in place
with a dated correction.

**Which series, and why not the obvious one.** Not Leibniz
(`π/4 = Σ (−1)ᵏ/(2k+1)`): its terms are dominated by no geometric series, so
the one cheap Cauchy witness this development has (`CReal.e`'s concrete
`exp_dominant_cauchy_body_concrete`) does not reach it. Instead **Euler's
transform of Leibniz**, `π/2 = Σ 2ᵏ(k!)²/(2k+1)!`, defined by its RECURSION
`t 0 = 1`, `t (k+1) = t k · (k+1)/(2k+3)` — so the ratio is definitional, no
factorial identity is ever built, `(k+1)/(2k+3) ≤ 1/2` needs no case split, and
every term is positive (no `(−1)ᵏ`, so none of `creal/alternating.rs`). The
domination series is `CReal.e`'s own `expDominant`, reused unchanged.

**Prelude-build delta, measured on this host by A/B (`creal_prelude_builds`,
debug, under lane contention):** 122.3 s with the whole `pi` step disabled →
**143.3 s** with all thirteen. The construction itself is free (117.9 s with
everything except `threeLePi` — inside the ~5 s run-to-run noise); **all of the
delta is `CReal.threeLePi`'s concrete rational evaluation**, and the size of
that delta is decided by four rational constants: bounding the four terms by
`1, 1/3, 1/8, 1/24` (largest formed `Nat` **864**) costs **+237 s**, while
`1, 1/3, 1/9, 1/18` (largest formed `Nat` **243**) costs **+21 s** — an 11x
swing from nothing but the choice of intermediate bound. The first attempt, on
the exact `S 4 = 32/21` (`Rat.normalize 800 525`), ran past 600 s and 5.9 GB
RSS and was killed.

**Next rung.** `CReal.sin`/`CReal.cos` at a general argument need a bound
depending on `|x|` — the power-series row, Spivak ch 24 — and after that the
*identification* of this π with a root of `cos`, which genuinely does need the
construction `creal/ivt.rs` refutes. Sharpening `π ≤ 3.2` needs the tail
bounded from index 4 rather than 0 (a re-indexed domination), the same call
`declare_e_le_four` makes for `e ≤ 4` versus `e ≤ 3`.

<!-- plan-section: landed-changes -->

| 2026-08-31 | `41bb7667d` | `CReal.pi` constructed from Euler's transform of Leibniz, with `CReal.piHalfConverges`, `CReal.piHalfLeTwo`, `CReal.piLeFour`, `CReal.twoLePi`, `CReal.threeLePi` — 13 axiom-free declarations, `+21 s` on the `creal` prelude build; `spivak.md`'s Ch 15–17 π claim corrected in place. |
