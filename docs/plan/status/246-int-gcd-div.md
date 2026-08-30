# Lane: int-gcd-div — closing `F:ml430-int-gcd-div-5e01872f` (`Int.gcd_div`)

<!-- plan-section: lane-status -->

**Your lane's block (`DONE for this pass`, int-gcd-div, 2026-08-29).**
`F:ml430-int-gcd-div-5e01872f` (`Int.gcd_div`) is **CLOSED** — `proved`,
axiom-free, statement identical to Mathlib's. Built the fourth bridge lemma
the `int-emod-negative` lane's handoff (`docs/plan/status/242-int-emod-negative.md`)
named but did not build, then `Int.gcd_div` itself, for a divisor of **any
sign or zero** — Mathlib's own hypotheses (`c ∣ a`, `c ∣ b`) carry no
restriction on `c`, and this proof does not add one.

**Verified the mirror-flip criterion myself, against the pinned Lean 4
source, before writing any proof.** Mathlib v4.30's `Int.gcd_div` is
`alias gcd_div := gcd_ediv` (`Mathlib/Data/Int/GCD.lean`); `Int.gcd_ediv`
itself is not restated in Mathlib at all — it lives in Lean 4 core
(`Init/Data/Int/Gcd.lean`, read at the pinned toolchain commit under
`/home/mjbommar/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/`),
stated over `/`. Core's own `instance : Div Int` (`Init/Data/Int/DivMod/Basic.lean`)
binds `/` to `Int.ediv`, with the comment "for compatibility with SMT-LIB" —
the SAME Euclidean division this development's `Int.ediv` already matches
bit for bit (confirmed by reading `Int.ediv`'s Lean 4 core recursive
definition and this repo's `int_prelude/division.rs` module doc side by
side). So this is a genuine same-definition mirror (honest flip per
CLAUDE.md's criterion), not a restatement of a different proposition — and
critically, since neither Mathlib's alias nor core's `gcd_ediv` carries a
`c ≠ 0` hypothesis, the fully general (`c` any sign, `c = 0` included)
statement is what had to be proved, not a restricted one.

Detail moved to [`../notes/246-int-gcd-div.md`](../notes/246-int-gcd-div.md).

<!-- plan-section: landed-changes -->

| 2026-08-29 | int-gcd-div | landed `Int.emod_eq_zero_iff_dvd_general` (`declare_emod_eq_zero_iff_dvd_general`, `int_prelude/dvd.rs`) — the sign-general `emod = 0 <-> dvd` bridge the prior lane named but did not build |
| 2026-08-29 | int-gcd-div | closed `F:ml430-int-gcd-div-5e01872f` (`Int.gcd_div`) via `declare_gcd_div` (`int_prelude/gcd.rs`) — mutual-divisibility proof for a divisor of ANY sign or zero, matching Mathlib's unrestricted hypotheses exactly (verified the mirror-flip against Lean 4 core's pinned source, not by name inference); `int_prelude::` 42 -> 47; axiom-free |
