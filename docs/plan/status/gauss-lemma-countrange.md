# Lane: gauss-lemma-countrange — least-residue sign counting toward Gauss's lemma

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, gauss-lemma-countrange, 2026-08-31).** Landed the
`Nat.countRange`-shaped least-residue sign-counting primitive ADR-0960 sized
as "this prelude does not build" — it does, and the 19 `countRange`
declarations `shape_search` reported are real, general machinery (subset/
union/compl/congr/split laws in `finite_set.rs`/`totient.rs`), not just
names attached to totient's one use.

New `crates/axeyum-lean-kernel/src/nat_prelude/gauss_lemma.rs`:
`Nat.leastResidue`/`Nat.gaussSignNeg`/`Nat.gaussNegCount` (three plain,
non-recursive `Definition`s), `Nat.gauss_residue_two_eq_double_of_lt` (the
`a := 2` mod-bypass: since `2k` never reaches `p` for `k <= m = (p-1)/2`, the
least-residue map is just doubling, no real reduction), and eight concrete
`gaussNegCount` instances (`p ∈ {7,11,13,17,19,23}` at `a := 2`, one at
`a := 3`) numerically confirming the classical `p mod 8` pattern before any
general theorem was attempted. All axiom-free, read from the kernel.

**The general symbolic closed form
(`gaussNegCount p 2 m = m - div m 2`) and the connecting theorem to
`a^m mod p` (Gauss's lemma's actual content) are NOT reached.** Both are
fully routed lemma-by-lemma in
[ADR-0970](../../research/09-decisions/adr-0970-gauss-lemma-counting-primitive-lands-connecting-theorem-stays-open.md)
— every lemma name and signature the closed-form induction needs was
confirmed to exist in-tree before writing the route down, on the standing
rule that a handoff's prerequisites must be verified, not guessed. This was
a deliberate stopping point: the route is long (~150-250 lines of
`congr`/`transport`/`or_elim` proof-term construction) and was judged more
likely to cost a full session in `TypeMismatch` debugging without a REPL
than a precisely sized route the next lane can execute mechanically.

Verification run this session: `cargo test -p axeyum-lean-kernel --lib
nat_prelude::` (242 passed, 0 failed), `cargo test -p axeyum-lean-kernel
--lib gauss_lemma::` (2 passed), `cargo clippy -p axeyum-lean-kernel --lib
-- -D warnings` (clean), `python3 scripts/check-autogenesis-holdout-isolation.py`
(PASS before and after — `artifacts/autogenesis/` untouched this session).

<!-- plan-section: landed-changes -->

| 2026-08-31 | gauss-lemma-countrange | `Nat.leastResidue`/`Nat.gaussSignNeg`/`Nat.gaussNegCount` (least-residue sign counting over `Nat.countRange`) plus the `a := 2` mod-bypass theorem and eight concrete instances land axiom-free in new `nat_prelude/gauss_lemma.rs` (ADR-0970), toward Gauss's lemma / the second supplementary law; the general closed form and the connecting theorem to `a^m mod p` stay open, fully routed for the next lane. |
