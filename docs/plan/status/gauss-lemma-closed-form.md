# Lane: gauss-lemma-closed-form-b — Gauss's-lemma `a := 2` closed form

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, gauss-lemma-closed-form-b, 2026-08-31).**
Verified ADR-0970's routed closed-form proof against the tree (every lemma
name/signature it depends on checked directly), then executed it. Landed in
`crates/axeyum-lean-kernel/src/nat_prelude/gauss_lemma.rs`:

- `Nat.gaussCountBleClosedFormDisj : ∀ half n, Disj(half, n)` — the general
  `countRange` closed-form invariant, by induction on `n` with `half` (and
  `t := div half 2`) held fixed.
- `Nat.gaussNegCountTwoClosedForm : ∀ m, Eq (gaussNegCount (succ (mul 2 m)) 2
  m) (sub m (div m 2))` — the classical closed form at the odd-prime shape
  `p = 2m+1`.

Both axiom-free, read from the kernel
(`theorem_axiom_footprint -- gaussCountBleClosedFormDisj` /
`-- gaussNegCountTwoClosedForm`, run separately since that tool keeps only
the first name argument: footprint `0` each). Full account, including three
direction/argument bugs found and fixed via the `render_lean`-diff probe
idiom, in
[ADR-0985](../../research/09-decisions/adr-0985-gauss-lemma-closed-form-lands-connecting-theorem-stays-open.md).

**Agreement with the six `a := 2` concrete instances ADR-0970 landed**,
recomputed independently: `sub m (div m 2)` equals the landed value for all
six `(p,m,expected)` = `(7,3,2)`, `(11,5,3)`, `(13,6,3)`, `(17,8,4)`,
`(19,9,5)`, `(23,11,6)`. A new kernel-level test
(`gauss_neg_count_two_closed_form_matches_the_landed_seven_two_instance`)
instantiates the closed-form theorem at `m := 3` and confirms the kernel's
own reduction, independently of the symbolic admission.

**The `F:nat-gauss-lemma` name collision named in the prior handoff was
avoided**: no fact was added this session (this lane landed kernel
declarations only), and every new kernel name
(`gaussCountBleClosedFormDisj`, `gaussNegCountTwoClosedForm`) is
unambiguously distinct from `Nat.gauss_lemma` (the pre-existing divisibility
cancellation theorem `lcm.rs` declares, matching `F:nat-gauss-lemma.json`).

**The connecting theorem to `a^m mod p` (Gauss's lemma's actual content) was
NOT attempted** — out of scope for this session per the brief. It still
needs the least-residue map's injectivity on `{1,…,m}`, a pairing lemma, and
a product-cancellation argument over `Int.prodRange`, exactly as ADR-0970
sized.

Verification run this session: `cargo test -p axeyum-lean-kernel --lib
gauss_lemma::` (3 passed), `cargo test -p axeyum-lean-kernel --lib
nat_prelude::` (243 passed, 0 failed — nonzero count confirmed), `cargo
clippy -p axeyum-lean-kernel --lib -- -D warnings` (clean), `python3
scripts/check-autogenesis-holdout-isolation.py` (PASS before and after —
`artifacts/autogenesis/` untouched this session, `held_out=146`).

<!-- plan-section: landed-changes -->

| 2026-08-31 | gauss-lemma-closed-form-b | `Nat.gaussCountBleClosedFormDisj` (general `countRange` closed-form invariant) and `Nat.gaussNegCountTwoClosedForm` (`gaussNegCount (succ (mul 2 m)) 2 m = sub m (div m 2)`, the classical odd-prime closed form) land axiom-free in `nat_prelude/gauss_lemma.rs` (ADR-0985), executing the route ADR-0970 sized and left open; agreement with all six landed `a := 2` concrete instances recomputed independently; the connecting theorem to `a^m mod p` stays open, unchanged sizing. |
