# Notes: 233-nat-rec-agreement

Detail moved out of [`../status/233-nat-rec-agreement.md`](../status/233-nat-rec-agreement.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

**THE BASE-CASE MISMATCH WAS NOT THE DIFFICULTY, and the brief expected it to
be.** `land`/`lor`/`ldiff` differ from *each other* in their fuel-exhaustion
rows — that is the absorbing-zero rule those three files establish — but none
of them differs from `bitwise`'s, because `bitwiseAux`'s general row is
`if f false true then n else 0` and evaluating a *concrete* `f` at the boundary
`Bool` literals reproduces each sibling's hand-chosen row by δβι alone:
`and false true = false → 0` matches `land`'s constant `0`;
`or false true = true → n` matches `lor`'s `n`. **Every base case in the proof
is `refl`, with no lemma.** The absorbing-zero rule decided what each sibling's
row had to be; `bitwise` re-derives the same answer from `f`. The one place
real proof content is needed is the per-bit combine, where
`bool_select_nat (f (beq (m%2) 1) (beq (n%2) 1)) 1 0` and `mul (m%2) (n%2)` are
both stuck at symbolic operands.

**FUEL-IRRELEVANCE IS NOT NEEDED HERE, and this is a negative result for the
seven blocked `natural-bitwise` facts.** `Nat.bitwise f m n := bitwiseAux f m m n`
and `Nat.land m n := landAux m m n` put the SAME expression in the fuel slot,
so the two recursions are indexed by **one** counter decrementing in lockstep,
never two that must be reconciled. The step does apply the IH at a
*non-canonical* fuel (fuel `k` against operand `m/2`), and that is harmless
precisely because agreement is proved fuel-parametrically. So the 7 facts need
fuel-irrelevance dispatched separately — **but** `bitwise_aux_eq_land_aux` /
`_lor_aux` are exposed for exactly that consumer, and they make
fuel-irrelevance for `bitwiseAux` and for `landAux`/`lorAux` interderivable:
prove it once, transport it.

Sketch for whoever takes it, in this machinery's own terms:
`agree_by_fuel_induction`'s `statement` closure may return **any** `Prop`, so
`fun fuel => ∀ m n, Le m fuel → Eq (landAux fuel m n) (land m n)` is directly
expressible — the helper does not assume an equation.

Gates: `cargo test -p axeyum-lean-kernel --lib nat_prelude` → **121 passed,
0 failed**, 2.92 s under `env -u RUST_MIN_STACK`; `cargo fmt --all --check`,
`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` and
`python3 scripts/validate-facts.py` (1921 facts, 0 errors) all clean. Two
mutations verified, each killing what it should: swapping `p.lor` for `p.land`
in the negative control kills exactly one test (120/1); replacing `lor`'s
`n = 0` guard with `land`'s constant `0` makes the kernel refuse the
declaration and the whole prelude build fails (0/121). NOT run: the aggregate
`just check` / `./scripts/check.sh`.
