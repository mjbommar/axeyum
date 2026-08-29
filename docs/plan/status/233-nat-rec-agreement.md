# Lane: nat-rec-agreement — prove two `Nat.rec`-defined functions agree

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-rec-agreement, 2026-08-29).** The boundary two
lanes stopped at is crossed. Six declarations landed, kernel-admitted on the
FIRST attempt, `nat` still `axiom=0 opaque=0 quotient=0`.

Machinery, in `nat_prelude/ops.rs` beside the other eliminators:

- `cases_mod_two` — the `Nat.mod _ 2 ∈ {0,1}` split `bitwise.rs` named as
  absent, as an eliminator over a motive that VARIES with the remainder. It is
  `cases_lt_bound` at `bound = 2` fed `mod_lt`'s witness. **It genuinely did
  not exist**: `powsq.rs`'s *private* `mod_two_eq_one_of_ne_zero` gives only
  the `= 1` half and needs `r ≠ 0` already in hand, and `Nat.even_or_odd` is
  `div`-shaped and never mentions `Nat.mod`.
- `agree_by_fuel_induction` — induction on a shared fuel counter with **both**
  value arguments generalized in the motive. The brief predicted this
  generalization would be the entire difficulty. It was.

Declarations, in a new `nat_prelude/rec_agreement.rs` (the theorems mention
`Nat.bitwise` *and* a sibling, so neither module owns them):

| name | statement |
| --- | --- |
| `Nat.lt_two_cases` | `∀ r, Lt r 2 → Or (Eq r 0) (Eq r 1)` |
| `Nat.mod_two_eq_zero_or_one` | `∀ n, Or (Eq (mod n 2) 0) (Eq (mod n 2) 1)` |
| `Nat.bitwise_aux_eq_land_aux` | `∀ fuel m n, Eq (bitwiseAux and_fn fuel m n) (landAux fuel m n)` |
| `Nat.bitwise_aux_eq_lor_aux` | `∀ fuel m n, Eq (bitwiseAux or_fn fuel m n) (lorAux fuel m n)` |
| `Nat.bitwise_and_eq_land` | `∀ m n, Eq (bitwise and_fn m n) (land m n)` |
| `Nat.bitwise_or_eq_lor` | `∀ m n, Eq (bitwise or_fn m n) (lor m n)` |

Facts: `F:nat-mod-two-eq-zero-or-one`, `F:nat-bitwise-and-eq-land`,
`F:nat-bitwise-or-eq-lor`. The two `_three_five` predecessors are kept (they
are *reduction*-based, independent of the induction) with their now-stale
"was NOT attempted" notes corrected in place rather than deleted, and
`bitwise.rs`'s module doc likewise.

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

<!-- plan-section: landed-changes -->

| 2026-08-29 | nat-rec-agreement | `mod 2 ∈ {0,1}` split + fuel-generalized agreement induction; `bitwise and_fn = land` and `bitwise or_fn = lor` proved universally |
