# Notes: 255-nat-binaryrec

Detail moved out of [`../status/255-nat-binaryrec.md`](../status/255-nat-binaryrec.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

Determined by **reading the declaration authority, not the source text**: every
inductive must go through `Kernel::add_inductive`, so I enumerated every
non-test call site of it in the prelude construction path. The complete list of
inductives any prelude declares is `True`, `False`, `And`, `Or`, `Iff`, `Eq`,
`Exists`, `Acc`, `Bool`, `Nat`, `Decidable` (`prelude.rs`), `Nat.le` and
`Nat.Fin` (`nat_prelude.rs`), `Char` (`string_prelude.rs`), `Eq` again
(`quotient.rs`). No product. Confirmed after the fact by the kernel itself:
`Nat.Pair` admitted with no `DeclarationExists` collision, and the
environment-derived `every_nat_declaration_is_checked_and_axiom_free` is green.

**The prelude's standing workaround is a `Bool`-SELECTED function, and it is
deliberate**, not an oversight: `Nat.xgcdAux fuel m n (sel : Bool)`
(`int_prelude/bezout_witnesses.rs`, whose module doc says so explicitly),
`Nat.divModState` (`division.rs`), and `creal/ivt.rs`'s `Bool → CReal` bracket
carrier. It keeps ONE recursion — so one induction proves both components — at
the cost of evaluating the step twice per component.

### What I built instead: `Nat.Pair`

A monomorphic, **zero-parameter, one-constructor** inductive, mirroring
`Nat.Fin`'s construction in `finite.rs` (`add_inductive`, then projections
through the kernel-generated recursor):

```text
Nat.Pair       : Type 0
Nat.Pair.mk    : Nat -> Nat -> Nat.Pair
Nat.Pair.fst   : Nat.Pair -> Nat          -- Pair.rec.{1}, constant motive
Nat.Pair.snd   : Nat.Pair -> Nat
Nat.Pair.fst_mk : ∀ a b, fst (mk a b) = a          -- refl (iota)
Nat.Pair.snd_mk : ∀ a b, snd (mk a b) = b          -- refl (iota)
Nat.Pair.eta    : ∀ q, mk (fst q) (snd q) = q      -- Pair.rec.{0}, refl branch
Nat.Pair.ext    : ∀ q r, fst q = fst r -> snd q = snd r -> q = r
```

**Not a parametric `Prod α β`.** The kernel's `add_inductive` handles that
shape (the test fixture proves it), but a general `Prod` belongs in the LOGIC
prelude where every carrier can reach it, and that is a wider decision than the
`Nat`-local need here. `Nat.Pair` is the `ℕ × ℕ` this prelude actually wants;
promoting it is a separate call.

**One real defect, found by the kernel and invisible to `cargo check`.**
`NatOps::congr` states its conclusion at `Nat`, so using it for `ext`'s two
component rewrites built `Eq AxNat (mk …) (mk …)` and the gate rejected with
`TypeMismatch { expected: AxNat, got: AxNat.Pair }`. Note this is the
*small-`expected`-id* shape CLAUDE.md warns about (`ExprId(3)`) **without**
being a sort error — `AxNat` is itself interned early. The fix is a local
`congr_nat_to`: keep the HYPOTHESIS at `Nat` (so `NatOps::transport` still
applies unchanged) and move only the motive's body to the target carrier.
Anyone building over `Nat.Pair`, `Nat.Fin`, or `CReal` will hit this; the
helper is in `binary_rec.rs` and generalizes to any carrier.

## 2. `Nat.binaryRec` — exact statement and shape

```text
Nat.binaryRecAux : Π (α : Type 0), α -> (Bool -> Nat -> α -> α) -> Nat -> Nat -> α
                                   z          f                   fuel   n

binaryRecAux α z f 0        n        ≡ z
binaryRecAux α z f (succ k) 0        ≡ z
binaryRecAux α z f (succ k) (succ m) ≡ f (beq ((succ m) % 2) 1) ((succ m) / 2)
                                         (binaryRecAux α z f k ((succ m) / 2))

Nat.binaryRec α z f n := binaryRecAux α z f n n
```

All three `Aux` rows are **definitional** (βδι) and are declared as `refl`
theorems (`binaryRecAux_zero_fuel`, `binaryRecAux_zero`, `binaryRecAux_succ`)
so consumers can rewrite with them; `binaryRec_zero` is likewise `refl`.

The device is `binary.rs`'s `testBitAux` one, as the brief pointed out:
recurse structurally on a FUEL counter, carrying `n` as an ordinary parameter
replaced by `n / 2` in the function VALUE. Motive `fun _ => Nat -> α`, so this
is large elimination into `Type 0`.

Three design points worth carrying forward:

- **The `n = 0` guard is not optional.** Without it, fuel `succ k` at `n = 0`
  applies `f` at `bit false 0 = 0` and the value depends on how much fuel
  remained — fuel-irrelevance would be FALSE, and with it every equation that
  reaches a non-canonical fuel. (Same family as the `land`/`lor` absorbing-zero
  rule, arriving from the other side: here the guard, not the row, carries it.)
- **`α` is an explicit `Type 0` argument, not a universe parameter**, and the
  motive is CONSTANT in `n`. That is forced, not chosen — see §3.
- **The bit is a `Bool`**, computed as `beq (n % 2) 1` — this prelude's ad-hoc
  `Nat.bodd`, the spelling `bitwise.rs` already uses. That makes the step's
  shape `∀ b n, α → α` line up with `Nat.bit : Bool -> Nat -> Nat`, which the
  evaluation checks exploit.

### The two theorems that are actual content

```text
Nat.binaryRecAux_agree_of_fuel :
  ∀ α z f fuel1 n fuel2, Le n fuel1 -> Le n fuel2 ->
    binaryRecAux α z f fuel1 n = binaryRecAux α z f fuel2 n

Nat.binaryRec_succ :
  ∀ α z f m, binaryRec α z f (succ m)
    = f (beq ((succ m) % 2) 1) ((succ m) / 2) (binaryRec α z f ((succ m) / 2))
```

`binaryRec_succ` is the equation Mathlib's `binaryRec` gets **definitionally**
from `WellFounded.fix` and a fuel encoding has to **prove**: the canonical
instance supplies fuel `succ m` while the recursive call needs fuel
`(succ m) / 2`.

Fuel-irrelevance is in the DOUBLE-fuel form for exactly the reason
`rec_agreement.rs`'s module doc gives — the canonical instance puts `n` in the
fuel slot, so a fuel-versus-canonical statement is self-referential. Proved by
`agree_by_fuel_induction` (`ops.rs`, `pub(super)` and reusable) on `fuel1` with
`n` and `fuel2` both generalized in the motive; the `n = succ m` step derives
`fuel2 = succ (pred fuel2)` from positivity and applies the IH at
`(div (succ m) 2, pred fuel2)`.

The hypotheses are load-bearing, not decoration: `binaryRecAux 0 n = z` for any
`n`, so the unconditional statement is false. (This is the same trap the `lor`
transport lane hit today from the other direction — see CLAUDE.md's
`lor_aux_comm_of_fuel` note.)

### Two lemmas promoted out of hiding place 2

`rec_agreement.rs`'s **private** `half_le_predecessor_of_succ` carries a doc
comment calling itself *"the fourth site with this exact arithmetic
(`log.rs`, `binary.rs`, `powsq.rs`), always duplicated because each fuel
family's `…Aux` type differs and there is nothing generic to promote it to."*
That reasoning is wrong: **the arithmetic never depended on any `…Aux` type;
only the wrapper did.** Both halves are now named kernel declarations:

```text
Nat.lt_two_mul_of_pos        : ∀ n, Lt 0 n -> Lt n (mul 2 n)
Nat.half_le_of_succ_le_succ  : ∀ m k, Le (succ m) (succ k) -> Le (div (succ m) 2) k
```

I did **not** edit `rec_agreement.rs` / `log.rs` / `binary.rs` / `powsq.rs` to
consume them (the brief put those files off-limits — four sibling lanes were
live in them). **Follow-up worth taking**: delete the four private copies and
route them here. It is a pure deletion, and it retires a duplication the code
itself had given up on.

## 3. The honesty verdict: a fuel encoding is NOT Mathlib's construction

Read at the pinned commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`,
`Mathlib/Data/Nat/BinaryRec.lean:88` — the actual source, provisioned locally
(`/data0/axeyum/lean-import-toolchain/mathlib4`), not inferred from prose:

```lean
def binaryRec {motive : Nat → Sort u} (zero : motive 0)
    (bit : ∀ b n, motive n → motive (bit b n)) (n : Nat) : motive n :=
  if n0 : n = 0 then congrArg motive n0 ▸ zero
  else
    let x := bit (1 &&& n != 0) (n >>> 1) (binaryRec zero bit (n >>> 1))
    congrArg motive n.bit_testBit_zero_shiftRight_one ▸ x
termination_by if n = 0 then 0 else n.log2.succ
decreasing_by ...
```

| | Mathlib | here |
| --- | --- | --- |
| recursion | **well-founded** on `if n = 0 then 0 else n.log2.succ`, compiled to `WellFounded.fix` | **structural** `Nat.rec` on a fuel counter |
| motive | **dependent**, `{motive : Nat → Sort u}`, universe-polymorphic | **constant**, `α : Type 0` as an explicit argument |
| arity | `zero`, `bit`, `n` | plus an explicit `fuel` |
| recursive equation | definitional (`binaryRec_eq`, modulo one side condition) | a **theorem**, needing fuel-irrelevance first |

**Verdict: a different `def` that agrees pointwise.** By CLAUDE.md's
mirror-flip criterion this is the `Nat.multichoose` / `Nat.minFac` case, not
the `Nat.descFactorial_of_lt` case, and the same verdict the sibling `minFac`
lane reached today.

The non-dependence is **forced, not a shortcut**: a fuel encoding's
fuel-exhaustion row must return a value for an ARBITRARY `n`, and only
`motive 0` is in hand. So there is no version of this construction that is
Mathlib's while remaining a fuel encoding. Closing the gap honestly needs
well-founded recursion over `Nat` — the machinery exists in principle (`Acc`
is declared in the logic prelude, with its recursor) and nothing in this
prelude drives a recursion with it today.

**Consequence for step 3, which the brief anticipated:**
`F:ml430-nat-fastfib-eq-cde11774` stays `open` **whether or not `fastFib` gets
built here**, because our `fastFib` would be built on this recursor. When it
lands it should land as a new local fact, the way
`F:nat-coprime-of-lt-minfac` did for `minFac`. Do not stretch the criterion.

I did **not** modify `F-ml430-nat-fastfib-eq-cde11774.json`; it is correctly
`open` already.

## 4. Where I stopped, and why

**Landed:** the pair type, the recursor, its four defining equations,
fuel-irrelevance, the recursive equation, the halving arithmetic, two evaluation
theorems and one Rust computation test.

**Not attempted:** `Nat.fastFibAux`, `Nat.fastFib`, `Nat.fastFib_eq`. The
brief set (1)+(2) as the expected outcome; (3)'s recursive equation is a bonus.
Saying it plainly: **`fastFib` is unbuilt.**

The remaining work, sized against what now exists rather than guessed:

1. **A binary INDUCTION principle** (`Nat.binaryRecInd : ∀ (P : Nat → Prop),
   P 0 → (∀ n, n ≠ 0 → P (n/2) → P n) → ∀ n, P n`). `binaryRec` is a
   *recursor* into `Type 0`; `fastFibAux_eq` needs to induct, and Mathlib's own
   proof is one `Nat.binaryRec` induction. This IS expressible by fuel
   (`∀ fuel n, Le n fuel → P n`, induction on fuel, using
   `Nat.half_le_of_succ_le_succ` — the same skeleton as
   `binaryRecAux_agree_of_fuel`, and probably ~120 lines by transcription).
   Estimated the cheapest next slice.
2. **`fastFibAux : Nat → Nat.Pair`** via `binaryRec Nat.Pair (mk 0 1) step`,
   and `fastFib n := Nat.Pair.fst (fastFibAux n)`. Now mechanical.
3. **The doubling identities at `Nat`.** `Int.fib_two_mul` and
   `Int.fib_two_mul_add_two` **already exist** (`int_prelude.rs:1201,1207`,
   landed today) — but over `ℤ`, and `fastFib` lives at `ℕ`. `Nat.fib_add`
   exists (`nat_prelude.rs:1842`); per `250`'s handoff it gives Mathlib's
   `fib_two_mul_add_one` at `m := n` by substitution alone. `fib_two_mul` at
   `ℕ` additionally needs `Nat.sub`-truncation care (`2*fib(n+1) ≥ fib n`
   always holds via `fib_le_succ`, so nothing truncates, but the proof must say
   so). **Decide first** whether to transport the two `Int` identities down or
   re-derive at `ℕ`; I did not measure which is cheaper.
4. **The `bit b n` bridge.** `binaryRec_succ` is stated at `succ m` with
   `(succ m) % 2` and `(succ m) / 2`. Mathlib's `binaryRec_eq` is stated at
   `bit b n`. Restating ours in `bit` form needs `bit_div_two : bit b n / 2 = n`
   and `bit_mod_two : bit b n % 2 = b.toNat`, **neither of which exists** —
   `bits.rs` has only `bit_false`, `bit_true`, `bit_true_pos`,
   `bit_false_le_bit_true`. Both follow from `div_mod_unique` against
   `div_mod_exec 1 (bit b n)` plus `b.toNat < 2`; call it ~60 lines. Worth
   doing regardless of `fastFib`: it is what the seven open `natural-bitwise`
   facts (`land_bit`, `lor_bit`, `ldiff_bit`, …) also want.

## Evidence and gates

- New facts: `F:nat-binary-rec-fuel-irrelevance`, `F:nat-binary-rec-succ`
  (the latter `depends_on` the former). Both `proved` / `kernel-lean` /
  `axiom_footprint: []`.
- `python3 scripts/validate-facts.py`: **1931 facts, 0 errors** (was 1929).
- `cargo test -p axeyum-lean-kernel --lib nat_prelude::`: **133 passed, 0
  failed**, including `every_nat_declaration_is_checked_and_axiom_free`
  (environment-derived, so a present-but-unlisted declaration fails it),
  `the_nat_prelude_declares_no_axioms`, and `the_build_is_deterministic`.
- Downstream preludes re-checked, because a new inductive in `nat` is exactly
  the shape that builds fine alone and breaks a consumer (CLAUDE.md's
  `Nat.inverseIndex` incident): `--lib int_prelude::` **49 passed**,
  `--lib rat_prelude::` **103 passed**.
- `nat_axiom_inventory --require-axiom-free nat` → `ok: nat trusted surface = 0`.
- `cargo fmt --all --check` clean; `cargo clippy -p axeyum-lean-kernel
  --all-targets -- -D warnings` clean.
- Determinism pin recomputed by **counting both lists** with a script, never
  hand-incremented: `89 + 463` → `93 + 477` (570 rendered rows).
- NOT run: the aggregate `just check` / `./scripts/check.sh` (per the brief;
  the coordinator re-runs the full gate before merging).

### The evidence whose exit status depends on the finding

The trusted gate admits a `Definition` on its TYPE, so `binaryRecAux`'s
admission says nothing about what it computes. Two `Eq.refl` theorems in the
prelude close only if it actually evaluates:

```text
Nat.binaryRec_rebuilds_thirteen : binaryRec ℕ 0 (fun b _ acc => bit b acc) 13 = 13
Nat.binaryRec_rebuilds_six      : … 6 = 6
```

The round trip is the discriminating workload: rebuilding `n` from its own bits
catches any misplaced bit, swapped guard, or off-by-one in the halving.
**Mutation-verified during construction** — restating `_rebuilds_thirteen` as
`= 11` (that is `0b1101` reversed, so a wrong-order traversal lands exactly
there) makes the prelude build fail with `DeclarationValueMismatch`, declared
`binaryRec … 13` against inferred `11`. Reverted immediately.

`pair_and_binary_rec_compute_with_transposed_negative_controls` repeats that as
a live `!def_eq` control and adds `Nat.Pair`'s. `mk 3 5` is deliberately
ASYMMETRIC, so `fst`/`snd` transposition changes the value — the failure a
commutative operator's numerals cannot expose on their own. Magnitudes are
tiny throughout: these numerals are unary `succ` towers.
