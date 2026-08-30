# Lane: ftc-rung3 — the Fundamental Theorem of Calculus, part I

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, ftc-rung3, 2026-08-27). FTC-I is landed.**
`CReal.hasDerivative_antiderivative : ∀ F a b (hab : le a b)
(u : UniformlyContinuousOn F a b) (kb : Nat), BoundedOn F a b kb →
HasDerivativeOn (antiderivative F a b hab u) F a b` — accepted by
`Kernel::add_declaration` on the **first attempt**, axiom-free, together with
the four lemmas it needed. Six declarations, six first-attempt accepts, and
the kernel rejected **nothing** in this lane.

| declaration | statement |
| --- | --- |
| `CReal.min_mono_left` | `∀ x y b, le x y → le (min x b) (min y b)` |
| `CReal.max_mono_right` | `∀ a u v, le u v → le (max a u) (max a v)` |
| `CReal.clamp_mono` | `∀ a b x y, le x y → le (max a (min x b)) (max a (min y b))` |
| `CReal.clamp_id` | `∀ a b x, le a x → le x b → Equiv (max a (min x b)) x` |
| `CReal.max_sub_min` | `∀ x y, Equiv (add (max x y) (neg (min x y))) (abs (add y (neg x)))` |
| `CReal.integralSplitAnywhere` | `integral_split_arbitrary` with its `PosBound` and `k` removed |
| `CReal.hasDerivative_antiderivative` | FTC-I, above |

**All three named lemmas were genuinely absent**, re-verified against
`creal.rs`'s name registry — the authoritative interning site, since every
`CReal.*` name is a `kernel.name_str(creal, …)` there and grep across
`crates/axeyum-lean-kernel/src/` finds no other. The lattice surface was
exactly the six order laws and three congruences: no monotonicity lemma, no
`max_sub_min`.

**The sizing missed a FOURTH lemma, and it was hiding place 2.** The spec's
error term is `F(x)·(y − x)` in the RAW `x`, `y`, while `G`'s argument is the
clamp, so the clamp must be shown to be the identity on `[a, b]`. That fact
existed as `derivative.rs`'s **private Rust helper**
`clamp_into_equiv_on_interval` — never a declaration, so no proof term could
cite it, and no name search could find it. It is now
`CReal.clamp_id`.

Detail moved to [`../notes/158-ftc-rung3.md`](../notes/158-ftc-rung3.md).

<!-- plan-section: landed-changes -->

| 2026-08-27 | ftc-rung3 | `CReal.hasDerivative_antiderivative` — **FTC-I**, axiom-free, first attempt — with `clamp_mono`, `clamp_id`, `max_sub_min`, `min_mono_left`, `max_mono_right` and `integralSplitAnywhere` (`integral_split_arbitrary` with its `PosBound` removed; `inv_index_irrelevant` was NOT needed) |
