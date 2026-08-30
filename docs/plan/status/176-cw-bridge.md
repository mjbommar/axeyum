# Lane: cw-bridge — the `close_within` → `CReal.Converges` regularity bridge

<!-- plan-section: lane-status -->

**Status: LANDED, axiom-free, accepted by `Kernel::add_declaration` on the
FIRST attempt (cw-bridge, 2026-08-28).** The bridge
`docs/plan/status/175-pi-r2b.md` named as the last structural gap under π
rung 2 exists and is public:

    CReal.converges_of_abs_diff_le :
      ∀ (f : Nat → CReal) (L : CReal) (K : Nat),
        (∀ n, CReal.le (CReal.abs (CReal.add (f n) (CReal.neg L)))
                       (CReal.ofRat (Rat.natDivSucc K n)))
        → CReal.Converges f L

`crates/axeyum-lean-kernel/src/creal/uniform_convergence.rs`. Read from the
kernel, not from source text: `shape_search --include-constructed --name
CReal.converges_of_abs_diff_le` gives `theorem arity=4 CReal -> CReal -> Nat
-> CReal.le -> CReal.Converges`, `consts=[CReal, CReal.Converges, CReal.abs,
CReal.add, CReal.le, CReal.neg, CReal.ofRat, Nat, Rat.natDivSucc]`, and
`prelude_theorem_inventory --include-constructed --release` prints
`creal  CReal.converges_of_abs_diff_le  0` — zero axioms.

## Was it genuinely absent? Yes — but the HARD half was not

Verified before building, not assumed. `shape_search --concl
CReal.Converges` returned 13 rows and not one takes a `CReal.le`-of-`abs`
hypothesis (`converges_of_close` and `converges_of_scaled_cauchy` both start
from a `Within`; `converges_of_equiv` wants exact `Equiv`;
`converges_squeeze` wants two existing `Converges`). `--name-like
close_within` returned exactly `close_within_of_within` and
`close_within_of_within_indexed`, both concluding `CReal.le` — the OTHER
direction. Grepped `within_of_two_sided_le`'s consumers and every
`close_within` site in `creal/` for an inline instance (hiding place 2); the
one that exists is `creal/ivt.rs`, and it is the Cauchy analogue, not this.

**But 175-pi-r2b's sizing — "a THIRD general bridge, comparable in size to
`converges_add`'s own construction … relating a real's sample at `n` to its
sample at `shift n`" — over-stated the work, and the reason is worth
recording because it is hiding place 1 again.** The `CReal.add` index-shift
regularity bridge ALREADY EXISTS as a general, public lemma:

Detail moved to [`../notes/176-cw-bridge.md`](../notes/176-cw-bridge.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | cw-bridge | `CReal.converges_of_abs_diff_le` — `close_within` evidence → `Converges`, axiom-free, first-attempt accept |
| 2026-08-28 | cw-bridge | the shift bridge it was sized to need already existed: `CReal.sharedIndexToCanonical` (`integral.rs`) + `cauchy_of_abs_diff_le` (`ivt.rs`) |
