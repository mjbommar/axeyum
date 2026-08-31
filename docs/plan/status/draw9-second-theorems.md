# Lane: draw9-second-theorems

<!-- plan-section: lane-status -->

## Status (2026-08-30) -- DONE for this session

Continued the draw-9 refill (ADR-0830) where `draw9-first-theorems` left
off. Its work was not yet in `origin/main` when this lane started (merged
local `main` into the lane branch to pick it up); frontier at that point was
10 dispatchable. Closed 7, left 3 open.

### Landed (7 facts flipped to proved, all kernel-lean, axiom_footprint: [])

New theorems built this lane:
- `Nat.land_self` (single-variable fuel induction --
  `Nat.land_aux_self_of_fuel`, simpler than `land_comm`/`land_assoc`'s
  double-fuel bridge since `land x x` already ties the value to the fuel
  slot) -> `F:ml430-nat-and-self-06a84ccc`
- `Nat.land_one_is_mod` (no induction: `land_comm` swaps the fuel slot onto
  the literal `1`, so the succ-row's own recursive call lands at literal
  fuel `0` and collapses by `refl`) -> `F:ml430-nat-and-one-is-mod-d861e96b`
- `Nat.land_mod_two_eq_mul` (internal bridge, `even_xor`'s bounded-projection
  technique transplanted to AND) + `Nat.land_mod_two_eq_one` ->
  `F:ml430-nat-and-mod-two-eq-one-3e873792`
- `Nat.land_div_two` (dual of `land_mod_two_eq_mul`: erases the LOW bit via
  `div` instead of the high recursive term via `mod`, then
  `land_aux_agree_of_fuel` fuel-irrelevance bridges the erased recursive
  term to the canonical `land (a/2) (b/2)`) -> `F:ml430-nat-and-div-two-1a2f7c33`
- `Nat.dist_pos_of_ne` (case split via `lt_or_gt_of_ne_local`, `sub`
  positivity from the strict order via `sub_add_cancel` +
  `pos_of_lt_add_left`) -> `F:ml430-nat-dist-pos-of-ne-00f5e22f`
- `Nat.dist_eq_intro` (case split on `le_total`, cancellation algebra;
  the other branch is the same argument with roles swapped, converted back
  via `dist_comm` twice) -> `F:ml430-nat-dist-eq-intro-294b44ad`
- `Nat.dist_triangle_inequality` (`sub_le_dist_sum` composed with
  `le_add_sub_self`, a new general unconditional lemma, plus
  `sub_le_iff_le_add`; two instances bound both `sub n k`/`sub k n`, and
  `Nat.sub` truncation means only one is ever nonzero) ->
  `F:ml430-nat-dist-triangle-inequality-b35e82d3`

All seven have concrete, discriminating evaluation tests and are registered
in `theorem_names` for `every_nat_declaration_is_checked_and_axiom_free`.
`nat_prelude::` sweep: 236 passed, 0 failed (up from 229 at lane start).
`cargo clippy -p axeyum-lean-kernel --lib -- -D warnings`: clean.

Two bugs found and fixed via bisection (not re-reading proof terms by hand):
- `land_one_is_mod`'s succ-branch chain jumped from the `guarded(...)`
  scaffolding straight to the bare value `bit_n`, skipping the
  `zero_add`/`one_mul` simplification the algebra actually needs.
- `sub_le_dist_sum`'s `mono3` step called `add_le_add_right` with arguments
  in the wrong slots (that lemma's signature is `(c, a, b, h : Le a b)`, not
  `(a, b, c, h)`). Found by writing a checkpointed debug-probe copy of the
  function returning `(value, matching_stmt)` at each intermediate, and
  bisecting checkpoint by checkpoint.

Previous lane's sizing of these 7 as needing machinery "of the same order as
`land_comm`/`land_assoc`" did NOT hold for 5 of them (`land_self`,
`land_one_is_mod`, `land_mod_two_eq_mul`/`land_mod_two_eq_one`,
`land_div_two` all closed WITHOUT the double-fuel induction `land_comm`
needed, by finding a route that fixes one operand concrete or projects a
bounded slice) -- checking the sizing before dispatching against it paid off
again, per CLAUDE.md's standing "a handoff's blocked-on-X is a claim about
one route" entry.

### Left open (3)

- `and_or_distrib_left`/`and_or_distrib_right` (`x &&& (y ||| z) = x &&& y
  ||| x &&& z` and its mirror) -- genuinely a full 3-variable, CROSS-operator
  identity (`land` AND `lor` together), not reducible to a single-operand
  fix or a bounded-bit projection the way the 5 above were. No
  `land`/`lor` joint distributivity machinery exists in the tree (checked:
  grepped for `land_lor`/`lor_land`/`and_or_distrib` across
  `nat_prelude/*.rs`, nothing). Sizing this honestly: it needs a joint
  induction relating `landAux`/`lorAux` at a shared fuel, comparable in
  scope to `land_assoc`'s own fuel-irrelevance construction (which needed
  `land_aux_assoc_of_fuel` plus a zero-propagation lemma) but wider, since
  two different operators' guard rows have to agree rather than one
  operator's. Not attempted -- correctly sized as out of this lane's budget,
  as opposed to assumed to be.
- `fermat_primefactors_one_lt` -- genuine number-theory content (prime
  factors of Fermat numbers via multiplicative order mod `p`); out of scope,
  unchanged from the previous lane's assessment.

### Holdout isolation

Before: `held_out=136 files_scanned=1110 settled=0 references=0 PASS`.
After (final): `held_out=136 files_scanned=1110 settled=0 references=0
PASS`. Unchanged -- this lane never touched `artifacts/autogenesis/`.

### Frontier

Start (after merging local `main` to pick up `draw9-first-theorems`): 10
dispatchable. End: 3 dispatchable (7 closed). The frontier script now also
reports `FAIL: G7 queue-below-floor` (3 dispatchable, floor 10) -- that gate
is about refilling the autogenesis nursery queue, out of this lane's scope
(`artifacts/autogenesis/` was not touched), and is not a regression this
lane caused; it fires once the queue shrinks regardless of who shrinks it.
