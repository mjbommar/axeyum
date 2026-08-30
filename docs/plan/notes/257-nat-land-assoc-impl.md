# Notes: 257-nat-land-assoc-impl

Detail moved out of [`../status/257-nat-land-assoc-impl.md`](../status/257-nat-land-assoc-impl.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- 3 of 4 base leaves (`a=0`; `a=succ,b=0`; `a=succ,b=succ,c=0`) close
  exactly as traced: `a=0` and `a=succ,b=0` each need ONE call to the
  already-existing `land_aux_zero_left_any_fuel` (the inner `landAux _ 0
  n` for symbolic `n`); `a=succ,b=succ,c=0` closes by **pure `d.refl`
  retyping**, no lemma at all, because `landAux`'s OUTER guard checks its
  SECOND argument first and `c=0` is literal there.
- The hard leaf (`a,b,c` all `succ`) needed exactly the arithmetic chain
  `252` traced: `add_eq_zero` → `mul_eq_zero` + `succ_ne_zero` (eliminate
  the `2=0` disjunct) → `rec_ab=0 ∧ bit_ab=0`; `zero_or_succ` on the inner
  `landAux fuel b c` (`Y`); in the `Y=succ q` branch, `div_mod_exec` +
  `div_mod_unique` reconstruct `div(succ q,2)`/`mod(succ q,2)` back to
  `Y`'s own `rec_bc`/`bit_bc`, which feeds `rec_ab=0` into the outer
  induction's own `ih` at `(half_a,half_b,half_c)` and `bit_ab=0` into
  `mul_assoc` -- **exactly the chain `252` specified, with no missing
  lemma and no new one needed.**
- The one place `252`'s prose was imprecise rather than wrong: it says
  the top-level structure is a 3-leaf tree "not a 2×2 grid" without
  spelling out that the `X=0` sub-case's proof does not need the `Y=succ
  q` witness `q` at all (it is available in scope from the outer
  `exists_elim` but simply unused) -- a detail that only matters for
  writing the Rust (the arrow-typed hypothesis at that leaf is `Arrow(Eq X
  0, …)`, and the exists-witness binder is still there, just dead).

**Two build errors in my own first pass, fixed before this was tested,
recorded because they are the two generic Rust traps this repository's
CLAUDE.md already names:** a missing `use crate::BinderInfo;` (needed for
my own private `or_elim`/`absurd`/`exists_elim` copies, per the existing
per-file convention), and one `d.add(d.mul(two, rec_bc), bit_bc)` --
`E0499`, the exact "cannot find type" -> "double mutable borrow" shape
CLAUDE.md's Hard Rules/Gotchas sections do not name explicitly but which
is the same family as the documented `d.kernel().const_(d.prelude()...)`
hazard: never nest two calls that each need `&mut d` in one expression.
Fixed by hoisting the inner call to a `let`.

Registered in `theorem_names` (coverage is environment-derived, so an
unregistered live declaration fails `every_nat_declaration_is_checked_and_
axiom_free` loudly). `the_build_is_deterministic`'s pin moved `89+465 →
89+466`, confirmed by the test itself passing (not hand-derived and
trusted blind).

**Test**: `land_aux_eq_zero_of_left_eq_zero_applies_at_a_mixed_concrete_
instance` -- symbolic restatement at fully free `fuel`/`a`/`b`/`c`, plus
`252`'s own non-vacuous Python-cross-checked witness `(fuel=2, a=1, b=2,
c=2)`: `land 1 2 = 0` (hypothesis genuinely true, not vacuous) while
`land 2 2 = 2` is genuinely **nonzero** -- the "mixed" case `252` measured
at 108/343 triples, not a corner where the whole statement degenerates to
`0 = 0`. Both directions asserted (`ab` defeq `0`, `bc` NOT defeq `0`).

**135 of 135 `nat_prelude::` tests pass** (was 134 before this lane).
`cargo fmt --edition 2024` on the three touched files and `cargo clippy -p
axeyum-lean-kernel --all-targets -- -D warnings` both clean.
`python3 scripts/validate-facts.py`: 1929 facts, 0 errors (unaffected --
no fact file touched, `F:ml430-nat-land-assoc-ad4775b8` and
`F:ml430-nat-lor-assoc-82c4d0fd` both remain `open` exactly as found).
Confirmed neither fact is pinned open independent of provability
(`grep -rln` for both fact ids across `scripts/` returns nothing).

## The propagation lemma's exact statement, as built

```
Nat.land_aux_eq_zero_of_left_eq_zero :
  ∀ (fuel a b c : Nat),
    Eq Nat (Nat.landAux fuel a b) Nat.zero →
    Eq Nat (Nat.landAux fuel a (Nat.landAux fuel b c)) Nat.zero
```

No `Le` hypothesis on `fuel` -- it holds at ANY fuel, including
insufficient fuel, because `landAux`'s fuel-exhaustion row is the
absorbing constant `0` and the whole inductive argument never needed a
sufficiency bound (verified concretely: it is what makes `fuel=0` -- the
degenerate case -- close by pure `refl`).

## `land_aux_assoc_of_fuel`: a complete, implementation-ready derivation

**Not built this lane** (budget), but every leaf below was hand-traced
against the ACTUAL helper signatures and the ACTUAL guard argument order
in `land.rs`/`rec_agreement.rs::guarded` (which `252`'s plan did not
cross-check this precisely -- see the correction below), so this should
transcribe into Rust with no further mathematical discovery needed.

**Statement:**
```
land_aux_assoc_of_fuel : ∀ fuel a b c,
  Eq (landAux fuel (landAux fuel a b) c) (landAux fuel a (landAux fuel b c))
```
via `agree_by_double_fuel_induction` again (fuel, a, b, c), no hypothesis
this time (a plain `Eq`, not an arrow).

**Base case (`fuel=0`):** both sides defeq `0` (the zero-fuel row is
constant regardless of the argument), and LHS is actually **defeq to
RHS directly** (both fully reduce to `Nat.zero`), so the base closure is
one line: `d.refl(LHS)` retyped as `Eq LHS RHS`. No `trans`/`symm`
plumbing needed, simpler than the propagation lemma's base case.

**CORRECTION TO `252`'s LEAF ORDER, verified against `guarded`'s actual
guard slots (`land.rs`: the SECOND positional argument, "n", is checked
OUTERMOST):** `252`'s prose says "case-split on `(a,b,c)` in that order,"
but its own four enumerated leaves are unambiguously split **`c` first,
then `b`, then `a`** -- write `X := landAux (succ k) a b`, `Y := landAux
(succ k) b c` (as `252` does); `X`'s own `n`-slot is `b`, `Y`'s own
`n`-slot is `c`, and the OUTER application `landAux (succ k) X c` has `c`
in its `n`-slot while `landAux (succ k) a Y` has `Y` in its `n`-slot. So
splitting `c` first is what makes the OUTER LHS resolve directly, and
what (via a second reduction) makes `Y` collapse to `0` for free without
touching `b`. The propagation lemma split `a,b,c` in `a,b,c` order for a
DIFFERENT reason (its own statement's outer application has `a` in the
`m`-slot, and its hypothesis is ABOUT `a,b` specifically) -- the two
lemmas are not the same shape and should not use the same split order.
**Use `cases_zero_succ` nested `c`, then `b`, then `a`.**

- **Leaf 1 (`c=0`, `a,b` untouched):** `landAux (succ k) X 0` is defeq `0`
  regardless of `X` (`n=0` literal, outer check alone resolves). `Y =
  landAux (succ k) b 0` is defeq `0` regardless of `b`, same reason; then
  `landAux (succ k) a Y` transports to `landAux (succ k) a 0`, defeq `0`
  regardless of `a`. **Zero lemmas, zero further case-splits** -- matches
  `252` exactly.
- **Leaf 2 (`c=succ c'`, `b=0`, `a` untouched):** `Y = landAux (succ k) 0
  (succ c')` -- `m=0` literal, `n=succ c'` literal nonzero: outer check
  resolves "proceed" (iota on two literal constructors), inner check
  resolves `m=0` true, giving `Y` defeq `0` by **two iota steps, no
  lemma** (this is SHARPER than `252`'s own prose, which did not verify
  this leaf could skip `land_aux_zero_left_any_fuel` entirely -- it can,
  because `b=0` is literal here, unlike the propagation lemma's own
  leaf 2 where the symmetric position was symbolic). `X = landAux (succ
  k) a 0` (`b=0` literal) is ALSO defeq `0` regardless of `a`, same
  one-step reason as leaf 1. Transport both zeros through and finish.
  **Zero lemmas.**
- **Leaf 3 (`c=succ c'`, `b=succ b'`, `a=0`):** `X = landAux (succ k) 0
  (succ b')` is defeq `0` by the same two-iota-step argument as leaf 2's
  `Y` (`m=0` literal, `n=succ b'` literal nonzero). Transport into `landAux
  (succ k) X (succ c')` gives `landAux (succ k) 0 (succ c')`, defeq `0` by
  the identical two-step argument (`succ c'` was ALREADY literal from the
  outer split). `Y = landAux (succ k) (succ b') (succ c')` is now a
  genuine stuck compound (do not evaluate it) -- but the RHS is `landAux
  (succ k) 0 Y` (`a=0` literal), whose OUTER check is on `Y` (NOT
  literal, stuck), so THIS one needs `land_aux_zero_left_any_fuel (succ
  k) Y`, which holds for ANY `n` including a stuck one. **One lemma call,
  exactly matching `252`'s "the existing `land_aux_zero_left_any_fuel`
  alone suffices."**
- **Leaf 4 (`c=succ c'`, `b=succ b'`, `a=succ a'`) -- the hard leaf.**
  Write `succ_a, succ_b, succ_c` for the three (now literal) candidates,
  `sk := succ k`. Define exactly as in the propagation lemma's hard leaf:
  `half_a/half_b/half_c := div(succ_a/b/c, 2)`, `bit_a/b/c := mod(succ_a/b/c,
  2)`, `rec_ab := landAux k half_a half_b`, `bit_ab := mul(bit_a,bit_b)`,
  `rec_bc := landAux k half_b half_c`, `bit_bc := mul(bit_b,bit_c)`. Then
  `X := landAux sk succ_a succ_b` is defeq `2*rec_ab+bit_ab`; `Y := landAux
  sk succ_b succ_c` is defeq `2*rec_bc+bit_bc` (both via `guarded`, both
  guards resolve `false`, all three operands literal `succ`).

  **Dichotomize `Y` via `zero_or_succ`:**

  - **`Y=0`:** mirror the propagation lemma via `land_aux_comm_of_fuel`,
    exactly as `252` describes for the top-level assoc proof's own
    `Y=0` case (this is the SAME mirroring trick, now instantiated at the
    concrete literal-succ triple):
    ```
    comm_bc   := land_aux_comm_of_fuel(sk, succ_b, succ_c)      : Eq Y (landAux sk succ_c succ_b)
    hyp_cb    := trans(landAux sk succ_c succ_b, Y, 0, symm(comm_bc), hyp_Y_zero)
    prop_cba  := land_aux_eq_zero_of_left_eq_zero(sk, succ_c, succ_b, succ_a, hyp_cb)
                 : Eq (landAux sk succ_c (landAux sk succ_b succ_a)) 0
    comm_ab   := land_aux_comm_of_fuel(sk, succ_a, succ_b)      : Eq X (landAux sk succ_b succ_a)
    comm_Xc   := land_aux_comm_of_fuel(sk, X, succ_c)           : Eq (landAux sk X succ_c) (landAux sk succ_c X)
    cong_X    := congr(X, landAux sk succ_b succ_a, comm_ab, |z| landAux sk succ_c z)
    LHS_zero  := trans/trans chain: landAux sk X succ_c -> landAux sk succ_c X
                 -> landAux sk succ_c (landAux sk succ_b succ_a) -> 0
    ```
    RHS: transport `Y→0` into `landAux sk succ_a Y`, giving `landAux sk
    succ_a 0`, defeq `0` regardless of `succ_a` (literal `n=0` after
    transport). Combine `LHS_zero`/`RHS_zero` via `trans`+`symm`.

  - **`Y=succ q`** (via `exists_elim`, witness `q`, `heq : Eq Y (succ
    q)`): **dichotomize `X` via `zero_or_succ`:**

    - **`X=0`:** `landAux sk X succ_c` transports to `landAux sk 0
      succ_c`, defeq `0` by a PURE two-iota-step reduction (both `m=0`
      and `n=succ_c` are now literal -- NO lemma needed here, sharper
      than the propagation lemma's own analogous branch, because there
      `n` was still symbolic; here it is literal from the outer split).
      RHS: `landAux sk succ_a Y` with hypothesis `X = landAux sk succ_a
      succ_b = 0` is **exactly** `land_aux_eq_zero_of_left_eq_zero(sk,
      succ_a, succ_b, succ_c, hx)`, whose conclusion IS `Eq (landAux sk
      succ_a Y) 0` verbatim (`Y` already denotes `landAux sk succ_b
      succ_c`, no substitution needed). `heq`/`q` unused, exactly as
      `252` notes.

    - **`X=succ p`** (via a second `exists_elim`, witness `p`, `hxp : Eq
      X (succ p)`) -- **the one truly generic leaf, needing reconstruction
      on BOTH sides:**
      ```
      cong_L := congr(X, succ_p, hxp, |z| landAux sk z succ_c)
                : Eq (landAux sk X succ_c) (landAux sk succ_p succ_c)
      cong_R := congr(Y, succ_q, heq, |z| landAux sk succ_a z)
                : Eq (landAux sk succ_a Y) (landAux sk succ_a succ_q)
      ```
      `landAux sk succ_p succ_c` now reduces via `guarded` (both literal
      succ) to `2*rec_Xc+bit_Xc` with `rec_Xc := landAux k (div succ_p 2)
      half_c`, `bit_Xc := mul (mod succ_p 2) bit_c`. Symmetrically
      `landAux sk succ_a succ_q` reduces to `2*rec_aY+bit_aY` with
      `rec_aY := landAux k half_a (div succ_q 2)`, `bit_aY := mul bit_a
      (mod succ_q 2)`.

      Reconstruct `div(succ_p,2)`/`mod(succ_p,2)` from `X`'s OWN
      decomposition, via `div_mod_unique`+`div_mod_exec` **exactly the
      pattern already built and tested in the propagation lemma's `Y=succ
      q` branch** (`candidate_divmod` from `hxp` retyped against `X`'s
      `2*rec_ab+bit_ab` unfolding, `bit_ab_lt_2` via
      `bit_product_le_left`+`mod_lt`+`lt_of_le_of_lt`, `exec_divmod` via
      `div_mod_exec(1, succ_p)`, `div_mod_unique` combining them) to get
      `half_p_eq : Eq (div succ_p 2) rec_ab` and `bit_p_eq : Eq (mod
      succ_p 2) bit_ab`. **Do the identical thing for `succ_q`** (this is
      the code already written for the propagation lemma's `Y=succ q`
      branch, reusable close to verbatim) to get `half_q_eq : Eq (div
      succ_q 2) rec_bc` and `bit_q_eq : Eq (mod succ_q 2) bit_bc`.

      Now the closing argument is clean and needs **no new lemma**:
      ```
      rec_Xc -[congr half_p_eq]-> landAux k rec_ab half_c
             -[ih at (half_a,half_b,half_c)]-> landAux k half_a rec_bc
             -[symm(congr half_q_eq)]-> rec_aY
      ```
      because `landAux k rec_ab half_c` IS `landAux k (landAux k half_a
      half_b) half_c` **syntactically** (that is what `rec_ab` denotes),
      matching `ih`'s own LHS shape at `(half_a,half_b,half_c)` exactly,
      and `landAux k half_a rec_bc` IS `landAux k half_a (landAux k
      half_b half_c)` matching `ih`'s RHS exactly. **This is `ih` applied
      at the halves, nothing more** -- the same "self-referential"
      technique `252` names for the propagation lemma's own hard leaf,
      now closing the OUTER induction instead.
      ```
      bit_Xc -[congr bit_p_eq]-> mul bit_ab bit_c
             -[mul_assoc(bit_a,bit_b,bit_c)]-> mul bit_a bit_bc   (LITERAL match, no massaging)
             -[symm(congr bit_q_eq)]-> bit_aY
      ```
      because `mul_assoc`'s stated LHS `mul (mul bit_a bit_b) bit_c` IS
      `mul bit_ab bit_c` literally (`bit_ab := mul bit_a bit_b`), and its
      RHS `mul bit_a (mul bit_b bit_c)` IS `mul bit_a bit_bc` literally.
      Finish with two `congr`+`trans` steps combining `rec_Xc_eq_rec_aY`
      and `bit_Xc_eq_bit_aY` into `Eq (landAux sk succ_p succ_c) (landAux
      sk succ_a succ_q)`, then chain through `cong_L`/`symm(cong_R)` to
      the actual goal `Eq (landAux sk X succ_c) (landAux sk succ_a Y)`.

  **No new arithmetic lemma is needed anywhere in this leaf** beyond what
  the propagation lemma already used (`div_mod_unique`, `div_mod_exec`,
  `mul_assoc`, `bit_product_le_left`, `mod_lt`, `lt_of_le_of_lt`) plus
  `land_aux_comm_of_fuel` (already in the tree) for the `Y=0` mirror.
  Budget this leaf at roughly DOUBLE the propagation lemma's hard leaf
  (two reconstructions instead of one), the rest of the theorem (leaves
  1-3, the `Y=0`/`X=0` sub-cases) at roughly the same size as the
  propagation lemma's easy leaves combined.

## `land_assoc` from `land_aux_assoc_of_fuel`: the fuel bookkeeping

Not derived to the same depth (no reason to -- it is mechanical, `land_
comm`'s own pattern one argument wider), but the shape is:

Pick a common fuel `F` sufficient for `a`, `b`, `c`, AND for `land a b`'s
own canonical fuel (`land a b ≤ a` via `land_le_left`, so `F ≥ a` already
suffices via `le_trans`). `F := a + b + c` works (or `a + (b + c)`,
whichever makes the `Le` derivations cleanest with `le_add_right`/
`add_comm`/`add_assoc`, exactly `land_comm`'s own `m + n` bookkeeping one
slot wider). Then:

1. `land_aux_agree_of_fuel(F,a,b,a) : Eq(landAux F a b)(land a b)` (needs
   `Le a F`, `Le a a` via `le_refl`).
2. `land_aux_agree_of_fuel(F,b,c,b) : Eq(landAux F b c)(land b c)` (needs
   `Le b F`, `Le b b`).
3. `land_aux_assoc_of_fuel(F,a,b,c) : Eq(landAux F (landAux F a b) c)
   (landAux F a (landAux F b c))`.
4. Congr step 1 into step 3's LHS-inner and step 2 into step 3's
   RHS-inner, giving `Eq(landAux F (land a b) c)(landAux F a (land b c))`.
5. `land_aux_agree_of_fuel(F, land a b, c, land a b) : Eq(landAux F (land
   a b) c)(land (land a b) c)` -- needs `Le (land a b) F`, obtained via
   `land_le_left` (`Le (land a b) a`) + `le_trans` with `Le a F`, and `Le
   (land a b) (land a b)` via `le_refl`.
6. `land_aux_agree_of_fuel(F, a, land b c, a) : Eq(landAux F a (land b
   c))(land a (land b c))` -- needs `Le a F` (already have) and `Le a a`.
7. Chain 4-6 to close `Eq(land (land a b) c)(land a (land b c))`, the
   `land_assoc` statement.

This is the exact same shape `land_comm` already executes (see
`rec_agreement.rs`'s `declare_land_comm`), widened from two `Le`
derivations to four. No new machinery.

## `lor_assoc`: still not attempted, still not a mechanical transport

Unchanged from `252`'s own warning, restated because it is still true and
still worth not re-deriving carelessly: `lorAux`'s fuel-exhaustion row is
pass-through (`n`, not `0`), so `lor a b = 0 → a=0 ∧ b=0` (OR's only
zero), and `lor a (lor b c)` when `lor a b = 0` is `lor 0 c = c`, **not
`0`** in general. The whole leaf-4 strategy above (dichotomize on
zero-ness, reconstruct via `div_mod_unique`) does not transport, because
`lor`'s interesting/absorbing values are different. **Simulate the `lor`
recursion in Python at small arguments before writing any Rust for it**,
per this repository's own standing rule.

## Counts

`nat_prelude`: 134 passed before this lane, **135 passed after** (1 new
declaration, a theorem; 1 new test). `the_build_is_deterministic`'s pin:
`89+465 → 89+466`. `nat` trusted surface still `axiom=0 opaque=0
quotient=0` (the new theorem's `axiom_footprint` is asserted empty in its
test). `cargo fmt --edition 2024 --check`-equivalent (via direct
`rustfmt --edition 2024` on the touched files) clean. `cargo clippy -p
axeyum-lean-kernel --all-targets -- -D warnings`: clean. `python3
scripts/validate-facts.py`: 1929 facts, 0 errors (neither target fact
touched; both remain `open`). NOT run: the aggregate `just check` /
`./scripts/check.sh` (coordinator re-verifies before merging, per this
repo's standing rule).

Neither `F:ml430-nat-land-assoc-ad4775b8` nor
`F:ml430-nat-lor-assoc-82c4d0fd` was touched (both remain `open`, exactly
as found).

## Commits

- `36b7d4f0c` -- wip: field/name plumbing + the whole propagation-lemma
  proof, landed before compiling (first-ten-tool-calls commit)
- `a397e7a67` -- feat: fixes the two build errors, adds the theorem_names
  registration + pin bump + the concrete/symbolic test; 135/135
  `nat_prelude::` tests pass
