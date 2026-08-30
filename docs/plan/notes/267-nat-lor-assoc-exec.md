# Notes: 267-nat-lor-assoc-exec

Detail moved out of [`../status/267-nat-lor-assoc-exec.md`](../status/267-nat-lor-assoc-exec.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

1. **`lor_bit_lt_two`** (private helper, no separate kernel declaration) --
   `Lt (bool_select_nat cond bit_b bit_a) 2` from `Lt bit_a 2`/`Lt bit_b 2`,
   via direct `Bool.rec` (same recursor `bool_select_nat_same` uses).
   Needed because `land`'s bound derivation (`bit_product_le_left` +
   `lt_of_le_of_lt`) is `mul`-specific; for `lor`'s `max`, the bound is
   direct since the selected value is EITHER `bit_a` or `bit_b`, both
   already `< 2` via `mod_lt`.
2. **`lor_bit_assoc`** (private helper, no separate kernel declaration) --
   `Eq (max (max bit_a bit_b) bit_c) (max bit_a (max bit_b bit_c))`, three
   nested `cases_mod_two` (`a`, `b`, `c`), 8 leaves, each `d.refl` -- exactly
   as specced, transcribed one nesting level past `lor_bit_comm`.
3. **`declare_lor_aux_assoc_hard_leaf`** (private, mirrors
   `declare_land_aux_assoc_hard_leaf`) -- the `a,b,c` all-positive leaf.
   `X`/`Y`'s zero branches now close via direct `absurd` from
   `lor_aux_ne_zero_of_right_ne_zero` (5-line closures, no propagation-lemma
   mirroring needed) rather than `land`'s mirrored
   `land_aux_eq_zero_of_left_eq_zero` argument. The fully-generic
   `X=succ p, Y=succ q` sub-case is a near-verbatim transplant of `land`'s
   analogous leaf, with `lor_aux`/`bit_or`/`lor_bit_assoc` substituted for
   `land_aux`/`mul`/`mul_assoc`.
4. **`declare_lor_aux_assoc_of_fuel`** (`Nat.lor_aux_assoc_of_fuel`) --
   base case and leaves 1-3 held EXACTLY as traced: base is one `d.refl`
   (both sides defeq `c` directly, no case split at all); leaf 1 and leaf 2
   are one `d.refl` each (pure computation plus defeq congruence through a
   reduced subterm -- e.g. leaf 1's RHS `lorAux sk a (lorAux sk b 0)` never
   itself reduces past its outer application for symbolic `b`, but the
   kernel's argument-wise defeq comparison recognizes the THIRD argument
   `lorAux sk b 0` as defeq `b`, which is what makes the plain `refl` work);
   leaf 3 needs exactly the one `lor_aux_zero_left_any_fuel` call the trace
   named, nothing more.
5. **`add_add_add_comm`** -- per-file private copy of the standing
   `(a+b)+(c+d) = (a+c)+(b+d)` four-term rearrangement (this prelude has no
   shared `add_add_add_comm`; see `nat_prelude::binomial`'s own copy, same
   convention).
6. **`lor_bit_le_sum`** (private helper) -- `Le (max bit_m bit_n) (add bit_m
   bit_n)`, one `cases_mod_two` per operand, 4 leaves, `Nat.le_refl` at
   `(0,0)`/`(0,1)`/`(1,0)` and `Nat.le_add_right(1,1)` at `(1,1)`.
7. **`declare_lor_aux_le_add`** (`Nat.lor_aux_le_add`) -- held exactly as
   sketched: base case and the `n=0`/`m=0` step rows via `le_add_right` +
   an `add_comm`/`zero_add`/`add_zero` transport (same pattern
   `land_assoc`'s own `Le b F` derivation uses); the both-positive row
   combines the IH with `lor_bit_le_sum` via
   `mul_le_mul_left`/`left_distrib`/`add_le_add_left`/`add_le_add_right`/
   `le_trans`, then rearranges `(2h_m+2h_n)+(bit_m+bit_n)` to
   `succ_m+succ_n` via `add_add_add_comm` plus the two `div_mod_exec`
   decompositions -- the ONE piece the trace flagged as unverified in
   Python beyond the top-level claim, and it held with no correction
   needed.
8. **`declare_lor_assoc`** (`Nat.lor_assoc`) -- `land_assoc`'s exact
   bookkeeping shape, one argument wider than `lor_comm`, EXCEPT the bound
   `Le (lor a b) F` (`F := add a b`) comes directly from `lor_aux_le_add` at
   `(a,a,b)` with no `le_trans` needed (`land_assoc` needs one, via
   `land_le_left`) -- confirmed exactly as the trace predicted.

## The one bug found, and how

Found during self-review (a manual re-check of the assembled term against
the intended nesting), BEFORE the first `cargo build`, not via a kernel
rejection: a first draft of `y_succ_case`'s closing (inside
`declare_lor_aux_assoc_hard_leaf`) had copy-pasted `land`'s closing shape
verbatim and left it closing over the OUTER `X`-dichotomy's binders
(`hxp_fv`/`hxp_ty`/`p_fv`/`x_succ_predicate`/`hx`/`hx_fv`/
`x_succ_exists_ty`) instead of its own `Y`-dichotomy binders
(`heq_fv`/`heq_ty`/`q_fv`/`y_succ_predicate`/`hy`/`hy_fv`/
`y_succ_exists_ty`). The mechanism: `land`'s original nests `Y` outer /
`X` inner, and this lane's version nests `X` outer / `Y` inner (to match
the order `not_x_zero`/`not_y_zero` are derived in) -- transplanting the
closing boilerplate without swapping which binder set belongs to which
level is exactly the trap. Fixed before the first compile; the kernel
accepted the corrected term, `cargo check -p axeyum-lean-kernel` and the
full `nat_prelude::` sweep both passed on the FIRST run after the fix.

## Verification run

`cargo check -p axeyum-lean-kernel`: clean, no warnings.

`cargo test -p axeyum-lean-kernel --lib nat_prelude::` (RUST_MIN_STACK
unset, confirmed via `env -u`): **153 passed, 0 failed** (was 152 before
this lane's merge base; +1 new test,
`lor_assoc_applies_at_a_nonzero_concrete_instance`), including
`the_build_is_deterministic` at the recomputed pin `93 + 508` (was
`93 + 505`; +3 new theorems: `lor_aux_assoc_of_fuel`, `lor_aux_le_add`,
`lor_assoc` -- taken from the panic's own count on the first run, not
hand-incremented) and `every_nat_declaration_is_checked_and_axiom_free`.

`cargo fmt --edition 2024` on all three touched files, then
`cargo fmt --check -p axeyum-lean-kernel`: clean.

`cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`: clean,
no warnings.

`python3 scripts/check-test-attribute-integrity.py`: `1513 files, 9082
#[test] attributes, 0 finding(s)`, exit 0 (checked directly, not through a
pipeline, per the banned-shell-idiom rule about `$?` after a pipe).

`python3 scripts/validate-facts.py`: `1944 facts checked, 0 errors`.

Both fact-ledger checker commands re-run directly:
- `nat_theorem_inventory -- lor_assoc | grep -Ec '^Nat\.lor_assoc[[:space:]]'`
  -> `1` (anchored, `/usr/bin/grep` explicitly, not the interactive
  `ugrep` shell function).
- `nat_axiom_inventory --require-axiom-free nat` -> `nat: axiom=0 opaque=0
  quotient=0 total_trusted=0`, `ok: nat trusted surface = 0`, exit 0.

NOT run: the aggregate `just check` / `./scripts/check.sh` (coordinator
re-verifies before merging, per this repo's standing rule), and no
workspace-wide gate.

## Ledger changes

- `artifacts/facts/F-nat-lor-assoc.json` (new) -- native theorem,
  `epistemic_status: proved`, `proof_route: kernel-lean`,
  `axiom_footprint: []`, three evidence rows (kernel admission, concrete
  nonzero-intermediate compute check, axiom-footprint inventory), modeled
  directly on `F-nat-land-assoc.json`.
- `artifacts/facts/F-ml430-nat-lor-assoc-82c4d0fd.json` -- flipped
  `open` -> `proved`, `proof_route: kernel-lean`, `axiom_footprint: []`,
  one `reconciliation-Nat.lor_assoc` evidence row pointing at
  `F:nat-lor-assoc`, modeled on `F-ml430-nat-land-assoc-ad4775b8.json`.
  `depends_on` unchanged (`F:ml430-nat-lor-bit-a2f98c7c`, still `open` --
  curriculum lineage, not this proof's actual dependency, exactly as
  `land_assoc`'s mirror records).

`scripts/gen-autogenesis-bitwise-family-projection.py` does not mention
either fact id or `Nat.lor_assoc` -- confirmed NOT pinned open independent
of provability, as the tracing lane reported.

## Counts

`nat_prelude`: 152 passed before this lane (per the trace doc's own
count), **153 passed after** (1 new test). `the_build_is_deterministic`'s
pin: `93+505 -> 93+508` (3 new theorems, all confirmed via the panic's own
mismatch on the first failing run, then re-verified green). `nat` trusted
surface: `axiom=0 opaque=0 quotient=0 total_trusted=0`, unchanged.
`python3 scripts/validate-facts.py`: `1939 -> 1944` facts (this lane's
merge base already carried 4 new facts from the merged `xor`/`bit_order`
work; +1 new fact this lane, `F:nat-lor-assoc`), 0 errors both before and
after.

## Commits

- `4508852a5` -- wip: nat-lor-assoc-exec checkpoint (first-ten-tool-calls
  commit, no source changes)
- `6a6e7cd1a` -- wip: `lor_bit_assoc`/`lor_aux_assoc_of_fuel`/
  `lor_aux_le_add`/`lor_assoc` built, not yet compiled/kernel-verified
- `5c345b124` -- feat: close `F:ml430-nat-lor-assoc-82c4d0fd` via native
  `Nat.lor_assoc` (fact ledger only; the kernel-side change had already
  compiled and passed the full `nat_prelude::` sweep by this commit)

`F:ml430-nat-lor-assoc-82c4d0fd` is now `proved`. `F:nat-lor-assoc` is
`proved`, `kernel-lean`, axiom-free.
