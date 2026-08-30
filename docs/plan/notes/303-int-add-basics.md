# Notes: 303-int-add-basics

Detail moved out of [`../status/303-int-add-basics.md`](../status/303-int-add-basics.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

| theorem | proof shape |
| --- | --- |
| `add_left_neg : -a + a = 0` | `add_comm` + `add_neg`, one `itrans` |
| `add_neg_eq_sub : a + -b = a - b` | `Eq.refl` — `Int.sub` is `sub.rs`'s plain non-recursive `Definition (fun a b => add a (neg b))`, so the declared type's RHS unfolds to the LHS by defeq alone |
| `add_left_comm : a+(b+c) = b+(a+c)` | `add_assoc` twice + `add_comm` once (congruence on the shared `+c`) |
| `add_mul : (a+b)*c = a*c+b*c` | `mul_comm` (thrice) + `left_distrib` once — this kernel only has LEFT distributivity, so right-distributivity is entirely a `mul_comm` rotation |
| `add_neg_cancel_left : a+(-a+b) = b` | mirror-image of `modeq.rs`'s private `cancel_neg_add_left(c,x) : Eq(neg_c+(c+x), x)` — could NOT reuse that helper directly, because here the OUTER term is the positive `a` and the inner negation is `neg a` (the helper would need `neg(neg a)`, not `a`, on the outside); wrote a new function with the assoc/neg/comm/zero steps in the mirrored order |
| `add_left_cancel : a+b=a+c -> b=c` | DOES reuse `modeq.rs`'s `cancel_neg_add_left(a,b)`/`cancel_neg_add_left(a,c)` (each `Eq(neg_a+(a+x), x)`), bridged by congruence on the hypothesis |
| `add_left_inj : i+k=j+k <-> i=j` | `mpr` is congruence on `i=j`; `mp` rotates both sides through `add_comm` (`i+k=j+k -> k+i=k+j`) and closes with `add_left_cancel` — so `add_left_cancel` had to be declared BEFORE `add_left_inj` in dispatch order (it references `p.add_left_cancel` inside its proof term) |

No `Int.rec` case split anywhere in the new file — every proof is pure
algebra on top of already-derived laws (`add_comm`, `add_assoc`, `add_zero`,
`add_neg`, `mul_comm`, `left_distrib` from `algebra.rs`; `Int.sub`'s
definition from `sub.rs`; `cancel_neg_add_left` from `modeq.rs`, already
`pub(super)` for `order_add.rs`'s prior reuse).

Dispatched in `build_int_prelude_uncached` right after
`sub::declare_mul_sub` (so `Int.sub` exists in the environment for
`add_neg_eq_sub` — referencing an undeclared constant gives `UnknownConst`,
which `cargo check` cannot see) and before `order::declare_difference_lemmas`.

`derived_laws`'s pin recounted `180 -> 187` via
`scripts/recount-pinned-inventory.py` (never hand-incremented).

## Fact ledger

All nine facts flipped `open -> proved`, `proof_route: kernel-lean`,
`axiom_footprint: []`. Each carries three evidence rows (kernel type match
via `int_theorem_inventory`, empty footprint via
`derived_laws_have_no_axiom_footprint` + `nat_axiom_inventory
--require-axiom-free integer`, environment-derived coverage via
`every_int_declaration_is_checked_and_axiom_free`) — every `checker_command`
spot-checked to return count 1 on the real name and count 0 on a fabricated
one.

`formal.kernel_theorem`/`formal.kernel_statement` set per the
`nineteen-mirrors-lost-their-statement` convention; `formal.statement` (the
pinned Mathlib quotation) was left untouched.

`depends_on` set from the local (non-`ml430`) fact IDs for each theorem's
direct kernel-level dependencies (`F:int-add-comm`, `F:int-add-assoc`,
`F:int-add-neg`, `F:int-add-zero`, `F:int-mul-comm`, `F:int-left-distrib`,
and — for `add_left_inj` — this lane's own `F:ml430-int-add-left-cancel`).
`add_neg_eq_sub` has none (its proof is `Eq.refl`, no theorem dependency).

`scripts/check-fact-depends-derived.py --fix` added one missing edge
(`F:nat-add-comm` under `F:ml430-int-add-comm`, since `Int.add_comm`'s proof
term uses `Nat.add_comm` directly) that my hand-written `depends_on` list
missed — this is exactly the tool's job (derive from the proof term, not from
memory).

## Verification (this session)

- `cargo test -p axeyum-lean-kernel --lib int_prelude::` — **49 passed, 0
  failed** (confirmed nonzero, includes
  `every_int_declaration_is_checked_and_axiom_free` and
  `derived_laws_have_no_axiom_footprint`, both green after the seven new
  names were added to `derived_laws`).
- `cargo fmt` (per-file `rustfmt --edition 2024`, both touched files) — no
  diff.
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings` — clean.
- `python3 scripts/validate-facts.py` — **2114 facts, 0 errors** (after the
  `depends_on` fix above).
- `python3 scripts/check-mirror-statement-fidelity.py` —
  `facts=2114|mirrors=374|hash_verified=362|unpinned=12|violations=0|verdict=PASS`.

**Commits** (not pushed, this worktree/branch
`worktree-agent-a30ed05ed441d7a8b`):
`a4b46e7e1` (`add_basics.rs` + prelude wiring + pin recount, verified before
committing), `a130aa969` (the nine-fact ledger flip).
