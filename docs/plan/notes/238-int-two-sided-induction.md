# Notes: 238-int-two-sided-induction

Detail moved out of [`../status/238-int-two-sided-induction.md`](../status/238-int-two-sided-induction.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

So the proof is two `Nat.rec` inductions whose terms have *definitionally* the
types the kernel expects. No `Nat.sub` truncation, no `natAbs` detour. That is
also why the down-step is stated with `Int.sub` rather than in the
`P (n+1) → P n` form: `sub` costs nothing here and is what a caller wants.

**`Int.fib_add`'s shape, for whoever takes the two downstream facts.**
Fibonacci is a two-step recurrence, so no single-index motive can step; the
motive is `Q k := P k ∧ P (k+1)`, the pairing device
`nat_prelude/fibonacci.rs` already uses for `Nat.fib_add`. Two things about the
downward step are worth carrying:

- It is stated as an **addition** and closed by an `add_right_cancel` helper
  rather than by subtracting — both `target + fib(m+n)` and
  `fib(m+n-1) + fib(m+n)` are shown equal to `fib(m+n+1)`, so no difference is
  ever formed and `Int.sub` never enters the algebra.
- `Q (n-1)`'s second component is `P ((n-1)+1)`, and `(n-1)+1` is **not**
  definitionally `n` for symbolic `n`; it needs an `int_eq_rewrite` transport
  along `sub_add_cancel`, which is `add_neg_cancel_right k (neg one)` read at a
  defeq type (`neg (neg one)` reduces to `one`).

**Three helpers the integer prelude lacked** and this lane built locally:
`neg_mul` (it carries `mul_neg`), `neg_add_cancel` (it carries `add_neg`),
`zero_add` (it carries `add_zero`), plus `add_regroup_four` — there is no
`add_add_add_comm`, and the ℕ side built its own private one for the same
reason.

**Negative controls.** `Int.induction_on`'s statement is mutation-tested:
`two_sided_induction.rs::build` takes a `Mutation` so the shipped **proof value**
is re-declared byte-identically against three perturbed statements (base at
`one`, up-step replaced by a second down-step, down-step replaced by a second
up-step); the kernel must reject all three, with an unmutated positive control
through the same route. `Int.fib_rec` and `Int.fib_add` are instantiated at
closed indices in every branch / sign combination and reduced against the
arithmetic, each with a wrong right-hand side that must not be `def_eq`.

**Ledger.** `F:ml430-int-fib-add-181b6a2c` flipped `open → proved`
(`kernel-lean`, axiom-free); new `F:int-two-sided-induction` and
`F:int-fib-rec`. Every `kernel-term` checker pins the **whole rendered type**,
not just the name, because these statements' factors can be transposed into
different-but-well-typed propositions the gate would prove just as happily —
verified discriminating (1 on the real row, 0 on a mutated one), with
`[[:space:]]` rather than `\t`. `validate-facts.py`: 1,924 facts, 0 errors.

**Overlap recorded rather than hidden.** `Int.fib_rec` proves the same
proposition as `F:ml430-int-fib-add-two-739358dd`, which was **already** `proved`
via a sealed *external* Lean capsule on the autogenesis import route. That
capsule lives outside this kernel's environment, so no `int_prelude` declaration
can cite it; `F:int-fib-rec` records the in-tree constructive declaration that
`Int.fib_add` actually consumes, and its `prior_art` says so explicitly. It is
not an independent new result.

**Still open, and now unblocked** — `F:ml430-int-fib-two-mul-0e70f3dd`
(`fib (2n) = fib n * (2 fib(n+1) - fib n)`) and, through it,
`F:ml430-int-fib-two-mul-add-two-0ba4a948`. Sizing, having built the machinery:
each is **~200–250 lines of `sub`-flavoured ring algebra and no new device**.
The route for the first is `Int.fib_add n n`, plus `fib(n-1) = fib(n+1) - fib n`
(a rearrangement of `Int.fib_rec` at `n-1`, whose index bookkeeping already
exists in `declare_fib_add`), plus `mul two n = add n n` — which this prelude
does not carry and which comes from `mul_comm` + `left_distrib` + `mul_one`,
since there is no `right_distrib`. The genuine friction is that both target
statements are written with `Int.sub`, so unlike `Int.fib_add` the algebra
cannot stay inside `add`/`mul`; expect an `eq_sub_of_add_eq`-shaped bridge to be
the first thing needed.

**Gates run (foreground, this worktree):**
`cargo test -p axeyum-lean-kernel --lib int_prelude::` → 44 passed, 0 failed;
`cargo fmt --all --check` clean; `cargo clippy -p axeyum-lean-kernel
--all-targets -- -D warnings` clean; `nat_axiom_inventory --require-axiom-free
integer` → `ok: integer trusted surface = 0`; `validate-facts.py` → 0 errors.
The workspace-wide `--lib` sweep and `just check` **did not run** in this lane.
