# Notes: 245-int-fib-two-mul

Detail moved out of [`../status/245-int-fib-two-mul.md`](../status/245-int-fib-two-mul.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

On top of it, `fib_pred_eq_sub(d, k) : Eq Int (fib (sub k one)) (sub (fib
(add k one)) (fib k))` — "`fib(k-1) = fib(k+1) - fib(k)`" — built from
`Int.fib_rec` at `k-1`, the index bridges `fib_shift_minus_one_plus_two`
(new, same `add_assoc` technique `declare_fib_add`'s `P 1` branch already
used inline) and `sub_add_cancel` (already existing, reused verbatim), and
`eq_sub_of_add_eq_left` itself.

Two small ring-rearrangement helpers were also needed and are equally
reusable: `add_sub_self_left(x,y) : Eq Int (add (sub x y) x) (sub (add x x)
y)` — "`(x-y)+x = (x+x)-y`" — and its addition-side analogue
`add_p_qp_eq_pp_q(p,q) : Eq Int (add p (add q p)) (add (add p p) q)` —
"`p+(q+p) = (p+p)+q`" — used by `fib_two_mul` and `fib_two_mul_add_two`
respectively to fold a doubled term back into the statement's `2*x` shape.

## What the kernel rejected, and why

Nothing was rejected by a bare `TypeMismatch` that named the real cause —
that is the whole story here. The full construction (all steps assembled
via `int_theorem`, symbolic `n`) failed to build, and **every** other test
in `int_prelude::` failed alongside it (one bad declaration poisons the
whole shared prelude build, per the standing gotcha) — so the failure count
said nothing about how many things were broken.

**A concrete instantiation test (n = ofNat 3) passed on every single named
intermediate value, with zero failures.** That is the trap this file
already documents under "a concrete instantiation can hide the bug a
symbolic one exposes" — and it is worth recording precisely why THIS bug
specifically survives concreteness, because it is a different mechanism
than the associativity-hole case already in `CLAUDE.md`.

The actual bug: `IntDev::isymm(a, b, h)` requires `h : Eq Int a b` and
returns `Eq Int b a` (it is genuinely symmetry, not a no-op relabeling).
Five call sites in this lane's new code passed `h`'s two endpoints to
`isymm` in the WRONG order — i.e. called `isymm(a, b, h)` where `h`'s real
type was `Eq b a`, not `Eq a b`. Each such call still *type-checks in
isolation* as long as you check it against a self-consistent (but equally
backwards) expectation, which is exactly what a naive intermediate-value
check does. The bug only surfaces when the (wrongly-typed) result is fed
into a `trans` further down the chain, at which point the accumulated
proof genuinely has the wrong type and `infer` reports a `TypeMismatch`
whose two `ExprId`s name neither the direction bug nor which `isymm` call
caused it.

Why concrete `n=3` didn't catch it: it isn't a defeq/reduction issue at
all (unlike the associativity-hole case) — `isymm`'s type requirement is
exactly as strict at a concrete literal as at a free variable. What
differed is that my *test* checked each named value against an expectation
I had ALSO derived from (silently) the same wrong mental model of
`isymm`'s direction, so the individual checks agreed with each other
without ever comparing against the ACTUAL data flow through `ichain`/
`itrans`. The symbolic test caught it only because I added a check for
`back_two` as its own named value for the first time — the concrete test
had skipped verifying it directly, jumping straight to `hc`.

**Diagnosis method:** re-derive the proof step by step against a genuinely
free `n` (a real `fresh_fvar`, not a concrete `ofNat`), pushed into an
explicit `LocalContext` via `ctx.push(LocalDecl { fvar, name, ty: int_ty,
info: BinderInfo::Default })`, then use `Kernel::infer_in`/`def_eq_in` (not
the ambient-context `infer`/`def_eq`, which build a fresh empty context and
report every free-variable-containing term as `UnboundFVar`) to check each
named intermediate ONE AT A TIME against its intended type, narrowing down
which named value first diverges. This found the exact `isymm` call within
minutes once applied; guessing at the term structure from the bare
`TypeMismatch { expected, got }` ExprIds would not have.

**General rule this adds to the standing "symbolic + concrete" pair:** a
symbolic check that only compares NAMED, isolated sub-terms against
individually-derived expectations can still miss a systematic direction
bug, if the same wrong mental model produced both the code and the
expectation. The check that actually finds it is the one that traces the
ACCUMULATED proof through the same combinators the real declaration uses
(`itrans`/`icongr` chains), not a parallel re-derivation of "what each
piece should equal."

## Reusability

- `eq_sub_of_add_eq_left` — general, `Int`-only, no dependency on
  Fibonacci. Reusable anywhere a recurrence/sum equation needs to become a
  difference.
- `fib_pred_eq_sub`, `fib_shift_minus_one_plus_two` — Fibonacci-specific but
  reusable by any future `Int.fib` identity needing `fib(k-1)`.
- `add_sub_self_left`, `add_p_qp_eq_pp_q` — pure ring rearrangements, no
  Fibonacci dependency, reusable by any proof needing to fold `x+x` (or
  `(x-y)+x`) back into a doubled/halved shape.
- `mul_two_eq_add_self` — checked before writing it: no `2*t = t+t` lemma
  existed anywhere in `int_prelude/` (the prelude has `left_distrib` only,
  no `right_distrib`). New, general, reusable by anything needing to move
  between the `2*x` and `x+x` spellings of doubling.

## Gates run (foreground, this worktree)

`cargo test -p axeyum-lean-kernel --lib int_prelude::` → 48 passed, 0
failed. `cargo fmt --all --check` clean (safe here: own isolated worktree,
not the shared checkout). `cargo clippy -p axeyum-lean-kernel --all-targets
-- -D warnings` clean (one `doc_markdown` lint fixed along the way).
`nat_axiom_inventory --require-axiom-free integer` → `ok: integer trusted
surface = 0`. `validate-facts.py` → 1925 facts, 0 errors. The
workspace-wide `--lib` sweep and `just check` did **not** run in this lane
(per brief).

Not pushed — commits are local to this worktree branch.
