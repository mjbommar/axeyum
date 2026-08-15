# Diary: the 30 axioms became hypotheses, and the refutation stopped needing them

Lane: `ordered-ring-reconstruct`. Date: 2026-08-15.

## The brief

`real-keystone` measured that `arith_prelude` is not an axiomatization of ℝ. It
is 8 carrier/operation constants and 22 laws of an **ordered commutative ring
with 1** — no `inv`, no `div`, no completeness, no Archimedean axiom, not even
totality — every one of them true of ℤ, and it built the ℤ model to prove the
package consistent. Then it wrote down the route it did not take, and left it:

> parameterise `crates/axeyum-solver/src/reconstruct/arithmetic.rs` over the
> ordered-ring interface so a Farkas refutation becomes
> `∀ (R : Type), <22 laws> → <refutation>`: empty footprint, **stronger** than
> today's statement, and recovering today's by instantiation. Solver change, not
> kernel.

That is what this lane did. It works, it is one function, and the result is
better than the brief predicted, because an independent Lean kernel confirms it.

## What it is

`generalize_over_ordered_ring` (`reconstruct/arithmetic/ordered_ring.rs`) takes
a finished proof term — whatever `reconstruct_lra_proof` or
`reconstruct_sos_proof` returned, already gated to `False` — and λ-abstracts the
constants out of it. The 30 `Real` declarations, then one binder per real
variable, then one per constraint hypothesis, in declaration order, which is
also dependency order, so each binder's type mentions only binders to its left.
Each binder's type is the declaration's type **as it stands in the environment**
with the earlier entries replaced by their bound variables. Nothing is written
by hand; the same discipline `build_int_model_of_arith` used for its
interpretation, for the same reason — an axiom whose statement changes has to
change the obligation rather than silently disagree with it.

Then the kernel infers the type of the wrapped term. We do not state it:

```
∀ (R : Sort 1) (add mul : R → R → R) (neg : R → R) (zero one : R)
  (le lt : R → R → Prop)
  (le_refl : ∀ a, le a a) (le_trans : …) … (sq_nonneg : ∀ a, le zero (mul a a)),
  ∀ (x0 : R), le (add x0 zero) zero → le (add (neg x0) (add one zero)) zero
            → False
```

33 binders for the two-row instance `x ≤ 0 ∧ 1 ≤ x`: 30 interface + 1 variable +
2 hypotheses. Measured footprint: **empty**.

The abstraction is the dual of `Kernel::abstract_fvars` — that one closes free
*variables*, this one closes *constants*, which is what a proof term over a
prelude actually mentions. Sixty lines including the memo.

## The three numbers, and the one that makes them mean something

Per fixture the example prints:

| fixture | original footprint | generalized | instantiated |
|---|---:|---:|---:|
| `x≤0, 1≤x` | 18 (15 `Real.*`) | **0** | 33 |
| `x+y≤0, 1≤x, 1≤y` | 22 (17 `Real.*`) | **0** | 35 |
| `x+y+z≤1, 1≤x,y,z` | 24 (17 `Real.*`) | **0** | 37 |
| `x<y, y<x` | 7 (4 `Real.*`) | **0** | 33 |
| `x·x<0` (SOS) | 10 (8 `Real.*`) | **0** | 32 |

The middle column alone is worth nothing. A footprint of zero is also what you
get from measuring the wrong declaration, from a tool that was never pointed at
your subject, or from a gate that ran no tests — this repository has shipped all
three. So the **original** column is printed beside it, from the same
`Kernel::axiom_footprint` call on the same run, and the fact's `checker_command`
greps for an empty column in a table whose control row is never empty.

The right-hand column is the recovery. Applying the generalized theorem to the
30 `Real` constants and to the refutation's own variable and hypothesis axioms
is a term the kernel accepts against `False` — the original statement, back,
with its trusted base back. Under the tight telescope (`RingTelescope::Used`,
abstracting only what the proof rests on) the recovered footprint is *identical*
to the original's, name for name. Under the full 30-binder interface it is a
superset: the instantiation mentions laws the proof never used, and those are
supplied and ignored. Both are exposed, because the difference is real and a
reader who saw only "superset" would rightly wonder what leaked.

## The part I did not expect: real Lean says it too

`render_lean_module` on the generalized term produces a self-contained module
that contains `False`, `Eq`, `Not`, the theorem, and — unlike every other
arithmetic module this repository emits — **no `axiom` line at all**. Committed
as `tests/fixtures/lean-modules/arithmetic-ordered-ring-farkas.lean`, so the
existing `lean_module_fixtures` suite runs a real binary over it:

```
$ lean crates/axeyum-solver/tests/fixtures/lean-modules/arithmetic-ordered-ring-farkas.lean
'axeyum_ordered_ring_refutation' does not depend on any axioms
```

Lean 4.30.0, commit `d024af09`. That is an independent kernel answering the same
question our `axiom_footprint` answers, and it moves `check-lean-gate.sh` from
112 to **113** real-Lean checks (floor 105, unchanged).

This matters more than the number. `theorem_axiom_footprint` — the example the
brief pointed me at — **cannot be pointed at this theorem**. It builds the
`nat`, `integer` and `real` preludes and nothing else, so grepping its output for
an ordered-ring refutation returns nothing, and nothing reads exactly like
axiom-freedom. That is the coverage trap CLAUDE.md describes, with my own subject
in it. The measurement is the same `Kernel::axiom_footprint` call, made where the
declaration actually lives (a solver-built kernel), plus a second kernel that
shares no code with ours.

## One tool lied, on schedule

The fact's footprint checker was first written as
`grep -qE '^ordered-ring\t[^\t]+\t0\t$'`. It passed. It passes in this shell
because `/usr/bin/grep` on this box is **ugrep 7.5.0**, which interprets `\t`;
GNU grep does not, and `/bin/sh` is dash, so the identical command run through
`sh -c` — which is how `check-fact-evidence-replay.sh` runs it — matched nothing
and exited 1. A checker whose verdict depends on which `grep` is installed is
not a checker. It is now `awk -F'\t'`, and it asserts the row *count* as well:
five `ordered-ring` rows at size 0, five `real-specific` rows NOT at size 0,
ten rows total. `F-int-add-assoc` avoided this by using `[[:space:]]`; I did not
read it closely enough before writing mine.

## Which of the 30 anything still uses

`real: axiom=30` is untouched and `nat_axiom_inventory` still reports it.
Reducing the trusted base was never the goal; making refutations not depend on it
was. So the honest accounting is: **no reconstructed refutation depends on any of
the 30 any more.** What the 30 are still *used* for is instantiation — a consumer
who wants a `Real`-specific conclusion applies the general theorem to them, and
that consumer's footprint is exactly as large as it ever was.

Of the 30, 21 are reached by at least one of the five fixtures. The nine that no
proof shape here has ever touched:

`le_trans`, `mul_le_mul_of_nonneg_left`, `add_lt_add_of_le_of_lt`, `mul_comm`,
`mul_assoc`, `mul_one`, `mul_zero`, `left_distrib`, `mul_nonneg`.

Six of those nine are multiplicative. That is not an argument for deleting them
— the mixed-Farkas and rational-weight SOS engines exist and will reach some of
them — but it does say the ordered-ring *interface* is larger than any single
refutation needs, which is exactly why the full-interface form is the uniform one
and the tight form is available when a caller wants the strongest statement.

## Where this stops

1. **It generalizes a finished term, so it reaches exactly as far as the
   reconstructors do.** The two QF_LIA instances in
   `artifacts/instances/infeasibility/` still have no Farkas path to a kernel at
   all (`lra_farkas_certificate` decides linear *real* arithmetic and declines
   them), and nothing here changes that. A fragment boundary, not a missing case.
2. **The facade still routes past the genuine reconstructor.**
   `prove_unsat_to_lean_module` sends a pure-Real conjunctive `unsat` to
   `ProofFragment::LraDpll`, whose module is the 21-line contentless shim the
   `infeasibility` lane documented. Generalizing that shim would produce an
   axiom-free theorem that says nothing, which is worse than not offering it, so
   the entry point here is the direct reconstructor. Fixing the dispatch order
   is still open and is now *more* worth doing.
3. **Size.** The five-row schedule core reconstructs to a 5 MB term; abstracting
   it makes a second copy and asks the kernel to infer through it. I did not run
   it, so I do not know whether it is 10 MB and fine or something worse. The
   fixtures here are small on purpose and I am not going to imply otherwise.
4. **The hypothesis-footprint gap the `infeasibility` lane named is untouched.**
   The generalized statement's hypothesis binders are still canonical
   `le L zero` props with generated names and no link back to the originating
   assertion. Binding them out of the environment makes them *visible* in the
   statement, which is a small improvement — you can now read the hypotheses off
   the theorem — but nothing checks that they are the rows they claim to be.
5. **It cannot generalize what the kernel cannot state**, and that boundary was
   never reached: this quantification is ordinary dependent-function abstraction,
   universe-monomorphic, over a `Sort 1` carrier into `Prop`. No new kernel
   feature was needed and none was added. If a future package acquires a law that
   quantifies over predicates or subsets (a completeness axiom would), the
   binder for it is still just a Pi, so the abstraction machinery is unaffected —
   the cost lands on whoever has to *satisfy* the hypothesis at instantiation.

## What I would tell the next person

**The expensive route and the correct route were pointing in opposite
directions.** Constructing ℚ, or ℝ, would have been weeks of setoid or gcd work
to *discharge* axioms about a carrier no consumer needs, and would have ended at
a theorem about one structure. Sixty lines of constant-abstraction gave a theorem
about all of them, with nothing assumed. When a lane's finding is "the axioms are
an interface", the answer is almost always to take the interface as a parameter,
not to build something that implements it.

**A zero is a measurement only if the same run produces a non-zero from the same
instrument.** I printed the original footprint next to the generalized one for
that reason, and wrote the fact's `checker_command` so its regex fails on the
control row. It cost four lines.

## Controls

- `cargo test -p axeyum-solver --lib --features full`: **1140 → 1148 tests**, green.
  Seven new in `ordered_ring_tests`, plus the axiom-free module-fixture gate.
- `cargo test -p axeyum-solver --features full --test corpus_regression`: green,
  1 test (nonzero).
- `cargo test -p axeyum-solver --features full --test lean_module_fixtures` under
  a real binary: 3 tests, 16 fixtures accepted, negative control rejects.
- `scripts/check-lean-gate.sh`: **12 suites, 49 tests, 113 real-Lean checks
  (floor 105)** — up one from 112, the added fixture. Parsed from the run, not
  typed.
- `validate-facts.py`: **97 facts, 0 errors**; `kernel-lean=32, 31 axiom-free`
  (was 96 / 31 / 30).
- clippy on `-p axeyum-solver --all-targets --features full`: no warning on any
  file this lane touched. (`-D warnings` on the workspace cannot pass right now:
  another lane's uncommitted `axeyum-cas/src/linear_elim.rs` has four.)
- `nat_axiom_inventory` untouched, deliberately: `real: axiom=30` still reads 30
  and should.
