# ADR-0536: The literal-`Nat` acceleration moves to Lean's two call sites, under Lean's `has_fvar` guard

Index-summary: Literal `Nat` arithmetic is called from the δ loop and from lazy-delta, never from the δ-free step, and only when neither operand mentions a free variable
Status: accepted
Date: 2026-08-20

## Context

[ADR-0459](adr-0459-kernel-nat-literal-arithmetic-is-name-keyed.md) added
`Kernel::reduce_nat_binop`, the port of Lean's `type_checker::reduce_nat` for the
fourteen two-argument cases, and described its placement as "tried after
`whnf_core` and before δ". **The code did not do that.** It was called from
inside `Kernel::whnf_no_unfolding_uncached` — and that function *is* Lean's
`whnf_core`, so the rule sat one layer below the placement its own ADR
specified. There was also no `has_fvar` guard anywhere.

In the pinned reference (lean4 `v4.30.0`,
`d024af099ca4bf2c86f649261ebf59565dc8c622`, the same commit ADR-0514 pins the
toolchain to) `reduce_nat` is defined at `src/kernel/type_checker.cpp:609` and
called from exactly two places, neither of them `whnf_core`:

- `type_checker::whnf`, `:670` — on the `whnf_core` result, **before**
  `unfold_definition`. Unguarded.
- `type_checker::lazy_delta_reduction`, `:978` — after offset equality and
  **before** the δ step, under
  `(!has_fvar(t_n) && !has_fvar(s_n)) || m_eager_reduce`. (`m_eager_reduce` is an
  elaborator-only mode; this kernel has no equivalent and takes the guarded
  branch always.)

The misplacement was not free. `Kernel::reduce_nat_binop` δ-normalises **both**
arguments of every `Nat.add`/`Nat.mul`/`Nat.div`/… application it meets, so
calling it from the δ-*free* normaliser does eagerly and speculatively exactly
the work lazy-delta exists to avoid. Measured on one `build_creal_prelude`
(2026-08-20, s4): it fires **1,192,536 times and produces a literal 575 times**
— 0.05% — and **1,192,313 of those probes are on a term that mentions a free
variable**. The rule had been dead since it landed and was switched on for the
first time by `502184d3f` (which aligned the native `Bool` with official Lean
constructor order, the condition `build_nat_binop_table` gates on); that build
went 8.7 s → 33.0 s. The `whnf_core` memo (`0887ab652`) took it to 13.0 s. This
ADR is about the remaining 6.5 s, and about the fact that closing it changes
what the kernel identifies.

## Decision

**`reduce_nat_binop` is called from `Kernel::whnf_core` (the δ loop) and from
`Kernel::lazy_delta_step`, never from `Kernel::whnf_no_unfolding_uncached`; and
at both sites it is guarded by `has_fvars`, so it fires only on an application
in which neither operand mentions a free variable.**

Concretely:

- `Kernel::whnf_core` — our name for Lean's `whnf` — tries the rule on the
  δ-free normal form, before `unfold_def`. This is Lean's `:670`.
- `Kernel::lazy_delta_step` — our `lazy_delta_reduction` — tries it on either
  side, after `def_eq_nat_offset` and before the δ case analysis, returning
  `def_eq_core` of the reduced side against the other. This is Lean's `:978`.
  Without this site the rule would be unreachable from the route that matters:
  `def_eq_core_uncached` normalises both sides with `whnf_no_unfolding` (Lean's
  `whnf_core`, which carries no `Nat` rule) and then comes straight here.
- The guard is `!self.has_fvars(e)`. For a two-argument application whose head is
  a closed `Const`, that is exactly "neither argument mentions a free variable" —
  the same condition Lean spells `!has_fvar(t_n) && !has_fvar(s_n)`.

**We deviate from Lean in one direction only, and it is the conservative one.**
Lean's `whnf` site is unguarded; ours is guarded. Since the guard can only
*prevent* a reduction, our kernel identifies a subset of what Lean's identifies.
That is a capability risk, never a soundness risk, and the reason it is a
decision and not a refactor. The measured price is below; the measurement is over
our corpus and is **not** a proof that nothing is lost.

`reduce_nat_succ` deliberately stays in `whnf_no_unfolding_uncached`. Lean's
`reduce_nat` covers the unary `Nat.succ` case too, so this is a residual
divergence — but a failing `reduce_nat_succ` probe costs one interned-name
comparison against `Nat.succ` before it reduces anything, where a failing binary
probe δ-normalises two arguments. It is the cost, not the placement, that this
ADR is closing; moving `succ` would change identification for no measured gain.

## Evidence

### Timing

`examples/prelude_build_timing`, release, `AXEYUM_PRELUDE_CACHE=0`, `taskset -c
0-7`, three interleaved rounds of all three variants on one host (s4,
2026-08-20), so drift and lane contention hit every variant equally. `creal`
seconds:

| variant | r1 | r2 | r3 | median |
|---|---|---|---|---|
| before — rule inside the δ-free step, no guard | 12.77 | 22.28 | 12.99 | **12.99** |
| Lean's placement, **no** guard at the `whnf` site | 13.38 | 12.12 | 12.01 | **12.12** |
| Lean's placement **+ the `has_fvars` guard** (this ADR) | 6.86 | 6.44 | 6.79 | **6.79** |

Read the middle row before the last one: **the placement alone buys nothing.**
Moving the rule to Lean's sites without the guard is 12.12 s against 12.99 s —
inside the run-to-run spread of this workload on a shared box (the 22.28 s is a
contention outlier, which is why the medians and not the means are quoted). The
entire 1.91× is the guard. That matters for what a future reader concludes: this
change is Lean-faithful *and* fast, but those are two independent facts and only
one of them is load-bearing for the number.

For scale: 8.71 s was the pre-regression time (before the acceleration was
switched on at all), so the kernel is now faster on this workload than it was
before literal-`Nat` arithmetic existed, while keeping the arithmetic.

### Identification delta — measured, not argued

Nothing observable changed. Every gate below was run on the post-change tree and
compared against the counts the previous lane recorded on the pre-change tree:

| gate | before | after |
|---|---|---|
| `cargo test -p axeyum-lean-kernel --lib` | 398 passed (at `0887ab652`) | **399 passed, 0 failed** in 2,148 s |
| `cargo test -p axeyum-lean-kernel` (lib + all 46 integration suites) | — | **609 passed, 1 failed** — and the one is pre-existing, see below |
| `cargo test -p axeyum-solver --features full --lib reconstruct::` | 300 passed (at `0887ab652`) | **312 passed, 0 failed** in 107 s |
| `python3 scripts/gen-lean-axiom-ledger.py --check` | `axreal=30`, all others 0 | `total=30 axreal=30 complex=0 creal=0 integer=0 logic=0 nat=0 rat=0 string=0 retired=35 axiom_free=7 unclassified=0`, exit 0 |
| `scripts/check-prelude-reuse-equivalence.sh` | — | `compared=8 failures=0`, counters live (`hits=18` on / `hits=0` off) |
| `scripts/check-clippy-complete.sh` | — | 618 of 618 workspace targets, **0 diagnostics** |

The lib sweep is 399 and not 398 because `4e1f9b092` — the commit this branch
started from, one after the memo — added one; `reconstruct::` is 312 and not 300
because the string-length lane landed twelve. No test was removed or filtered by
this change; the diff only appends, so "0 failed" is the claim and the count is
the control on it.

**The one failure is `real_lean_wellfounded_elaborator_divergence`, and it is not
this change.** It fails byte-identically on an unmodified `HEAD` extracted into a
`scripts/lane-snapshot.sh` tree — same two Lean errors, same line numbers. It is
not even a failure of our kernel: the test writes a module and hands it to the
**real** pinned `lean` binary (v4.30.0, `d024af09`, `matches_pin=true`), and
Lean's *elaborator* rejects it with a type mismatch on
`axeyum_proof_share_1 = AxNat.zero.succ.succ` even with every proof spelled
`def` — which is precisely the assertion the test makes about ADR-0517's account
of the divergence. That is a live, separate finding, recorded here only so the
next reader of this sweep does not attribute it to the `Nat` rule.

`reconstruct::` was run from a `scripts/lane-snapshot.sh` tree, and that is not
fastidiousness. Run in the shared checkout it reported **8 failed** — every one
in `reconstruct::arithmetic::string_length::tests`, all saying "over the **2**
budget" while the committed `MAX_UNARY_TERMS` is `128`. A sibling lane's mutation
harness was rewriting that constant in the shared worktree while this build read
it. Nothing distinguishes that from a real regression except looking, so: when a
gate is the evidence for a claim, run it on a tree nobody else is editing.

**No declaration stopped admitting.** That is a measurement over the preludes,
the import corpora and the reconstruction suites this repository carries; it is
not a theorem about definitional equality. A term whose `Nat` operands mention a
free variable *and* reduce to literals anyway is exactly what we stop
accelerating, and one is constructed below — so the class is nonempty, and only
our corpus says it is unreached.

### What the guard gives up, as a fixture rather than a claim

`has_fvars` is **structural**. It cannot see that `(fun _ : Nat => 7) x` reduces
to a literal, so `Nat.mod ((fun _ : Nat => 7) x) 0` is refused by the guard even
though both operands normalise to literals. `tests/nat_literal_arithmetic.rs`
constructs exactly that, in an environment where `Nat.mod`'s declared body is the
stub `fun _ _ => Nat.zero` while the accelerated answer is Lean's `x % 0 = x`.
The two answers differ, so the fixture reports which one decided:

- at the **`whnf_core`** site, reached through a recursor whose major it
  normalises: a closed major `Nat.mod 7 0` selects the *successor* minor (the
  accelerated `7`), and the same major with `7` written as `(fun _ => 7) x`
  selects the *zero* minor (the stub's `Nat.zero`);
- at the **lazy-delta** site, reached through `def_eq` directly: closed
  `Nat.mod 7 0` is `7`, and `Nat.mod ((fun _ => 7) x) 0` is `Nat.zero`.

The second is the identification cost, written down as an assertion. Note what
is *not* lost: the kernel does not get stuck, it computes the environment's own
answer. The unbounded-successor-chain hazard ADR-0459 exists to remove is only
reachable through a declaration whose body really does recurse — and there the
two answers agree, which is what
`accelerated_addition_agrees_with_unaccelerated_recursion` pins.

### Mutation matrix

Four mutations, each applied alone to the post-change tree, each run against the
whole `nat_literal_arithmetic` suite (16 tests, 16 passing unmutated):

| mutation | tests that die |
|---|---|
| delete the `reduce_nat_binop` call in `whnf_core` | **1** — `a_recursor_major_is_accelerated_by_the_delta_loop` |
| delete the `!self.has_fvars(whnfd)` guard in `whnf_core` | **1** — `an_open_recursor_major_is_decided_by_the_declaration_not_the_acceleration` |
| delete the `reduce_nat_binop` block in `lazy_delta_step` | **5** — `totality_conventions_match_lean`, `false_equations_are_still_refused`, `predicates_return_the_right_bool_constructor_and_refuse_the_other`, `acceleration_trusts_the_declared_type_not_the_body`, and `arithmetic_is_arbitrary_precision`, which **overflows the stack and aborts the harness** |
| delete the `has_fvars` conjunction in `lazy_delta_step` | **1** — `an_open_operand_is_decided_by_the_declaration_in_lazy_delta` |

Three of the four kill **exactly one** test, and the three are distinct — so each
guard is separately pinned rather than jointly covered by one shared check. That
property is the one this repository has been burned by: six of seven guards in an
earlier suite were individually removable because they all rejected through a
single downstream check.

The fourth is deliberately not narrowed. Deleting the whole lazy-delta *call site*
is not a guard mutation, it is removing half the rule, and it takes five tests with
it — including a stack overflow on `2^64`-scale literals. That abort is worth
naming: it is ADR-0459's unbounded-successor-chain hazard reproducing on demand,
and it is what says the lazy-delta site is the one that carries the rule's reason
for existing. The `whnf_core` site alone does not stop it.

The mutation matrix measures the guards that exist. The question it cannot
answer — and the one CLAUDE.md says to ask instead — is whether the *data* can
express the distinction the producer makes. Here it can: the producer's only
distinction is closed-versus-open, `has_fvars` is a field on every expression
node, and the fixtures above sit on both sides of it. The distinction that is
*not* expressible is "open but reduces to a literal", and rather than leave that
as a gap, the guard is defined to refuse it and a test asserts the refusal.

## Alternatives

**Keep Lean's exact placement, unguarded at the `whnf` site.** Measured (middle
row above): 12.12 s, no improvement. Rejected — it is faithfulness bought at the
whole price of the change, on a rule that fails 99.95% of the time.

**Keep the rule in the δ-free step and rely on the `whnf_core` memo.** That is
the status quo this ADR replaces: 12.99 s, and the rule keeps calling the δ
normaliser from inside the δ-free one, which is a structural inversion the memo
hides rather than fixes.

**Guard per-argument instead of on the application.** Identical: the head of a
two-argument `Nat` application is a closed `Const`, so `has_fvars(app)` is the
disjunction of the two arguments' flags. Rejected as strictly more code for the
same predicate.

**Make the guard semantic — "reduces to a literal" — instead of structural.**
That is the guard that would lose nothing, and it is unimplementable: deciding it
*is* the reduction whose cost the guard exists to avoid.

**Add a probe counter to `Kernel` so the guard could be asserted directly.**
Rejected once the stub-body fixture was found: the differing-answer environment
already makes the guard's effect observable through ordinary `def_eq`, with no
new field on the trusted kernel and no counter that a future reader has to trust.

## Consequences

- `build_creal_prelude` is 6.79 s, from 12.99 s — and from 33.0 s at the peak of
  the regression. Six call sites rebuild a prelude, so this is on the critical
  path of the reconstruction route, not a microbenchmark.
- The kernel now identifies a **subset** of what Lean's kernel identifies, in one
  named place: a `Nat` operation whose operands mention a free variable and
  reduce to literals anyway. Nothing in our corpus reaches it. If an imported
  declaration ever declines for this reason, the fix is known and cheap — drop
  the guard at the `whnf_core` site only, which restores Lean's exact behaviour
  at the cost of the middle row of the timing table.
- `reduce_nat_succ` remains at the old placement, and remains a divergence from
  Lean's `reduce_nat`. Revisit if it ever shows up in a profile; it is one name
  comparison per constant-headed reduction step today.
- ADR-0459's description of the placement is now true of the code. Its trust
  argument — name-keyed, type-validated, body-unverified — is untouched: this ADR
  moves *where* the rule runs and *when* it is allowed to, never *what* it
  computes.
