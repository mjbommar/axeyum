# ADR-0614: Prelude `Nat` numerals are compact literals, not unary towers

Status: proposed
Date: 2026-08-28
Supersedes-nothing: written as ADR-0613 by its lane; renumbered to 0614 by the coordinator because a sibling lane took 0613 the same hour (`adr-0613-unsat-is-certified-by-following-hints-not-by-searching-for-them.md`, already on `main`).
Index-summary: `NatOps::num` emits `Lit::Nat(n)` instead of `succ^n Nat.zero`, so closed `Nat` arithmetic in every prelude reaches the kernel's existing `reduce_nat_binop` acceleration — measured at 1.6 million times faster on `Nat.gcd 512 1875`, and the difference between reducing and a stack overflow on `Nat.div 13125 25`. The two representations are definitionally equal through Lean's own offset-equality rule; no proof term changed and all seven preludes still admit. PROPOSED rather than accepted because the win is not where it was expected: the prelude build's own clock does not improve (it was never spending its time here), while every numeral's RENDERED form changes, which moves 12 pinned statement strings, 3 autogenesis scripts, 5 fact `checker_command`s and 388 fact `formal.statement` strings. That trade is a coordinator decision, and the alternative that avoids it — reducing `Nat.zero` to `Lit::Nat(0)` so unary towers collapse in `whnf` — is stated and unmeasured.
Index-status: proposed

## Coordinator decision (2026-08-28): NOT ADOPTED, and the implementation is not on `main`

This ADR stays **proposed**. The measurement is accepted in full; the change is
declined on the trade it exposes.

- The diagnosis is CONFIRMED and the numbers are not marginal: `Nat.gcd 512
  1875` is **1,600,000x** faster as literals, and `Nat.div 13125 25` — the
  magnitude `Rat.normalize` actually forms — is the difference between 10 µs
  and a **stack overflow**.
- `Lit::Nat(n)` really is definitionally equal to `succ^n Nat.zero` by rules
  already in the kernel, and **no proof term needed editing**: all seven
  preludes re-admitted unchanged.
- **And the win is approximately zero where it was expected.** Interleaved A/B
  from one binary, cache off: `creal` 14.91 s -> 14.23 s (4.6%), with a
  contended re-run putting the *unary* side FASTER at 23.4 s. Noise exceeds
  effect. The prelude build was never spending its time in numeral arithmetic.
- The cost is not zero and it is mostly invisible: every numeral's RENDERED
  form changes, moving 12 pinned statements, 3 autogenesis scripts (2 of them
  gates), 5 fact `checker_command`s, and **388 fact `formal.statement` strings
  — documentation, so those drift SILENTLY.**

Paying a ledger-wide rendering change for a measured 0% is a bad trade, so the
`NatOps::num` change stays on `worktree-agent-af9ebc3a92c6ad626` rather than
landing. What lands here is the **probe** (`examples/nat_numeral_whnf_probe`),
which is permanently useful and changes nothing.

**The lane was right not to repin the 12.** Rewriting a drift pin mechanically
is how real drift gets masked, and `AxNat.zero` also renders from direct
`zero()` calls that `num` never touched, so a textual rewrite would have been
unsound as well as unsafe.

**Revisit when a real workload is numeral-bound.** The pi rung-2 case that
started this was: one declaration went 587 s -> 113 s purely by keeping formed
magnitudes small. That is the same mechanism, and it says the remedy is to
avoid forming large magnitudes rather than to make large magnitudes cheap.

**A mutation result worth keeping**: deleting `nat_offset`'s `Lit::Nat` arm
killed **all five** guard tests rather than the predicted one, because
`build_nat_prelude` itself stops admitting. That arm became load-bearing for
the prelude, where it had not been.

## MEASUREMENT UPDATE (2026-08-28): the "zero benefit" number is STALE

The decision above rests on an A/B measuring `creal` at 14.91 s -> 14.23 s
(4.6%, noise exceeding effect). **That A/B ran before `trig_fn`, `cos_sign`
and `uniform_convergence` landed on 2026-08-27**, and those three files are
now 78% of the prelude build (`creal_prelude_builds` 12.60 s -> 105.51 s).

Re-measured on the current tree: literal numerals are **-11% overall**, and
**81x on one declaration** — `cos_sign::declare_cos_wide_nonpositive`, 9.74 s
-> 0.12 s. The mechanism is confirmed by δ-unfold counting: healthy
declarations run 1.6-3 `unfold_def` attempts per successful unfold, the
regressed ones run 40-120 : 1, and `CReal.sinFn` alone is 2,426 unfolds
against 291,261 attempts, 98% of them `Nat.succ`. `whnf` is walking unary
towers, not unfolding definitions.

**The decision does not change, and the reason it does not change is
unaffected**: the cost is still a ledger-wide RENDERING change moving 12
pinned statements, 3 autogenesis scripts, 5 `checker_command`s and 388 fact
`formal.statement` strings that would drift silently. -11% does not buy that.

What changes is that **"measured at zero" must no longer be quoted as the
reason.** The honest statement is: the benefit is real but modest in
aggregate, concentrated in a small number of declarations, and the local
remedy is strictly better — bounding the magnitude a declaration FORMS took
one declaration 587 s -> 113 s and another 9.74 s -> a fraction of that,
without touching how any numeral renders.

Note also the second flavour, which literals do **not** fix: a concrete
witness threaded through an application (`geom_16_over_25_k_final` builds
`633` as a unary `Nat.mul` and carries `K = ka*633 + ka*2` through the whole
M-test), so every `whnf` re-derives the tower. That is
`declare_e_converges`'s hazard arriving as a magnitude, and only a proof
change reaches it.

## Context

The kernel carries Lean's `reduce_nat` acceleration. `Kernel::reduce_nat_binop`
(`tc.rs`) evaluates `Nat.add`/`sub`/`mul`/`div`/`mod`/`gcd`/`pow`/`beq`/`ble`
and the bitwise operations directly on `Lit::Nat` arguments, guarded by
`Kernel::build_nat_binop_table` against the environment's own declarations. It
is tested by four suites — `nat_literal_semantics`, `nat_literal_arithmetic`,
`nat_literal_bignum`, `real_lean_nat_literal_crosscheck` — and it is why real
Lean exports touching `Char`/`UInt32`/`Fin` import in 0.05 s instead of
exhausting an 8 GB address space.

**No numeral this repository's own preludes built could reach it.**
`NatOps::num` was

```rust
let mut e = self.zero();
for _ in 0..n { e = self.succ(e); }
e
```

and the rule fires only when **both** arguments whnf to `Lit::Nat`. `Nat.zero`
is a `Constructor` with no definition, so it never whnfs to `Lit::Nat(0)`;
`Kernel::reduce_nat_succ` therefore returns `None` on `succ (Const Nat.zero)`
and the tower never collapses bottom-up. Roughly 2,280 `num` call sites across
`nat_prelude`, `int_prelude`, `rat_prelude`, `creal` and `complex` were all on
the slow side of a fast path that had been built, tested and trusted.

The visible symptom was in `Rat.normalize`, whose `gcd` and division run at the
magnitude of the products being normalized, and in `creal`'s index arithmetic.
A lane bounding an intermediate at `8/75 ≤ 7/64` (largest `Nat` 525) rather
than `512/1875 ≤ 7/25` (largest `Nat` 13,125) took a prelude build from
**587.02 s to 113.46 s** — one variable, 5.2×, and no explanation until the
representation was looked at.

## The measurement

`examples/nat_numeral_whnf_probe` builds the same arithmetic term twice and
times `Kernel::whnf` on each. It classifies the reduct (`lit:` / `succ-tower:` /
`stuck`) so a run that reduced nothing cannot be read as a fast one. Release,
this host, 2026-08-28:

| operation | unary | literal | ratio |
| --- | ---: | ---: | ---: |
| `Nat.mul 25 21` | 2,304 µs | 11 µs | 210× |
| `Nat.mul 75 75` | 25,831 µs | 12 µs | 2,150× |
| `Nat.mul 125 105` | 52,399 µs | 10 µs | 5,240× |
| `Nat.gcd 512 1875` | 25,624,109 µs | 16 µs | 1,600,000× |
| `Nat.div 13125 25` | **stack overflow** | 10 µs | — |

The `div` row is the one that matters most: at the magnitude `Rat.normalize`
actually forms, the unary route does not merely lose, it aborts the process.

## Decision

`NatOps::num(n)` emits `self.kernel().lit(Lit::Nat(NatLit::from(n)))`.

`NatOps::num_unary(n)` keeps the old body, for any caller that needs the
constructor spine *syntactically* present rather than up to conversion. No
in-tree caller needs it today — every one of the ~2,280 sites moved to literals
and all seven preludes still build — so it exists for the tests in
`tests/nat_prelude_numerals_are_literals.rs` and as the honest half of the pair.

## Why this is sound

`Lit::Nat(n)` and `succ^n Nat.zero` are definitionally equal, and by rules the
kernel already had rather than by anything added here:

- `Kernel::def_eq_nat_offset` is Lean's offset equality. `Kernel::nat_offset`
  exposes one zero/successor layer of **either** representation — a literal by
  `NatLit::predecessor`, a constructor spine by `unfold_apps` — and ordinary
  `def_eq_core` compares the predecessors.
- `Kernel::nat_literal_to_constructor` (Lean's `nat_lit_to_constructor`) exposes
  a constructor layer of a literal, so `Nat.rec` still ι-reduces on one. An
  induction written against the unary form is unaffected.

Neither rule is new and neither widens conversion: they are the same two rules
that already let an imported Lean term mix the representations.

**What IS new is that the prelude build now depends on them.** Deleting the
`Lit::Nat` arm of `Kernel::nat_offset` used to be invisible to
`build_nat_prelude`; it now makes the prelude fail to admit at all
(`TypeMismatch`, measured — see the mutation controls below). That is a real
shift in what the prelude's admission rests on, and it is recorded here rather
than left to be discovered. It is a shift onto a rule this kernel already
trusts for every Lean import, checked by four suites and cross-checked against
real Lean.

The empirical half of the soundness argument is that **all seven preludes still
build**. Every proof term in `nat`/`integer`/`rat`/`axreal`/`creal`/`complex`/
`string` re-passes `Kernel::add_declaration` with numerals in the new
representation, which is the only thing that ever verifies a proof term here.

### The guard, and its mutation controls

`crates/axeyum-lean-kernel/tests/nat_prelude_numerals_are_literals.rs`, five
assertions chosen so that no two reject through one shared check. Measured
2026-08-28 in a lane worktree:

| mutation | tests killed |
| --- | --- |
| `num` reverted to the unary tower | exactly `num_builds_a_compact_literal`, `prelude_arithmetic_reaches_the_literal_fast_path` |
| `Kernel::nat_offset` loses its `Lit::Nat` arm | **all five** — `build_nat_prelude` itself stops admitting |
| the negative control's expectation flipped | exactly `distinct_numerals_are_not_definitionally_equal` |

The first mutation leaves the two definitional-equality tests green, which is
the point: they pass under *either* representation, because that
interchangeability is what makes the change safe. The second was expected to
kill one test and killed five; the finding is the paragraph above, and it is why
the row is recorded rather than the prediction.

Two deliberate choices in the guard:

- `prelude_arithmetic_reaches_the_literal_fast_path` asserts the reduct's
  **shape**, not a clock. `Lit::Nat` is reachable here only through
  `reduce_nat_binop`, so a unary numeral structurally cannot produce one — it
  whnfs to `Nat.succ …`. A timing assertion would be flaky under lane
  contention and would measure the host.
- The negative control's pairs differ by **one** successor layer. A failing
  `def_eq` has no early exit, so a control built from large or structurally
  unrelated terms is unbounded — one such control cost 300 s and 3.1 GB
  elsewhere in this repository. `(7, 8)` is equally discriminating and free.

## What this does NOT buy, measured

**The prelude build's wall clock does not improve.** Interleaved A/B on this
host, `AXEYUM_PRELUDE_CACHE=0`, the same binary built from the two `num` bodies:

| prelude | unary | literal |
| --- | ---: | ---: |
| `nat` | 193,520 µs | 191,185 µs |
| `integer` | 362,928 µs | 371,985 µs |
| `rat` | 762,554 µs | 784,360 µs |
| `creal` | 14,914,239 µs | 14,227,281 µs |

`creal` is ~4.6% faster in the round measured under comparable load, and a
second round under 6.2 load put the unary side at 23.4 s — noise larger than the
effect. **Treat the prelude-build win as zero.**

That is not a contradiction of the microbenchmark; it locates it. The committed
preludes do not spend meaningful time reducing closed `Nat` arithmetic at large
magnitudes. The 5.2× incident that motivated this was a *specific declaration*
forming a 13,125-magnitude `Nat`, and the general cost is paid only by whoever
hits that shape.

So the value of this change is not a speedup on today's tree. It is that a
lane can now form a numeral of any magnitude without the kernel's cost going
superlinear in it, and without `Nat.div` at four digits overflowing the stack.
The 587 s → 113 s incident becomes impossible rather than avoided by luck.

## The blast radius, measured — and why this is `proposed`

No proof term changed and no proof was edited. What changed is every numeral's
**rendered** form: `lean_pp` prints `Lit::Nat(n)` as `n`, where it printed
`AxNat.zero` and `AxNat.succ AxNat.zero`. `AxNat.succ x0` — a successor of a
*variable*, built by `succ` rather than `num` — is unchanged, which is the
detail that confirms only `num`-built numerals moved.

Measured on this branch, 2026-08-28:

| surface | count | effect |
| --- | ---: | --- |
| `cargo test -p axeyum-lean-kernel --lib` | **913 passed, 12 failed** | every failure a pinned rendered-statement string |
| pinned statements, by file | 6 `rat_prelude_tests.rs`, 3 `int_prelude_tests.rs`, 1 `nat_prelude_tests.rs`, 2 `creal_tests.rs` | red until repinned |
| autogenesis scripts matching the old rendering | 3 | `check-autogenesis-bitwise-semantic-law-demand.py`, `check-autogenesis-holdout-contamination.py`, `gen-autogenesis-open-lemma-candidate-ranking.py` — the first two are gates |
| fact `evidence` (i.e. `checker_command`s) | **5** | `F-nat-choose-succ-self-eq-zero`, `F-nat-euclid-lemma`, `F-nat-exists-prime-dvd`, `F-nat-exists-prime-gt`, `F-nat-zero-choose-succ` |
| fact `formal.statement` | **388** | documentation; nothing re-derives these, so they drift silently rather than going red |

The 12 failures are all of the form

```
 left: "… (Rat.natDivSucc 1 x0)) (Rat.natDivSucc (AxNat.succ x0) 0))"
right: "… (Rat.natDivSucc (AxNat.succ AxNat.zero) x0)) (Rat.natDivSucc (AxNat.succ x0) AxNat.zero))"
```

— the same mathematics, one representation apart. **They were deliberately not
repinned by the lane that made this change.** A drift pin rewritten mechanically
is exactly how a real drift gets masked, and `AxNat.zero` also renders from a
direct `zero()` call that `num` never touched, so a textual rewrite is not
sound; each pin has to be replaced by the string the kernel actually renders.
More importantly, the 388 silently-drifting statements are a ledger-wide
question, and `artifacts/` was outside the lane's scope.

So the decision this ADR asks for is not "is the change correct" — it is, and
the guard proves it — but **is a ledger-wide change in how numerals render
worth a benefit that the prelude-build A/B measures at zero.**

## The alternative that avoids the rendering change entirely (UNMEASURED)

Make `Kernel::reduce_nat_succ` (or `whnf_core`'s `Const` arm) reduce
`Const Nat.zero` to `Lit::Nat(0)`. The kernel already treats the two as the same
value — `Kernel::nat_literal_ext` is Lean's `is_nat_lit_ext` and accepts
`Nat.zero` in place of the literal — so a unary tower would collapse bottom-up
in `whnf` and `reduce_nat_binop` would fire, while every *stored* term and every
rendered statement stayed exactly as it is today. Blast radius zero.

Two things must be measured before believing it, and this lane measured
neither:

- `reduce_nat_succ` recurses through `whnf_core` once per layer, so the
  `Nat.div 13125 25` **stack overflow probably survives** — the tower is still
  walked at depth 13,125. The literal form does not build the tower at all.
- Collapsing towers on every `whnf` adds a probe to a hot path; ADR-0536 records
  that switching the binary acceleration on once took a prelude build from 8.7 s
  to 33.0 s, so a new eager rule there is not free.

## Consequences

- Anything that inspects a prelude numeral's **syntax** now sees `Lit::Nat`.
  Nothing in tree did; `num_unary` is there if something needs to.
- `Kernel::nat_offset`'s literal arm and `nat_literal_to_constructor` are now
  load-bearing for `build_nat_prelude`. Do not narrow either without running
  the prelude suites.
- Offset equality recurses once per successor layer, so `def_eq` between a
  literal `n` and a **hand-built** `succ^n zero` is O(n) stack. Prelude code
  never builds the second, and the guard keeps its own sizes small for exactly
  this reason.
- The `587 s` and `5.2×` figures quoted here are from the incident report that
  motivated the work, not re-measured by this ADR. The probe table and the A/B
  table are.

## Alternatives considered

**Make `Nat.zero` whnf to `Lit::Nat(0)`.** This would let `reduce_nat_succ`
collapse a tower bottom-up and leave `num` alone. Rejected: it is a change to
the *kernel's* reduction on a constructor, affecting every import, to work
around a choice made in the prelude — and it would still cost O(n) reduction
steps per numeral where the literal costs one.

**Leave it, and fix the numerals in the one declaration that hurt.** That is
what the 587 s incident did, and it is why the general problem stayed invisible
for as long as it did. The next lane to form a large `Nat` pays it again.
