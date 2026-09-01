# Prelude Build Cost — why the kernel got slow, and how to bisect it

The prelude build is a shared resource: dozens of tests build one, so a single
declaration that makes it slow blocks every lane's gate, including finished work
that is only waiting to publish. One declaration has taken the `creal` prelude
from 18.7 s to 92.6 s, and another from 14.8 s to a 1 GiB release stack
overflow.

These are the measured causes, in the order worth checking. The trigger index is
in [CLAUDE.md](../../CLAUDE.md#gotchas); correctness failures are in
[Kernel Proof Engineering](kernel-proof-engineering.md).

## Bisect before you theorise

Three attributions for one slow build were propagated in briefs before anyone
measured: operand *size* (a threshold that does not exist), nesting *depth*
(refuted by a flat construction that failed identically), and a stack *envelope*
overrun (plausible, arrived at without testing). Do not reach for any of them.

- **Run it in `--release` first.** Debug frames cost up to 32x release frames, so
  a debug-only margin overrun disappears in release. This separates *a debug-only
  margin problem* from everything else — it does NOT separate a grown
  requirement from a divergent term.
- **Then `scripts/check-kernel-stack-envelope.sh --measure --profile release
  --prelude <p>`.** A real requirement bisects to a passing power of two and
  prints it; a divergent term never finds one.
- **Bisect WITHIN the declaration.** Build a throwaway variant keeping only leg
  1, then only leg 2, and time each. That isolated a whole 77-second regression
  in one experiment.
- **Read the harness's own `finished in Xs`, not wall-clock**, when other lanes
  are running.

## Two unrelated representations of one value force a full unfold

**TWO STRUCTURALLY-UNRELATED REPRESENTATIONS OF THE SAME VALUE FORCE A FULL
`Definition` UNFOLD, AND THE COST LANDS ON EVERY PRELUDE BUILD.** Measured
2026-08-26. `riemannSum_integral_close`'s second leg built
`sample(CReal.integral F a b hab u, e)` and had to show it defeq to a
hand-rebuilt `speedup(raw, K)` term that never mentions `CReal.integral` at
all. The two share no head symbol, so the kernel fully delta-unfolded
`CReal.integral`'s `Definition` -- whose stored value embeds an entire
`regular_of_scaled_cauchy` construction -- **on every prelude build**.

`creal_prelude_builds` went **18.7 s -> 92.6 s** from that one declaration,
and because dozens of tests build a prelude, the full `--lib` sweep went from
802 tests in 316 s to **timing out at 1700 s with 95 tests done**. An
unrunnable gate blocks all publication, including other lanes' finished work.

**The fix is to make the two sides the SAME `ExprId`, not merely defeq.**
Route through the already-checked theorem (`integral_converges` via
`exists_elim`) instead of re-deriving its witness triple by hand: the
eliminated witness builds the value with the identical `const_app` recipe, so
the definition is never unfolded. Restored to **18.4 s**, statement unchanged.

**This is NOT the concrete-witness/lazy-delta family above**, and treating it
as one wastes the diagnosis -- everything here was symbolic, with no concrete
`Nat` partial evaluation. Nor is `--release` the discriminator. What found it
was **bisecting WITHIN the declaration**: build a throwaway variant keeping
only leg 1, then only leg 2, and time each. Leg 1 was 18.35 s, leg 2 alone was
95.15 s -- the whole regression, isolated in one experiment.

The general rule: **when a proof must relate a value produced by a
`Definition` to a value you rebuilt yourself, reach for the theorem that
already names it.** If a prelude build slows by a multiple, bisect the
declaration by legs before reaching for any of the documented families.


## A symbolic test can be pathological — delete it and say so

**A SYMBOLIC TEST CAN BE PATHOLOGICAL, AND THE RIGHT MOVE IS TO DELETE IT AND
SAY SO.** Measured 2026-08-26: a lane added an extra symbolic negative control
that built fvars from a separate `IntDev`; it pegged one core at **10.7 GB RSS
for over twelve minutes** before being killed. Not slow — pathological. The
lane removed the test, recorded it in the commit message, and did **not**
investigate. That is correct: the real verification is `creal_prelude_builds`
plus the environment-derived coverage assertion, and a hanging test in the
suite is worse than a missing one. If a test behaves this way, delete it,
say so, and move on.


## A concrete witness can cost the kernel more than a symbolic one

**A CONCRETE WITNESS CAN COST THE KERNEL MORE THAN A SYMBOLIC ONE, and the
symptom is unbounded WORK rather than a stuck term.** Measured 2026-08-26.
`declare_e_converges` built its per-`n` proof against the **concrete**
`k_final` (an unreduced `Nat.mul`/`Nat.add` expression) and let
`exists_intro`'s argument check decide `speedup_term(n) =?= seq(e, n)`. The two
sides have different head symbols, so lazy-delta unfolds **both in lockstep**
-- and because `k_final` is concrete enough for `Nat.mul`/`Nat.add` to
*partially* fire against the still-symbolic `n`, that drives a partial
evaluation of `sumRange` at a symbolic index which never re-synchronises.

`declare_converges_of_cauchy`, the existing pattern it was copying, never hits
this: its `K` stays a **bound variable** all the way to `add_declaration`, so
the same arithmetic stays stuck against two free variables and simply never
runs. **Build generically over a bound `(k, h)` and substitute the concrete
pair only in the final Pi-application.**

The cost is not subtle. The parent commit built the prelude in **14.8 s on the
default 2 MiB stack**; the defective one overflowed **1 GiB in RELEASE**,
against a measured release budget of 131,072 bytes for `creal` -- roughly
8,000x over.

**The dangerous part is the misdiagnosis, not the bug.** A stack overflow here
is indistinguishable from the resource limit that ADR-0584 measures, and the
coordinator had *just* measured `creal` at exactly zero margin -- a perfectly
plausible explanation, arrived at without testing. Wrapping the test in a
bigger stack made it *look* fixed. **A wrapper that silences a real failure is
worse than no wrapper**, and it is the checker-that-cannot-fail defect arriving
by a route none of the existing guards cover.

The first test is one command and costs nothing: **run it in `--release`.**
Debug frames cost up to 32x release frames, so a debug-only margin overrun
disappears in release. Do that BEFORE characterising any stack overflow, and
bisect against the parent commit rather than reasoning about which
explanation fits.

**BUT `--release` IS NOT SUFFICIENT, AND THIS FILE USED TO SAY IT WAS.**
Measured 2026-08-28: `reconstruct::arithmetic::monomial_bound` aborted with
SIGABRT **in release**, and it was NOT runaway recursion — it was a finite,
bounded requirement that had simply grown past the default in **both**
profiles. `creal` went debug 2,097,152 -> 16,777,216 and release 131,072 ->
8,388,608 in two days of ordinary development.

So the rule separates *a debug-only margin problem* from *everything else*.
It does **not** separate a grown requirement from a divergent term, and
treating "fails in release" as proof of non-termination sends you hunting a
bug that does not exist. (I made exactly that call and reported it as fact.)

**The command that actually decides it is `--measure`:**

    scripts/check-kernel-stack-envelope.sh --measure --profile release --prelude <p>

A real requirement bisects to a passing power of two and prints it. A
divergent term never finds one. Then raise the row in
`artifacts/kernel-stack-envelope.tsv` and say what grew — and note that
`--check` was **RED on `main` and nobody had run it**, so it will not tell
you on its own.

Two second-order traps this incident exposed:
- **An overflow aborts the process, so only the FIRST affected test is
  named.** Four more suites were failing for the same reason and reported
  nothing. Do not scope the fix to the test that appeared in the log.
- **A prelude built on the CALLING thread inherits a `#[test]`'s 2 MiB.**
  The fix belongs in the constructor (one 256 MiB worker thread covering
  every call site), not in a wrapper around each test — otherwise a
  *consumer's* process aborts at the front door.


## One bad declaration poisons the shared prelude build

**ONE BAD DECLARATION POISONS THE SHARED PRELUDE BUILD, SO THE FAILURE COUNT
TELLS YOU NOTHING ABOUT HOW MANY THINGS ARE BROKEN — AND A NARROW FILTER CAN
MISS IT ENTIRELY.** Measured 2026-08-28: one wrong `choose_le_succ` base case
produced `TypeMismatch` across **all 95** `nat_prelude::` tests, because every
one of them builds the same prelude. Nothing in that output distinguishes "95
broken theorems" from "one broken theorem"; the same shape has been seen at
230 failures from a single name collision.

Two consequences:

- **Bisect by toggling declarations, not by reading failures.** The lane found
  it by commenting out each of the five `declare_choose_*` calls in
  `declare_choose_all` one at a time against a single fast test. Serial, cheap,
  and it names the culprit exactly; reading 95 identical `TypeMismatch`es does
  not.
- **A single-test filter is not a gate for a prelude change.** The same lane
  ran `--lib <that one theorem>` and it PASSED, then the full `nat_prelude::`
  sweep failed. **The mechanism for that is NOT established** — `prelude_cache`
  is process-wide and in-memory (ADR-0464), so it cannot carry state between
  two `cargo test` invocations, and the lane's cache explanation does not hold
  up. Do not propagate it as fact. What IS established is the observation, and
  the rule it supports: after touching any `declare_*`, run the whole
  `<prelude>::` sweep and confirm a NONZERO count, never a filtered subset.


## Every `Nat` numeral this prelude builds is unary

**EVERY `Nat` NUMERAL THIS PRELUDE BUILDS IS UNARY, SO THE KERNEL'S BINARY
LITERAL FAST PATH NEVER FIRES — AND THAT, NOT NESTING DEPTH, IS WHY LARGE
CONSTANTS BLOW THE BUILD BUDGET.** Found 2026-08-27 by a lane chasing a
587 s prelude build, verified independently by reading the three sites:

- `NatOps::num` (`nat_prelude/ops.rs`) is `let mut e = self.zero(); for _ in
  0..n { e = self.succ(e); } e`. `13125` is 13,125 nested `succ`
  applications.
- `Kernel::reduce_nat_succ` (`tc.rs`) whnfs its argument and requires
  `ExprNode::Lit(Lit::Nat(_))`. **`Nat.zero` is a `Const` with no
  definition, so it never whnfs to `Lit::Nat(0)`** — `reduce_nat_succ`
  returns `None` on `succ (Const Nat.zero)` and the tower never collapses
  bottom-up.
- `Kernel::reduce_nat_binop` — the accelerated `add`/`sub`/`mul`/`div`/`mod`/
  `gcd`/`pow`/`beq`/`ble` — needs **both** arguments to whnf to `Lit::Nat`.
  They never do.

So every `gcd` and division inside `Rat.normalize`, and all index arithmetic
in `creal`, runs by unary recursion, and cost is superlinear in the largest
magnitude **formed** — not in the depth of the expression and not in the
operand count.

The A/B that isolates it on one variable: bounding an intermediate at
`8/75 <= 7/64` (largest `Nat` **525**) instead of the exact
`512/1875 <= 7/25` (largest `Nat` **13,125**) took a prelude build from
**587.02 s to 113.46 s**.

**Two earlier attributions for the same symptom were WRONG and were
propagated in briefs before this was measured** — operand *size* alone (a
60,000 threshold that does not exist; the real run's max operand was 46,875
and was fine) and *nesting depth* (refuted by a flat construction that
failed identically). Do not reach for either.

**MEASURED 2026-08-28, AND THE SCOPE IS NARROWER THAN THIS ENTRY FIRST
IMPLIED.** `examples/nat_numeral_whnf_probe` times the same term built both
ways and classifies the reduct, so a run that reduced nothing cannot look
fast:

    mul 25 21     2,304 us  ->    11 us      210x
    mul 125 105  52,399 us  ->    10 us    5,240x
    gcd 512 1875  25.6 s    ->    16 us  1,600,000x
    div 13125 25  STACK OVERFLOW ->10 us      --

So the mechanism is real and catastrophic **when a declaration forms a large
magnitude**. But converting EVERY prelude numeral to `Lit::Nat` moves the
`creal` prelude build only 14.91 s -> 14.23 s (4.6%, with a contended re-run
putting the unary side *faster*) — **noise exceeds effect.** The prelude
build as a whole was never spending its time here.

Two consequences. First, do not reach for a global numeral change to relieve
a slow build; it is measured at zero (ADR-0614, proposed and NOT adopted —
the cost is 388 fact `formal.statement` strings whose rendering would drift
silently). Second, the remedy is local and it is the one the pi rung-2 case
proved: **keep formed magnitudes small**, which took one declaration from
587 s to 113 s.

What to do about it, in order:
- **Keep formed magnitudes small.** Choose intermediate bounds that land on
  the value the next step needs rather than the exact quotient. In the case
  above `7/64` is *forced* — it is `(7/25)/(8/5)^2` — and the remaining
  factors ride `mul_le_mul_of_nonneg_left` instead of an evaluation.
- **Do not reach for `Rat.ble`'s computational close on large operands.**
  Closing `le` by `Eq.refl` at `Bool.true` is a SMALL-NUMBERS tool. It
  settles `64/25 <= 3` cheaply and does not reach `-13/1875`; two
  independent constructions both blew the budget through it.
- Note the kernel's binary literal machinery EXISTS and is tested
  (`nat_literal_semantics`, `nat_literal_arithmetic`, `nat_literal_bignum`,
  `nat_literal_to_constructor`, `NatOffset`). It is simply not what the
  prelude constructs.


## `cargo-serialized.sh` takes a host-wide flock, so timing measures the queue

**`scripts/cargo-serialized.sh` TAKES A HOST-WIDE FLOCK, so a TIMING run
under lane contention measures the QUEUE.** A lane lost a 600 s run to the
wall this way with nothing to show. Read the test harness's own
`finished in Xs` rather than wall-clock, or run the prebuilt binary under
`target/debug/deps/` directly, which takes no lock. Use the wrapper for
CORRECTNESS, the prebuilt binary for MEASUREMENT.


## A negative control must differ in a SMALL term

**A NEGATIVE CONTROL MUST DIFFER IN A *SMALL* TERM, or the control itself is
the pathology.** Measured 2026-08-27. A lane's control transposed two whole
`riemannSum`s in a conclusion and asserted `!Kernel::def_eq` for
non-vacuity. Both sides are then FAILING defeq checks across different
endpoints, which forces full unfolds of `sumRange`'s `Nat.rec` over a symbolic
`succ m`: **>300 s and RSS 2.0 -> 3.1 GB with no sign of stopping**, against
**34.9 s** for the positive check on the identical proof term. A *failing*
defeq is unbounded in a way a succeeding one is not -- there is no early exit.

The replacement varies only the term count in the bound (`ofNat m` vs
`ofNat (succ m)`), leaving the left-hand side the identical `ExprId`. Equally
discriminating (false at `m := 0`) and free. This pairs with the standing rule
that a pathological test is worth deleting rather than debugging: here the
pathology was in the *control*, not the subject.


