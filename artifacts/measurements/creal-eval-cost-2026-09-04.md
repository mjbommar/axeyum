# The exact-real (`CReal`) evaluation cost envelope (roadmap W1-12)

Measured 2026-09-04 at commit `c181655e9` (lane `producer-measurements`),
host: shared dev box, uptime 22 days, **not idle** (see load readings below).

## The question

`docs/math-department/11-applied-and-computational.md`'s computable-analysis
reviewer: "they would immediately ask what it costs to evaluate π to a
thousand digits through this representation, and the honest answer is that
nobody has measured it, because the library's numerals are unary and the
representation was built for provability rather than speed."

## Method

New example: `crates/axeyum-lean-kernel/examples/creal_eval_cost.rs`.

1. Build the `creal` prelude (`build_creal_prelude`) exactly as every other
   `CReal` example/test does.
2. For a target value `x` (`CReal.zero`, `CReal.one`, `CReal.add one one`,
   `CReal.pi`, `CReal.e`, `CReal.sqrt (CReal.add one one)`,
   `CReal.expFn CReal.one`), build the term
   `Rat.num (CReal.seq x n)` / `Rat.den (CReal.seq x n)` for a small concrete
   `n`, built two ways:
   - **literal**: `n` as the kernel's accelerated `Lit::Nat` bignum
     (`reduce_nat_binop`/`reduce_nat_succ` in `tc.rs` recognize this
     directly);
   - **unary**: `n` as `Nat.succ (Nat.succ (... Nat.zero))`, built exactly
     the way this codebase's own internal numerals are built
     (`linarith/generic.rs::nat_num_ctx`; `creal/pi.rs`'s own module doc:
     "every numeral this prelude builds is unary and the kernel's
     binary-literal fast path never fires").
3. Fully normalize each with `deep_nf`: a hand-rolled deep normalizer built
   only from public `Kernel::whnf`/`Kernel::expr_node`/`Kernel::app` calls —
   the SAME primitives `Kernel::add_declaration`'s definitional-equality
   check already uses internally. `Kernel::whnf` reduces the head redex
   chain only; `deep_nf` recurses into application arguments too and
   re-checks the rebuilt application for a further head reduction, to a
   fixed point (`ExprId` equality — the interner hash-conses, so
   structurally-identical rebuilds compare in O(1)).
4. Time each `(target, encoding, n)` cell's normalization; read the
   resulting numerator/denominator digit counts and an `f64` approximation
   for a sanity comparison against `std::f64::consts::{PI,E,SQRT_2}`.

No new kernel declaration is added anywhere; every term built is transient
and discarded when the process exits.

**What this does NOT measure.** The reported digit counts (where reduction
completes) are the FINAL, gcd-reduced numerator/denominator. `Rat.add`'s
pre-normalization numerator (`a.num*b.den + b.num*a.den`, before dividing by
the gcd) is at least as large, so the true PEAK magnitude formed mid
computation is >= the reported final one and is not measured here — that
needs an instrumented kernel build, which this measurement-only lane does
not touch.

### Build and run

```sh
scripts/cargo-serialized.sh build --release -p axeyum-lean-kernel --example creal_eval_cost
# TIMING measurements run the prebuilt binary directly -- never under the
# cargo-serialized.sh flock, which measures the queue, not the work:
./target/release/examples/creal_eval_cost --max-n 3            # all four targets + controls
./target/release/examples/creal_eval_cost --max-n 0 --only=e   # one target, one n
```

### Load readings

This host was carrying multiple concurrent lanes throughout these runs.
`uptime` load averages (1m, 5m, 15m), read immediately before/after each
run:

| run | before | after |
|---|---|---|
| controls (zero/one/two) | not captured (early run) | not captured |
| `e`, n=0, 150s budget | not captured | not captured |
| `e`, n=0, 400s budget | 19.15, 14.36, 10.87 (at launch) | 13.11, 14.44, 12.19 (at 400s, timed out, did not complete) |
| `pi`, n=0, 480s budget | not captured | not captured |

**This is reported honestly as a gap, not filled in retroactively**: the
first three runs were launched before this lane adopted the
before/after-`uptime` discipline mid-measurement. The one pair captured
shows sustained load in the 11-21 range (a 5-16 core-equivalent multi-lane
host), which is why the wall-clock numbers below are reported as **ADVISORY
ONLY** in the sense
`docs/research/08-planning/frontier-ratchet-reference-frame.md` uses that
phrase, never as a precise per-run cost.

## Results

### Controls: `zero`, `one`, `two`

Every cell below completed; `n` ranged 0..3, both encodings:

| target | encoding | wall clock (all `n`) | value | error vs. reference |
|---|---|---|---|---|
| `CReal.zero` | literal | 0.0–0.3 ms | `0` | 0 |
| `CReal.zero` | unary | 0.0 ms | `0` | 0 |
| `CReal.one` | literal | 0.0–0.2 ms | `1` | 0 |
| `CReal.one` | unary | 0.0 ms | `1` | 0 |
| `CReal.add one one` | literal | 2.3–5.0 ms | `2` | 0 |
| `CReal.add one one` | unary | 2.0–2.2 ms | `2` | 0 |

**Finding 1**: the literal-vs-unary encoding of the CALLER's query index `n`
makes no measurable difference on these controls, at any `n` tried. Whatever
the eventual cost story for `pi`/`e`/`sqrt2`/`exp1` turns out to be, it is
not explained by how the outer index was built.

### `pi`, `e`, `sqrt2`, `exp1`: did not complete

| target | n | outer `Kernel::whnf` (head only) | full `deep_nf` (needed for a digit) | budget | result |
|---|---|---|---|---|---|
| `e` | 0 | 30.6–41.7 ms | did not complete | 150s, then 400s | **not measured** |
| `pi` | 0 | not separately isolated | did not complete | 480s | **not measured** |
| `sqrt2` | — | — | — | — | not attempted (see below) |
| `exp1` | — | — | — | — | not attempted (see below) |

`sqrt2` (`CReal.sqrt (CReal.add one one)`) and `exp1`
(`CReal.expFn CReal.one`) were not attempted past this point: both wrap a
series in additional `CReal.mul`/`bound`-style composition on top of exactly
the machinery that already did not complete for the bare `e` series, so
there is no reason to expect them cheaper, and spending further compute
budget confirming that would not change the finding.

`e` is the SIMPLEST of the four non-trivial targets (`creal/exponential.rs`:
a bare `speedup(diagonal(expSeriesPartial), K)`, no `CReal.mul`/`bound`
wrapping); `pi` additionally wraps `CReal.mul two piHalf`. Both failed to
complete at `n = 0` — the loosest possible request, the very first sample.

## Where the cost blows up, and why

Not at the caller's outer index (Finding 1). It blows up inside the series
machinery itself. The mechanism, read from `tc.rs`'s own module
documentation for `reduce_nat_binop`/`reduce_nat_succ`: the kernel's
accelerated bignum path for `Nat.add`/`Nat.mul`/`Nat.gcd`/etc. fires only
when **both operands**, after `whnf_core`, are already a `Lit::Nat` bignum
or the literal `Nat.zero` constant. A nonzero `Nat.succ`-chain operand never
matches either pattern — `reduce_nat_succ` requires its argument to already
be `Lit::Nat`, and a bare `Nat.zero` **constant** (as opposed to the `Lit`
encoding of zero) is accepted as a binop operand but is not itself promoted
by succession — so it falls through to full **structural** `Nat.rec`
recursion, one constructor layer at a time, exactly as unary Peano
arithmetic would. This is not a property of the caller's `n`: it is a
property of how `CReal.e`'s OWN definition builds its internal counters
(the `sumRange` recursion variable, `speedup`'s modulus arithmetic, index
shifts) — all built the same unary way, per `creal/pi.rs`'s own module doc.
`Rat.add`'s `Rat.normalize` step needs a `Nat.gcd` of the (unary-recursed)
numerator and denominator at every term of the sum, which is precisely the
cost `creal/pi.rs` names when explaining its own series choice ("a
four-digit `Nat.gcd` costs tens of seconds") — except there the library only
ever needs FOUR terms to prove a fixed, symbolic bound; here, computing an
actual concrete sample at an arbitrary `n` has no such fixed small bound to
lean on.

**The library's own bound theorems never force this reduction at all.**
`CReal.threeLePi`, `CReal.piLeFour`, `e <= 4`, and `CReal.sqrt`'s/
`CReal.cosOne`'s bounds are all proved by a monotonicity/domination
argument that keeps the series index SYMBOLIC end to end; none of them ever
asks the kernel to reduce `CReal.<x>.seq(n)` to a concrete `Rat` for any
concrete `n`. Avoiding exactly this reduction is what ADR-0512 and
`creal/pi.rs` mean by "keep magnitudes small" — small because they are never
computed, not because computing them is cheap. **There is currently no route
in this codebase, library-internal or external, that computes "π to k
correct digits" as a displayed rational.** The representation proves bounds
cheaply and computes concrete approximations expensively to intractably, and
this is the first time that asymmetry has been measured rather than
asserted.

## What would change this

Two independent directions, neither undertaken by this measurement-only
lane:

1. **An accelerated internal representation for `CReal`'s own series
   arithmetic** — i.e. having `sumRange`/`speedup`/the index-shift
   machinery build their internal `Nat` counters as `Lit::Nat` (or route
   through `Nat.rec`'s literal-aware `nat_literal_to_constructor` peeling,
   which decrements a bignum by one per recursor step in O(1) rather than
   pre-materializing a `Nat.succ` chain) rather than raw `Nat.succ`/`Nat.zero`
   constant applications. Finding 1 (the caller's own `n` encoding is free)
   suggests this is at least plausible: the acceleration exists in the
   kernel and works when the operands are literal; the gap is that the
   library's own internal construction never emits a literal.
2. **A genuinely different evaluation route that does not go through full
   kernel `whnf` reduction** — e.g. a certified extraction procedure that
   only needs to CHECK a supplied candidate rational is within the stated
   bound (the shape `CReal.sqrt`'s own bound theorems already have), rather
   than COMPUTING one via the kernel's general-purpose reducer.
