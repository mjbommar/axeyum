# Notes: 250-nat-fastfib-minfac

Detail moved out of [`../status/250-nat-fastfib-minfac.md`](../status/250-nat-fastfib-minfac.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

1. **`Nat.minFacAuxMinimal`** (`min_fac.rs`): `∀ fuel n candidate, Le 2
   candidate → Eq (add candidate fuel) n → (nothing in [2,candidate) divides
   n) → nothing in [2, minFacAux fuel n candidate) divides n`. Proved by
   induction on `fuel`, with `n`/`candidate` generalized inside the motive —
   the same seed-generalization `fibonacci.rs`'s `fib_aux_add_two_gen` uses,
   for the same reason (the induction hypothesis is needed at a DIFFERENT
   `candidate` than the one the goal states). The succ case needs `candidate`
   expressed as `succ (pred candidate)` (via `pos_implies_succ_pred`, from
   `2 ≤ candidate`) because `div_mod_exec` requires a positive divisor spelled
   as a successor; the actual divisibility decision is a `Bool.rec` case
   split on `beq (mod n candidate) zero` with a DEPENDENT motive carrying the
   selector's own equation — the identical technique `primes.rs`'s
   `least_divisor_search` succ case uses to decide `succ j ∣ m`.
2. **`Nat.min_fac_minimal_of_two_le`**: specializes (1) to `minFac` itself at
   `n ≥ 2`, by unwinding `minFac`'s two `bool_select_nat` boundary wrappers
   (`is_zero`, `is_one`) — both provably `false` since `2 ≤ n` rules out
   `n = 0`/`n = 1` (via `zero_lt_of_ne_zero`/`ne_of_lt`/`ne_symm`/
   `beq_eq_false_of_ne`) — down to `minFacAux (n-2) n 2`.
3. **`Nat.coprime_of_lt_min_fac`**: `∀ n m, Not (Eq m zero) → Lt m (minFac n)
   → Eq (gcd n m) one`. Case split on `n`: `n = 0` (`minFac 0 = 2`, so
   `m < 2 ∧ m ≠ 0` forces `m = 1`, and `gcd 0 1 = 1` directly), `n = 1`
   (`minFac 1 = 1`, vacuous), `n ≥ 2` (the real argument, exactly as
   `241`'s handoff sketched: if `g := gcd n m ≠ 1`, trichotomy via
   `lt_or_eq_of_le` at `(1, g)` gives `g ≥ 2`; `g ∣ n` and `g ≤ m < minFac n`
   — the last step via `le_of_dvd` on `g ∣ m` — contradicts (2)'s
   minimality).

New fact `F:nat-coprime-of-lt-minfac` (NOT the `ml430` id) records this;
`F:ml430-nat-coprime-of-lt-minfac-0f79bdba` stays `open`, correctly.

**One real bug, one real infrastructure trap, both from bisecting:**

- Placing `declare_min_fac_minimal_all` beside `declare_min_fac_all` (its
  natural home) produced `UnknownConst` across the WHOLE shared prelude
  build — a forward reference, since `Nat.add_sub_cancel_of_le`
  (`diagonal.rs`) is declared far later in `build_nat_prelude`'s dispatch
  order. Confirmed by toggling the three new `declare_*` calls one at a time
  against the single fast `min_fac_computes_the_least_prime_factor_with_negative_controls`
  test (per CLAUDE.md's standing rule for this failure shape) rather than
  reading the ~230-failure cascade. Fixed by moving the dispatch call to the
  very end of `build_nat_prelude`, after everything it depends on.
- The first working `declare_coprime_of_lt_min_fac` attempt used
  `cases_lt_bound` to split on `m` inside the `n = 0` branch and then tried
  to apply the OUTER `ne : Not (Eq m zero)` hypothesis to a proof of
  `Eq zero zero` built for the LITERAL `m = 0` sub-case — a straight type
  error (`TypeMismatch`, `expected: Eq _fvar.1 zero`, `got: Eq zero zero`),
  because `cases_lt_bound`'s branches are proofs about the LITERAL, with no
  access to hypotheses about the real variable being split. The actual
  argument needed is `lt_or_eq_of_le` + `or_cases` directly on `m` itself
  (derive `m ≤ 1` from `m < 2`, then split `m < 1` — contradicts `ne` — from
  `m = 1` — direct), never substituting `m` away.

Debugging technique worth naming: `Fixture::new`'s `build_nat_prelude(&mut
k).expect(...)` panic prints only raw `ExprId` numbers on a `TypeMismatch`.
Temporarily patching it to `k.render_lean` both sides (removed before the
final commit) turned an opaque `TypeMismatch { expected: ExprId(35828), got:
ExprId(9488) }` into the two lines above in one run, instead of several
rounds of guessing.

## `F:ml430-nat-fastfib-eq-cde11774` — mirror stays `open`, precise reason, not attempted

Read Mathlib's actual source at the pinned commit (`c5ea0035…`,
`Mathlib/Data/Nat/Fib/Basic.lean`), not inferred from the fact's prose:

```
def fastFibAux : ℕ → ℕ × ℕ :=
  Nat.binaryRec (fib 0, fib 1) fun b _ p =>
    if b then (p.2 ^ 2 + p.1 ^ 2, p.2 * (2 * p.1 + p.2))
    else (p.1 * (2 * p.2 - p.1), p.2 ^ 2 + p.1 ^ 2)
def fastFib (n : ℕ) : ℕ := (fastFibAux n).1
```

Two independent obstacles, either alone enough to force "structurally
different `def`":

1. **`Nat.binaryRec`** recurses on `n`'s BINARY representation (roughly,
   halving at each step via `bodd`/`div2`), not on the unary predecessor
   `Nat.rec` provides. This kernel has no such combinator; building one
   needs well-founded recursion over a genuinely new measure (the machinery
   exists in principle — `lt_well_founded`, `ops.rs` — but nothing in this
   prelude drives a *log-time* recursion with it today).
2. **`fastFibAux` returns `ℕ × ℕ`**, and — per `fibonacci.rs`'s own module
   doc — "this kernel has no tuple type (confirmed today when a sibling lane
   could not reify a 2×2 adjugate)". `fibAux`'s existing curried-accumulator
   trick (two ordinary `Nat` PARAMETERS instead of a pair) works for
   `fibAux`'s STRUCTURAL recursion because currying and a step function
   compose the same way a pair-projection would; it does NOT by itself solve
   binary recursion, since the thing being recursed on (the bit pattern of
   `n`) still needs a well-founded device, not just an accumulator shape.

So building a genuine `Nat.fastFib` here is a real keystone (a new
well-founded/log-time recursion combinator over `Nat`'s bits, applied to a
pair-shaped state via the curried-accumulator device once that combinator
exists) — not a same-day slice, and NOT attempted. Two things that would
make the eventual attempt cheaper, found while reading `fibonacci.rs`:

- **The doubling identities are already free.** `fib_add` is proved:
  `fib (m+n+1) = fib m * fib n + fib (m+1) * fib (n+1)`. At `m := n`, this
  IS Mathlib's `fib_two_mul_add_one` (`fib (2n+1) = fib(n+1)^2 + fib(n)^2`)
  verbatim — a two-line corollary (substitute, no new induction). Mathlib's
  `fib_two_mul` (`fib (2n) = fib n * (2*fib(n+1) - fib n)`) needs the same
  substitution plus `Nat.sub`-truncation care (`2*fib(n+1) ≥ fib n` always
  holds via `fib_le_fib_succ`, so no truncation actually fires, but the
  proof has to say so). Neither was built this lane — no fastFib
  construction needs them yet without the recursion device — but a lane
  attempting fastFib should reach for `fib_add(n, n)` first rather than
  re-deriving the doubling identities from scratch.
- **Do NOT build a trivial `fastFib := fib`** to close this cheaply. The
  fact's `formal.statement` (`n.fastFib = Nat.fib n`) is purely extensional
  and such a definition would technically satisfy it by `refl`, but it
  would not be a mirror of anything Mathlib's `fastFib` IS — an alias isn't
  "fast" in any sense the source cares about, and per the mirror-flip
  criterion this would be exactly the kind of checker-that-cannot-fail this
  repository's own gotchas warn against (satisfying a proposition while
  discarding the content the definition was supposed to carry).

## Verification run

- `cargo test -p axeyum-lean-kernel --lib nat_prelude::` (targeted filter):
  **128 passed, 0 failed** (was 127 before this lane, per `241`'s own
  count). Includes `every_nat_declaration_is_checked_and_axiom_free`,
  `the_nat_prelude_declares_no_axioms`, `the_build_is_deterministic`, and
  the new `coprime_of_lt_min_fac_applies_at_a_concrete_instance` (concrete
  discriminating instance `n=25, m=4`, `minFac 25 = 5`, plus a negative
  control `gcd 25 5 ≠ 1` confirming the strict bound is load-bearing).
- `cargo clippy -p axeyum-lean-kernel --all-targets -- -D warnings`: clean.
- `rustfmt --edition 2024` on every touched file.
- `python3 scripts/validate-facts.py`: **1927 facts, 0 errors** (was 1926).
- `nat_prelude` count: **88 + 457** theorems+definitions rendered by
  `the_build_is_deterministic` (was `88 + 454`; +3 theorems
  `minFacAuxMinimal`/`min_fac_minimal_of_two_le`/`coprime_of_lt_min_fac`, 0
  new definitions), recounted via `theorem_names()`'s own list length, not
  hand-incremented.
- `nat` trusted surface: `nat_axiom_inventory --require-axiom-free nat` →
  `ok: nat trusted surface = 0`, unchanged.
- NOT run: the aggregate `just check`/`./scripts/check.sh` (single-lane
  targeted change, per standing convention — the coordinator re-runs the
  full gate before merging).

## Sizing for whoever attempts `fastFib` next

Not a "quick extension" of this lane — a genuinely separate, larger slice.
In order:

1. A well-founded (or fuel-bounded-by-`n`-with-a-halving-measure) recursion
   combinator over `Nat`, distinct from the structural `Nat.rec` every
   fuel-recursive definition in this prelude uses so far (`minFacAux`,
   `logAux`, `sqrtAux`, `clogAux`, `fibAux` itself are all UNARY-fuel, not
   binary-halving).
2. A curried two-`Nat`-accumulator state (mirroring `fibAux`'s existing
   device) threaded through that recursion instead of a `Prod`.
3. The two doubling identities above, both cheap once `fib_add(n,n)` is
   reached for.
4. The final `fastFibAux_eq`/`fastFib_eq` bridge, by induction along
   whatever the new combinator's own recursion principle is (mirroring how
   `fastFibAux_eq` in Mathlib itself is one `Nat.binaryRec` induction).
