# Diary — quantifier negation duality (lane `quant-duality`), 2026-08-14

One fact, closed end to end: `F:quantifier-negation-duality` went from
`epistemic_status: open` to `proved`, carrying a certificate a checker
re-derives from a fresh parse. Before: `unknown`. After: `unsat` with
`kind=unsat-bool-simplification certified=1 arena=ok`.

```sh
# before                                        # after
; evidence kind=unknown certified=0 ...         ; evidence kind=unsat-bool-simplification certified=1 recheck=na arena=ok ms=0
unknown                                         unsat
```

Both measured with

```sh
cargo run --release -q -p axeyum-bench --example smtcomp_cli -- \
  --evidence artifacts/facts/smt2/neg-quantifier-negation-duality.smt2
z3 -smt2 artifacts/facts/smt2/neg-quantifier-negation-duality.smt2   # unsat, 4.13.3
```

---

## Was the one-rule diagnosis right?

**Half right, and the missing half was the whole difficulty.**

The handoff said the gap needed only a structural `¬∀x.P ↔ ∃x.¬P` rewrite — no
instantiation heuristic, no new decision procedure. The first clause is correct
and that rule is genuinely necessary. The second clause is where it broke: that
rule alone does not close the file, and no amount of tuning it would.

The reason is a property of this IR, not of the mathematics. `parse.rs`'s
`fresh_quantifier_symbol` gives **every binder occurrence its own arena symbol**,
so the benchmark's four `x`s are four *different* symbols:

```
(assert (not (and (= (not (forall ((!q.x.0 U)) (P !q.x.0))) (exists ((!q.x.1 U)) (not (P !q.x.1))))
                  (= (not (exists ((!q.x.2 U)) (P !q.x.2))) (forall ((!q.x.3 U)) (not (P !q.x.3)))))))
```

That is deliberate and good — it is what makes every substituting pass in the
tree capture-safe without a capture check (ADR-0016 chose named binders and
deferred de Bruijn). But it means the duality push turns the first conjunct into

```
(= (exists !q.x.0 . not (P !q.x.0)) (exists !q.x.1 . not (P !q.x.1)))
```

which is *alpha-equivalent*, hash-consed apart, and completely invisible to
`eq.reflexive.v1`. `Op::Forall(SymbolId)` carries the binder *inside the
operator*, so interning can never merge two alpha-variants. Nothing anywhere in
the tree decided alpha-equivalence — I looked; the concept did not exist.

So the fact needed **two** capabilities, not one, and the second was the real
gap.

---

## The rules, exactly

**`quant.negation_duality.v1`** (`crates/axeyum-rewrite/src/canonical.rs`,
`push_negation_through_quantifier`):

```
not (forall x. b)  ->  exists x. not b
not (exists x. b)  ->  forall x. not b
```

**`eq.alpha_equivalent.v1`** (same file, in `rewrite_eq`): `(= p q)` folds to
`true` when `p` and `q` are both quantifiers at the root and
`axeyum_rewrite::alpha_equivalent(p, q)`.

**`alpha_equivalent`** (`crates/axeyum-rewrite/src/alpha.rs`, new) decides
equivalence up to (a) bound-variable renaming and (b) the duality itself,
in one walk that carries a **negation parity**: a `not` on either side flips
the parity, and at odd parity a `forall` matches an `exists` with the bodies
compared at odd parity. It allocates nothing and rewrites nothing.

That last property is why it can live in a *checker*.
`crates/axeyum-solver/src/bool_simplify.rs` — the small self-checking
propositional normalizer behind `Evidence::UnsatBoolSimplification` — now uses
it in its `Op::Eq` case, on Boolean-sorted operands only. It still treats every
quantified subformula as an opaque atom and instantiates, skolemizes and expands
nothing; the one thing it now knows about quantifiers is when two of them are
the same formula written differently. Under that, both conjuncts normalize to
`true`, the outer `not` to `false`, and the assertion is refuted **on the
untouched original terms**.

One plumbing change was needed to make the canonicalizer reachable at all: the
word-level preprocessing pipeline is skipped on quantified queries (it treats
the assertion list as ground, and the trigger/e-matching routes need the
original structure), so the new rules would have been dead code in the solver.
`canonicalization_discharges_quantifiers` in `auto.rs` runs the canonicalizer
from `checked_quantified_fast_path` and adopts the result **only when it is
quantifier-free**, propagating **only `unsat`**. A partial simplification is
discarded, so every query the existing quantifier portfolio handles still
reaches it byte-identical; and because only refutations propagate, the change
cannot turn anything into `sat`.

---

## Which shapes it provably cannot wrongly fire on

The duality *rewrite* is the easy half. It performs **no substitution** — it
flips the operator and wraps the body in one `not`, leaving the body
byte-for-byte the term it was. The classic soundness hazard of quantifier
rewriting is therefore structurally absent rather than handled. It is valid for
any body (nested quantifiers, a vacuous binder, a shadowed binder) and does not
even need a non-empty carrier: over an empty one both sides are `false`.

The *equivalence predicate* is the delicate half, because a wrong `true` there
is a wrong-`unsat` generator. Four traps, each pinned as a negative test in
`alpha.rs`:

1. **The pointer fast path.** `left == right` is not sufficient once a binder
   has been renamed underneath. `forall x. P(x)` against `forall y. P(x)`
   reaches the two bodies as the *same interned term* `P(x)` — yet the second
   leaves `x` free and the two are inequivalent. Fixed by taking the fast path
   only while the correspondence is pointwise identity, and never at odd parity.
2. **The escaping right-hand binder.** A forward-only correspondence accepts
   `forall x. P(y)` against `forall y. P(y)`: the left `y` is unmapped, the right
   symbol is also `y`, so "unmapped symbols must be identical" passes — but the
   right *binds* that `y`.
3. **One-sided shadowing.** This one I shipped into my own working tree and
   caught only on a second read of the finished code, which is worth recording
   plainly: the first implementation looked up the *left* symbol's partner and
   compared it to the right symbol. On

   ```
   left  = forall x. forall z. R(x, z)
   right = forall y. forall y. R(y, y)      -- the inner y shadows the outer
   ```

   the correspondence is `[(x,y), (z,y)]`, so `x` maps to `y` and `z` maps to
   `y`, both argument positions "match", and the predicate returns `true` for two
   formulas that are not equivalent (`right` is `forall y. R(y,y)`). Nothing in
   the near-miss set or the 1048-file sweep generated it — it needs a *repeated
   binder name on one side only*, which my generator's `rename` step could not
   produce. Fixed by matching **binder depth on both sides** rather than symbol
   identity in one direction: a symbol occurrence is matched by *which enclosing
   binder binds it*, and the two depths must agree. `right_hand_shadowing_is_not_alpha_equivalent`
   is the test; I confirmed it fails against the old one-sided lookup before
   keeping it, so it is a real regression guard and not decoration.
4. **Falling through at odd parity.** If the odd-parity case ever reached the
   ordinary structural comparison it would accept `P(x)` against `P(x)` and
   thereby claim a formula is its own negation. Odd parity admits exactly four
   shapes (peel a `not`; `forall`/`exists`; `exists`/`forall`; the two Boolean
   constants) and declines everything else. `a_term_is_never_the_negation_of_itself`
   is the test that would catch a regression here.

Traps 2–4 turned out to be one discipline stated three ways, which is the
lesson: match a symbol by the binder that binds it, on both sides, never by
name and never in one direction only.

Also pinned: binder sorts must match at both parities; swapped bound arguments
(`forall x,y. R(x,y)` vs `forall a,b. R(b,a)`) are rejected; distinct free
symbols are never interchangeable; and inner binders shadow outer ones.

Beyond the unit negatives, three measurements:

* **Six near-misses of the duality**, each confirmed `sat` by z3 first, then
  pinned in `bool_simplify.rs` and driven through the whole front door — axeyum
  returns `sat` on all six, agreeing with z3. Notably `not (forall x. P x)` vs
  `forall x. not (P x)` (quantifier not flipped) and vs `exists x. P x` (body
  not negated), which are the two shapes a sloppy rule accepts.
* **An exhaustive replay** (`crates/axeyum-rewrite/tests/quantifier_duality.rs`,
  `replay_is_exhaustive`): 24 quantified Bool/BV shapes, every assignment to
  their free symbols enumerated, original vs canonicalized compared through the
  IR evaluator, which enumerates the bound domains itself. The canonicalizer's
  own precondition guard samples four assignments; this samples all of them.
  A wrinkle worth recording: the near-miss test originally used `BitVec(2)`
  binders, where *both* misses collapse to constants and prove nothing. They are
  only contingent over a `Bool` binder with body `x ∨ a`, and the test now
  asserts the contingency through the evaluator rather than assuming it.
* **A 1048-file randomized differential sweep** against z3 (four seeds) over
  generated quantified UF formulas of this family — true dualities,
  alpha-variants, near-misses, and unrelated pairs, at nesting depth up to 3
  with deliberate binder shadowing. **0 disagreements**, 33 + 69 axeyum
  `unknown` (incompleteness, not unsoundness).

---

## What else this unlocks

* **Alpha-equivalence exists now.** It was gap #4 in the quantifier survey I ran
  at the start of this lane: "two structurally identical formulas over different
  binder symbols are different terms, and the memo/e-graph layers treat them as
  unrelated." `axeyum_rewrite::alpha_equivalent` is public and cheap, and the
  obvious next consumers are e-matching (two alpha-variant triggers are one
  trigger) and the instantiation memo.
* **The canonicalizer is no longer quantifier-blind.** Before this lane,
  `Op::Forall`/`Op::Exists` sat in the "declined, no local rewrite" arm with
  *zero* rules — not even vacuous-binder elimination. The duality push is the
  standard first step of NNF, so a miniscoping or prenexing pass now has
  somewhere to land.
* **Any propositional tautology over quantified atoms** is now reachable, not
  just this one. That is the class no instantiation heuristic can touch, because
  there is nothing to instantiate.

**What it did not fix.** I swept all 17 `artifacts/facts/smt2/` files: no other
ledger file was `unknown`, so nothing else flipped. Worth a separate lane
though: `neg-barber-no-such-barber.smt2` (`F:barber-no-such-barber`, still in
the import backlog) already decides `unsat` and agrees with z3, but reports
`kind=unsat-uncertified certified=0`. It is a decided fact waiting on a
certificate, not on a capability — a strictly easier task than this one was.

---

## On the ledger entry

`proof_route` is `smt-term-level`, which is the honest choice among the six but
needs its caveat stated, and the fact's `notes` states it: this is **not**
exhaustive evaluation. The carrier `U` is uninterpreted and cannot be
enumerated. What `smt-term-level` and this route share is the trust base — a
refutation at the term layer that trusts neither the bit-blaster, the CNF
encoder, nor the SAT solver, because nothing was blasted. `smt-clausal` would be
a lie (no CNF, no DRAT) and `search-certificate` would be a lie (no witness, no
cover).

`axiom_footprint` is not `[]` and could not be — only `kernel-lean` can deliver
axiom-freedom. It names what is actually trusted rather than copying the
`["axeyum-ir.bool-evaluator", "classical-two-valued-bool-semantics"]` string the
other SMT-route facts carry, because the bool evaluator is not used here:

```json
["axeyum-solver.bool-simplification-normalizer",
 "axeyum-rewrite.alpha-and-duality-equivalence",
 "classical-two-valued-bool-semantics",
 "smtlib-first-order-quantifier-semantics"]
```

The three `checkers` are the producing solve (canonicalizer rewrite to `false`),
`Evidence::check` against a fresh parse (the `bool_simplify` normalizer, no
rewriting at all), and z3 4.13.3. The first two share the `alpha_equivalent`
predicate and differ in everything else; z3 is the only fully independent
implementation, and it is the one that matters.

---

## Gates

All run with a confirmed nonzero test count, since several of these compile to
zero tests without the right feature flag and then exit 0:

| gate | result |
|---|---|
| `cargo test -p axeyum-solver --lib --features full` | 1140 passed |
| `cargo test -p axeyum-solver --features full --test corpus_regression` | 1 passed |
| `cargo test -p axeyum-solver --test progress_frontier --features full -- --test-threads=1` | 10 passed, no frontier movement |
| `cargo clippy --workspace --all-targets --all-features -- -D warnings` | clean |
| `cargo test -p axeyum-rewrite` | 167 passed (25 new in `alpha`, 7 in `quantifier_duality`) |
| `python3 scripts/validate-facts.py` | 52 facts, 0 errors |
| `python3 scripts/fact-frontier.py` | import backlog 10 → 9 |

Two manifest ratchets fired on the new rules and had to be satisfied rather than
edited around, which is the point of them: `every_default_rule_declares_a_guard`
(57 → 59) and `default_rules_fire_on_focused_examples`, which requires a focused
firing example per rule.
