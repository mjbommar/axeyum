# Lane: prime-char-mirrors — the `Mathlib.Data.Nat.Prime.Defs` characterizations

<!-- plan-section: lane-status -->

**DONE (`prime-char-mirrors`, 2026-08-30), CORRECTED AFTER A DISPATCH
COLLISION.** This lane was scoped as "everything in the
`Mathlib.Data.Nat.Prime.Defs` characterization family except five named
facts", which the sibling `prime-dvd-mirrors` lane was assigned. That
sibling went on to declare **fourteen** facts, not five, and landed on
`main` first. Nine of this lane's fifteen original declarations were
exact `NameId` collisions (`DeclarationExists` on merge); a tenth,
`F:ml430-nat-prime-eq-two-or-odd-44a91651`, was a duplicate PROOF of the
same fact under a different Rust name
(`prime_eq_two_or_mod_two_eq_one` vs this lane's
`prime_eq_two_or_odd_mod`) — no compile collision, but pointless
duplication once the sibling's version was already on `main`.

**Surviving from this lane, in `nat_prelude/prime_char.rs`: 5 facts.**

```text
Nat.prime_not_prime_pow_two_le   2<=n -> ~Prime(x^n)
Nat.prime_not_prime_pow_ne_one   n!=1 -> ~Prime(x^n)
Nat.prime_eq_one_of_pow          Prime(x^n) -> n=1
Nat.prime_not_coprime_iff_dvd    ~Coprime m n <-> exists p, Prime p /\ p|m /\ p|n
Nat.prime_mul_eq_prime_sq_iff    Prime p -> x!=1 -> y!=1 -> (x*y=p^2 <-> x=p /\ y=p)
```

The other ten (`prime_one_le`, `prime_pos`, `prime_one_lt`,
`prime_ne_zero`, `prime_ne_one`, `prime_not_dvd_one`,
`prime_eq_one_or_self_of_dvd`, `prime_eq_two_or_odd`,
`prime_eq_two_or_odd_mod`/`prime_eq_two_or_mod_two_eq_one`,
`prime_mod_two_eq_one_iff_ne_two`) are the sibling's, in
`nat_prelude/prime_dvd_mirrors.rs` — untouched, fact files left exactly
as `main` had them (`git checkout --theirs`), never re-flipped.

`nat_prelude::` **203 passed, 0 failed** (`main`'s post-collision
baseline, unchanged in count since nothing here adds a new theorem name
`main` doesn't already have — the surviving 5 were already counted).
`every_nat_declaration_is_checked_and_axiom_free` and
`the_nat_prelude_declares_no_axioms` both pass. `cargo clippy -p
axeyum-lean-kernel --all-targets --all-features -- -D warnings` and
`cargo fmt --all --check` both clean. `validate-facts.py`: **2265
facts, 0 errors** after `check-fact-depends-derived.py --fix`.

## What the merge actually required (for whoever reads this next)

1. Deleted three whole functions from `prime_char.rs` —
   `declare_prime_numeric_bounds` (6 theorems), `declare_prime_parity_facts`
   (3 theorems, including the `_mod` duplicate), and
   `declare_prime_eq_one_or_self_of_dvd` — plus their `NatPrelude` struct
   fields, `name_str` initializers, and their 10 lines in
   `nat_prelude_tests.rs`'s `theorem_names`. None of these were git merge
   CONFLICTS in the field/name_str sections — the two lanes inserted at
   different line numbers, so git merged both blocks in additively,
   leaving duplicate Rust struct field names that only `cargo check` would
   catch. **A clean 3-way merge is not evidence of no collision** when the
   collision is at the semantic level (same field name, different
   insertion point) rather than the line level.
2. **One real call-site bug**, exactly the risk flagged going in: this
   lane's `prime_sq_factor_case` called the survivor
   `prime_eq_one_or_self_of_dvd` with the OLD arity-1 argument order
   (`[p_var, prime_hyp, k, dvd_k_p]`, written against this lane's own
   now-deleted arity-1 declaration). The sibling's surviving version is
   arity-2 (`p_var` then `m_var` both auto-bound before the hypotheses),
   so the correct call is `[p_var, k, prime_hyp, dvd_k_p]`. Caught by
   reading the sibling's actual `d.theorem(name, arity, …)` call before
   trusting the shared name — NOT by the type checker, which would have
   rejected it anyway, but only after burning a compile cycle.
3. **Build-order fix**: `declare_prime_mul_eq_prime_sq_iff` needs
   `prime_eq_one_or_self_of_dvd`, which now lives in
   `declare_prime_dvd_mirrors_all` — called much later in the build
   sequence than this lane's original call site. Moved the call to
   immediately after `declare_prime_dvd_mirrors_all(&mut d, &p)?;`.
4. Ten fact files (`F-ml430-nat-prime-{eq-one-or-self-of-dvd,
   eq-two-or-odd (both), mod-two-eq-one-iff-ne-two, ne-one, ne-zero,
   not-dvd-one, one-le, one-lt, pos}`) were `git checkout --theirs`'d
   entirely — confirmed byte-identical to `main` afterward — and never
   re-flipped, per instruction.

Mirror-flip determination, and everything about WHY each surviving fact's
`Nat.Prime` hypothesis is spelled with this prelude's inline primality
predicate rather than a named `Prime`, is unchanged from before the
merge — see the surviving facts' own evidence `notes` fields and
`prime_char.rs`'s module doc.

## Not attempted / not in scope

- Everything in `prime_dvd_mirrors.rs` is the sibling's — not touched
  beyond reading it to fix the call-site bug above.
- `F:nat-totient-*` facts from the same nursery draw were out of scope.
- Nothing in this family was held out.

## Working files

- `crates/axeyum-lean-kernel/src/nat_prelude/prime_char.rs` — now 5
  theorems plus their shared private helpers
  (`prime_pow_ge2_contradiction`, `prime_sq_factor_case`, `prime_two`,
  local `prime_condition`/`prime_parts`/`dvd_intro`/`dvd_elim`/etc.
  copies — see the file's own module doc for why these stay
  per-file-private).
- `crates/axeyum-lean-kernel/src/nat_prelude.rs`,
  `crates/axeyum-lean-kernel/src/nat_prelude/nat_prelude_tests.rs` —
  the duplicate field/name_str/`theorem_names` entries removed.
- 10 fact files reset to `main`'s content (untouched otherwise); 5 fact
  files under `artifacts/facts/F-ml430-nat-prime-{not-prime-pow (both),
  eq-one-of-pow, not-coprime-iff-dvd, mul-eq-prime-sq-iff}.json` remain
  `proved`, owned by this lane.
