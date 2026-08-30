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

Detail moved to [`../notes/357-prime-char-mirrors.md`](../notes/357-prime-char-mirrors.md).

