# Lane: coprime-backlog — close the Nat.Coprime import backlog

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, coprime-backlog, 2026-08-28).** Landed four of
the five targeted facts with real, axiom-free kernel proofs (the brief's bar
was three). The fifth, `coprime_two_left` (`Coprime 2 n ↔ Odd n`), was not
attempted: `Odd` has no existing predicate anywhere in this prelude (grepped;
`Nat.even_or_odd` in `powsq.rs` is the closest primitive, giving a computed
half but no named `Odd`), so it needs a fresh `∃ k, n = 2*k+1` construction
plus a local `two_divisor_dichotomy`-style case split before the coprimality
argument even starts — sizeable enough on its own that it was not worth
risking the other four for. A future lane can lift `two_divisor_dichotomy`
straight from `irrational.rs` (already a local copy there, `perfect.rs`'s own
copy being `fn`-private) and build the `Odd` existential the same way `dvd`'s
own witness predicate is built (`NatOps::dvd_predicate`).

Landed, each a separate declaration in `crates/axeyum-lean-kernel/src/
nat_prelude/primes.rs` (new fields + build-order wiring in `nat_prelude.rs`,
registered in `nat_prelude_tests.rs`'s environment-derived `theorem_names`
so `every_nat_declaration_is_checked_and_axiom_free` covers them):

- `Nat.coprime_of_dvd_left : dvd a1 a2 → gcd a2 b = 1 → gcd a1 b = 1`
- `Nat.coprime_of_dvd_right : dvd b1 b2 → gcd a b2 = 1 → gcd a b1 = 1`
- `Nat.prime_dvd_iff_not_coprime : prime p → (dvd p n ↔ ¬(gcd p n = 1))`
- `Nat.coprime_add_self_right : gcd m (n+m) = 1 ↔ gcd m n = 1`

All four route through `Kernel::add_declaration` (real proof terms, not
assumed), rest on zero axioms (`nat_axiom_inventory --require-axiom-free
nat`: axiom=0 opaque=0 quotient=0), and are wired into
`fact-ledger F:ml430-nat-coprime-of-dvd-left-b0e2aa94`,
`F:ml430-nat-coprime-of-dvd-right-a640bd56`,
`F:ml430-nat-prime-dvd-iff-not-coprime-77854741`,
`F:ml430-nat-coprime-add-self-right-c3ed0f45` (now `proved`, `proof_route:
kernel-lean`, `formal.language: lean4` = actual `render_lean` output, not
the Mathlib surface text -- `Coprime`/`Prime` have no separate name in this
prelude, matching `coprime_of_lt_prime`'s established convention).

Detail moved to [`../notes/184-coprime-backlog.md`](../notes/184-coprime-backlog.md).

<!-- plan-section: landed-changes -->

| 2026-08-28 | coprime-backlog | 4/5 `Nat.Coprime` import-backlog facts proved axiom-free (`coprime_of_dvd_left/right`, `prime_dvd_iff_not_coprime`, `coprime_add_self_right`); `coprime_two_left` deferred, needs a fresh `Odd` construction |
