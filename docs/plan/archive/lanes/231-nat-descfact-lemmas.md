# Lane: nat-descfact-lemmas — four descFactorial/factorial facts, all landed

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, nat-descfact-lemmas, 2026-08-28).** All four
target facts landed: `descFactorial_self`, `descFactorial_le`,
`self_le_factorial` (all new proofs), and `descFactorial_of_lt` (a status
flip — the declaration already existed and already stated the fact's
`formal.statement` verbatim; nothing needed but evidence + the status flip).
`descFactorial_eq_factorial_mul_choose` (landed by a prior lane) was the main
tool for the first two; `self_le_factorial` is a direct induction,
independent of that bridge. Skipped `F:ml430-mutation-7afa5ec620720a1501bf349d`
per brief (a deliberately-perturbed negative control in this family).

Kernel gate: `cargo test -p axeyum-lean-kernel --lib nat_prelude` — 119
passed, 0 failed (was 116 before this lane; +3 new theorems +1 test — see
below). `python3 scripts/validate-facts.py`: 0 errors, `open` 85 -> 84,
`proved` 1824 -> 1825. `cargo fmt`/`clippy --all-targets` clean on the
touched files.

Nothing was kernel-rejected. Every proof term type-checked on the first
attempt against `Kernel::add_declaration`; no misdiagnosis, no bisect
needed. `nat_prelude` inventory count (`definition_names`/`theorem_names`
sum, `the_build_is_deterministic`'s own pin): 85+429=514 before this lane,
85+432=517 after (+3 theorems: `descFactorial_self`, `descFactorial_le`,
`self_le_factorial`; 0 new definitions). Both increments were read off the
test's own panic message, never hand-counted.

<!-- plan-section: landed-changes -->

| 2026-08-28 | nat-descfact-lemmas | `Nat.descFactorial_self` (`n.descFactorial n = n!`, via the existing `descFactorial_eq_factorial_mul_choose` bridge at `k := n` plus `choose_self`/`mul_one`); closes `F:ml430-nat-descfactorial-self-899fc0e0` |
| 2026-08-28 | nat-descfact-lemmas | `Nat.descFactorial_le` (monotone in the base for fixed exponent: `k <= m -> k.descFactorial n <= m.descFactorial n`, via `choose_le_choose` + `mul_le_mul_left` + two transports across the bridge equation); closes `F:ml430-nat-descfactorial-le-2b8cc09a` |
| 2026-08-28 | nat-descfact-lemmas | `Nat.self_le_factorial` (`n <= n!`, direct induction on `n` using `one_le_factorial`, independent of the `descFactorial`/`choose` bridge); closes `F:ml430-nat-self-le-factorial-cfdffc69` |
| 2026-08-28 | nat-descfact-lemmas | `F:ml430-nat-descfactorial-of-lt-fbcf5d26` status flip only — `Nat.descFactorial_of_lt` already existed and already matched the fact's `formal.statement` verbatim; attached evidence (kernel-term + axiom-footprint checkers) and flipped `epistemic_status` to `proved`, no new proof work |
