# Lane: totient-gcd-mul — the last of the three totient mirrors

<!-- plan-section: lane-status -->

**DONE (`totient-gcd-mul`, 2026-08-30).** Closes
`F:ml430-nat-totient-gcd-mul-totient-mul-2e1d13c7` (the last of the three
`ml430` totient mirrors ADR-0668 opened), the largest of the three:

```text
Nat.totient_gcd_mul_totient_mul : ∀ a b,
  totient(gcd a b) * totient(a*b) = totient(a) * totient(b) * gcd(a,b)
```

New file `crates/axeyum-lean-kernel/src/nat_prelude/totient_gcd_mul.rs`, one
`declare_totient_gcd_mul_all(&mut d, &p)?` call wired in after
`declare_totient_dvd_chain_all`. `nat_prelude::` 221 → 222 passed, 0 failed.
`cargo fmt --all --check`-equivalent (`rustfmt --edition 2024` on the touched
files) clean; `cargo clippy -p axeyum-lean-kernel --all-targets -- -D
warnings` clean; `python3 scripts/validate-facts.py`: 2270 facts, 0 errors;
`python3 scripts/check-fact-depends-derived.py --fix`: nothing to fix.

## ADR-0668's sizing: held on two counts, corrected on one

ADR-0668 called this target "the largest of the three; strong induction on
`gcd(a,b)`, base case the already-landed multiplicativity, reducing to a
four-leaf ε truth table where Euclid's lemma is load-bearing (fails at 450
composite triples)."

Detail moved to [`../notes/379-totient-gcd-mul.md`](../notes/379-totient-gcd-mul.md).

