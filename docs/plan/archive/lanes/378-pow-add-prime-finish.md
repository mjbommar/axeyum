# Lane: pow-add-prime-finish — closing the Fermat-prime lemma

<!-- plan-section: lane-status -->

**Your lane's block (`DONE`, pow-add-prime-finish, 2026-08-30).**

`F:ml430-nat-pow-of-pow-add-prime-ab61d0d3` (`Nat.Prime (a^n+1) -> exists m,
n = 2^m`, the classical fact behind Fermat primes) is now `proved`, axiom-free,
`proof_route: kernel-lean`.

**The prior handoff's sizing of the remaining work did NOT hold up, and it is
worth recording why.** It called the odd-factor extraction ("`n` not a power
of two has an odd factor `> 1`") "a genuine well-founded-recursion
undertaking" needing `WellFounded.fix`, on the grounds that every existing
strong-induction construction in this prelude (`gcd`, `bezout_witnesses`,
`modeq`, `wilson`, `exists_prime_factorization`) uses it. That generalization
was wrong: **ordinary structural `Nat.rec` on a FUEL BOUND** (`Le n fuel`,
instantiated at `fuel := n` via `le_refl`) gives the induction hypothesis for
*every* `n' <= fuel-1`, which is exactly the strong-induction shape this
argument needs (recurse on `half := div n 2`, not on `n`'s predecessor). No
`WellFounded`, no `Acc`, no `lt_well_founded` anywhere in the final
construction. `bit_order.rs`'s `msb_exists_of_le_fuel` already uses this exact
pattern for an unrelated predicate (most-significant-bit existence) and was
the template that made the three-lemma bound (`lt_two_mul_of_pos` +
`lt_of_lt_of_le` + `le_of_succ_le_succ`) cheap to find.

**What landed** (`crates/axeyum-lean-kernel/src/nat_prelude/pow_add_prime.rs`,
extended — same file the prior lane started, ~600 new lines):

- `Nat.pow_two_or_has_odd_factor : ∀ n, Ne n zero → Or (∃ m, Eq n (pow 2 m))
  (∃ e t, Eq n (mul e (succ (mul 2 t))) ∧ Ne t zero)` — the odd-factor
  extraction. Splits on `Nat.even_or_odd` (already proved, `powsq.rs`), then
  on `half := div n 2` itself via `cases_zero_succ` (`Nat`'s own
  constructors, no decidability dance): even+half=0 is `n=0` (contradiction);
  odd+half=0 is `n=1=2^0`; even+half=succ hp recurses via the outer fuel `ih`
  and reassembles at `n` (`n = 2*half`); odd+half=succ hp answers directly
  with witness `e:=1, t:=half` (`half ≠ 0` for free, being `succ hp`).
- `Nat.pow_of_pow_add_prime` — the fact itself. The odd branch's witnesses
  `(e,t)` feed the prior lane's `dvd_pow_add_one_of_odd_mul_exp`, exhibiting
  `a^e+1 ∣ a^n+1`; primality (spelled inline, matching
  `primes.rs`/`factorization.rs`'s convention — no `Nat.Prime` predicate)
  forces that divisor to be `1` or `a^n+1`, and both are excluded: `a^e+1 ≥ 2`
  from `pow_pos` (needs only `1 < a`), and `a^e+1 ≠ a^n+1` from `e < n` (needs
  `exponent_of(t) > 1` from `t ≠ 0`, via `mul_lt_mul_left`, combined with
  `pow_injective` and `lt_irrefl`).

Both admitted through the trusted `Kernel::add_declaration` gate, axiom-free
(`Kernel::axiom_footprint` empty, confirmed by
`nat_prelude_tests::every_nat_declaration_is_checked_and_axiom_free` and by
`nat_axiom_inventory --require-axiom-free nat`, exit 0). Verified against a
genuinely FREE `n` (resp. `a, n`) via `Kernel::infer_in` in a real
`LocalContext` — **and** at the concrete instance `n = 6`: the construction's
own recursion, traced by hand (`6=3+3` even; `3=succ(1+1)` odd with witness
`t=1`; reassembled at `n=6` as `e := 2*1 = 2`), produces witness `e=2, t=1`
(`6 = 2*(2*1+1) = 2*3`), matched against an INDEPENDENTLY built statement of
the `n=6` disjunction in the new test
(`pow_two_or_has_odd_factor_and_pow_of_pow_add_prime_apply_at_free_and_concrete_instances`,
`nat_prelude_tests.rs`) via `declare_theorem`, which checks the kernel proof's
type against that exact statement, not merely against SOME provable type — a
genuine re-check, not a tautology. Largest numeral formed anywhere: `6` (the
theorems themselves are proofs about free variables, per the "keep formed
magnitudes small" rule; nothing here forces a large unary tower).

Full `nat_prelude::` sweep: **222 passed, 0 failed** (was 221 immediately
after merging `main`, which itself had landed unrelated `parity`/`sup_laws`
work from sibling lanes; +2 theorems +1 new test net from this lane).
`cargo fmt --all --check` and `cargo clippy -p axeyum-lean-kernel --all-targets
-D warnings` both clean (two `#[allow(clippy::too_many_arguments)]` added for
helpers threading through 8 `ExprId`s, matching the file's existing
convention on `pow_of_pow_add_prime_contradiction`).

**Fact ledger**: `artifacts/facts/F-ml430-nat-pow-of-pow-add-prime-ab61d0d3.json`
flipped `open` → `proved`, `formal.statement` UNCHANGED (only
`formal.kernel_theorem` added, per the "don't overwrite a mirror's statement"
rule), three evidence rows added (two `kernel-term` — one per theorem, each
`checker_command` verified against both the real name and a fabricated one
with `/usr/bin/grep -cE`, anchored — plus one `exhaustive-enumeration` for the
axiom-free trusted surface). `depends_on` populated by
`scripts/check-fact-depends-derived.py --fix` from the proof term's direct
dependencies (13 edges to existing `Nat`/generic facts); `python3
scripts/validate-facts.py` reports **0 errors** over 2270 facts. Partition
checked before touching anything: `artifacts/autogenesis/nursery-v2-extension.json`
has this fact's `"partition": "development"` — never held-out.

**For the next lane**: nothing left on this specific fact. The two new
theorems (`pow_two_or_has_odd_factor`, `pow_of_pow_add_prime`) are reusable —
`pow_two_or_has_odd_factor` in particular is a general-purpose 2-adic
odd/even-part split that could feed other `n = 2^k * odd` arguments
(quadratic reciprocity's `Nat`-side lemmas, further Fermat-number work) without
re-deriving the fuel-induction machinery.

<!-- plan-section: landed-changes -->

| 2026-08-30 | pow-add-prime-finish | `Nat.pow_two_or_has_odd_factor` (odd-factor extraction, ordinary fuel-bounded `Nat.rec`, NOT `WellFounded.fix` — the prior handoff's sizing was wrong) and `Nat.pow_of_pow_add_prime` — closes `F:ml430-nat-pow-of-pow-add-prime-ab61d0d3` (open → proved, axiom-free); 222/222 `nat_prelude::` |
