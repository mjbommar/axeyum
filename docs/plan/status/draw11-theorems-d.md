# Lane: draw11-theorems-d — proving theorems from the refilled dispatch queue (ADR-0925 draw 11), continued

<!-- plan-section: lane-status -->

**Done (`DONE`, draw11-theorems-d, 2026-08-31).** Measured 15 dispatchable
at session start (`python3 scripts/check-dispatchable-frontier.py`), as the
brief predicted. Closed **5** `ml430` mirrors, all axiom-free on the Nat
prelude's trusted surface (`nat_axiom_inventory --require-axiom-free nat`
exits 0 throughout, `axiom=0 opaque=0 quotient=0`):

- `Nat.add_choose : (i+j).choose j = (i+j)! / (i!*j!)` — the
  division-normal form of the sibling lane's already-proved
  `add_choose_mul_factorial_mul_factorial`. Converted product → exact
  division via the standard `div_eq_of_mul_eq` route (a third copy of the
  private helper already used in `coprime_lemmas.rs`/`lcm_gcd_lemmas.rs`,
  per this crate's per-file local-helper convention). New module
  `nat_prelude/add_choose_div.rs`.
- `Nat.add_descFactorial_eq_ascFactorial : (n+k).descFactorial k =
  (n+1).ascFactorial k` — no induction needed. Both sides already had a
  closed form through the SAME shared RHS (`k! * choose(n+k) k`) via two
  already-proved bridge lemmas (`desc_factorial_eq_factorial_mul_choose`,
  `asc_factorial_succ_eq_factorial_mul_choose`); just chained through the
  shared term. New module `nat_prelude/add_desc_factorial_asc_factorial.rs`.
- `Nat.ascFactorial_eq_div : (n+1).ascFactorial k = (n+k)! / n!` — chains
  the PRIVATE induction inside `choose_factorial_add.rs`
  (`desc_factorial_add_eq_factorial_at`, exposed `pub(super)` for reuse
  rather than re-derived — this crate's "extract, don't re-derive"
  convention) through `div_eq_of_mul_eq` again, then the
  `add_descFactorial_eq_ascFactorial` bridge above. New module
  `nat_prelude/asc_factorial_div.rs`.
- `Nat.add_factorial_le_factorial_add : i + n! <= (i+n)!` (given `1<=n`)
  and its unconditional-in-`n` corollary
  `Nat.add_factorial_succ_le_factorial_add_succ` — the one genuine
  induction this lane built from scratch (on `i`, `n`/hypothesis held
  fixed). Base case needs `zero_add` on both sides (`Nat.add` recurses
  RIGHT, so `add(zero,x)` is stuck for symbolic `x`); the step needs
  `succ_add` on both sides plus one arithmetic fact
  (`1 <= (j+n)*(j+n)!`) fed through `add_le_add_left` — the
  `factorial(succ x) = mul(factorial x, succ x)` unfold cost NO lemma at
  all, since `factorial_succ` is itself proved by `Eq.refl` (`defs.rs`)
  and `mul` recurses right same as `add`, so the kernel accepts the
  assembled term by defeq at the final check (same technique
  `divisibility.rs`'s existing `factorial_lt_of_lt` already uses). New
  module `nat_prelude/add_factorial_le.rs`. The whole 9-step induction
  type-checked on the first kernel attempt.

Every new declaration has a concrete-instance test in its own file
(`add_choose_div_tests.rs`, `add_desc_factorial_asc_factorial_tests.rs`,
`asc_factorial_div_tests.rs`, `add_factorial_le_tests.rs` — same
merge-hazard convention as `bit_extra_tests.rs`) with a genuinely
discriminating negative control each, and each new name added to
`nat_prelude_tests.rs`'s `theorem_names` in the SAME commit that declared
it. All five facts flipped to `proved` with kernel-term + axiom-footprint
evidence (rendered type compared against `formal.statement` verbatim via
`nat_theorem_inventory`, anchored `grep`), `depends_on` derived via
`check-fact-depends-derived.py --fix`, and statements pinned via
`check-settled-fact-statements.py --write` (caught and fixed an oversight
mid-session: the pins file wasn't included in the first two flip commits;
repaired in a follow-up commit before the third flip, diff purely
additive both times).

**Full `nat_prelude::` sweep after every change: 255 passed, 0 failed**
(251 baseline before this lane's first declaration, +1/+1/+1/+2 for the
four new declarations' tests, no regressions at any step, no wrong
negative controls caught this session). `bash scripts/lane-prepush-fmt.sh`
run before the final commit (7 files reformatted, whitespace-only,
re-verified 255/0 after).

Holdout isolation: `python3 scripts/check-autogenesis-holdout-isolation.py`
→ `PASS`, `held_out=146`, measured before this lane's first fact edit and
again after every subsequent flip — unchanged throughout.
`artifacts/autogenesis/` was never touched.

**10 declined without attempting** (reported precisely, not silently
skipped): the three `int` `gcd`/`Coprime` facts (`exists_gcd_one`,
`exists_gcd_one'`, `gcd_dvd_iff`) and six `Nat` facts were left for TIME,
not because they were sized and found hard —
`F:ml430-nat-add-factorial-lt-factorial-add-7501a8c8` and
`F:ml430-nat-add-factorial-succ-lt-factorial-add-succ-ec0fa8d3` (the
STRICT companions of this session's non-strict pair) ARE sized: the
non-strict induction above does not extend directly, because a `2 <= i`
hypothesis on a symbolic `i` needs `le_dest`+`exists_elim` to peel `i` into
`2 + k` before a `k`-indexed induction can even start (the base case at
`i=2` needs its own direct strict argument via `factorial_lt_of_lt`, not
just re-use of the non-strict result) — real, bounded extra work, not
declined for difficulty, declined for time. `F:ml430-nat-size-bit-c601dbf0`
and `F:ml430-nat-size-le-size-c4b98f53` were sized and found genuinely
harder: `Nat.size n := sizeAux n n` is a FUEL-indexed recursion (fuel on
the first argument, not `n` itself), so relating `size(bit b n)` to
`size(n).succ` needs the same fuel-sufficiency machinery this file's
gotchas document for `land`/`lor` (a fuel-irrelevance lemma, not a direct
unfold) — not attempted this session.
`F:ml430-nat-squarefree-ext-iff-7218327d` needs an argument at the strength
of unique factorization (two squarefree numbers with the same set of prime
divisors are equal) that this prelude's `factorization.rs` explicitly does
NOT attempt (module doc: uniqueness needs a `List`/`Finset` this kernel
does not have) — sized as out of reach on this route, not merely time.
`F:ml430-nat-fermat-primefactors-one-lt-58343c6f` was already sized and
declined in detail by a sibling lane the same session
(`docs/plan/status/395-draw11-theorems.md`); re-verified the blocker
(multiplicative-order theory + a quadratic-reciprocity supplementary law,
neither present in this prelude) is still real before leaving it alone.
`F:ml430-nat-coprime-mul-add-mul-ne-mul-51b56f70` has a clean textbook
route (Gauss's lemma both directions plus `le_of_dvd`, with a small case
split at `m=0`/`n=0`) that this lane sized but did not start, purely for
remaining time/context budget.

**Hardest thing this session:** not any single proof step but recognizing,
BEFORE writing code, which of the four `ml430` mirrors in the
`choose`/`factorial` family were free rides through already-proved bridge
lemmas (three of four — `add_choose`, `add_descFactorial_eq_ascFactorial`,
`ascFactorial_eq_div`, none needing a new induction) versus which one
genuinely needed a fresh induction from raw arithmetic
(`add_factorial_le_factorial_add`) — and that the fresh one still worked
first-try only because the `factorial(succ x) ≡ mul(factorial x, succ x)`
defeq (confirmed by reading `defs.rs`'s `factorial_succ` proof: literally
`d.refl(rhs)`) meant an entire lemma application could be skipped and
replaced with nothing, relying on the kernel's own defeq check at the
final `add_declaration` — the same technique `divisibility.rs`'s existing
`factorial_lt_of_lt` already used, found by reading that file rather than
assuming a named rewrite step was needed everywhere `factorial(succ _)`
appears.

<!-- plan-section: landed-changes -->

| 2026-08-31 | `d1923474d` | feat: `Nat.add_choose` (division-normal form), with test (251 pass) |
| 2026-08-31 | `440e264c6` | facts: flip `Nat.add_choose` to proved |
| 2026-08-31 | `6608a27cb` | feat: `Nat.add_descFactorial_eq_ascFactorial`, with test (252 pass) |
| 2026-08-31 | `2cce64b26` | facts: flip `Nat.add_descFactorial_eq_ascFactorial` to proved |
| 2026-08-31 | `ee5c0be33` | feat: `Nat.ascFactorial_eq_div`, with test (253 pass) |
| 2026-08-31 | `43e45606f` | facts: flip `Nat.ascFactorial_eq_div` to proved; catch up statement pins |
| 2026-08-31 | `a0ffe4a5c` | feat: `Nat.add_factorial_le_factorial_add` + succ corollary, with tests (255 pass) |
| 2026-08-31 | `42a386df5` | facts: flip both `add_factorial_le_factorial_add` facts to proved |
| 2026-08-31 | `552837296` | style: rustfmt this lane's new files |
