# Notes: 369-nat-parity-div

Detail moved out of [`../status/369-nat-parity-div.md`](../status/369-nat-parity-div.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- `F:ml430-nat-even-add-31386639` (`Even(m+n) <-> (Even m <-> Even n)`) and
  `F:ml430-nat-even-add-39e3bc07` (`Even(m+n) <-> (Odd m <-> Odd n)`): NOT
  missing any single lemma. These need a 4-branch case split on `(m%2, n%2)`
  (nested `Nat.mod_two_eq_zero_or_one` on `m` then `n`), computing `(m+n)%2` in
  each of the 4 leaves (the arithmetic is the same `succ_add`/defeq-reduction
  technique `even_add_one` already uses, just doubled), then combining into the
  OUTER `Iff` — which itself has an `Iff` on one side, so each leaf's
  construction must produce a full `Iff (Even m <-> Even n) ...`-shaped term
  directly (no generic `iff_congr` combinator exists in this kernel to build it
  generically; `int_prelude/parity.rs`'s `even_add`/`even_add'` do exactly this
  shape already, over `Int` — read `even_add_family_stmt_and_proof` there for
  the case-tree structure to mirror, NOT to transport). Sizing: roughly 2-3x
  `even_add_one`'s proof volume (4 leaves vs. 2, each producing a compound
  `Iff`), no new arithmetic lemma needed.
- `F:ml430-nat-even-div-395c6b5e` (`Even (m/n) <-> m % (2*n) / n = 0`): genuinely
  Nat-specific, no `Int` analog exists for this one (division doesn't carry
  over the same way). Needs relating `Nat.div`/`Nat.mod` under SCALING the
  divisor by 2 (`m/n` vs `m % (2n) / n`) — I did not find an existing lemma of
  this shape in `division.rs`/`div_mod_lemmas.rs`/`mod_mul_lemmas.rs` (checked
  all three). This is more substantial than the other two blockers: it likely
  needs a new `Nat.div_mod_scale`-shaped identity built from `div_mod_exec`/
  `div_mod_unique` at divisor `2*n` compared against divisor `n`, not just a
  case split on existing facts.

**Skipped per brief:** `fermat`/`prime`-family facts in the same
`check-dispatchable-frontier.py --json` dispatchable set (`F:ml430-nat-coprime-fermatnumber-*`,
`F:ml430-nat-fermatnumber-*`, `F:ml430-nat-odd-fermatnumber-*`,
`F:ml430-nat-fermat-primefactors-one-lt-*`, `F:ml430-nat-pow-of-pow-add-prime-*`,
`F:ml430-nat-totient-gcd-mul-totient-mul-*`) — sibling lanes own those.

Held-out check: all 10 originally-dispatched facts (and the 3 remaining open
ones) verified against `check-dispatchable-frontier.py --json`'s `held_out`
list before starting — none are held-out.
