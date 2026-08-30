# Notes: 376-parity-finish

Detail moved out of [`../status/376-parity-finish.md`](../status/376-parity-finish.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

- `Nat.even_add : ∀ m n, Even (m+n) ↔ (Even m ↔ Even n)`
  (`F:ml430-nat-even-add-31386639`) and `Nat.even_add' : ∀ m n, Even (m+n) ↔
  (Odd m ↔ Odd n)` (`F:ml430-nat-even-add-39e3bc07`) — new file
  `crates/axeyum-lean-kernel/src/nat_prelude/even_add_family.rs`. The
  handoff's sizing ("NOT missing any single lemma... roughly 2-3x
  `even_add_one`'s proof volume") was directionally right but the "no new
  arithmetic lemma needed" part undersold it: `Nat.add`/`Nat.Even`/`Nat.Odd`
  are witness-based (`Even n := Exists k, n = k+k`) in THIS prelude, not
  `mod`-based like `Int.even_add`/`Int.even_add'`, so the four-way
  case-split combine machinery (`TruthFact`/`iff_fact`/`mk_iff_both_true`/
  `mk_iff_both_false`, ported structurally from `int_prelude/parity.rs`) had
  to be paired with a NEW witness-arithmetic piece (`sum_shape`) relating
  `add m n`'s own Even/Odd witness to `m`'s and `n`'s via
  `Nat.add_add_add_comm`/`Nat.succ_add` plus the definitional
  `add x (succ y) ≡ succ (add x y)`. The `OO` (both-odd) leg needs
  `succ_add` twice plus one re-association step; that's the leg the
  concrete test (`(3,3)`, both Odd) exercises with a real `Odd 3` witness.
  Both facts share this one construction, only the inner predicate
  (`Even`/`Odd`) differs.
- `Nat.even_div : ∀ m n, Even (m/n) ↔ m % (2*n) / n = 0`
  (`F:ml430-nat-even-div-395c6b5e`) — new file
  `crates/axeyum-lean-kernel/src/nat_prelude/even_div.rs`. The handoff sized
  this as the hardest of the three, needing a NEW `Nat.div_mod_scale`-shaped
  identity built from `div_mod_exec`/`div_mod_unique` at divisor `2*n` after
  checking `division.rs`/`div_mod_lemmas.rs`/`mod_mul_lemmas.rs`. It needed
  NONE of that: `mod_mul_lemmas.rs`'s `Nat.mod_mul_right_div_self : ∀ m n k,
  m % (n*k) / n = (m/n) % k` — UNCONDITIONAL, no positivity hypothesis on
  `n` or `k` — is exactly this identity at `k := 2`. The whole fact reduces
  to `Nat.even_iff_mod_two_eq_zero` at `q := m/n`, bridged by `Nat.mul_comm`
  (`2*n` vs `n*2`) and transported along the resulting `Eq` via `Eq.rec`
  directly (`NatOps::transport`/`eq_motive` used as a general `Iff`
  congruence tool, not for arithmetic rewriting). ~75 lines including the
  module doc; no case split on `n` needed (the borrowed lemma already
  handles `n = 0` via its own `cases_zero_succ`). This is the sharpest
  instance this session of "verify the handoff, don't inherit it" — the
  fact sized as MOST work was the LEAST work, because the prior lane's
  three-file search for a scaling identity happened to land one file short
  of where it actually lived.

**Int-transport route re-checked, same finding as the handoff reported.**
Did not re-derive the Int-side `ofNat`/`natAbs` bridge cost (an `Iff`-inside-
`Iff` congruence lemma this kernel lacks) since the handoff's finding held
up structurally: `int_prelude/parity.rs`'s `even_add`/`even_add'` are
`mod`-based and this prelude's `Nat.Even`/`Odd` are witness-based, so a
direct Nat-level construction (mirroring the COMBINE machinery, not the
mod-arithmetic) was cheaper than bridging carriers, exactly as reported.

**Frontier after this lane's three closes:** re-ran
`check-dispatchable-frontier.py --json` after merging local `main` — 8
dispatchable facts remain, ALL either explicitly fermat-family
(`fermat-primefactors-one-lt`, `fermatnumber-{one,strictmono,two,zero}`,
`odd-fermatnumber`, `pow-of-pow-add-prime` — this last one's
`formal.statement` is literally `1 < a → n ≠ 0 → Prime (a^n+1) → ∃ m, n =
2^m`, the Fermat-number primality shape) or bundled with that cluster by
the prior lane's own skip list (`totient-gcd-mul-totient-mul` — a general
totient identity, not fermat-shaped on its face, but named explicitly in
`369-nat-parity-div.md`'s "Skipped per brief" list alongside the fermat
facts as sibling-lane territory). Per this lane's brief ("skip anything in
the fermat or creal families"), none of these 8 were taken. The dispatch
gate (`G7 queue-below-floor`) is currently failing (8 dispatchable against a
floor of 10) — NOT this lane's to fix per its brief ("do NOT run
`gen-autogenesis-nursery-refill.py`"); flagging for whichever lane owns
queue refill next.
