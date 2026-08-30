# Notes: 235-nat-bitwise-facts

Detail moved out of [`../status/235-nat-bitwise-facts.md`](../status/235-nat-bitwise-facts.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

| fact | Mathlib name | class | reason |
| --- | --- | --- | --- |
| `F:ml430-nat-bitwise-bit-4c4b28a8` | `Nat.bitwise_bit'` | (3) blocked | general `Nat.bitwise f (bit a m) (bit b n) = bit (f a b) (bitwise f m n)` — lives in `bitwise.rs`, owned by the sibling Opus lane right now, not mine to touch |
| `F:ml430-nat-bitwise-comm-1a273bae` | `Nat.bitwise_comm` | (3) blocked | general `bitwise`; depends_on `bitwise-swap`; `bitwise.rs` territory |
| `F:ml430-nat-bitwise-swap-7175e90e` | `Nat.bitwise_swap` | (3) blocked | general `bitwise`; depends_on `bitwise-bit`; `bitwise.rs` territory |
| `F:ml430-nat-even-xor-78a39432` | `Nat.even_xor` | (3) blocked | needs a public `Nat.xor`/`^^^`. We have no standalone `Nat.xor` — only one ad hoc `bitwise xor_fn 3 5` numeral check inline in `bitwise.rs`. `xor := bitwise xor` in Mathlib too (confirmed at the pinned commit), so this is squarely `bitwise.rs`'s domain |
| `F:ml430-nat-land-assoc-ad4775b8` | `Nat.land_assoc` | (3) blocked | depends_on `land-bit`; same missing machinery |
| `F:ml430-nat-land-bit-b9ab7475` | `Nat.land_bit` | (3) blocked | see analysis below — needs fuel-irrelevance for `landAux` at differing fuel amounts |
| `F:ml430-nat-land-comm-7e6ad72e` | `Nat.land_comm` | (3) blocked | Mathlib's route is via `bitwise_comm`; a *direct* proof over our own `landAux` needs a "landAux is independent of which sufficient fuel you pick" lemma — same missing machinery as `land-bit` |
| `F:ml430-nat-ldiff-bit-6be49bb8` | `Nat.ldiff_bit` | (3) blocked | same shape as `land-bit`, for `ldiff` |
| `F:ml430-nat-lor-assoc-82c4d0fd` | `Nat.lor_assoc` | (3) blocked | depends_on `lor-bit`; same missing machinery |
| `F:ml430-nat-lor-bit-a2f98c7c` | `Nat.lor_bit` | (3) blocked | same shape as `land-bit`, for `lor` |
| `F:ml430-nat-lor-comm-2666d7ef` | `Nat.lor_comm` | (3) blocked | same as `land-comm`, for `lor` |
| `F:ml430-nat-lt-of-testbit-72f64ab8` | `Nat.lt_of_testBit` | (2) mirror mismatch | needs `Bool`-valued `testBit`; ours (`binary.rs`) is `Nat -> Nat -> Nat` (0/1), a different codomain, not merely a different construction of the same type |
| `F:ml430-nat-lt-xor-cases-c43a1e85` | `Nat.lt_xor_cases` | (3) blocked | needs `Nat.xor` (`bitwise.rs`) *and* `testBit`/`xor_trichotomy` reasoning |
| `F:ml430-nat-testbit-eq-inth-ffa07392` | `Nat.testBit_eq_inth` | (3) blocked | needs `n.bits : List Bool` + `List.getI` — this kernel has **no `List` type at all**, and `Bool`-valued `testBit` — the deepest-blocked fact in the family |
| `F:ml430-nat-testbit-land-dfef7ca4` | `Nat.testBit_land` | (2) mirror mismatch + **DO NOT CLOSE** | Bool-vs-Nat mismatch, *and* named as a load-bearing dependency of `scripts/gen-autogenesis-bitwise-family-projection.py --check` (a live `just` target), which `raise`s if this fact's `epistemic_status != "open"`. Closing it breaks that gate regardless of provability |
| `F:ml430-nat-testbit-ldiff-16f94162` | `Nat.testBit_ldiff` | (2) mirror mismatch + **DO NOT CLOSE** | same as above, same script |
| `F:ml430-nat-testbit-lor-7644e067` | `Nat.testBit_lor` | (2) mirror mismatch + **DO NOT CLOSE** | same as above, same script |
| `F:ml430-nat-zero-of-testbit-eq-false-e244c9a1` | `Nat.zero_of_testBit_eq_false` | (2) mirror mismatch | Bool-vs-Nat mismatch; provable as an ANALOGOUS Nat-valued statement via existing `sum_test_bit_eq`, but restating it would be "manufacturing a flip" against a pinned Bool-typed `formal.statement` — must stay open |
| `F:ml430-mutation-a6dd1759bce60d820292e107` | (mutation of `Nat.lor_comm`) | **⛔ MUTATION (operator-substitution), skipped** | `fact-frontier.py` flags it; `formal.statement` is `n \|\|\| m = n &&& m`, false in general (e.g. `n=1,m=2`: `3 != 0`) |

**Why the "boundary" bites 7 facts, not just the one example in the brief.**
The brief's worked example (`bitwise and_fn m n = land m n`) is about
relating `bitwise.rs`'s `Nat.rec` to `land.rs`'s. `land_bit`/`lor_bit`/
`ldiff_bit` don't touch `bitwise` at all, but they hit an **equally hard,
independently-necessary** instance of the same class: our `land m n :=
landAux m m n` uses `m` as BOTH the fuel and the first data argument. To prove
`land (bit a m) (bit b n) = bit (a&&b) (land m n)`, unfolding `landAux` at
fuel = `bit a m` (a stuck `add`/`mul` term for symbolic `m`, not literally a
`succ`) requires: (a) exposing `bit a m`'s constructor shape via a real case
split (is `a=false ∧ m=0`, i.e. is `bit a m` itself `0`?), and (b) relating
the resulting recursive call `landAux (pred (bit a m)) m n` — fuel now
`pred(bit a m) ≈ 2m-1`, NOT `m` — back to `landAux m m n = land m n`. Step
(b) is exactly "landAux is independent of fuel choice once fuel ≥ the data",
a lemma the prelude does not have (verified: `land.rs`/`lor.rs`/`ldiff.rs`
declare only `_zero_left`, `_zero_right`, and one or two concrete-numeral
checks — no `_bit`, `_comm`, or `_assoc` exist today). Since the brief says
"a sibling Opus lane is building exactly that machinery right now... if a
fact needs it, classify as (3) and name it rather than attempting it," all
seven of `land-bit`/`land-comm`/`land-assoc`/`lor-bit`/`lor-comm`/
`lor-assoc`/`ldiff-bit` are classified (3) rather than attempted, to avoid
duplicating that work.

**Mathlib comparison performed at the pinned commit** (per the brief's
instruction and the CLAUDE.md "flip" criterion) — read directly from
`/data0/axeyum/lean-import-toolchain/mathlib4` at
`c5ea00351c28e24afc9f0f84379aa41082b1188f` (`Mathlib/Data/Nat/Bitwise.lean`),
not inferred from prose:

- `Nat.land/lor/ldiff := Nat.bitwise <and/or/diff>`, and `Nat.bitwise` is a
  well-founded recursion on `div2`/`bodd` needing `Quot.sound`/`propext`
  through the equation compiler (confirmed by the module's own `-- for
  unfolding bitwise` core import). Our `land`/`lor`/`ldiff` are each an
  independent, axiom-free `Nat.rec`-fuel construction. Same conclusion as the
  brief's stated boundary.
- `Nat.testBit (n i : ℕ) : Bool` — confirmed Bool-valued from its use sites
  (`testBit_land : testBit (m &&& n) k = (testBit m k && testBit n k)`, using
  `Bool.&&`). Our `Nat.testBit : Nat -> Nat -> Nat` (`binary.rs`,
  `testBitAux`) returns `{0,1}` as a `Nat` — already used that way by our own
  proved `Nat.testBit_zero`/`testBit_succ`/`testBit_le_one`/`sum_testBit_lt`/
  `sum_testBit_eq` (all `AxNat`-typed per `nat_theorem_inventory`). This is a
  genuine codomain mismatch, not an alternate encoding of the same type.
  `Nat.xor := bitwise xor` (confirmed at `lt_xor_cases`/`even_xor`'s own
  module) — no standalone public `Nat.xor` exists in our prelude.

**No code changed.** No `nat_prelude/{bits,land,lor,ldiff}.rs` edits, no
`nat_prelude.rs`/`nat_prelude_tests.rs` edits, no fact ledger edits (in
particular the three `testbit-{land,lor,ldiff}` facts were left untouched,
per their gate dependency). `python3 scripts/validate-facts.py` not needed
since nothing in `artifacts/facts/` changed.

**Gate status:** `timeout 600 scripts/cargo-serialized.sh test -p
axeyum-lean-kernel --lib nat_prelude` — see report; ran to completion,
confirmed nonzero test count, all green (expected: no source changed).
`cargo fmt --all --check` / `clippy --all-targets` not run against changed
Rust (none). See the coordinator's report for exact numbers if run.

**For the next lane:** do not re-attempt `land-bit`/`lor-bit`/`ldiff-bit`/
`*-comm`/`*-assoc` until the sibling Opus lane's fuel-irrelevance +
`Nat.mod _ 2 ∈ {0,1}` case-split machinery lands (check whether it landed in
`ops.rs`/`bitwise.rs` first — `grep` for a new public lemma name there, then
reread this file's boundary paragraph before touching `land.rs`/`lor.rs`/
`ldiff.rs`). The `bitwise-*`/`even-xor`/`lt-xor-cases` group needs
`bitwise.rs`'s general `Nat.bitwise` and a public `Nat.xor` — check with the
owning lane before touching. The `testbit-*`/`lt-of-testbit`/
`zero-of-testbit-eq-false`/`testbit-eq-inth` group needs a **new**
Bool-valued `Nat.testBit` (a parallel construction to the existing Nat-valued
one in `binary.rs`) plus, for `testbit-eq-inth` specifically, a `List` type
this kernel does not have at all — size that as new infrastructure, not a
proof task, and do **not** close `testbit-land`/`testbit-lor`/`testbit-ldiff`
even if a Bool `testBit` lands, without first re-checking
`gen-autogenesis-bitwise-family-projection.py`'s `--check` gate.
