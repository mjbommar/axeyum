# Lane: arithmetization — Gödel numbering of the first-order syntax (W3-7)

<!-- plan-section: lane-status -->

**Your lane's block (`PARTIAL`, arithmetization, 2026-09-05).** The
arithmetization of `fo_syntax.rs` is landed and the numbering is proved
injective; representability of substitution, the diagonal lemma and Gödel I
are **not** landed, and they are all blocked on the same single missing
construction (a decoder `Nat -> FO.Formula`), which is sized below.
Two new files, `crates/axeyum-lean-kernel/src/fo_code.rs` and
`fo_numbering.rs`, registered from the crate root beside the other `fo_*`
modules, plus one new example binary
(`examples/fo_code_inventory.rs`). Every declaration has an empty
`Kernel::axiom_footprint`
([ADR-1640](../../research/09-decisions/adr-1640-godel-numbering-gets-its-own-pairing-because-nat-pair-is-a-blind-family.md)).

## What landed

1. **A pairing with a proved round trip.**
   `FO.Code.tri`, `FO.Code.pair a b := tri (a + b) + a`, `FO.Code.step`,
   `FO.Code.unpair`, `FO.Code.fst`, `FO.Code.snd`; and
   `FO.Code.pair_zero_succ`, `FO.Code.pair_succ`, `FO.Code.unpair_pair`,
   `FO.Code.fst_pair`, `FO.Code.snd_pair`, `FO.Code.pair_inj_left`,
   `FO.Code.pair_inj_right`.
2. **The numbering.** `FO.Term.code`, `FO.Formula.code` — each constructor is
   `FO.Code.pair tag payload` with a distinct tag and the payload nesting
   field codes to the right.
3. **Injectivity.** `FO.Term.code_injective`, `FO.Formula.code_injective`.

## The pairing is a new one, and not reusing `Nat.pair` was forced twice over

`Nat.pair` (`nat_prelude/avg_pair.rs`) and its `sqrt`-based projections
(`nat_prelude/unpair.rs`) already exist, and neither has a round-trip theorem.
This lane did not supply one:

- **Partition check.** `Nat.pair`, `Nat.avg`, `Nat.unpaired` and
  `Nat.Primrec` are the constants of the **held-out** families
  `natural-avg-pair` (10 rows) and `natural-primitive-recursion` in
  `artifacts/autogenesis/nursery-v2-extension.json`
  (`"partition": "held-out"`, `"answer_access": "withheld-during-episode"`).
  Proving `unpairLeft (Nat.pair a b) = a` would spend a blind evaluation
  population this lane was not given. Nothing in this lane's diff touches any
  `Nat.pair`/`Nat.avg`/`Nat.unpaired` declaration or states any theorem about
  one.
- **Independently, cost.** `Nat.pair`'s inverse reads `Nat.sqrt`, itself a
  fuel recursion, so the round trip is a theorem about `sqrt (b*b + a)` on top
  of a fuel-recursive definition, with a fuel-agreement lemma underneath.

## Why the anti-diagonal pairing, specifically

The choice is decided by what the INVERSE has to be, not by what the pairing
looks like. `2^a (2b+1) - 1` inverts through the 2-adic valuation, which
recurses on `n / 2` — not structurally smaller, so fuel plus a fuel-agreement
lemma, and every step needs `(2m+1) % 2 = 1` and `(2m+1) / 2 = m`. The
anti-diagonal enumeration's successor is a function of the previous pair
alone,

```text
step (mk a 0)        = mk 0 (succ a)
step (mk a (succ b)) = mk (succ a) b
```

so `FO.Code.unpair` is `step` iterated `n` times — a plain `Nat.rec` on `n`,
no fuel, no `Nat.div`, no `Nat.sqrt`. Both `step` equations hold by ι, because
`step` is a `Nat.rec` on the pair's second component. The round trip is then
ONE structural induction, on the CODE rather than on either component:

```text
P n := Π a b, Eq Nat (pair a b) n -> Eq Nat.Pair (unpair n) (Nat.Pair.mk a b)
```

The only `Nat` theorems the whole two-file slice imports are `zero_add`,
`succ_add`, `succ_injective`, `succ_ne_zero`.

## Small formulas get small codes, and that is what made the tests possible

`⌜bot⌝ = 0`, `⌜eqf (var 0) (var 0)⌝ = 2`, `⌜imp bot bot⌝ = 27`,
`⌜all bot⌝ = 35`, `⌜ex bot⌝ = 44`. Every numeral in this kernel is unary, so a
`2^a (2b+1)` pairing would have put a two-constructor formula out of reach of
any `def_eq`. The evaluation tests check eleven such codes against
hand-computed numerals.

## Injectivity: 16 + 81 cases, two shapes

An outer structural induction carrying
`Π u, Eq Nat (code t) (code u) -> Eq _ t u`, with an inner case analysis on
`u`. The 12-of-16 and 72-of-81 off-diagonal cases are one construction:
`FO.Code.pair_inj_left` reads the two tags off the hypothesis, and distinct
unary numerals are refuted by stripping `succ`s with `Nat.succ_injective`
until `Nat.succ_ne_zero` applies. The diagonal cases peel the payload with
`pair_inj_left`/`pair_inj_right`, convert each component (a `Nat` field is
already an equality, an `FO.Term` field goes through
`FO.Term.code_injective`, a recursive field through the induction
hypothesis), and recombine by congruence one argument at a time.

Proving `pair a b = pair c d -> a = c` *directly* would have been a double
induction with a `Nat`-level case split inside it. Through the round trip it
is three `Eq` steps, and that is what makes the 97 syntax-level cases
affordable.

## What did NOT land, and the obstruction is ONE thing

Representability of substitution (`substCode ⌜φ⌝ ⌜t⌝ = ⌜φ[t]⌝`), the diagonal
lemma, and Gödel I are all downstream of a **decoder** `Nat -> FO.Formula`: a
syntax operation "as a `Nat -> Nat` function" must take a code apart, act, and
rebuild, and without the rebuild `substCode` cannot be DEFINED, so its
commuting lemma cannot be STATED, so the diagonal lemma has nothing to
diagonalize.

The numbering supplies the taking-apart — `FO.Code.fst`/`snd` compute and the
round trip says they are right — but a decoder recurses on `FO.Code.snd n`,
which is not structurally smaller than `n`. Sized:

1. `decodeAux : Nat -> Nat -> FO.Formula` (fuel, code) with a nine-way case
   tree on the tag, i.e. a nested `Nat.rec` at motive `fun _ => Nat ->
   FO.Formula` — the shape `nat_prelude`'s `logAux` / `sqrtAux` /
   `binaryRecAux` already use. Roughly one slice per type (`FO.Term` then
   `FO.Formula`).
2. A fuel-agreement lemma of the `Nat.binaryRecAux_agree_of_fuel` shape — one
   induction.
3. A bound `depth φ <= code φ`, so the code can be its own fuel — one
   induction, needing `Nat.le` transitivity and the monotonicity of
   `FO.Code.pair` in each argument.

Recorded as the `open` fact `F:fo-formula-decoder`, with
`F:fo-diagonal-lemma` and `F:fo-first-incompleteness` open behind it.

Separately, and NOT the binding constraint: ADR-1636 records that the Leibniz
equality rule is absent from `FO.Provable`, and the diagonal lemma's
biconditional needs it. That is a second prerequisite. It was not landed here
either, because with (1)-(3) missing there is nothing for it to be used on.

## Files

| path | what |
| --- | --- |
| `crates/axeyum-lean-kernel/src/fo_code.rs` | the pairing, its structural inverse, the round trip, injectivity |
| `crates/axeyum-lean-kernel/src/fo_code/tests.rs` | evaluation tests + the axiom-freedom sweep |
| `crates/axeyum-lean-kernel/src/fo_numbering.rs` | `FO.Term.code`, `FO.Formula.code`, both `code_injective` |
| `crates/axeyum-lean-kernel/src/fo_numbering/tests.rs` | code values, the copy-paste controls, statement pinning, the derived every-declaration sweep |
| `crates/axeyum-lean-kernel/examples/fo_code_inventory.rs` | the `checker_command` for the `F:fo-code-*` facts; fails on absence |

## Mutations RUN (not predicted)

Both applied to this lane's own isolated worktree -- no other lane reads it --
built, run, and restored byte-for-byte (sha256 compared before and after,
`git status` on the two files empty afterwards). Baseline for all rows:
`cargo test --release -p axeyum-lean-kernel --lib -- fo_code:: fo_numbering::
--test-threads=4`, **17 passed, 0 failed, exit 0**.

| mutant | what changed | outcome |
| --- | --- | --- |
| A | `FO.Code.pair a b := tri (a + b) + a` becomes `a + b`, i.e. the pairing stops being injective | **killed 17 of 17** (exit 101). The kernel rejects `FO.Code.pair_zero_succ` first -- `pair 0 (succ k)` no longer δι-reduces to `tri (succ (0 + k))` -- so the prelude does not build and every test in both modules dies. |
| C | `split_payload` swaps `FO.Code.pair_inj_left` and `pair_inj_right`, i.e. the payload's head and tail are read the wrong way round | **killed 10 of 17** (exit 101), 7 survive. `FO.Term.code_injective` is rejected with `TypeMismatch`: the `f1`/`f2` diagonal cases get `Eq Nat (code t) (code u)` where the congruence wants `Eq Nat k l`. The 7 survivors are the `fo_code::` tests, which do not build the numbering prelude -- the mutation is confined to `fo_numbering.rs`, and that partition is the finding, not a gap. |

Mutant C is this lane's substitute for the brief's second named mutant ("the
substitution commuting lemma with `code t` and `code φ` swapped"). That lemma
did not land -- see below -- so there was nothing to mutate; C is the same
defect class (two components of one code read in the wrong order) on the
theorem that DID land, and it is named as a substitution rather than passed
off as the original.

## Gates, with counts and exit statuses

| gate | result |
| --- | --- |
| `cargo test --release -p axeyum-lean-kernel --lib -- fo_code:: fo_numbering:: --test-threads=4` | 17 tests, 17 passed, exit 0 |
| `cargo test --release -p axeyum-lean-kernel --lib -- fo_ --test-threads=4` (whole `fo_*` group) | 57 tests, 57 passed, exit 0 |
| `cargo clippy --release -p axeyum-lean-kernel --all-targets -- -D warnings` | exit 0 |
| `cargo fmt --all --check` | exit 0 |
| `examples/fo_code_inventory --require-axiom-free --expect-count 42` | `42 FO arithmetization declarations`, `axiom-free: yes (42 declarations checked)`, exit 0 |
| `examples/fo_code_inventory FO.Formula.decode --exact` (absence control) | exit 1, "an absent declaration is a failed check, not an empty report" |
| `python3 scripts/validate-facts.py` | 2876 facts, 0 errors, exit 0 |
| `python3 scripts/check-settled-fact-statements.py` | `SETTLED_FACT_STATEMENTS|PASS`, exit 0 |

## One gate is RED, and it is not this lane's

`python3 scripts/check-kernel-trusted-core.py` exits **1**:

```text
FAIL D: file(s) joined the trusted core: ['metric_prod.rs'].
```

Checked rather than assumed. `metric_prod.rs:183` carries
`pub fn all(&self) -> Vec<(&'static str, NameId)>` on a `Names` struct, which
is what puts it on the derived path from an admission gate; it was last
touched by `c3249653d` (lane `metric`, W2-10), and
`git merge-base --is-ancestor c3249653d 5f969ad57` succeeds, so the gate was
already red at this lane's base. Neither `fo_code.rs` nor `fo_numbering.rs`
appears anywhere in the trusted-core report, and neither declares a
`fn all` on a `Names` struct -- `CodeNames::rebuild` returns `Self` and is
`pub(crate)`. This lane did not change the trusted surface.

<!-- plan-section: landed-changes -->

| 2026-09-05 | `399b10e9b` | `FO.Code` — the anti-diagonal pairing, its structural inverse, the round trip and both injectivities; a new pairing rather than `Nat.pair`, which is a held-out family (ADR-1640). |
| 2026-09-05 | `2f986f4c2` | `FO.Term.code`, `FO.Formula.code` and both `code_injective` — the Gödel numbering of the first-order syntax, 16 + 81 cases (ADR-1640). |
