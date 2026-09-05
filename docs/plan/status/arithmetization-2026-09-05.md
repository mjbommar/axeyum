# Lane: arithmetization — Gödel numbering of the first-order syntax (W3-7)

<!-- plan-section: lane-status -->

**Your lane's block (`PARTIAL`, arithmetization, 2026-09-05).** The
arithmetization of `fo_syntax.rs` is landed, the numbering is proved
injective, and the decoder and `substCode` are built and computing. The
diagonal lemma and Gödel I are **not** landed; what is between here and them
is now a PROOF gap with no missing construction, sized below.
Three new files, `crates/axeyum-lean-kernel/src/fo_code.rs`,
`fo_numbering.rs` and `fo_decode.rs`, registered from the crate root beside
the other `fo_*` modules, plus one new example binary
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
4. **The decoder and the coded operations** (deliverable 2's construction).
   `FO.Term.decodeAux`, `FO.Term.decode`, `FO.Formula.decodeAux`,
   `FO.Formula.decode` — fuel-recursive, with a right-nested `Nat.rec` tag
   tree whose last arm is the catch-all — and on top of them
   `FO.Code.substCode : Nat -> Nat -> Nat` (exactly the roadmap item's
   signature) and `FO.Code.isFormulaCode : Nat -> Bool`.

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

## What did NOT land, and it is a PROOF gap now

Not landed: the round trip `FO.Formula.decode (FO.Formula.code p) = p`, and
therefore the commuting lemma
`substCode (⌜φ⌝) (⌜t⌝) = ⌜Formula.subst φ (Subst.cons t Subst.id)⌝`, the
diagonal lemma, and Gödel I.

Before `fo_decode.rs` the obstruction was a missing CONSTRUCTION: `substCode`
could not be defined, so its commuting lemma could not be stated. It is
defined now, and evaluation-tested, so what remains is proof-term engineering
with nothing missing under it. Building the decoder also changed the sizing in
two ways that were not visible from the numbering alone:

1. **The fuel-agreement lemma is avoidable.** State the round trip additively,
   `Π t f, decodeAux (Nat.add f (size t)) (code t) = t`, with the fuel on the
   LEFT of the `add`. `Nat.add` recurses on its RIGHT argument here, so
   `Nat.add f (Nat.succ x)` ι-reduces and the recursive call's fuel *is* the
   induction hypothesis's fuel rather than merely bounded by it. The binary
   cases then need only `Nat.add_assoc` and `Nat.add_comm` — no `Nat.le`, no
   subtraction, no `max`. That removes the
   `Nat.binaryRecAux_agree_of_fuel`-shaped lemma this lane's own earlier
   sizing had put in the list.
2. **There is a cost nobody had counted: one transport per tag.**
   `FO.Code.fst (code (and_ p q))` is NOT definitionally `4` — `FO.Code.fst`
   unfolds to `Nat.Pair.fst (unpair …)` and `unpair` of a symbolic code is
   stuck — so each of the 4 + 9 minors must rewrite along
   `FO.Code.fst_pair`/`snd_pair` FIRST, after which the numeral is literal and
   the tag tree ι-reduces. This was invisible until the tag tree existed.

`size p <= code p` also remains, but only to justify the self-fuelled wrappers
`decode n := decodeAux n n`; the `decodeAux` round trip in (1) does not use it.

The diagonal lemma has a SECOND prerequisite that is not the binding one:
ADR-1636 records the Leibniz equality rule as absent from `FO.Provable`
(`eqf_refl` is the only equality rule), and the biconditional needs it. It was
not landed here because with the round trip missing there is nothing for it to
be used on.

Recorded as the `open` facts `F:fo-formula-decoder` (whose statement now says
the construction is landed and the theorem is not), `F:fo-diagonal-lemma` and
`F:fo-first-incompleteness`.

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

| D | `FO.Formula.decodeAux`'s tag tree swaps the `all` and `ex` arms | **killed 5 of 11** (exit 101), 6 survive. Baseline for this row is the decoder suite alone (`-- fo_decode::`), 11 passed. Unlike A and C this mutant still ADMITS -- both arms have the same type -- so the kill is BEHAVIOURAL, and the five that died are exactly the ones that distinguish the two quantifiers: `formula_decode_aux_inverts_the_code_at_every_constructor`, `an_out_of_range_tag_falls_into_the_catch_all_arm`, `zero_fuel_returns_the_default_not_the_answer`, `subst_code_round_trips_a_closed_formula`, `the_self_fuelled_wrappers_agree_where_the_code_pays_for_itself`. The 6 survivors are the `FO.Term` rows, `isFormulaCode`, the numeral helper and the two axiom sweeps -- none of which mentions `all` or `ex`. |

Mutant C is this lane's substitute for the brief's second named mutant ("the
substitution commuting lemma with `code t` and `code φ` swapped"). That lemma
did not land -- see below -- so there was nothing to mutate; C is the same
defect class (two components of one code read in the wrong order) on the
theorem that DID land, and it is named as a substitution rather than passed
off as the original.

**One mutation attempt was NOT APPLIED and is not counted.** The first run of
mutant D used an anchor written before `rustfmt` joined the arm list onto one
line, so the `assert s.count(old) == 1` in the harness fired and the source was
never edited. The suite then ran green -- which is what a SURVIVED mutant also
looks like. It is recorded here because "the mutation did not apply" and "the
guard is not load-bearing" are indistinguishable from the test output alone,
and only the assertion separated them. The row above is the re-run with the
corrected anchor.

## Gates, with counts and exit statuses

| gate | result |
| --- | --- |
| `cargo test --release -p axeyum-lean-kernel --lib -- fo_code:: fo_numbering:: --test-threads=4` | 17 tests, 17 passed, exit 0 |
| `cargo test --release -p axeyum-lean-kernel --lib -- fo_decode:: --test-threads=4` | 11 tests, 11 passed, exit 0 |
| `cargo test --release -p axeyum-lean-kernel --lib -- fo_ --test-threads=4` (whole `fo_*` group) | 57 tests, 57 passed, exit 0 |
| `cargo clippy --release -p axeyum-lean-kernel --all-targets -- -D warnings` | exit 0 |
| `cargo fmt --all --check` | exit 0 |
| `examples/fo_code_inventory --require-axiom-free --expect-count 48` | `48 FO arithmetization declarations`, `axiom-free: yes (48 declarations checked)`, exit 0 |
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
| 2026-09-05 | `a15383b71` | The every-declaration sweep derived from the environment, and `examples/fo_code_inventory.rs`, which fails on absence (ADR-1640). |
| 2026-09-05 | `76513ea48` | Three proved facts for the numbering and three open rows above it, each naming its own obstruction (ADR-1640). |
| 2026-09-05 | `d8a858e63` | `FO.Term.decode`, `FO.Formula.decode`, `FO.Code.substCode` and `FO.Code.isFormulaCode` — the decoder, so what remains above the numbering is a proof gap and not a missing construction (ADR-1640). |
