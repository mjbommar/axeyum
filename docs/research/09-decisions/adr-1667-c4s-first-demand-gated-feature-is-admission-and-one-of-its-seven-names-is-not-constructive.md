# ADR-1667: C4's first demand-gated feature is admission, and one of its seven names is not constructive

Status: accepted
Date: 2026-09-05
Index-summary: ADR-1662's recommended trusted-substitution extension, built and re-measured over the same 756 mirrors -- and **population survival is unchanged, 390 admitted before and after**, because the blockers are layered. `dif_pos`, `Eq.subst`, `And.left` and `Nat.le_of_lt_add_one` are reconstructed and kernel-checked; `Quot` needed no substitution at all (the kernel already derives all four package types itself, so the gate was over-broad -- this overturns doc 294's hard rule); `eq_self`, the largest blocker at 97 rows, is NOT constructive (its own Lean 4.30 closure reaches `propext`, re-confirming docs 240 and 295, which ADR-1662 lost). The five names fall to zero as first blockers and the same 150 rows reappear behind the next declaration, exactly -150/+150. What is actually behind the 361: **217 rows behind axioms this kernel excludes** (propext/funext/em), 114 behind Lean's well-founded-recursion machinery, 30 behind ordinary constructive names

## Context

[ADR-1662](adr-1662-the-statement-import-blocker-is-a-proof-inside-the-definition-closure-not-the-variable-block.md)
censused all 756 pinned `F:ml430-*` Mathlib mirrors through the real
statement-only import route and found that 361 of them are refused by one
class: the statement's own DEFINITION closure reaches a proof-bearing
declaration, so `import_statement_ndjson`'s proof-isolation gate refuses the
stream. Nine declarations account for all 361.

Its recommendation, and the C4 task this ADR closes: extend the independently
reconstructed `trusted_substitution` set over the **seven constructive names**
(337 rows), holding `em` (23) and `propext` (1) back because substituting a
classical axiom enlarges the trusted surface rather than reconstructing it.

C4 of the
[library-artifact compatibility roadmap](../../plan/library-artifact-compatibility-roadmap-2026-08-30.md)
admits a feature only against before/after population survival, exact Lean
differential behaviour, no enlarged trusted surface, and a downstream consumer.
This ADR is that admission.

## Decision

**Six of the seven are done, one of the seven was misclassified, and one of the
six needed no substitution at all.**

- `dif_pos` (34 rows), `Eq.subst` (7), `And.left` (12) join
  `trusted_substitution::SUBSTITUTABLE_THEOREMS`: each is rebuilt from this
  kernel's own `Eq.rec` / `Decidable.rec` / `And.rec` primitives, and the
  stream's own `type`/`value` for those records is parsed and discarded.
- `Nat.le_of_lt_add_one` (24) joins
  `nat_order_substitution::SUBSTITUTABLE_NAT_ORDER_THEOREMS`: it is admitted
  under the STREAM's declared type (Mathlib spells it with the order
  typeclasses) with a value this project builds, validated by inferring the
  candidate's type and requiring `def_eq` against that declared type.
- **`Quot` (73) is not a substitution.** It is the four-declaration quotient
  package, and `Kernel::add_quotient_package` already derives all four types
  itself and checks the delivered candidates against them before admitting any
  of them. The gate refused it only because `DeclarationKind::Quotient` was on
  the refusal list unconditionally. A type former and its eliminators are not a
  proof, so the fix is an exemption, not a reconstruction:
  `is_exempted_native_quotient` lets exactly the four canonical names through,
  and only when this import actually recorded admitting the validated package.
- **`eq_self` (97) is NOT constructive and stays blocked.** ADR-1662 grouped it
  with the six. That is wrong: `eq_self : (a = a) = True` is an equality between
  two `Prop`s, and Lean 4.30 proves it through `eq_true`, which is `propext`
  applied to an `Iff`. This kernel is intuitionistic and has no `propext`
  (`crates/axeyum-lean-kernel/src/prelude.rs`), so substituting `eq_self` is the
  same decision as substituting `propext` -- the one ADR-1662 deliberately did
  not take. It belongs with `em` and `propext`, and this ADR does not take it
  either.
- **`Nat.mod_lt` (90) is not attempted here** and is not in the same difficulty
  class as the others. Measured decomposition below.

**And the headline of the re-measurement is that none of it moved the
population.** 390 statements crossed before and 390 cross after. The five names
fall to zero as first-reported blockers and the same 150 rows reappear behind
the next declaration in their own closure — `funext` (+62), `eq_self` (+34),
`WellFounded.Nat.eager_eq` (+24), `And.right` (+19), `asymm` (+10), `ne_eq`
(+1). The blockers in this population are layered, and after this lane
**217 of the 361 sit behind axioms this kernel deliberately excludes** and 114
behind Lean's well-founded-recursion machinery. Thirty are ordinary
constructive names still worth substituting; nothing else is.

So the decision this ADR also records is a **negative** one, and it is the more
useful half: C4's demand-gate picked this feature by count, the feature was
built exactly as specified, and its measured effect on the criterion C4 admits
against is zero. A demand gate that ranks by FIRST-reported blocker cannot see
a layered frontier — the next one should rank by full-closure blockers, which
is what doc 295 did by hand for a single row and what this run now makes cheap
for all 756.

## Evidence

### The nine names, and what each one turned out to need

Row counts are ADR-1662's first-reported-blocker distribution over the same 756
mirrors. "First-reported" is the whole reason the after-census is a RE-RUN: the
150 rows this lane addresses do not become 150 admissions, they become 150 rows
that now report whatever was behind their first blocker.

| declaration | rows | kind | what it needed | landed |
|---|---:|---|---|---|
| `eq_self` | 97 | Theorem | **`propext`.** Not constructive. | no -- see below |
| `Nat.mod_lt` | 90 | Theorem | five more theorems, two of them about `Nat.modCore`'s well-founded definition | no -- decomposition below |
| `Quot` | 73 | Quotient | nothing: the kernel already derives the package | **yes**, as an exemption |
| `dif_pos` | 34 | Theorem | `Decidable.rec` + `False.rec` + proof irrelevance | **yes** |
| `Nat.le_of_lt_add_one` | 24 | Theorem | `Nat.le_of_succ_le_succ`'s construction under the stream's own type | **yes** |
| `em` | 23 | Theorem | classical -- held back by ADR-1662 | no, deliberately |
| `And.left` | 12 | Theorem | `And.rec` at universe 0, constant motive | **yes** |
| `Eq.subst` | 7 | Theorem | `Eq.rec` | **yes** |
| `propext` | 1 | Axiom | an axiom -- held back by ADR-1662 | no, deliberately |

150 of the 361 rows' first blockers are addressed here; 211 remain
(`eq_self` 97, `Nat.mod_lt` 90, `em` 23, `propext` 1).

### Two of these were already measured, and ADR-1662 lost them

Before writing a line of this, the prior record was searched. Two of the
findings below are **re-confirmations, not discoveries**, and saying so is the
point — a repository that rediscovers its own measurements is paying twice:

- [`docs/autogenesis/240-the-cascade-is-exact.md`](../../autogenesis/240-the-cascade-is-exact.md)
  (2026-08-22) already found "`eq_self` (20 rows) needs `propext`, which this
  kernel does not have".
- [`docs/autogenesis/295-mod-lt-and-eq-self-cascades-are-not-a-two-name-extension.md`](../../autogenesis/295-mod-lt-and-eq-self-cascades-are-not-a-two-name-extension.md)
  (2026-08-27) re-derived it from a real `Nat.Coprime` export and classified
  `eq_self` as **architecturally permanent under this kernel's design**, not
  deferred. It also measured the `Nat.mod_lt` cascade at 15 remaining names for
  one representative statement, seven of them generic well-founded-recursion
  internals — correcting ADR-0604 §2 and doc 294, which had both said "exactly
  two names".

ADR-1662 nonetheless grouped `eq_self` with the constructive six. That is the
one row of its recommendation this ADR corrects, and the correction now has a
TEST behind it rather than a document.

### `eq_self` is not constructive, measured rather than argued

Lean 4.30's `eq_self : ∀ {α : Sort u} (a : α), (a = a) = True` is an equality
between two `Prop`s. Its exported closure is `Eq`, `True`, `Iff`, **`propext`
(Axiom)**, `trivial`, `eq_true`, `rfl` — and its value is
`eq_true (a = a) (rfl a)`, where `eq_true` is `propext` applied to an
`Iff.intro`. This kernel is intuitionistic — `crates/axeyum-lean-kernel/src/prelude.rs`
states it has no `Classical.em`, no `propext` and no `funext` — so there is no
reconstruction of `eq_self` here that is not first a decision to admit
`propext`.

That is ADR-1662's own held-back decision, arriving under a different name. It
is not taken here.

The measurement is a test, not a comment:
`trusted_substitution::c4_admission_tests::eq_self_is_propext_dependent_and_therefore_not_substituted`
imports the pinned Lean 4.30 export of the real declaration
(`docs/plan/fixtures/lean4export-v4.30-eq-self.ndjson`), reads
`Kernel::axiom_footprint(eq_self)`, and requires `propext` to be in it. It fails
if a pin move ever makes `eq_self` axiom-free — which would be the signal to
revisit — and it fails if anyone adds `eq_self` to `SUBSTITUTABLE_THEOREMS`
without taking the `propext` decision.

### `Quot`: overturning a stated hard rule, and why that is not a weakening

[`docs/autogenesis/294-statement-only-import-goal-record.md`](../../autogenesis/294-statement-only-import-goal-record.md)
records `Quotient` as refused "by hard rule", and doc 295 classifies the one
`Nat.Coprime` row it blocks as **permanent**. This ADR overturns that, so the
reasoning has to be exact.

Doc 294's stated ground is that a reconstruction "structurally CANNOT exist"
for `Quotient` — which is TRUE and is not a reason to refuse. The quotient
package IS primitive; there is nothing underneath it to rebuild it from. But
"reconstructed rather than trusted" is not the only way this crate avoids
trusting a stream, and for the quotient package the kernel already has the
other way: `Kernel::add_quotient_package` **derives all four package types
itself** from canonical `Eq`/`Eq.refl` and checks the delivered candidates
against them — exact names, order, kinds, universe arities, binder
information — atomically, before any of them enters the environment
(`crates/axeyum-lean-kernel/src/quotient.rs`, ADR-0365). Nothing about the
stream's `quot.type` records is believed. That is the same guarantee a
substitution gives, obtained a different way.

The rest of doc 294's ground was the code itself
("`is_exempted_trusted_declaration` never exempts `Quotient`, by hard rule,
verified in `src/lib.rs`"), which is a description of the gate, not a reason
for it.

Three things bound the change:

1. **`Quot.sound` cannot arrive by this route, at three independent points.**
   It is not in `NATIVE_QUOTIENT_PACKAGE`; it is not in this kernel at all
   (ADR-0456, ADR-1595); and `lean4export`'s `quot.kind` has no spelling for
   it — `QuotKind` is `{Type, Ctor, Lift, Ind}` and a fifth quotient record of
   any kind is rejected by `import_quotient` before the gate ever sees it.
   `Quot.sound` is the only member of Lean's quotient story that STATES a
   proposition; the other four are a type former and its eliminators, in the
   same sense `Nat` and `Nat.rec` are — and `Recursor` was never on the
   refusal list.
2. **The trusted surface does not move.** `check-kernel-trusted-core.py`
   measures the trusted CODE (`quotient.rs`'s 605 function lines are in the
   core whether or not any stream delivers a package), not the admitted
   declarations, so admitting a package changes nothing it counts. Measured
   before and after below.
3. **The axiom accounting does not move either.** ADR-1595 prices the quotient
   package on exactly this: `Kernel::axiom_footprint` counts
   `Declaration::Quotient` as trusted base. It still does — a theorem that
   reaches `Quot.lift` is still visibly not axiom-free, and
   `the_native_quotient_package_does_not_block_a_statement` asserts that for
   all four members rather than claiming it in prose.

What changes is only this: a statement whose PROPOSITION cannot be written
without the quotient type former is now expressible as a goal instead of being
refused. Refusing it was never about proof-smuggling; it was about the gate
being coarser than its own reason.

### `Nat.mod_lt`'s decomposition, measured from the pinned export

Not attempted here, and not in the same difficulty class as the other six. Its
exported closure carries 42 proof-bearing declarations; **36 of them are already
substituted** by this crate. Exactly six are not:

| remaining | why |
|---|---|
| `Nat.not_lt_zero` | `fun n => Nat.not_succ_le_zero n` — within the existing `nat_order_substitution` machinery |
| `Nat.lt_or_ge` | `Nat.brecOn` course-of-values recursion, which no substitution module builds yet |
| `Nat.lt_of_not_le` | `Or.resolve_right (Nat.lt_or_ge b a) h` — free once `Nat.lt_or_ge` exists |
| `Nat.modCoreGo_lt` | the well-founded descent inside `Nat.modCore.go` |
| `Nat.modCore_lt` | `dite` on `0 < y` over `Nat.modCoreGo_lt` |
| `Nat.mod_lt` | the `Nat.decLe` case split over `Nat.modCore_lt` and `Nat.lt_of_not_le` |

All six are needed for any of the 90 rows to move, because the closure is
admitted whole. The list is read from `lean4export Mathlib -- Nat.mod_lt`
against the same pins, intersected with the union of this crate's four
substitution lists — a measurement, not an estimate.

**It is also a LOWER bound, and doc 295 measured the other end.** This is
`Nat.mod_lt`'s OWN closure. A census row that reports `Nat.mod_lt` as its first
blocker is a whole STATEMENT closure, which drags in more: doc 295 enumerated
one such row (`Nat.Coprime`, which forces `Nat.gcd`'s value) at **15**
remaining names, seven of them generic well-founded-recursion internals
(`WellFounded.Nat.eager_eq`, three `WellFounded.Nat.fix._proof_*`, a private
`Nat.gcd._unary._proof_1`). The two numbers answer different questions and both
are right; quoting either without saying which is how "exactly two names"
became the standing estimate in ADR-0604 §2.

### Controls

Every substitution carries a positive control (the reconstruction is admitted by
`Kernel::add_declaration`, its `axiom_footprint` is empty, and
`theorem_dependencies` is empty — so it cites no theorem at all) and a
**negative control in which the reconstructed VALUE is offered at a deliberately
wrong type with every Rust-side guard bypassed**, so the kernel is the only
thing that can refuse it:

| substitution | negative control | why it is not vacuous |
|---|---|---|
| `dif_pos` | its value at `dif_neg`'s type | both types are real and well-formed and differ only in which branch the right-hand side names — the exact copy-paste failure a mirrored construction produces |
| `Eq.subst` | its value at the reversed-transport type (`motive b -> motive a`) | a real, inhabited proposition, built here from the same pieces |
| `And.left` | its value at `And.right`'s type | `a` and `b` are two distinct bound `Prop`s; a name-based check would not even look |
| `Nat.le_of_lt_add_one` | its value at `Nat.le_succ`'s type, both read from the same pinned fixture | a real Pi over `Nat` from the same real stream |

One thing the `Nat.le_of_lt_add_one` fixture taught, worth recording because it
cost a build cycle: **`nat_order_substitution::discover` is EAGER.** It requires
`Bool`, `Bool.rec`, `True`, `True.intro`, `False`, `False.rec` and the `Eq`
family before it will build anything, even for a name whose own construction
touches none of them. The first fixture — `lean4export Mathlib -- Nat.le_of_lt_add_one`,
that declaration's own closure and nothing else — carries none of those, so
`reconstruct` declined with `RequiredDeclarationUnavailable` and all three tests
failed identically. The committed fixture is
`lean4export Mathlib -- Nat.le_of_lt_add_one Bool True False Nat.ble Nat.pred Nat.sub`,
which is what a real statement closure looks like. (The optional
`pred`/`sub`/`ble`/`and` primitives are already lazy, via
`check_required_optional_prims`; the eager set is not, and making it lazy is a
separate change nobody needed yet.)

The failure mode is worth naming as well: a decline shows up as
`Ok(None)`-looking test breakage two `.expect`s downstream, and the panic line
does not distinguish the two. Reading the fixture's own inductive list is what
found it, not reading the panic.

`Nat.le_of_lt_add_one` additionally has a control at this crate's OWN guard
(`a_mismatched_wire_ty_makes_reconstruct_decline`): a mismatched `wire_ty` must
make `reconstruct` decline rather than coerce, which is the mutation target for
the `def_eq` check inside it.

The native quotient exemption's three guards — the kind check, the fixed-name
check, and the "this import actually admitted the validated package" check — are
each exercised on their own in `lib.rs::native_quotient_tests`, so deleting any
one of the three kills exactly one test. `quot_sound_is_never_exempted` is the
one that matters most: it adds `Quot.sound` to the admitted list and requires the
exemption to refuse it anyway.

At the integration level, `tests/statement_adapter.rs` carries both halves: a
statement stream whose closure carries the complete quotient package now crosses
(and the report names exactly the four members), and a stream carrying an
ordinary provable `Theorem` **beside** the same validated package is still
refused by name — so the new `continue` cannot be the reason a proof-bearing
declaration got in.

### Before / after over the same 756-row population

`artifacts/measurements/statement-import-blocker-census-2026-09-05-after-c4.json`,
measured at `88609630f` against the same pins (Mathlib `c5ea00351c28`, Lean
4.30.0), over a freshly re-exported set of the same 751 streams (elaboration
reproduced the baseline exactly: 5 failures, same three classes, 3/1/1; export
751 of 751, rc 0, no empty stream; negative control rejected).

**Population survival is unchanged: 390 admitted before, 390 after. Every class
count is identical.**

| class | before | after | delta |
|---|---:|---:|---:|
| `admitted` | 390 | 390 | +0 |
| `trusted-declaration-in-closure` | 361 | 361 | +0 |
| `coercion-variable-block` | 3 | 3 | +0 |
| `field-notation-variable-block` | 1 | 1 | +0 |
| `elided-proof-glyph` | 1 | 1 | +0 |

**And the frontier moved by exactly the amount it should have.** Each of the
five names this lane addressed falls to zero as a first blocker, and the same
150 rows reappear behind the next declaration in their closure. The two columns
balance to the row: −150 and +150.

| first blocking declaration | before | after | delta |
|---|---:|---:|---:|
| `Quot` | 73 | 0 | **−73** |
| `dif_pos` | 34 | 0 | **−34** |
| `Nat.le_of_lt_add_one` | 24 | 0 | **−24** |
| `And.left` | 12 | 0 | **−12** |
| `Eq.subst` | 7 | 0 | **−7** |
| `funext` | 0 | 62 | **+62** |
| `eq_self` | 97 | 131 | **+34** |
| `WellFounded.Nat.eager_eq` | 0 | 24 | **+24** |
| `And.right` | 0 | 19 | **+19** |
| `asymm` | 0 | 10 | **+10** |
| `ne_eq` | 0 | 1 | **+1** |
| `Nat.mod_lt` | 90 | 90 | +0 |
| `em` | 23 | 23 | +0 |
| `propext` | 1 | 1 | +0 |

That is the C4 answer, and it is not the one the roadmap's exit criterion was
shaped to expect: **the feature does exactly what it was specified to do, and
population survival measures zero.** The blockers in this population are
LAYERED, and the layer underneath the constructive names is mostly axioms this
kernel deliberately does not have:

| what is behind the 361 | rows | share |
|---|---:|---:|
| axioms this kernel excludes (`eq_self`→`propext` 131, `funext` 62, `em` 23, `propext` 1) | **217** | 60% |
| Lean's well-founded-recursion machinery (`Nat.mod_lt` 90, `WellFounded.Nat.eager_eq` 24) | **114** | 32% |
| ordinary constructive names, still substitutable (`And.right` 19, `asymm` 10, `ne_eq` 1) | **30** | 8% |

The 30 in the last row are the measured next increment — `And.right` is
`And.left` mirrored, `ne_eq` is `Eq.refl`, `asymm` is an order lemma — and this
lane deliberately stops rather than take them, because the measurement above
predicts they will move the frontier by exactly 30 and survival by 0 again. A
census re-run is what would establish that, not an argument.

**The quotient exemption's evidence is the −73, not an admitted-row
attribution.** No admitted row in this population carries a quotient package
(`rows_naming_the_quotient_package` is 0), so the only observable is that 73
rows stopped reporting `Quot` and started reporting what is behind it. 153
admitted rows name at least one reconstructed substitution, all of them from
the pre-existing set.

### The trusted surface, before and after

A substitution is a CALLER of `Kernel::add_declaration` (ADR-0601); nothing in
this lane touches a file inside the kernel crate's trusted core, and the
measurement says so rather than the claim resting on inspection.

| gate | before | after |
|---|---|---|
| `check-kernel-trusted-core.py` | exit 1, 257 trusted functions / **5,534** trusted function lines | exit 1, 257 / **5,534** — output byte-identical (`diff` empty) |
| `check-trust-closure.py` | exit 1, `failures=2` | exit 1, `failures=2` — output byte-identical |
| `gen-lean-axiom-ledger.py --check` | exit 0, `total=30 axreal=30 … axiom_free=8` | exit 0, same |
| `check-autogenesis-holdout-isolation.py` | exit 0, `held_out=216 files_scanned=1132 references=0 verdict=PASS` | exit 0, identical |
| `clippy -p axeyum-lean-import --all-targets -- -D warnings` | — | exit 0 (five findings in this lane's own code fixed first: two `similar_names`, two `map_unwrap_or`, one `match_same_arms`) |
| `check --workspace --all-targets` | — | exit 0 — run because `ImportReport` gained a PUBLIC field, and a kernel-crate-clean change is not a workspace-clean change |
| `check-merge-hygiene.sh` | — | PASS, `markers=0 adr_index=ok generated=current` |
| `check-links.sh` | — | exit 0, `all links ok` |
| `validate-facts.py` | — | exit 0; no fact changed |

### Two real-Lean suites are red, and both were measured red on `main` first

`cargo test -p axeyum-lean-import` is green on **26 of 28 integration suites and
all 150 lib tests** (146 passed, 4 ignored), including the ten in
`statement_adapter` and every control this lane added. Two suites fail, both of
them real-Lean gates on the moved 4.34.0-rc1 pin:

| suite | failure |
|---|---|
| `real_lean_wire_differential::our_kernel_admits_nothing_the_real_lean_kernel_refuses` | `violations=2` of 307 mutants: `level.max-kind:1322:max-to-imax` (`DecidablePred`, `max u 1` vs `imax u 1`) and `level.succ:1534:+1` (`Sigma.mk` universe too big) |
| `thin_lean_adapter_goal_pack::the_eight_required_categories_are_each_graded_correctly_by_real_pinned_lean` | category `wrong_goal` graded `accepted`, expected `rejected` |

**Both were re-run at the pre-change commit `26a245dc4` in an isolated snapshot
and fail identically** — same `WIRE_DIFFERENTIAL` counts (`generated=11622
checked=307 lean_kernel_rejected=113 violations=2`), the same two violation ids,
and the same `wrong_goal` assertion, with the pinned toolchain present and
`matches_pin=true` in both runs (so neither is a skip). This lane touches **zero
files in `axeyum-lean-kernel`** (`git diff --name-only 26a245dc4 HEAD --
crates/axeyum-lean-kernel/` is empty), and neither suite reaches
`import_statement_ndjson` — both use `import_ndjson`, where
`trusted_substitution` is off. Reasoning would have said the same thing; the
snapshot run is what makes it a measurement.

They are the same family as the three gates `14-lean-lang.md` records as red on
`main` since the pin moved on 2026-09-03, and they belong to whoever owns that
pin move. `stricter_than_lean=0` in both runs, so the direction of the
disagreement is "we admit what Lean refuses" and not the reverse.

Two of the four gates below were **already red on `main`** before this lane and are
recorded here so the next reader does not attribute them to it:
`check-kernel-trusted-core.py` fails `FAIL D: file(s) joined the trusted core:
['image_group.rs']`, and `check-trust-closure.py` fails on a stale disclosure
plus an identity-map drift. Both produce byte-identical output before and
after. (The 5,534 figure also corrects ADR-1600's 5,526, which this lane's brief
quoted: the core grew by 8 lines when `image_group.rs` joined it, which is the
same event `FAIL D` is reporting.)

The published artifact carries **counts per class and per family and ids only
for non-held-out rows**: 205 held-out ids in the population, 551 ids listed,
**0 held-out ids listed**. No fact file changed status; nothing was proved,
attempted, or dispatched.

## Alternatives

**Substitute `eq_self` by adding `propext` to the kernel.** Rejected, and it is
the whole reason this ADR reports a correction rather than seven substitutions:
`propext` is an axiom, admitting it moves the axiom-freedom metric for every
theorem whose proof reaches it, and ADR-1662 explicitly separated that decision
from this one. 97 rows is a large prize and it is exactly the size of prize that
makes a trusted-surface decision worth taking deliberately rather than as a side
effect of a substitution list.

**Substitute `Quot` the way the theorems are substituted** -- reconstruct a
`Quot` declaration from primitives. Rejected as incoherent: the quotient package
IS primitive. There is nothing underneath it to rebuild it from, which is
precisely why `Kernel::add_quotient_package` exists and why it derives the four
types rather than checking a proof.

**Keep refusing the quotient package, as doc 294's hard rule says.** Rejected,
with the reasoning spelled out under Evidence: the rule's stated ground is that
a RECONSTRUCTION cannot exist, which is true and beside the point, because the
kernel already derives the four package types itself. Refusing it costs 73 rows
the ability to STATE their proposition, and buys nothing the gate exists for.

**Exempt `DeclarationKind::Quotient` outright.** Rejected. The exemption is
pinned to the four canonical names AND to this import having actually completed
the validated package, so a stream that renames a package member, delivers a
partial package, or delivers a fifth quotient record gets nothing. `Quot.sound`
-- the one member of Lean's quotient story that states a proposition -- is
absent from the list on purpose, absent from this kernel entirely
(ADR-0456/ADR-1595), and has no `quot.kind` spelling in this exporter, so it
cannot arrive by this route at all.

**Admit `Nat.le_of_lt_add_one` at a type of our own** (the bare
`Nat.le (succ n) (succ m) -> Nat.le n m` shape our prelude uses). Rejected: the
spelling is the thing that blocks the rows. Mathlib states it with `LT.lt Nat
instLTNat` and `HAdd.hAdd`, and a substitution that only works against the bare
shape would pass its own test and change nothing in the census. It is admitted
under the stream's own type, and its committed regression fixture is the pinned
Lean 4.30 export of the real declaration.

## Consequences

**The blocker distribution moves, it does not shrink by subtraction.**
ADR-1662 said this and it is worth repeating: the census reports the FIRST
trusted declaration each stream meets, so unblocking one name exposes whatever
was behind it. The after-census is a re-run, never an arithmetic adjustment of
the before-census. Measured here, that caveat turned out to be the whole
result: −150 first blockers, +150 first blockers, +0 admissions.

**C4's demand gate needs a different ranking.** It admits a feature when it is
"the smallest shared blocker for a preregistered high-value population", and
the census it reads ranks by FIRST-reported blocker. On a layered frontier
that ranking is a measure of ORDER IN THE STREAM, not of demand: `Quot` looked
like 73 rows of demand and was worth 0. The census now records enough to rank
by full-closure blockers instead (the streams are on disk and the per-row
report names what each import substituted), and doing that before the next
demand-gated feature is the cheapest correction available.

**Two of the three things behind the new frontier are project-level decisions,
not engineering.** `propext` (via `eq_self`, 131 rows), `funext` (62) and `em`
(23) are axioms this kernel deliberately excludes; ADR-1595 and ADR-0512 priced
the same commitment for quotients and for ℝ. 217 of 361 rows now sit behind
that commitment, which makes "should this kernel stay intuitionistic for
IMPORTED STATEMENTS" a question with a number attached for the first time.
This ADR does not answer it.

**`ImportReport` gained one field.** `native_quotient_package` carries the four
names, populated only on the success path of `add_quotient_package`, read back
from the ADMITTED declarations rather than the wire records. It is the field a
caller consults to tell "this kernel's own quotient package" apart from "a
trusted declaration the stream delivered", exactly as `substituted_theorems` is
for the reconstructions.

**Axiom accounting is unchanged.** `Kernel::axiom_footprint` still counts every
`Declaration::Quotient` a proof reaches, so a theorem that uses `Quot.lift` is
still visibly not axiom-free. The quotient exemption is about ADMITTING a
statement, never about what a later proof may claim.

**Three earlier claims are corrected, not extended.**

- ADR-1662's "seven constructive names" is six. `eq_self` is `propext`-dependent.
- `docs/autogenesis/294-…`'s "`Quotient` never exempted, by hard rule" and
  `docs/autogenesis/295-…`'s `permanent — Quot` row no longer hold. The
  reasoning is under Evidence; both documents are left as written, per this
  repository's convention for a superseded measurement, and this ADR is the
  correction they point forward to.
- ADR-0604 §2's "exactly two names (`Nat.mod_lt`/`eq_self`)" was already
  corrected by doc 295 and is corrected again here from a different direction:
  `Nat.mod_lt`'s own closure needs six, a statement closure reaching it needs
  more, and `eq_self` needs an axiom rather than a construction.

**A lane that re-derives an existing measurement pays twice.** Two of this
lane's three findings were in the tree already (docs 240 and 295) and were
re-derived because ADR-1662 — written eight days later, by a different lane, on
a bigger population — recommended the opposite. The cheap defence is the one
this ADR now carries: the finding is a TEST, so the next census cannot quietly
re-recommend `eq_self`.

**What this does NOT establish.** Nothing here proves any mirror. An admitted
goal is an open fact with a kernel goal; no fact changed status in this lane and
no held-out row's id was read, quoted, or used. And the whole measurement is
bound to one pin pair (Mathlib `c5ea0035`, Lean 4.30.0), like the census it
extends.

## Related

- [ADR-1662](adr-1662-the-statement-import-blocker-is-a-proof-inside-the-definition-closure-not-the-variable-block.md)
  -- the census this implements, and the recommendation this corrects
- [ADR-0604](adr-0604-lean-is-the-surface-syntax.md) -- the statement-only import
  route
- [ADR-0601](adr-0601-three-producers-one-trust-anchor.md) -- one trust anchor;
  a substitution is a CALLER of `Kernel::add_declaration`, never a change inside
  the kernel
- [ADR-1595](adr-1595-quotients-stay-setoids-and-quot-sound-stays-out.md) --
  why `Quot.sound` is out, and the `axiom_footprint` accounting this exemption
  leaves untouched
- [ADR-0456](adr-0456-real-is-an-ordered-ring-modelled-by-int.md) -- the earlier
  pricing of the same choice for ℝ
- [`docs/autogenesis/294-statement-only-import-goal-record.md`](../../autogenesis/294-statement-only-import-goal-record.md)
  -- the `Quotient` "hard rule" this overturns, and the gate's own mutation test
- [`docs/autogenesis/295-mod-lt-and-eq-self-cascades-are-not-a-two-name-extension.md`](../../autogenesis/295-mod-lt-and-eq-self-cascades-are-not-a-two-name-extension.md)
  -- the earlier `eq_self`/`Nat.mod_lt` measurement this re-confirms and extends
- [`docs/plan/library-artifact-compatibility-roadmap-2026-08-30.md`](../../plan/library-artifact-compatibility-roadmap-2026-08-30.md)
  -- C4
