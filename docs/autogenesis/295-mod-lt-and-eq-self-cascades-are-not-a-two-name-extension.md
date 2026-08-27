# 295 — `Nat.mod_lt`/`eq_self` are not a two-name allowlist extension: measured, not estimated

Date: 2026-08-27
Lane: allowlist-clippy

## Task

Doc 294 (and ADR-0604 §2's amendment) predicted that closing the 15
`Nat.Coprime` `TrustedDeclaration` declines from doc 292 needs exactly two
new allowlist entries — `Nat.mod_lt` and `eq_self` — following
`nat_order_substitution.rs`'s established pattern (build an independent
proof from primitives discovered in the foreign kernel, validate against the
stream's own declared type via `infer`/`def_eq`, never read the stream's own
value). This task's brief: check our kernel already proves each equivalent,
add the substitution, re-run the real failing export, and report the
closable/permanent split. **If our kernel does not have the equivalent, that
is a finding — report the exact statement needed and stop, never weaken the
guard.**

## Method

Pulled doc 292's own exports from s5 (`/home/mjbommar/lean-import-scale/
flywheel-2-exports/*.ndjson`; pins reverified unchanged: mathlib4
`c5ea00351c28e24afc9f0f84379aa41082b1188f`, lean4export
`a3e35a584f59b390667db7269cd37fca8575e4bf`). Wrote a standalone NDJSON
decoder (not committed — a throwaway analysis tool, kept in scratch) that
parses the same `lean4export` wire format `axeyum-lean-import`'s
`import_expression`/`import_theorem` consume (`{"in":…}`/`{"il":…}`/
`{"ie":…}` records) and renders any named declaration's type/value as a
readable term, plus enumerates every `thm`/`ax`/`opaque` record in a file.
Cross-checked every claim against the real, built
`statement_goal_record` example (`cargo run -p axeyum-lean-import --example
statement_goal_record`), never trusted from the decoder alone.

## Finding 1: `Nat.mod_lt` — our kernel has the STATEMENT, not a substitutable proof

Our kernel already proves the identical statement shape:
`crates/axeyum-lean-kernel/src/nat_prelude/gcd.rs:26-30`,
`p.mod_lt : ∀ x y, 0 < y → mod x y < y` (declared via `d.theorem(p.mod_lt, 2,
…)`, induction on `y`).

The real Mathlib/Lean-core wire type for `Nat.mod_lt` (decoded from
`nat-coprime-add-self-left.ndjson`, name id 1354) is exactly the same shape:
`∀ x y, 0 < y → x % y < y` (`%` resolving through `HMod.hMod`/`instHMod`/
`Nat.instMod`/`Nat.mod`). So on the STATEMENT alone, yes — our kernel has
the equivalent.

**But the substitution pattern's actual requirement is stronger, and this is
where it fails.** `nat_order_substitution`'s discipline (its own doc
comment, and `is_exempted_trusted_declaration`'s) is: never reuse the wire's
own proof value, always independently reconstruct a candidate from
primitives, then validate that candidate against the wire's own declared
type. Our kernel's `mod_lt` proof is built over **our own** `Nat.mod`
(`div_mod_exec`, a structural bounded-induction definition) — an entirely
different definitional route from the wire's `Nat.mod`, which (confirmed by
decoding it) is Lean 4 core's real well-founded-recursion definition
(`Nat.modCore`/`Nat.modCore.go`, termination justified by
`Nat.div_rec_lemma` — already bridged). Our proof's reasoning never touches
that recursion at all, so it cannot be replayed as a proof about the wire's
`Nat.mod` — a fresh, independent construction is needed that reasons about
**that** recursive structure.

**Measuring what that construction actually needs (not estimating it)**:
enumerated every `thm`-kind record in `nat-coprime-add-self-left.ndjson` —
the *smallest* representative export in the `Nat.mod_lt`-first-blocker
family (52 theorem-kind declarations total, `admitted_declarations` in the
low hundreds). Of those 52, **37 are already covered**
(`trusted_substitution::SUBSTITUTABLE_THEOREMS`,
`nat_order_substitution::SUBSTITUTABLE_NAT_ORDER_THEOREMS`,
`nat_le_brecon_substitution::SUBSTITUTABLE_NAT_LE_BRECON_THEOREMS`,
`nat_no_confusion_substitution::SUBSTITUTABLE_NAT_NO_CONFUSION_THEOREMS`).
**15 are not**, not 2:

| name | shape |
|---|---|
| `Nat.mod_lt` | the named target |
| `Nat.modCore_lt` | `∀ x y, 0 < y → Nat.modCore x y < y` — a genuine dependency of `Nat.mod_lt`'s own wire value, and a **separately admitted top-level `thm` record** in its own right (not removed by substituting `Nat.mod_lt`) |
| `Nat.modCoreGo_lt` | `∀ fuel y, 0 < y → ∀ x, x < fuel → Nat.modCore.go y _ fuel x _ < y` — the fuelled-recursion form `modCore_lt` reduces to |
| `WellFounded.Nat.eager_eq` | `∀ n, WellFounded.Nat.eager n = n` — an unfolding equation for Lean 4 core's *eager/memoized* fixpoint acceleration strategy |
| `WellFounded.Nat.fix._proof_1` | a generic fuel-decrease lemma over an arbitrary measure `h : α → Nat`, universally quantified — not Nat-specific arithmetic, WF-recursion infrastructure |
| `WellFounded.Nat.fix._proof_2` | sibling of the above |
| `WellFounded.Nat.fix.go._proof_1` | sibling of the above, for the `go` fuelled variant |
| `_private.Init.Data.Nat.Gcd.0.Nat.gcd._unary._proof_1` | `Nat.gcd`'s own private termination obligation |
| `Nat.lt_of_not_le`, `Nat.lt_or_ge`, `Nat.eq_of_beq_eq_true`, `Nat.ne_of_beq_eq_false`, `Nat.not_lt_zero`, `Nat.zero_lt_of_ne_zero`, `Nat.le_of_lt_add_one` | ordinary order/`beq` lemmas in `nat_order_substitution`'s existing style, but needing a primitive (`Nat.beq`) that module does not yet discover |

Seven of those fifteen (`Nat.mod_lt` through `_unary._proof_1`) are genuine
well-founded-recursion internals — not more Nat arithmetic identities in
`nat_order_substitution`'s existing mold, but the general
`WellFounded.fix`/eager-fixpoint machinery Lean 4 core's equation compiler
emits for *any* WF-recursive definition. Reconstructing them means
independently re-deriving that machinery's unfolding behaviour from
primitives (`Acc`, `WellFounded`, the measure function) — a materially
different and larger undertaking than `nat_order_substitution`'s 28 entries,
matching doc 294's own sizing warning ("matching or exceeding… in scope")
but **measured here to be at least that large for a single representative
fact**, not merely predicted. This is a new capability class, not a
same-day allowlist extension, and building it responsibly is out of
proportion for this task. **Reported as a finding, per the brief's own
stop condition — not attempted, and nothing in the guard was weakened.**

A larger export in the same family (`nat-coprime-two-left.ndjson`, the
`eq_self`-first-blocker case) has **175** theorem-kind declarations,
including the same seven WF-recursion internals plus dozens of
`Monoid`/`Semiring`/`Distrib`-class instance proof obligations for numeral
`2` and `Nat.pow` — confirming the cascade only grows for the other 8
`Nat.mod_lt`-first-blocker facts and the `eq_self`-first-blocker facts alike
(every one of the 15 states something about `Nat.Coprime = (Nat.gcd _ _ =
1)`, so every one forces `Nat.gcd`'s value — and hence this whole cascade —
to be admitted, regardless of which name is reported first).

## Finding 2: `eq_self` needs `propext`, which this kernel deliberately excludes — permanent, not deferred

Decoded `eq_self`'s real wire value (`nat-coprime-two-left.ndjson`, name id
2802): `eq_self := fun α a => eq_true (Eq.refl a)`, where `eq_true : {p :
Prop} → p → (p = True) := propext (Iff.intro …)` in Lean 4 core. The
STATEMENT itself is `∀ {α} (a : α), (a = a) = True` — a propositional
equality **between two different Props** (`a = a` and `True`), which is
exactly what propositional extensionality is for; a kernel with only
built-in proof irrelevance (any two proofs of the *same* Prop are equal)
cannot derive it, because `a = a` and `True` are not the same Prop
syntactically.

This kernel is deliberately intuitionistic:
`crates/axeyum-lean-kernel/src/prelude.rs:61` states outright that
`Classical.em`, `propext`, and `funext` do not exist here, and
`trusted_substitution.rs`'s own doc comment is explicit that `propext` "is a
genuine axiom, independent of everything else in the kernel," is
"deliberately absent from `SUBSTITUTABLE_THEOREMS`," and "nothing here
attempts to derive it." This matches an *earlier*, independent measurement
this project already made and had half-forgotten: doc 240 (2026-08-22)
already found "`eq_self` (20 rows) needs `propext`, which this kernel does
not have" in the general adapter-blocker census — this task re-derives the
same fact from the `Nat.Coprime` family's own real export, rather than
trusting the old doc's memory of it.

So `eq_self` is not "sizeable future engineering" like the `Nat.mod_lt`
cascade — it is **architecturally permanent under this kernel's design**,
in the same sense `Quot` is: adding it would mean adding `propext` as a
genuine new axiom, which is a project-level design decision (this kernel's
intuitionistic commitment), not a lane-scoped allowlist edit. Per the
brief: reported as the exact missing primitive, not attempted, guard not
weakened.

## No code changes made

Per the brief's own stop condition, and because nothing above is safely
closable within a reviewed, reasonable scope: **no changes to
`trusted_substitution.rs`, `nat_order_substitution.rs`,
`nat_le_brecon_substitution.rs`, or `nat_no_confusion_substitution.rs`.**
`git diff --stat` against all four is empty in this lane's commit.

## Guard mutation test (confirms the guard is still real, unmodified)

Reproduced doc 294's exact mutation on the same guard
(`crates/axeyum-lean-import/src/lib.rs`'s `import_statement_ndjson` scan,
`if matches!(identity.kind, Axiom | Theorem | Opaque | Quotient)` →
`if false && matches!(…)`):

- `cargo test -p axeyum-lean-import --lib --test statement_adapter --test
  statement_goal_record`: **exactly 3 tests turned red** —
  `statement_adapter::unrelated_axiom_is_rejected`,
  `statement_adapter::proof_bearing_target_is_rejected`,
  `statement_goal_record::a_theorem_reachable_only_through_an_auxiliary_definition_still_poisons_the_stream`
  — identical to doc 294's own result.
- Restored via `git checkout -- crates/axeyum-lean-import/src/lib.rs`;
  `git diff --stat` empty; re-ran the same three suites clean (106 lib + 8 +
  3 passed, 0 failed, 4 ignored — unrelated pre-existing).

## Re-run on the real failing exports

`cargo run -p axeyum-lean-import --example statement_goal_record` against
three of doc 292's own files, unchanged since that measurement:

| fact | target | result |
|---|---|---|
| `nat-coprime-add-self-left` | `coprimeAddSelfLeft` | `TrustedDeclaration { name: "Nat.mod_lt", kind: Theorem }` — unchanged |
| `nat-coprime-of-lt-minfac` | `coprimeOfLtMinFac` | `TrustedDeclaration { name: "Quot", kind: Quotient }` — unchanged |
| `nat-coprime-primes` | `coprimePrimes` | `TrustedDeclaration { name: "eq_self", kind: Theorem }` — unchanged |

All three reproduce doc 292's table exactly, confirming the census is still
accurate and this task's non-closure is not a regression or a stale
measurement.

## The closable/permanent split (classification method: measured closure, not first-reported name)

**0 of the 15 close.** Classification is by what actually blocks the fact's
full admission closure (enumerated via the standalone decoder over each
file's `thm`/`ax`/`opaque` records, cross-checked against
`SUBSTITUTABLE_*` lists), not by the single first-reported blocker name:

| class | count | facts | why |
|---|---:|---|---|
| permanent — `Quot` (hard rule) | 1 | `coprime_of_lt_minFac` | `Nat.minFac` reaches `Quot` directly; never exempted, by hard rule (doc 294, unchanged) |
| permanent — needs `propext` | 5 | `coprime_iff_isrelprime`, `coprime_of_dvd'`, `coprime_primes`, `coprime_two_left`, `Prime.dvd_iff_not_coprime` | first-reported blocker `eq_self` needs propositional extensionality; this kernel deliberately has none (Finding 2) |
| deferred — WF-recursion cascade, substantial future engineering | 9 | `coprime_add_self_left`, `coprime_add_self_right`, `coprime_of_dvd_left`, `coprime_of_dvd_right`, `coprime_one_left_iff`, `coprime_one_right_iff`, `coprime_self_add_left`, `Coprime.symmetric`, `not_coprime_zero_zero` | first-reported blocker `Nat.mod_lt`, but the real closure needs ≥7 WF-recursion-internal theorems (Finding 1) that are not, in principle, permanently unconstructible — just out of scope for this task |

The distinction between the last two rows matters: the `propext` row is a
project-level architectural boundary (closing it means adding an axiom this
kernel's design deliberately excludes); the WF-recursion row is ordinary,
sizeable engineering that a future task could complete without any design
change, once someone independently reconstructs Lean 4 core's generic
`WellFounded.fix` unfolding behaviour from primitives (the same kind of
project `nat_order_substitution`, `nat_le_brecon_substitution`, and
`nat_no_confusion_substitution` already are, at roughly the same or greater
scope than any one of them).

## What this corrects

ADR-0604 §2's amendment and doc 294 both state the remaining gap as "exactly
two names… `Nat.mod_lt`/`eq_self`," sized against `nat_order_substitution`'s
existing 28 entries. Measured here: the real closure for the *smallest*
representative fact in the family already needs 15 additional names beyond
existing coverage, not 2, and 7 of those are a structurally different kind
of construction (generic WF-recursion infrastructure) that
`nat_order_substitution`'s technique does not cover at all. Neither ADR-0604
nor doc 294 is amended by this lane (out of scope — the coordinating lane
owns ADR/frontier amendments per this task's brief); this document is the
measurement for whoever does.

## Did not touch

`trusted_substitution.rs`, `nat_order_substitution.rs`,
`nat_le_brecon_substitution.rs`, `nat_no_confusion_substitution.rs` (no
allowlist edits — nothing safely addable, see above), `artifacts/facts/`,
`artifacts/autogenesis/`, `scripts/fact-frontier.py`, any contract/decline
validator, ADR-0604 itself, or doc 294/292.
