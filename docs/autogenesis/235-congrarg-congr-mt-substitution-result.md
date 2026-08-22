# `congrArg`/`congr`/`mt` are reconstructed and kernel-checked — and 233's "no tail" claim was wrong

Date: 2026-08-22

Plan: [`233-adapter-blocker-is-three-theorems.md`](233-adapter-blocker-is-three-theorems.md)
(itself building on [`226`](226-production-measurement-and-general-producer-plan.md) P4).

## What was built

`crates/axeyum-lean-import/src/trusted_substitution.rs`: a fixed, reviewed
substitution list, `SUBSTITUTABLE_THEOREMS = ["congrArg", "congr", "mt"]`
(`propext` deliberately absent — it is a genuine axiom and nothing here
attempts to derive it). For an exact name in that list, `import_theorem`
(in statement-isolation mode only — see below) discards the untrusted
stream's `type`/`value` for that record and instead calls this module, which:

- discovers `Eq`/`Eq.refl`/`Eq.rec` (for `congrArg`/`congr`) or `Not`/`False`
  (for `mt`) structurally in the *current* kernel, checking their shape
  rather than assuming it (`Eq.rec` must be a two-universe-param `Recursor`;
  `Not` must be a zero-universe unfoldable `Definition`; `False` a
  zero-constructor `Inductive`) — never trusting that a compatible primitive
  exists;
- builds `congrArg`'s and `congr`'s value directly from `Eq.rec` applications
  (`congr` as `Eq.trans (congrArg f h2) (congrArg (fun k => k b) h1)`, with
  both the two `congrArg` steps and the transitivity themselves built from
  `Eq.rec` — never by naming `congrArg`/`congr`/`Eq.trans`), and `mt`'s value
  as the bare propositional lambda `fun a b hab hnb ha => hnb (hab ha)`;
- closes each construction's own free variables via `Kernel::abstract_fvars`
  immediately after building each internal motive, then wraps outer-to-inner
  into the final `Pi`/`Lam` telescope (`close_telescope`) — the same
  discipline `bounded_induction_support::build_congr` uses. An earlier
  version of this module tried to defer all closing to one final
  `Kernel::infer_and_close_scoped_fvars` call and **admitted nothing**: every
  `Eq.rec` application failed to typecheck against its own motive, because
  ordinary beta reduction cannot see through a lambda whose body still
  references its parameter as a raw free variable rather than a bound one.
  That failure mode and the fix are recorded in the module's own doc comment
  so it is not rediscovered.

`ImportReport` gained `substituted_theorems: Vec<String>` — the exact names
this import reconstructed itself. `import_statement_ndjson`'s
trusted-declaration gate exempts a declaration only when it is *structurally*
a `Theorem` **and** its name is recorded in `substituted_theorems` — a
declaration of kind `Axiom`/`Opaque`/`Quotient` can never be exempted no
matter what that list says (`is_exempted_trusted_declaration`, mutation-tested
below). Ordinary `import_ndjson` is untouched: the substitution only fires in
the new `import_into_staging_kernel_with_trusted_substitution` path used
exclusively by `import_statement_ndjson`.

## No Mathlib proof reaches the producer

For each of the three names, the untrusted stream's `type` and `value` fields
are still *parsed* (so a malformed record is still rejected as malformed
regardless of name — the wire-format check is unconditional) but their
resulting `ExprId`s are never used to build the admitted declaration; the
admitted `(type, value)` pair is built entirely from this module's own
`Eq`/`Eq.rec`/`Eq.refl`/`Not`/`False` term construction. Six unit tests
(`trusted_substitution::tests`) independently kernel-check each
reconstruction and assert `axiom_footprint = 0` and `theorem_dependencies = 0`
for the admitted declaration — i.e. the checked value is axiom-free and does
not depend on any other theorem (trusted or otherwise). The real end-to-end
run below independently confirms this held for every one of the 114 real
Mathlib-derived streams: `congrArg`, `congr`, and `mt` no longer appear as
**any** row's reported trusted-declaration blocker, in any of the 114 rows
that used to name one of them.

## Mutation table

| Guard | Mutation | Result |
|---|---|---|
| `is_exempted_trusted_declaration`: `kind == Theorem &&` | deleted (any kind can be exempted) | `an_axiom_is_never_exempted_regardless_of_the_substituted_list` and `opaque_and_quotient_are_never_exempted` FAIL — exactly 2 |
| `is_exempted_trusted_declaration`: `.iter().any(...)` | replaced with `true` (any name exempted) | `a_theorem_absent_from_the_substituted_list_is_never_exempted` and `an_empty_substituted_list_exempts_nothing` FAIL — exactly 2 |
| `reconstruct`: `if !SUBSTITUTABLE_THEOREMS.contains(...)` guard | deleted | `reconstruct_rejects_names_outside_the_fixed_set` FAILS (panics on `unreachable!()` for `"propext"`) — exactly 1 |

Each mutation was applied, run, and reverted in this same session; the
reverted state is what is reported below and reproduces the passing test
runs.

## The negative control

`F:ml430-mutation-7afa5ec620720a1501bf349d` (`n! = 0`, false) maps to
`r046.ndjson`. Before and after this change it is identically:

```
kernel-rejection candidate-typecheck-failed
DeclarationValueMismatch { declared: ExprId(2383), inferred: ExprId(2401) }
```

Unaffected and still declined — this row never reached `adapter-rejection` in
either run (it reaches the producer and is declined there), so it is not a
row this change touches, but it confirms the substitution introduces no path
by which a false candidate becomes admissible.

## Re-running the frozen 2026-08-19 reflexivity census

Re-run via `cargo run --release -p axeyum-lean-import --example
statement_reflexivity_coverage -- <archive>/streams <archive>/mapping.json`
against the same hash-pinned archive `233` and the original
`mathlib-reflexivity-coverage-v1.json` manifest read
(`/nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1`).
This is a diagnostic re-run, not a replacement for the frozen manifest — the
frozen artifact and its `tooling_commit` pin are untouched.

**Top-level outcome distribution: unchanged.**

| Outcome | Before | After |
|---|---:|---:|
| `adapter-rejection:trusted-declaration` | 114 | 114 |
| `admissible-proof` | 2 | 2 |
| `kernel-rejection:candidate-typecheck-failed` | 7 | 7 |
| `producer-decline:terminal-not-exact-equality` | 15 | 15 |

**But the reported blocking declaration per row changed completely** (the
classifier reports whichever trusted declaration a canonical-content sort
happens to place first, and that is genuinely a different name once the top
three are gone):

| Blocking declaration | Before | After |
|---|---:|---:|
| `congrArg` | 56 | **0** |
| `congr` | 38 | **0** |
| `mt` | 19 | **0** |
| `propext` | 1 | 1 |
| `eq_of_heq` | 0 | 41 |
| `eq_self` | 0 | 20 |
| `Quot` (Quotient package) | 0 | 19 |
| `if_neg` | 0 | 18 |
| `ite_self` | 0 | 15 |

Zero of the 114 rows moved out of `adapter-rejection`. `congrArg`/`congr`/`mt`
are demonstrably gone from the *reported* blocker in every row that used to
name one — the substitution unambiguously fires on real data, at scale — but
every one of those rows was *already* blocked by additional trusted
declarations the reported "first blocker" field was hiding.

## Why: 233's "no tail" measurement only ever showed the first blocker

`import_statement_ndjson`'s gate scans *every* admitted declaration and
returns on the first one of kind `Axiom`/`Theorem`/`Opaque`/`Quotient` it
finds, in `declaration_identities` order — which is a **canonical structural
content sort**, not the stream's admission order and not a dependency
ordering. 233 read that one reported name per row and concluded four names
covered 114 of 114. That is a true count of *first-reported blockers*; it is
not a count of *all* blockers, and the two are very different here.

Measured directly (independent Rust tool, `axeyum_lean_import::import_ndjson`
+ counting `declaration_identities` by kind) on `r000.ndjson` — one of the 56
streams 233 attributed to `congrArg` alone:

```
counts by kind: {"Constructor": 27, "Definition": 105, "Inductive": 22, "Recursor": 22, "Theorem": 32}
total trusted (Axiom|Theorem|Opaque|Quotient): 32
```

32 trusted declarations, not 1: `congrArg`, `eq_of_heq`, `Eq.symm`,
`noConfusion_of_Nat`, and **28 further `Nat.*` lemmas** — `Nat.le_trans`,
`Nat.sub_le`, `Nat.div_rec_lemma`, `Nat.le.brecOn`,
`Nat.not_le_of_not_ble_eq_true`, and so on — the auxiliary theorems Lean's
compiler generates around well-founded `Nat` division/subtraction recursion
and `Decidable`-based comparison. A from-scratch scan of every one of the 114
`train`/`development` streams' raw declaration records (not just the
admitted-kernel view, as an independent cross-check) found the **same ~30
names present in all 114**, confirming this is not one unusual stream: this
population is uniformly blocked by a shared closure of Lean/Mathlib `Nat`
infrastructure theorems, of which `congrArg`/`congr`/`mt`/`propext` are just
whichever four happen to sort first across the population.

## What this changes about the plan

233's "if the three theorems are reconstructed, 137 of 138 reach a producer"
projection does not hold; it should be retracted. The real remaining surface
per row is on the order of 30 declarations, most of which (`Nat.le_trans`,
`Nat.sub_le`, `Nat.div_rec_lemma`, ...) are **substantive `Nat` facts**, not
one-line consequences of `Eq.rec` — reconstructing them independently means
re-proving a meaningful slice of Lean core's `Nat` library against axeyum's
own kernel, which is an undertaking on the scale of `nat_prelude` work
already tracked elsewhere in this repository, not a small fixed
three-declaration substitution. `Quot` (19 of the secondary blockers, and
present without being reconstructible) is architecturally in the same
category as `propext`: a genuine primitive, not a derivable theorem, and nothing
here or planned should attempt to substitute it.

The three theorems named in this plan (`congrArg`, `congr`, `mt`) **are**
fully reconstructed, independently kernel-checked, axiom-free, and verified
at scale to no longer block on their own account — that capability is real
and is not undone by this finding. What is retracted is the claim that
removing them was sufficient to unblock the population; it was not, and the
gap is now measured rather than assumed.

## Reproduction

```sh
cargo test -p axeyum-lean-import --lib trusted_substitution::
cargo test -p axeyum-lean-import --lib statement_isolation_tests
cargo run --release -p axeyum-lean-import --example statement_reflexivity_coverage -- \
  /nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/streams \
  /nas3/data/axeyum/autogenesis/coverage/26fcc2c2f-mathlib-v4.30.0-reflexivity-train-development-v1/mapping.json
```
