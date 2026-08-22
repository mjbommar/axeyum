# Array (QF_ABV) elimination proofs in Alethe — design + the Carcara obstacle

Status: **design note (empirically grounded); its central obstacle was REFUTED on
2026-08-21 — read the box in §2 before anything else.** Records what producing an Alethe
proof for axeyum's array elimination (P3.5) actually requires, the obstacle found
by inspecting the Carcara checker, and the recommended path — so the next session
starts correct rather than assuming arrays have first-class proof rules. Mirrors
the design-first approach that de-risked the QF_BV bitblast proof system.

## What axeyum does today (the reduction to prove)

`axeyum_rewrite::eliminate_arrays` (ADR-0010) lowers `QF_ABV` → `QF_BV` by:
1. **Read-over-write (ROW):** `(select (store a i v) j)` ⇒ `(ite (= i j) v (select a j))`,
   applied bottom-up so every `store` is eliminated.
2. **Ackermann:** the remaining `(select a k)` terms become fresh BV variables, with
   congruence side-conditions `k1 = k2 ⇒ sel_{a,k1} = sel_{a,k2}` for reads of the
   same array.

The result is a `QF_BV` formula axeyum can already prove `unsat` with a complete,
dual-checkable Alethe proof (the P3.3 driver `prove_qf_bv_unsat_alethe`). So an
array proof is: **justify the reduction, then compose with the QF_BV proof.**

## The obstacle: RESOLVED 2026-08-21 — Carcara DOES have array rules

> **This section was the load-bearing claim of the note and it is now false.**
> It is kept, struck through by this box, because it was quoted verbatim into six
> doc comments, into `check_alethe`'s rule dispatch, and into the design of two
> emitters, and a reader who meets those needs to know where the belief came from.
>
> Carcara 1.1.0 (`ufmg-smite/carcara` at `6624ea80`, 2026-08-12) registers four
> array rules in `carcara/src/checker/shared.rs`:
>
> | rule | premises | conclusion |
> |---|---|---|
> | `arrays_idx` | — | `(= (select (store a i e) i) e)` |
> | `arrays_row` | `(not (= i j))` | `(= (select (store a i e) j) (select a j))` |
> | `arrays_row_contra` | `(not (= (select (store a i e) j) (select a j)))` | `(= i j)` |
> | `arrays_ext` | `(not (= a b))` | `(not (= (select a k) (select b k)))`, `k` a `choice` term |
>
> `arrays_idx` **is** axeyum's `read_over_write_same`, shape for shape:
> `carcara/src/checker/rules/arrays.rs::idx` matches
> `(= (select (store a i1 e1) i2) e2)` and asserts `i1 = i2` and `e1 = e2`, which
> is exactly `is_read_over_write_same` in `crates/axeyum-cnf/src/alethe.rs`. Only
> the NAME differed, and the name is what an external checker answers to.
>
> Measured — same problem, same proof, one identifier changed:
>
> ```text
> $ carcara check row.alethe p.smt2       # :rule read_over_write_same
> [ERROR] checking failed on step 'rw' with rule 'read_over_write_same': unknown rule
> invalid
> $ carcara check idx.alethe p.smt2       # :rule arrays_idx
> valid
> ```
>
> **This mattered to a published number.** `Evidence::portable_artifact` counted
> every `Evidence::UnsatAletheProof` as an artifact an external checker can read.
> The `QF_ABV` read-over-write-same route emitted `read_over_write_same`, so a
> proof Carcara answers `invalid` was being counted toward the "externally
> checkable" figure — the same defect as the `lia_generic` case that function's
> own comment warns about, one level down, and worse, because `lia_generic` is at
> least *holed* by Carcara while an unknown rule is a hard rejection.
>
> Fixed 2026-08-21: `check_alethe` accepts `arrays_idx` and `arrays_row` under
> Carcara's semantics, `prove_qf_abv_unsat_alethe` emits `arrays_idx`, and
> `portable_artifact` decides Alethe portability from the artifact's rule
> vocabulary (`axeyum_cnf::non_carcara_checked_rules`) instead of from its variant.
> `crates/axeyum-solver/tests/carcara_crosscheck.rs` runs the real binary on the
> shipped proof, on the same proof with the old name (negative control), and on a
> tampered conclusion.
>
> `read_over_write` — the general `ite` form — still has **no** Carcara
> counterpart. `arrays_idx` is its `i = j` case and `arrays_row` its `i ≠ j` case;
> the unconditional `ite` equality needs a case split over the two, which nothing
> emits yet. It stays internal-only, and the vocabulary gate says so.
>
> Also measured the same day, with Carcara available for the first time on this
> host: **five crosscheck tests that assert Carcara acceptance actually fail** —
> four `ufbv_*_congruence_is_accepted_by_carcara` with
> `parser error: identifier '!fn_app_2' is not defined` (the emitted `.smt2` does
> not declare the Ackermann function symbol the proof names), and
> `route2_bvsub_rewrite_proof_is_accepted_by_carcara` with
> `rule 'bv_poly_simp': unknown rule`. They had been skipping, silently, for as
> long as they have existed. Not fixed here; recorded so the next lane does not
> read them as green.

*What follows is the original 2026-07 analysis, correct as of the Carcara it was
read against and wrong now.*

Inspecting `references/carcara/carcara/src/checker/`:
- There is **no array rule file** (rules cover bitvectors, LIA, clausification,
  congruence, resolution, tautology, strings, PB, quantifiers, `rare`,
  reflexivity/transitivity/subproof) and **no `select`/`store` primitive rule** in
  the dispatch (`shared.rs`).
- Array rewrites (incl. ROW) are expressed as **`rare` steps** — Carcara's `rare`
  rule (`rules/rare.rs`) checks a rewrite against a NAMED rule loaded from cvc5's
  external **RARE rule database** (`rare_rules` passed into the checker). Without
  that database a `rare` step is `RareRuleNotFound`.

Consequence: a Carcara-`valid` array proof would require shipping/loading cvc5's
RARE database and emitting `rare` steps that reference its exact rule names — a
heavier external dependency than the bitvector path (which uses first-class
`bitblast_*` rules). This is the array analogue of the `lia_generic` situation
(Carcara holes it), but more so: arrays have *no* native rules at all.

**2026-07-09 qualification (ADR-0075).** This obstacle applies to array axioms,
especially ROW and the disequality/diff-witness direction of extensionality. It
does not apply to ordinary equality congruence. The direct conflict
`a=b ∧ select(a,i)≠select(b,i)` now renders literal SMT-LIB `select` and is
accepted by Carcara using only `eq_reflexive`, `eq_congruent`, optional `symm`,
and resolution. The same artifact checks in-tree and reconstructs in Lean with
no array-elimination trust step.

## Recommended path: internal-checker first

Target axeyum's **own `check_alethe`** (which already validates the full QF_BV
proofs internally, after this session's `bitblast_*`/equality/CNF rule port), not
Carcara-validity, for the array layer:

1. **Add array-axiom rules to `check_alethe`** as sound *structural* checks (the
   same style as the ported `eq_*`/`bitblast_*` rules):
   - `read_over_write`: a step concluding
     `(= (select (store a i v) j) (ite (= i j) v (select a j)))` is valid by the
     ROW axiom (structural shape check).
   - `read_over_write_same`/`_diff`: the collapsed forms when `i`,`j` are
     syntactically equal/known-distinct.
   - Array extensionality already routes through congruence-over-`select`-as-UF
     (`prove_unsat_by_congruence`, used in dispatch) — reuse it.
2. **Ackermann congruence** is plain `eq_congruent` over `select` treated as an
   uninterpreted function — already emittable (`prove_qf_uf_unsat_alethe` /
   `euf_alethe`).
3. **Compose**: `assume` the array assertions → ROW/Ackermann rewrite+congruence
   steps reduce them to the `QF_BV` formula → the P3.3 QF_BV proof closes to `(cl)`,
   chained by `trans`/`resolution` (the same bridge shapes already validated).

So the bridge inventory is the *same* as QF_BV (cong/trans/resolution + the new
array-axiom rules); only the array-axiom rules are new, and they are sound
structural checks our checker can own without Carcara.

## Carcara-validity for array axioms as a later step

For external Carcara validation of ROW/extensionality-axiom proofs: emit the ROW
rewrites as `rare` steps with cvc5 rule names and integrate the cvc5 RARE database
into the cross-check harness (parallel to building Carcara itself). Until then,
those array-axiom steps are **internally checkable** (`check_alethe` + the new
array rules), matching the project's "independent checker" rule via the in-tree
checker. Plain select congruence is already externally checked per ADR-0075.

## Function elimination (Ackermann, ADR-0013) — same shape

`QF_UF`/`QF_UFBV` function elimination is pure Ackermann congruence, which already
emits via `eq_congruent` (P3.2/P3.3). No new rules needed beyond what exists; the
P3.5 work there is wiring the function-elimination reduction's congruence
side-conditions into a composed proof, not new checker rules.

## Bottom line for P3.5

- Arrays: direct select congruence is now Carcara- and Lean-checked. Add/compose
  the remaining `check_alethe` array-axiom rules with the existing QF_BV/EUF
  proof machinery for broader `unsat` proofs; Carcara-validity of those axiom
  steps still needs the cvc5 RARE DB (deferred).
- Functions: compose existing `eq_congruent` Ackermann steps (no new rules).
- The hard, blocking unknown ("does Alethe have array rules?") was answered **no**
  in 2026-07 and the answer is now **yes** — see the box at the top. Design around
  `arrays_idx` / `arrays_row` / `arrays_row_contra` / `arrays_ext`, which an
  external checker owns, and keep the in-tree-only shapes (notably the `ite`-form
  `read_over_write`) clearly labelled as such.

## What this does NOT buy — measured 2026-08-21

`arrays_idx` does not make the `unsat-array-axiom` family portable, and the census
says so per instance. Over the 85 certified `unsat` instances that family covers in
the committed dominance audits (`crates/axeyum-bench/examples/array_axiom_portability_probe.rs`):

| `ArrayAxiomKind` | instances | share |
|---|---:|---:|
| `ReadCongruence` | 70 | 82.4% |
| `ReadOverWrite` | 8 | 9.4% |
| `StoreShadowing` | 5 | 5.9% |
| `SelectIte` | 1 | 1.2% |
| `StoreIteSelect` | 1 | 1.2% |

Every rung declines, and each for a different measured reason:

- **`arrays_idx` reaches 1 of the 85.** Exactly one instance's certificate is the
  ROW-same shape (`solver__array__write1.btor.smt2`), and in it the disequality is
  buried inside a BTOR bv1 encoding — `(= #b1 (bvnot (ite (= v1 (select (store a0
  v0 v1) v0)) #b1 #b0)))` — not asserted at top level, so the `assume` an Alethe
  proof needs is not a problem assertion. 67 of the 70 `ReadCongruence` instances
  have the same bv1-wrapped head.
- **The existing zero-trust Alethe ladder reaches 0 of 85.**
  `prove_qf_abv_unsat_alethe`, `prove_qf_uf_unsat_alethe`,
  `prove_qf_ufbv_unsat_alethe`, `prove_qf_abv_unsat_alethe_via_elimination` and
  `prove_qf_dt_unsat_alethe_via_simplification` all decline every one.
- **`eliminate_arrays` then bit-blast reaches 0 of 85**, and this is the
  structural blocker rather than a tuning one: array elimination rewrites every
  `select`-of-`store` to an `ite`, and `prove_qf_bv_unsat_alethe`'s fragment has
  no `Op::Ite` arm at all. Carcara has no `bitblast_ite` either, so the composition
  is not one flag away.
- The one clean McCarthy instance (`solver__array__smtaxiommccarthy.smt2`) asserts
  the general `ite` form at top level. That needs the `arrays_idx`/`arrays_row`
  case split described above — the smallest real slice of new work this note
  points at, worth 1 instance.

So the honest sizing for this family is: **the rule vocabulary was never the
binding constraint; the bv1 encoding and the missing `ite` support are.**
