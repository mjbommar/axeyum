# Array (QF_ABV) elimination proofs in Alethe — design + the Carcara obstacle

Status: **design note (empirically grounded).** Records what producing an Alethe
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

## The obstacle: Alethe/Carcara has no array theory rules

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
- The hard, blocking unknown ("does Alethe have array rules?") is resolved: **no**,
  so do not design around primitive array rules — design around ROW-as-axiom-rule
  + Ackermann-as-congruence, which the in-tree checker can own.
