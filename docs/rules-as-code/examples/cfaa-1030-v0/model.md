# CFAA V0 Formal Model

The model is [`rules.json`](rules.json). This page records what it encodes and
the choices a reader should check before trusting a result.

## Facts

One count charges exactly one of the modeled offenses: (a)(2), (a)(3), (a)(4),
(a)(5)(A), (a)(5)(B), (a)(5)(C), (a)(6), or (a)(7). The model does not decide
whether the elements of the offense are met; the offense is an input.

| Fact | Sort | Provision |
|---|---|---|
| `off_a2` … `off_a7` | Bool | (a)(2) … (a)(7) |
| `prior_conviction` | Bool | (c)(2)(C), (c)(3)(B), (c)(4)(C)–(D); "conviction" as defined in (e)(10) |
| `commercial_gain`, `criminal_or_tortious_purpose` | Bool | (c)(2)(B)(i), (ii) |
| `info_value_usd` | Int, dollars | (c)(2)(B)(iii) |
| `loss_usd` | Int, dollars | (c)(4)(A)(i)(I); "loss" as defined in (e)(11) |
| `medical_impairment`, `physical_injury`, `public_safety_threat`, `justice_security_computer` | Bool | (c)(4)(A)(i)(II)–(V) |
| `computers_damaged` | Int | (c)(4)(A)(i)(VI) |
| `serious_bodily_injury`, `death` | Bool | (c)(4)(E), (F) |
| `damage_or_loss_suffered` | Bool | (g) |

## Predicates

Each predicate is keyed to one provision and quotes an anchor phrase from it.
The groups are:

- **Harm factors.** `harm_I` … `harm_VI` at (c)(4)(A)(i)(I)–(VI), and
  `harm_any_I_VI` at (c)(4)(A)(i).
- **Clause applicability.** `c2A_applies` … `c4G_applies`, one per clause of
  (c)(2)–(c)(4), with `c2A_max` … `c4G_max` holding each clause's maximum term.
- **Maximum.** `max_years` at (c): the largest maximum among applicable clauses.
- **Civil action.** `civil_factor_I_V`, `civil_action_available`, and
  `civil_economic_damages_only` at (g).

## Modeling choices

1. **Overlapping clauses take the larger maximum.** For a repeat (a)(2) offense
   with an aggravator, (c)(2)(B) and (c)(2)(C) both apply by their terms. The
   model reports both and takes 10 years. The overlap itself is a checked
   finding (`penalty-overlap-c2b-c2c-sat`), so the choice is visible.
2. **"Any other offense" in (c)(4)(G)(i)** is read as residual to the offenses
   reached by (c)(4)(A)–(F). The text cites none of them; the rules file declares
   that justification explicitly, and `compiled.json` records it as declared,
   not textual.
3. **(c)(4)(E) and (F) displace (A)–(C)** because those subparagraphs open with
   "except as provided in subparagraphs (E) and (F)". (D) and (G) carry no such
   exception; (E) and (F) reach only (a)(5)(A) conduct, so (D) never meets them,
   and (G) is residual.
4. **Life is encoded as 1000** (`LIFE`), larger than every finite maximum.
5. **Out of scope:** (a)(1) and (c)(1); attempts and conspiracies under (b) and
   every "attempt" clause of (c); fines; forfeiture under (i) and (j); the
   two-year limitations period and the negligent-design exclusion of (g); and
   the investigative authority of (d). The cross-references these leave
   unconsumed are listed in `out_of_scope_refs` with a reason.

## Encoding for the solver

`rules_ir.py` emits Boolean predicates as `define-fun`. Int-valued case splits
(`ite`, `max`) are emitted as declared constants with defining clauses
(`c => v = a`, `not c => v = b`; `v >= v_k` and `v = v_1 or … or v = v_n` for a
maximum), and the exactly-one offense constraint is stated with Boolean clauses.
Both keep each obligation Boolean structure over linear integer atoms, the
fragment where Axeyum produces a checked lazy-arithmetic refutation
(`unsat-arith-dpll`). With Int-valued `ite` terms left in place the solver
still answers `unsat`, but without a certificate.
