# ADR-2120: quantifier activation by assignment — the instance clause carries its own activation literal, and the whitelist that was supposed to supply one fires on 3 of 525 files

Status: proposed
Index-summary: [ADR-2113] located `UFLIA`'s blocker at `rej_nocontext` — 100.0 % of 2,139,815 rejections, a positively occurring universal under a disjunction whose every matched tuple is discarded because `A ∨ (∀y.B(y))` does not entail `B(t)` — and named a **boolean-assignment guard on quantifier activation** as the fix, with [ADR-2114] finding the same engine refusing 127 of 134 `AUFDTLIRA` files at five syntactic shape guards. This lane sized that fix before building it and the sizing changes what should be built. **The mechanism both references use is not a separate SAT literal reaching the e-matcher; it is a CLAUSE.** z3 emits `¬q ∨ body[x:=t]` (`qi_queue.cpp:274-289`) and cvc5 emits `(=> q body)` which its CNF stream turns into the same clause (`instantiate.cpp:293`) — and this repository **already builds that clause**, in `positive_instance_formula` (`qinst_egraph.rs:1587`), which replaces the universal in its owner disjunction and hands back `A ∨ B(t)`: the activation literal carried in the term, valid unconditionally, retracted for free by the ground solver's own search. What gates it is `PositiveContext`, whose path whitelist is `BoolAnd`/`BoolOr` **only** (`:1334-1336`) — so a path crossing a `not`, a `=>`, or an `ite` branch yields `context: None` and the tuples are dropped at `:6213`. Measured with a polarity-tracking parser over all 1,200 Tier 1 rows of the six quantified divisions, joined to the ledger verdict and validated against [ADR-2114]'s 134 observed `mbqi_exit` rows (**126 of 129 agree; 82 of 85 on the discriminating subset where containment is equality**): the shipped whitelist finds a context on **3 of 525 undecided files**, while **97 of 525 (18.5 %)** hold a positively occurring split universal it refuses — `UFLIA` 52 of 114, `AUFLIRA` 11 of 22, `UFNIA` 23 of 146. The broad shape ceiling is reported too and is **refused by its own control**: 368 of 525 undecided files (70.1 %) hold the shape, but so do 499 of 675 DECIDED files (73.9 %), so shape presence is not a predictor and only the narrower column is a ceiling. Two further findings this lane's sources do not yet record: the positive replacement is admitted into `ground` but never into `ground_derivations`, so `collect_ground_derivations` (`:4957`) returns `None` and any `unsat` downstream of one ships **uncertified**; and [ADR-2113]'s claim that `OnlineQuantifierClauseSession` "abstracts every arithmetic atom to a fresh boolean" is refuted — `with_opaque_bool_atoms` is never called, so on an arithmetic atom the session **declines to exist**, which inverts its follow-on claim about the interleaved check being suppressed on `UFLIA`.
Index-status: proposed
Date: 2026-09-15

## Context

[ADR-2113] and [ADR-2114] are two independent trace lanes on two divisions that
arrived at one engine defect, and neither is trigger selection nor the datatype
theory.

- **UFLIA.** 429 of 478 silent universals sit under a disjunction and
  `rej_nocontext` is 100.0 % of 2,139,815 rejections. 98.2 % of the ground terms
  z3 substitutes are already in our ground set. We find the instances and throw
  them away.
- **AUFDTLIRA.** MBQI's refutation loop never ran on 132 of 134 files; on 127 the
  reason is one of five purely syntactic quantifier shape guards. Every one of
  those guards falls through to `prove_unsat_by_ematching` — so the two ADRs
  describe the same engine from two ends.

[ADR-2113] names the fix as "gate quantifier activation on a boolean assignment"
and says: *size (b) — widen where a `PositiveContext` is computed — first, build
(a)*. This lane did exactly that, and §1's measurement is why (b) is what gets
built.

## Decision

**Sizing first, and the sizing moved the target.** Three things are decided.

1. **The mechanism is a CLAUSE, not a literal plumbed into the matcher.** Both
   references gate instantiation on a SAT assignment, but the *artifact* they
   produce is the valid clause `¬q ∨ body[x:=t]` (§2). This repository already
   produces the identical clause by a different route — `positive_instance_formula`
   rewrites the owner in place, so the residual context IS the activation literal
   and the ground solver's own search IS the assignment. Nothing needs a new SAT
   variable for a quantifier.
2. **What blocks it is the path whitelist, and the whitelist is measured at
   near-zero coverage.** `PositiveContext` accepts `BoolAnd`/`BoolOr` steps only.
   On the six quantified divisions' 525 undecided Tier 1 rows it computes a
   context on **3 files**; **97** hold a positively occurring split universal it
   refuses. The widening is polarity tracking through `BoolNot`, `BoolImplies`
   and the two `Ite` branches, with the `Ite` condition, boolean `=`/`xor` and
   every `Forall` step still refused — the last for the counterexample already
   recorded at `qinst_egraph.rs:1346-1349`, which this lane did not attempt to
   work around.
3. **The certificate hole is fixed in the same change or the lever does not
   ship.** Today a positive replacement enters `ground` without entering
   `ground_derivations`, so every later `collect_ground_derivations` returns
   `None`. Widening the whitelist without closing that would convert a rarely
   taken uncertified path into a common one, which is the opposite of this
   repository's direction of travel.

## 1. Sizing, before any Rust

**Denominator, read from the ledger rather than quoted.**
`bench-results/ledger/t1-<DIV>-db31113fa.tsv`, 200 rows per division, `verdict
== unknown`:

| division | T1 rows | undecided | decided |
|---|---:|---:|---:|
| `AUFDTLIRA` | 200 | 81 | 119 |
| `AUFLIRA` | 200 | 22 | 178 |
| `UF` | 200 | 106 | 94 |
| `UFDTLIRA` | 200 | 56 | 144 |
| `UFLIA` | 200 | 114 | 86 |
| `UFNIA` | 200 | 146 | 54 |
| **total** | **1,200** | **525** | **675** |

(The brief's "645 undecided Tier 1 rows" is the seven-division figure including
`QF_NIA`'s 116, which is quantifier-free and not this lane's population:
525 + 116 = 641 on this snapshot. The number used below is 525, derived here.)

**The instrument.** `bench-results/quant-activation-20260915/qshape.py` — a
polarity-tracking s-expression classifier, not a grep, because the two guards
that decide this population are decided by the term tree: `nested-binder-in-matrix`
is *"strip the whole `forall` prefix, does the matrix still hold a quantifier"*
and `quantifier-below-top-level` is *"this assertion's root is not a `forall`
and it holds one somewhere"*. `(assert (forall ((x Int)) (or … (forall …))))`
and `(assert (or P (forall …)))` are the same file to a grep and land in
different guards here. `let` is **resolved, not expanded** (CLAUDE.md records a
lane's `let`-expander reaching 63.4 GB on this corpus), and the counts are over
the **DAG**: see §6 for the 105-digit integer the first version printed.

**The two columns, and why they are reported apart.**

- `activation_target` — the file holds a positively occurring universal that is
  not a unit assertion, either below a disjunction or inside another binder's
  matrix. This is the **shape ceiling**.
- `widen_target` — the file holds such a universal whose path to the assertion
  root crosses a connective the shipped whitelist refuses. This is the **lever's
  ceiling**, and it is a strict subset.

| division | undec | shape target | share | **widen target** | **share** | whitelist fires |
|---|---:|---:|---:|---:|---:|---:|
| `AUFDTLIRA` | 81 | 81 | 100.0 % | **4** | 4.9 % | 0 |
| `AUFLIRA` | 22 | 21 | 95.5 % | **11** | 50.0 % | 0 |
| `UF` | 106 | 94 | 88.7 % | **6** | 5.7 % | 2 |
| `UFDTLIRA` | 56 | 35 | 62.5 % | **1** | 1.8 % | 0 |
| `UFLIA` | 114 | 99 | 86.8 % | **52** | 45.6 % | 1 |
| `UFNIA` | 146 | 38 | 26.0 % | **23** | 15.8 % | 0 |
| **total** | **525** | **368** | **70.1 %** | **97** | **18.5 %** | **3** |

**The last column is the finding.** `PositiveContext` — the machinery that
exists precisely to make a nested universal's tuples usable — computes a context
on **3 of 525 undecided files** across all six divisions. That is a direct,
independent confirmation of [ADR-2113]'s `rej_handoff = 0`: the whitelist is not
under-powered on this corpus, it is very nearly inert.

**The discrimination control, which refuses the broad reading.** Run on the
DECIDED rows as well, because "the target shape is present on the files we fail"
is worth nothing unless the files we decide are a different population:

| | undecided | decided |
|---|---:|---:|
| shape target | 368 / 525 (**70.1 %**) | 499 / 675 (**73.9 %**) |
| widen target | 97 / 525 (**18.5 %**) | 103 / 675 (15.3 %) |

**Shape presence does not predict undecidedness** — it is marginally *commoner*
on the files we decide. `AUFDTLIRA` is 100.0 % on both sides and `UFDTLIRA` runs
the wrong way (62.5 % undecided against 68.1 % decided). So the 368 is a ceiling
on *shape*, not an estimate of convertible files, and this ADR does not quote it
as one. The narrower column separates the two populations in four divisions of
six and is the number the lever is sized on.

**The predicted shape-guard exit**, for the [ADR-2114] half, on the undecided
rows:

| division | nested-binder | q-below-top | multi-binder | no-top-universal | refutation-loop |
|---|---:|---:|---:|---:|---:|
| `AUFDTLIRA` | 81 | 0 | 0 | 0 | 0 |
| `AUFLIRA` | 6 | 16 | 0 | 0 | 0 |
| `UF` | 73 | 25 | 8 | 0 | 0 |
| `UFDTLIRA` | 15 | 34 | 1 | 0 | 6 |
| `UFLIA` | 78 | 27 | 9 | 0 | 0 |
| `UFNIA` | 5 | 115 | 1 | 25 | 0 |
| **total** | **258** | **217** | **19** | **25** | **6** |

**519 of 525 undecided files are diverted to e-matching by a shape guard before
MBQI's refutation loop is reached**, which is [ADR-2114]'s 127-of-134 finding
re-derived independently across all six divisions.

### 1a. The classifier is joined to a run that happened

A classifier only ever compared against itself is the un-failable checker this
repository keeps deleting. `exit-agreement.py` joins the predicted `mbqi_exit` to
[ADR-2114]'s observed one over its 134 traced `AUFDTLIRA` files
(`bench-results/dt-quant-trace-20260915/census/axtrace-134.tsv`):

| | n |
|---|---:|
| observed rows with at least one exit | 129 |
| observed rows where the rung was never reached | 5 |
| **prediction among the observed exits** | **126 of 129 (97.7 %)** |
| **discriminating subset** — observed set has exactly ONE exit, so containment IS equality | 85 |
| **prediction equals observed there** | **82 of 85 (96.5 %)** |

The join is containment and not equality because `axtrace`'s `mbqi_exit` is every
`[mbqi-shape]` line the run printed, comma-joined — the ladder re-enters the rung
many times per file over assertions the preprocessor has already rewritten, so
one file commonly shows two exits. A containment test against a usually-large set
drifts toward answering yes for everything, which is why the discriminating
subset is printed beside it and carries the real number.

**The three disagreements all run one way** — the classifier predicts
`quantifier-below-top-level` where the run observed `refutation-loop` (2) or
`nested-binder-in-matrix` (1), i.e. the prediction is stricter than what the
rung saw, which is what preprocessing does. There are **zero** in the direction
"the run took an exit the classifier said was impossible".

### 1b. The instrument's own controls

Seven fixtures under `bench-results/quant-activation-20260915/controls/`, each
carrying its expected row in its header, and every one matches:

| fixture | what it pins |
|---|---|
| `c1-unit-forall` | a unit universal is not a target (`refutation-loop`) |
| `c2-forall-under-or` | `(or p (forall …))` is a split universal the whitelist ACCEPTS |
| `c3-negative-forall` | **the polarity control**: `(not (forall …))` is an existential, `exists_pos=1`, target 0 |
| `c4-nested-binder-in-matrix` | the SPARK shape, `nested-binder-in-matrix` |
| `c5-multi-binder` | `multi-binder-prefix`, and NOT a target |
| `c6-let-resolved` | one binder behind two `let` references at two polarities, counted once |
| `c7-forall-under-implies` | **the discriminating control for the last column**: positive, but the path crosses `=>` and `not`, so the whitelist REFUSES it |

`c2` against `c7` is the pair that makes the `widen target` column mean
something: without it the classifier could report every split universal
identically and the "whitelist fires on 3 files" number could not be produced.

## 2. Two design claims, `file:line` on three sides

Read from the shipped sources in `references/z3` (master) and `references/cvc5`
(main), each citation printed back before it was written down.

### 2a. The universal becomes a SAT literal, and the instance clause carries its negation

| | |
|---|---|
| **z3** | `internalize_quantifier` mints the variable: `bool_var v = mk_bool_var(q); … d.set_quantifier_flag(); m_qmanager->add(q, generation);` (`smt_internalizer.cpp:647-666`). A `(or A (forall …))` becomes a two-literal root clause, because `internalize_assertion`'s `OP_OR` arm internalizes each argument and calls `mk_root_clause` (`smt_internalizer.cpp:307-316`). Instantiation starts only on assignment: `if (get_assignment(v) == l_true) { … assign_quantifier(…); }` with the comment *"All universal quantifiers have positive polarity in the input formula. So, we can ignore quantifiers assigned to false"* (`smt_context.cpp:1473-1487`), reaching `m_qmanager->assign_eh(q)` at `:1869-1872`. |
| **z3, the clause** | `qi_queue.cpp:274-289` builds the lemma and **prepends `¬q` into the same clause**: `args.push_back(m.mk_not(q)); args.append(…s_instance…); lemma = m.mk_or(args);`, with `lemma = m.mk_or(m.mk_not(q), s_instance)` in the non-disjunctive case. It is asserted as a **root/aux clause** through `internalize_instance` (`:336`) — no assumption literal, no push/pop. The clause is the first-order validity `(¬∀x.φ) ∨ φ[x:=t]`. |
| **cvc5** | A `FORALL` under an `OR` is not in the CNF stream's connective list, so it falls through to `convertAtom` with `canEliminate = false` (`cnf_stream.cpp:522-556`, `:292-300`). On assertion, `preNotifyFact` routes it to `getQuantifiersEngine()->assertQuantifier(atom, polarity)` (`theory_quantifiers.cpp:173-190`); at `polarity = true` it lands in the **context-dependent** `CDList d_forall_asserts` (`first_order_model.cpp:91-95`, declared `first_order_model.h:170-171`), which every module iterates (`instantiation_engine.cpp:158-171`). |
| **cvc5, the clause** | `Node lem = NodeManager::mkNode(Kind::IMPLIES, q, body);` (`instantiate.cpp:293`) — the CNF stream turns `(=> q body)` into exactly `{¬q_lit} ∪ lits(body)`. Same clause as z3's, built one level higher. |
| **ours** | `positive_instance_formula` (`qinst_egraph.rs:1587-1592`) takes `(owner, path, vars, bindings)` and returns `owner` with the universal at `path` replaced by its instance — i.e. **`A ∨ B(t)`**. The residual context `A` is the activation literal and it is inside the term. `NestedDiscovery::stage` (`:1785-1835`) is the only consumer. |

**So the clause content is the same on all three sides.** What differs is where
the activation literal comes from: z3 and cvc5 mint a fresh boolean for the
quantifier; we reuse the disjunction the universal already sits in. Ours needs no
SAT-variable plumbing at all — the ground solver assigns `A`, and when it assigns
`A` false the clause propagates `B(t)`, which is exactly z3's behaviour with
`q_lit` forced true.

### 2b. What is refuted, and it was this brief's own hypothesis

**"The clause is valid, so backtracking retracts it for free and z3 keeps it."
Half right, and the half that is wrong matters.** The clause *is* valid — but z3
**deletes it on backjump**. `CLS_AUX` is not a lemma (`smt_clause.h:48`), so
`mk_clause` takes the non-lemma branch and pushes onto `m_aux_clauses` without
`mark_for_reinit` (`smt_internalizer.cpp:1586-1593`); `pop_scope_core` truncates
that vector to the scope watermark (`smt_context.cpp:2063` push, `:2560`
`del_clauses`), and `pop_scope_core` is the CDCL backjump path, called from
`resolve_conflict` at `:4430-4432`. The fingerprint that de-duplicates the
instance is popped in the same breath (`:2564`), so the instance can be
re-derived later. Only the conflict clauses *learned from* it survive.

cvc5 does the opposite: the instantiation lemma carries `LemmaProperty::INPROCESS`,
which does not include `REMOVABLE` (`lemma_property.h:26-37`,
`prop_engine.cpp:186`), so it is a permanent input clause for the whole
check-sat.

**Consequence for us: neither retention policy is forced by soundness**, because
the clause is valid either way. Our ground set is a flat `Vec<TermId>` re-checked
from scratch each round (`quantifier_qf_check`, `qinst_egraph.rs:3486-3498`), so
we are structurally on cvc5's side — the clause persists — and that is sound. It
is a *cost* decision, not a correctness one, and this ADR records it so the next
lane does not re-derive it.

**A second refutation, of this brief's framing rather than of a reference.**
"cvc5 does not prenex out of a disjunction" is false as stated. `prenexQuant`
defaults to `SIMPLE` and `computePrenex`'s own doc shows it pulling a `forall`
out of an `or` (`quantifiers_rewriter.h:217-221`). What is true is narrower and
is what the claim needs: the rewriter only fires on `FORALL`/`EXISTS` nodes
(`quantifiers_rewriter.cpp:598-620`), so **a top-level assertion `(or A (forall
x. P))` is never prenexed** — the node is an `OR`, the rewriter does not fire,
and the `FORALL` reaches `convertAtom` as a leaf. `(forall y. (or A (forall x.
P)))` *is* prenexed at the default. Miniscoping is the default in the other
direction (`miniscopeQuant = CONJ_AND_FV`, `quantifiers_options.toml:13-35`) and
its `OR` arm only calls `computeSplit`, which partitions disjuncts by disjoint
variable sets and does not distribute (`quantifiers_rewriter.cpp:2295-2302`).

### 2c. Where ours refuses, and which half is widenable

`collect_nested_registrations_rec` sets `context: positive.then(|| …)` and
`positive` is threaded as
`let step_positive = positive && matches!(op, Op::BoolAnd | Op::BoolOr);`
(`qinst_egraph.rs:1553`). So `context == None` has exactly two causes:

- **a crossed `Forall`** — a real unsoundness, with the counterexample already
  in the doc at `:1346-1349`: in `A ∨ ∀u.(B(u) ∨ ∀y.Q(u,y))` a replacement that
  also substituted `u := c` would yield a formula the original does not entail.
  **This lane does not touch it.** It is `forall_under_binder`, and §1 measures
  it as the bulk of the broad shape column — which is the other reason that
  column is not quoted as a convertible-file estimate.
- **a step through a connective outside `{BoolAnd, BoolOr}`** — `BoolNot`,
  `BoolImplies`, `Ite`, boolean `Eq`/`Xor`. `BoolAnd`/`BoolOr` are monotone, so
  the whitelist establishes positivity without tracking polarity at all; the doc
  says so (*"the whitelist is what establishes monotonicity"*). Tracking polarity
  instead reaches strictly more positions with the same monotone-replacement
  lemma: `¬` flips, `=>` flips its antecedent and keeps its consequent, and
  `ite(c,t,e) ≡ (c ∧ t) ∨ (¬c ∧ e)` is monotone in `t` and `e` but **not** in
  `c`. So `Ite`'s condition, `BoolXor` and boolean `Eq` stay refused — they are
  bipolar, and a bipolar position is not a positive one.

`BoolImplies` is a real node that survives the front end
(`crates/axeyum-ir/src/arena.rs:1055`, `crates/axeyum-smtlib/src/parse.rs:2510`),
so this is not a shape the parser has already normalised away — which §1's
97-file column measures directly.

## 3. Two findings this lane's sources do not record

Both were produced while mapping the seam and both are load-bearing for whoever
builds on this.

**(a) The positive replacement forfeits the certificate.** `NestedDiscovery::stage`
pushes the replacement formula into `ground` (`qinst_egraph.rs:1826`) but takes
`retained: &HashMap<…>` **immutably** (`:1780`) and never writes into
`ground_derivations`. So at the next `collect_ground_derivations` the
`derivations.get(&term)?` at `:4957` returns `None` and the whole certificate is
declined. The `unsat` is still **sound** — `positive_instance_formula` re-derives
and checks the conclusion in line — but the evidence path is severed, and there
is no `QuantifierGroundDerivation` variant that could describe a positive
replacement (`:4826-4832` has `Instance` and `Propagation` only). Any widening of
the whitelist turns a rarely taken uncertified path into a common one unless this
is closed in the same change.

**(b) [ADR-2113]'s online-session mechanism is refuted.** Its consequences
section says `OnlineQuantifierClauseSession` *"abstracts every arithmetic atom to
a fresh boolean (`euf_egraph.rs:2163-2180`)"* and therefore *"structurally cannot
see the LIA half of a refutation"*, and that while alive it *suppresses* the
arithmetic-aware per-round check. The abstraction arm is real but is gated on
`opaque_bool_atoms` (`euf_egraph.rs:2188-2191`), and the session builds its
encoder as `EufEncoder::new(&atom_terms).with_bool_apply_atoms()`
(`qinst_egraph.rs:4137`) — **`with_opaque_bool_atoms` is never called**, so the
flag stays `false`. `encode_app` has no arithmetic arm and ends `_ => return
None`, so on an arithmetic atom `encode` returns `None`, the `?` at `:4142` fires
and **the session declines to exist**. The suppression at `:2447` is real
(`if online_clauses.is_none()`), but on `UFLIA` the session should therefore be
`None` and the interleaved check should be running, not suppressed. The direction
of the conclusion is inverted by the corrected mechanism. **This is recorded, not
re-measured here**; the next lane on that give-up should confirm it with
`AXEYUM_QTRACE=1` before building against either version.

## 4. What ships, and the second blocker that was not predicted

`AXEYUM_QINST_POSITIVE_PATH`, shipped `0` — byte for byte today's behaviour.

### 4a. The registration rule

`positive_path_step` replaces the inlined
`positive && matches!(op, Op::BoolAnd | Op::BoolOr)` with a polarity rule, and
level `0` **is** that expression with its sticky `false` renamed to `None`, so
an unset environment does not reach one line of the new rule. Level `1` tracks
polarity: `not` flips, `=>` flips its antecedent and keeps its consequent, an
`ite` BRANCH keeps.

Refused at **every** level, and none of it is conservatism:

| refused | why |
|---|---|
| the `ite` CONDITION | `ite(c,t,e) ≡ (c ∧ t) ∨ (¬c ∧ e)`, so `c` occurs at BOTH polarities and a replacement inside it is monotone in neither direction |
| both arguments of a boolean `=` / `xor` | the same, for the same reason |
| every step crossing a `Forall`/`Exists` | a real unsoundness, with the counterexample already in `PositiveContext`'s own doc |
| arriving at a NEGATIVE position | `¬(∀y.B)` is an existential; replacing it by `B(t)` STRENGTHENS the owner |
| `BoolImplies` at any arity but 2 | the front end folds an n-ary `=>` right-associatively into binary pairs, so a wider node is a shape this rule has not been argued for. Refused rather than guessed at |

### 4b. The blocker the sizing did not predict, found by running the fixture

`prove_quantified_unsat_via_egraph_impl` partitions the assertions into ground
terms and top-level `forall`s, and when the `forall` list is **empty** it returns

    e-matching: no universal is asserted; the nested quantifiers present are
    registered, not instantiated

**before any registration is compiled.** So on a query whose universals are ALL
nested — exactly the shape this mechanism exists for — the registration
machinery was unreachable, whatever the whitelist said. This was found by
probing the lane's own fixtures and reading the `unknown` detail, not by reading
the code: the first three fixtures all came back `unknown` with a context
already computed at level 0, which is a combination the design says should be
impossible.

At level 1 the loop runs on registrations alone when at least one carries a
context. It is not a weaker check — a registration with a context is a universal
whose instances are admissible as the entailed replacement
`owner[∀y⃗.B := B(t⃗)]`, which is the same inference the loop already performs
beside an asserted universal. What changes is only that the loop is allowed to
start.

### 4c. The checker is not gated by the level

`positive_instance_formula` walks the path itself at a fixed
`CHECKER_POSITIVE_PATH_LEVEL`, refuses arrival at a negative position, and
re-derives the conclusion from `(owner, path, vars, bindings)` alone. Reading
the lever there would make a certificate's validity depend on an environment
variable — the same certificate accepted under one process and refused under
another. The two constants are separate for exactly that reason, and the
consequence is deliberate: at level 0 the producer never builds a `not`/`=>`
path, so the checker's extra reach is unreachable.

### 4d. The certificate hole, closed in the same change

§3(a) is not a note for a later lane; widening the rule without closing it would
have turned a path taken on 3 files into one taken on 97. So
`QuantifierPositiveReplacementCertificate` and a `PositiveReplacement` variant
now exist, with `check_positive_replacement` requiring **both**:

* the owner is an original assertion, **or** `owner_derivation` checks here and
  concludes exactly `owner`. A missing `owner_derivation` on a non-asserted
  owner is a refusal, never a pass;
* `positive_instance_formula` re-derives the conclusion and it **equals** the
  recorded one.

`portable_certificate` declines on the new variant exactly as it declines on
`Propagation` — its positional form has no field for a path or an owner — and
now says so in its own comment. The decline is the intended outcome: the
refutation is still checked in the producing arena, and it is the PORTABLE form
that cannot be produced.

## 5. Tests, and what each one can fail on

`crates/axeyum-solver/tests/quantifier_positive_path.rs`, **15 tests, 0 failed.**

**Soundness-negative**, five SATISFIABLE fixtures at BOTH levels, through the
isolated loop and through the front door. The load-bearing one is
`SAT_OTHER_DISJUNCT_TRUE`: `p` true, `(or p (forall y. q y))`, `(not (q w))` —
SAT, and refuted the moment anything admits the bare instance `q(w)` instead of
the clause `p ∨ q(w)`.

**`SAT_UNDER_NOT` was rebuilt after its first version turned out to be a
decoration.** As first written, the other disjunct was unconstrained, so a rule
that took the `not` step *without* its flip produced `t ∨ ¬q(w)` — which is
satisfiable, so the fixture could not fail and the mutation that removes the
flip would have SURVIVED it. It now asserts `¬f` alongside
`(or f (not (forall y. q y)))` and `(q w)`: still SAT (some `y` fails `q`, and
`w` is not that one), but a missing flip now yields `¬q(w)` and contradicts the
asserted `q(w)`. A single missing polarity flip is a wrong `unsat`.

**The conversion**, which is what stops every assertion above from being passed
by an engine that refutes nothing.
`the_widened_level_converts_a_refutation_the_shipped_level_cannot_reach`:
`UNSAT_OTHER_DISJUNCT_FALSE` differs from `SAT_OTHER_DISJUNCT_TRUE` in ONE
polarity and is `unknown` at level 0, **`unsat` at level 1**. And
`the_converted_refutation_carries_its_replacement_derivation` requires that
refutation to carry a `PositiveReplacement` derivation, so the certificate is
asserted to EXIST rather than argued to be possible.

**The producer's polarity half is read one step before the verdict.**
`a_universal_at_a_negative_position_is_never_registered` asserts a registration
COUNT of zero for the `not` fixture and the `ite`-condition fixture at both
levels, because a test that reads a count cannot be passed by an engine that
simply failed to reach the query.

Plus: an off-path equivalence check, determinism across runs, the guard's
restoration, and `the_positive_path_guard_does_not_cross_a_thread_boundary`,
which is why the A/B uses the environment variable and not the guard —
`smtcomp_cli` solves on a watchdog worker thread.

### 5a. Mutation

`mutation_controls.py qinst-positive-path`, baseline green at 15 tests. **Every
guard deleted kills at least one named test:**

| guard deleted | killed |
|---|---|
| the instance is rebuilt INTO its owner, so the clause carries the activation literal | **3** — `a_correct_positive_replacement_certificate_is_accepted`, `the_bare_instance_is_refused_as_a_replacement_conclusion`, `a_satisfiable_query_is_not_refuted_at_any_level` |
| `not` flips the polarity | **3** — `a_replacement_at_a_negative_position_is_refused`, `a_universal_at_a_negative_position_is_never_registered`, `a_satisfiable_query_is_not_refuted_at_any_level` |
| the checker refuses ARRIVAL at a negative position | **1** — `a_replacement_at_a_negative_position_is_refused` |
| a replacement's owner must be an assertion or carry its own derivation | **1** — `a_replacement_whose_owner_is_not_trusted_is_refused` |
| the recomputed conclusion must equal the recorded one | **1** — `the_bare_instance_is_refused_as_a_replacement_conclusion` |

`--check-anchors`: `suites=146 anchors=1087 stale=0`.

The two that kill three are the two deepest obligations, and
`positive_instance_formula` is both the producer and the checker, so a mutation
in it breaks both roles at once. The number is reported as measured rather than
trimmed to one.

**And what the table does not claim.** The FRONT-DOOR soundness test SURVIVES
the activation-literal mutation, because the ladder decides those fixtures `sat`
on an earlier rung and never reaches the e-matching route. The isolated loop is
the attributable instrument and the front door is not; that is why both exist,
and a mutation table that reported only the front door would have shown a
survivor where the guard is in fact load-bearing.

## 6. What this lane measured about its own instrument

**The count column was a tree count, and it printed a 105-digit integer.** The
first version of `qshape.py` summed a `let`-bound value's findings at every
reference site — the count substitution would have produced. The sharing in this
corpus is exponential, so on one `UFNIA` file the `pos_forall_split` column came
back as
`19333712651538768287122690770408562218469782946764596007845122206226268509741231960340352811642371702784`,
and a per-division SUM of such columns is not a quantity anyone can read. Each
class is now a **set of binder node identities**, so a universal shared under
twenty `let` references is one universal — which is what it is in the arena the
solver builds. `c6-let-resolved` is the fixture that pins it: its `any_quant`
went from 2 to 1 on the fix, and the per-file boolean columns did not move, which
is how the fix was shown not to have changed the ceiling it was measuring.

The failure mode this avoided is worth naming, because the number was never going
to be caught by a verdict check: a tree count is *monotone in the same direction*
as a DAG count, so every share, every ranking and every "division X is larger
than division Y" statement would have come out the same. Only the absolute
column was absurd, and only because one file happened to be extreme enough to be
unreadable rather than merely wrong.

## Consequences

*(Added with §4.)*

[ADR-2113]: adr-2113-uflia-the-instance-we-never-produce.md
[ADR-2114]: adr-2114-aufdtlira-what-the-model-finder-cannot-represent.md
