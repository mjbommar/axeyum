# Lane diary: `facts-logic` -- the `S:logic-and-proof` strand

Date: 2026-08-14. Source: the 205 concepts carrying `strand: S:logic-and-proof`
in the private math-education concept graph. Output: 21 facts in
`artifacts/facts/`, 15 supporting SMT-LIB files in `artifacts/facts/smt2/`.

Nothing in this document reproduces prose, definitions, or lesson text from the
private corpus. Concept ids are cited; every statement was written here.

## What landed

| status | count | ids |
| --- | --- | --- |
| `proved` | 14 | `de-morgan-laws`, `excluded-middle`, `double-negation-elimination`, `peirce-law`, `contraposition`, `modus-ponens-valid`, `modus-tollens-valid`, `resolution-rule-sound`, `nand-functional-completeness`, `ex-falso-quodlibet`, `exportation`, `tseitin-and-gate`, `xor-associative`, `no-self-negating-proposition` |
| `refuted` | 1 | `affirming-the-consequent` |
| `open` | 6 | `quantifier-negation-duality`, `barber-no-such-barber`, `excluded-middle-not-intuitionistic`, `godel-first-incompleteness`, `fol-validity-undecidable`, `continuum-hypothesis-independent` |

All 21 also carry `external_status` (the field a concurrent lane added to the
schema while this lane was running -- see complaint 1). Every `proved` fact is
`external_status: proved`; the one `refuted` fact is `external_status: refuted`;
and **all six `open` facts are `external_status: proved` too**. Nothing in this
strand is mathematically open. All six gaps are ours.

### How the 15 checked ones were actually checked

Each has a file in `artifacts/facts/smt2/` asserting the **negation** of its
`formal.statement`. Run through

```sh
cargo run -q -p axeyum-bench --example smtcomp_cli -- --evidence artifacts/facts/smt2/<file>.smt2
```

all 14 `proved` facts return

```
; evidence kind=unsat-term-level certified=1 recheck=na arena=ok
unsat
```

`unsat-term-level` is the strongest `unsat` evidence variant in the codebase:
`certify_qf_bv_by_enumeration` evaluates every Boolean assignment through the
`axeyum-ir` evaluator, trusting neither the bit-blaster, the CNF encoder, nor
the SAT solver. `arena=ok` is `Evidence::check` re-running that enumeration
against a **fresh parse** of the file, so the re-validation does not reuse
anything the producing solve held in memory. `recheck=na` is expected and
correct here: there is no serialized clausal certificate to re-parse because
the route never went to CNF.

`affirming-the-consequent` returns `sat` with `kind=sat-model certified=1
arena=ok` -- the model replays against the original assertions. Witness:
`p := false, q := true`.

Two independent cross-checks were run on top of that:

1. **z3 oracle.** `z3 -smt2` on all 17 committed files. Every verdict agrees.
2. **Round-trip from the fact files themselves.** A script regenerated an
   SMT2 file from each fact's own `formal.statement` string (wrap in `(not ...)`,
   declare `free_symbols` as `Bool`) and re-ran it. 15/15 matched. The
   committed `.smt2` files were then *regenerated from the facts* so the fact
   text and the `checker_command` target cannot drift. This mattered: my first
   `nand` file used a `define-fun` the fact's inlined statement did not, and
   the round-trip is what forced them into agreement.

## The axiom footprint, and the correction that changed it

My brief originally said the Nat layer measures zero axioms via
`prelude_axiom_inventory`. The coordinator corrected this mid-task: that
example never builds the Nat or **logic** preludes, so zero rows meant "never
enumerated". The correct tool is `nat_axiom_inventory` (landed `006a7da27`).
I re-ran it:

```
logic:   axiom=0 opaque=0 quotient=0 total_trusted=0
nat:     axiom=0 opaque=0 quotient=0 total_trusted=0
real:    axiom=30  integer: axiom=34  string: axiom=1
```

and then read `crates/axeyum-lean-kernel/src/prelude.rs` to see what "zero"
covers. `build_logic_prelude` declares exactly `True`, `False`, `And`, `Or`,
`Iff`, `Not` (as `a -> False`), `Eq`, `Exists`, plus `Acc`/`WellFounded`/`Bool`/
`Nat`. No `Classical.em`, no `propext`, no `Quot.sound`. It is an
**intuitionistic** core.

This is the single most consequential finding of the lane, and it is why **no
fact here carries `axiom_footprint: []`**. Every one carries

```json
["axeyum-ir.bool-evaluator", "classical-two-valued-bool-semantics"]
```

which names the trust base of the *route that established it*. Writing `[]`
would have been wrong twice over: nothing here went through the kernel at all,
and three of these facts (`excluded-middle`, `double-negation-elimination`,
`peirce-law`) are **not provable in our kernel's logic** and could not be
without admitting a new axiom.

The generalised lesson the coordinator drew is right and worth restating in
this repo's own idiom: *an empty result from a tool never pointed at your
subject is indistinguishable from a strong negative result.* `total_trusted=0`
for `logic` means the kernel assumes nothing, not that it can prove anything.

## Concepts I skipped, and why

Of 205 concepts in the strand, roughly 150 yield no proposition at all. The
skip categories, with examples:

* **Pedagogy and process** -- `C:polya-method`, `C:productive-struggle`,
  `C:stuck-is-normal`, `C:notice-and-wonder`, `C:showing-your-working`,
  `C:devise-a-plan`, `C:look-back`, `C:restate-the-problem`. These are
  strategies. There is no proposition.
* **Definitions dressed as topics** -- `C:tautology`, `C:premise`,
  `C:conclusion`, `C:lemma`, `C:corollary`, `C:definition`, `C:statement`,
  `C:truth-value`. A definition is not a fact. Several of these appear in my
  facts as `concept_refs` with `relation: uses`, which is the right place for
  them.
* **Puzzles and instances** -- `C:sudoku-logic`, `C:kenken`, `C:cryptarithm`,
  `C:knights-and-knaves`, `C:logic-puzzle`. Each names a *family* of instances.
  A specific instance would be a `claim`, not a `fact`, and the family is a
  topic. Worth noting the near-miss: a fixed Sudoku instance's uniqueness *is*
  a proposition our solver could settle, and would be a good source of
  `computed` facts for whoever wants volume. I did not pursue it because it
  would be padding rather than mapping the strand.
* **Group/set-theory concepts that leaked into this strand** --
  `C:abelian-group`, `C:cyclic-group`, `C:dihedral-group`, `C:cayley-table`,
  `C:subgroup`, `C:power-set`, `C:cartesian-product`. Real propositions live
  here (Lagrange, `|P(S)| = 2^|S|`) but they belong to an algebra/sets lane and
  I did not want to collide with one.
* **Not a mathematical proposition at all** -- `C:church-turing-thesis` is a
  thesis about the adequacy of a definition, not a theorem; it is cited as
  `relation: presupposes` from `F:fol-validity-undecidable` rather than made a
  fact. Same for `C:elegance`, `C:mathematical-certainty-limits`,
  `C:legal-evidence`, `C:scientific-method`.
* **Empirical/computed propositions I chose not to import** --
  `C:busy-beaver` (BB(5) = 47,176,870, machine-checked in Coq in 2024) and
  `C:four-colour-machine-proof` are genuine propositions with genuine external
  machine-checked evidence. When I skipped them the schema had no honest slot
  for "settled elsewhere, not checked here". `external_status` landed mid-task
  and now there is one -- `epistemic_status: open` plus
  `external_status: proved` plus a `prior_art` citation is exactly right for
  both. I did not go back and add them because they are number-theory /
  graph-theory imports rather than logic-strand propositions, but they are the
  obvious first entries for an import lane, and the mechanism now exists.

## Frictions and defects found

### 1. `smtcomp_cli` misreports a bare uncertified `unsat` as `arena=FAIL`

`artifacts/facts/smt2/neg-barber-no-such-barber.smt2` prints:

```
; evidence kind=unsat-drat certified=0 recheck=na arena=FAIL ms=325
unsat
```

Two of those fields are wrong, and the solver is not at fault:

* **`kind=unsat-drat` names a proof that does not exist.**
  `Evidence::kind_label` (`crates/axeyum-solver/src/evidence.rs:718`) maps
  `Evidence::Unsat(_)` -- *both* `Some(proof)` and `None` -- to the string
  `"unsat-drat"`. This result is a bare `Evidence::Unsat(None)` (confirmed by
  `recheck=na`, which only `Unsat(Some(_))` can escape, plus `certified=0`).
  So the harness's own label advertises a DRAT certificate for a result that
  has no certificate at all.
* **`arena=FAIL` reads as "a certificate was examined and did not hold up",**
  which is the most alarming thing an evidence line can say. The truth is
  "there was nothing to examine". `Evidence::check_outcome` gets this right --
  it returns `NothingToCheck(NoCheckReason::UncertifiedUnsat)` at
  `evidence.rs:840` -- but `Evidence::check` collapses that to `Ok(false)`
  (`evidence.rs:1068`), and `smtcomp_cli` renders `Ok(false)` as `FAIL`
  (`crates/axeyum-bench/examples/smtcomp_cli.rs:137`).

This is a textbook instance of the CLAUDE.md gotcha that "tools in this repo
have lied more often than the solver has been weak." The fix is small:
`smtcomp_cli` should call `check_outcome` and print `arena=none` (or `na`) for
`NothingToCheck`, and `kind_label` should distinguish `Unsat(None)` as
`unsat-bare`. I did not make the change -- `smtcomp_cli` and `evidence.rs` are
hot files and other lanes are live in this checkout -- but I would rate it a
worthwhile small ticket, because an evidence-coverage dashboard built on these
strings will currently show a *failure* where the truth is *absence*, and those
two need very different responses.

### 2. `unsat-term-level` never reports `recheck=ok`, by construction

Every propositional fact here shows `recheck=na`. That is correct behaviour --
there is no serialized artifact for an enumeration certificate -- but it means
the "re-checked (text-only)" coverage metric structurally cannot count the
*strongest* evidence variant we produce. A reader comparing `certified` against
`recheck` on a Boolean-heavy corpus will read a gap that is not one. Worth a
sentence in the coverage docs.

### 3. The solver returns `unknown` on the quantifier de Morgan duality

`F:quantifier-negation-duality` is the most actionable open item this lane
produced. The file is a purely propositional combination of four quantified
atoms over one uninterpreted sort:

```
(assert (not (and (= (not (forall ((x U)) (P x))) (exists ((x U)) (not (P x))))
                  (= (not (exists ((x U)) (P x))) (forall ((x U)) (not (P x)))))))
```

axeyum: `unknown` in 18 ms. z3: `unsat` immediately. This needs no
instantiation heuristic and no model finding -- only a structural rule relating
`not forall x.phi` to `exists x.not phi`, i.e. quantifier-level de Morgan, applied before anything
else looks at the formula. It is the direct analogue of the already-proved
`F:de-morgan-laws`, it is inside the fragment we advertise, and closing it
flips an `open` fact to `proved` with real evidence. If one item from this
diary reaches the roadmap, make it this one.

## Roadmap feedback: where the formalism could not express the proposition

This is the part I was asked to prioritise. Six propositions in the strand are
mathematically settled and **cannot be stated in axeyum at all**. They fail for
exactly three reasons, and the reasons nest.

### Gap A -- no reflection: formulas and derivations are not in the domain of discourse

This blocks the largest and most important class. `axeyum-ir` has terms for
values and functions over sorts. It has no term denoting *a formula*, *a
derivation*, or *a proof system*. Consequently none of these can be stated:

* `F:godel-first-incompleteness` -- needs a provability predicate over our own
  formulas. (Godel numbering is *not* the obstacle; arithmetic on codes we
  could do. The obstacle is that `Provable_T(<phi>)` has to range over syntax.)
* `F:fol-validity-undecidable` -- quantifies over algorithms and over the set of
  all first-order sentences.
* `F:excluded-middle-not-intuitionistic` -- asserts the *non-existence* of a
  derivation in a named proof system.
* The deduction theorem proper (`Gamma, p |- q <=> Gamma |- p -> q`). I landed its object-
  level semantic shadow as `F:exportation` and said so in that fact's notes;
  the metatheorem itself is out of reach.
* **Refutation-completeness of resolution.** `F:resolution-rule-sound` pins
  one-step soundness -- which is what DRAT replay actually needs -- but the
  completeness half is a statement about a proof system.
* **Equisatisfiability of the Tseitin transformation.** `F:tseitin-and-gate`
  pins the single-gate equivalence, which is the correctness core; the general
  statement quantifies over formulas.

Note how much of this is *about our own stack*. Four of the six blocked
statements are metatheorems the project's identity sentence ("untrusted fast
search, trusted small checking") implicitly relies on. We check certificates
rather than prove the checker complete, which is a defensible engineering
choice, but the north star says "a complete framework for general reasoning,
logic, and proving", and a framework that cannot state the correctness of its
own encoder has a visible ceiling. **Concrete suggestion:** the cheapest
partial answer is not full reflection but a *deep embedding* -- an inductive
`Formula` datatype in the Lean kernel with an evaluation function and a
`Derivation` relation. `axeyum-lean-kernel` already builds recursive inductive
datatype families with recursors and a size measure (`add_recursive_datatype_family`,
`recursive_datatype_size`), so the machinery exists; nothing has been pointed
at syntax yet. A deep-embedded propositional logic with a checked soundness
theorem for resolution would be a real, bounded, landable slice, and it would
convert three of the six items above from "unstatable" to "stated and open".

### Gap B -- one logic per route, and nothing that records the difference

axeyum has **two reasoning routes with two different logics** and no object
that relates them:

* the SMT route fixes a two-valued `Bool` sort, so it proves
  `F:excluded-middle`, `F:double-negation-elimination` and `F:peirce-law` in
  microseconds;
* the Lean kernel route has an intuitionistic logic prelude with
  `total_trusted=0`, in which none of those three has a proof term and none can
  get one without a new axiom.

Today nothing records this. `axiom_footprint` describes the route that *did*
establish a fact and is silent about routes that *cannot*. The practical
consequence is concrete and near-term: **any reconstruction lane that pipes an
SMT `unsat` into the kernel will hit a wall on every classical tautology**, and
it will surface as an opaque kernel error rather than as a recognised
logic mismatch. Suggestion: either add `Classical.em` to the logic prelude as
an explicit, inventoried axiom (making the footprint honest and non-empty and
the reconstruction possible), or add a `logic` discriminator to facts and
refuse reconstruction of classically-established facts into the constructive
kernel. Either is fine; the current silence is not. I landed
`F:excluded-middle-not-intuitionistic` specifically to hold this open.

### Gap C -- first order only, no cardinality

`F:continuum-hypothesis-independent` fails for a reason the others do not: it
quantifies over *subsets of the reals*. There is no second-order quantification
and no cardinality apparatus anywhere in the stack, and `Real` is a first-order
ordered field. This is the furthest-out gap and I am not proposing work on it;
it is recorded so that "complete framework for general reasoning" is measured
against something rather than asserted.

### A near-gap worth naming: skolemisation is invisible

My first `neg-barber-no-such-barber.smt2` hand-skolemised `exists b` into a constant.
Sound, standard, and completely invisible in the artifact -- nothing in the fact
or the file said a transformation had happened. I rewrote it to use the
existential directly (same verdict). But the general point stands: the fact
schema records a `checker_command` and a statement, and has no place to record
that the command checks a *transform* of the statement rather than the
statement. For a route with a preprocessing pipeline as long as ours, that is a
real hole in self-containment.

## Top 3 schema / tooling complaints

**1. `epistemic_status` conflated "the status of the proposition" with "the
evidence in this ledger" -- FIXED MID-TASK BY ANOTHER LANE; one residual ask.**
This was going to be my headline complaint. Godel's first incompleteness
theorem is not `open`. Nor is the barber theorem, nor `BB(5) = 47,176,870`. But
the validator (rightly) refuses `proved` without a `check_status: "checked"`
row, and the enum offered nothing between, so I had written all six frontier
facts as `open` with a loud `notes` paragraph explaining that `open` was the
wrong word.

While I was working, a concurrent lane added `external_status` to
`fact.schema.json` and a matching rule to `scripts/validate-facts.py`. That is
exactly the fix. I adopted it across all 21 facts, which cost one regeneration
and produced a genuinely informative signal:

> **every one of my six `open` facts carries `external_status: proved`.** Zero
> of them are open mathematically. All six are "axeyum cannot say this yet".
> That is the frontier map, and before `external_status` existed there was
> nowhere to put it.

The validator change also required `provenance.prior_art` for any settled
`external_status`, which is correct and which I complied with -- adding a
citation to each of the 15 checked facts. I marked every one with
`"attribution": "standard textbook attribution; this lane did not consult the
primary source"`, because I did not, and the rule's stated purpose (not
laundering unverified claims about the literature) is defeated if lanes supply
citations from memory without saying so. **Recommend making that admission a
first-class optional field rather than a convention I invented.**

The residual ask: three of my `open` facts have `formal.fragment: "none"` and a
`formal.statement` that is an English comment explaining why it cannot be
dispatched. The schema says the self-extension loop "picks an `open` fact and
dispatches its `formal.statement` to the solver" -- a loop filtering on status
alone will feed a comment to the parser. **Have the validator warn when
`epistemic_status: open` co-occurs with `formal.fragment: "none"`,** so the
combination is visibly a frontier marker rather than a work item.

**2. `axiom_footprint` has no vocabulary and no validation, so it cannot be
compared across routes.** The schema calls it "the metric the project
publishes", but it is a free-form `string[]` whose example values are Lean
axiom names. Mine are not Lean axiom names -- they cannot be, because these
facts were established by exhaustive Boolean enumeration -- so
`["axeyum-ir.bool-evaluator", "classical-two-valued-bool-semantics"]` is
honest, useful, and *not comparable* to `F:nat-add-comm`'s `[]`. Two facts with
different footprints today might differ in strength or might just differ in
which lane wrote them. The near-miss is worse than the ambiguity: had I taken
the brief's original "Nat is axiom-free" line at face value and written `[]`, a
reader would have concluded these classical tautologies were axiom-free, when
in fact our own kernel cannot prove three of them at all. **Ask:** a small
controlled vocabulary (or at least a documented namespace convention like
`lean:`/`route:`), and a rule that the footprint must be non-empty unless the
establishing evidence is a `kernel-term`.

**3. The `evidence[].kind` enum has no value for the strongest thing we
produce, and `check_status` cannot express "checked, twice, independently".**
Fourteen of my facts rest on `unsat-term-level`, which is neither an
`unsat-certificate` (nothing is serialized) nor quite an
`exhaustive-enumeration` in the enum's apparent sense -- I used the latter and
explained in `notes`, which means the distinction is not machine-readable.
Separately, each of those results was validated three ways: the producing
solve, `Evidence::check` against a fresh parse, and an independent z3 run. All
three collapse to the single token `"checked"`. The one field that could carry
this -- cross-oracle agreement, which CLAUDE.md treats as the highest-value
signal in the repo -- has nowhere to go but prose. **Ask:** allow multiple
evidence rows to be marked as independent confirmations of one another, or add
an optional `cross_checked_by` field. Cheap, and it turns the repo's own
stated gold standard into something a dashboard can count.

## Reproduction

```sh
# all 17 supporting files, our solver
for f in artifacts/facts/smt2/*.smt2; do
  echo "$f"; cargo run -q -p axeyum-bench --example smtcomp_cli -- --evidence "$f"
done

# independent oracle
for f in artifacts/facts/smt2/*.smt2; do z3 -smt2 "$f"; done

# the kernel's trusted surface
cargo run -q -p axeyum-lean-kernel --example nat_axiom_inventory 2>&1 >/dev/null

# ledger consistency
python3 scripts/validate-facts.py
```

Last run of the validator with this lane's files in place:

```
47 facts checked, 0 errors  (computed=1 conjectured=3 open=11 proved=31 refuted=1)
  external: 7 settled elsewhere but not here (import backlog), 24 unclassified
  NOVEL -- established here, not settled in the literature: F:rado-r4-a5-b4
```

The totals include other lanes' concurrent work.
