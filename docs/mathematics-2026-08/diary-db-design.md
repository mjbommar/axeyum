# Diary: database design as a certificate-carrying decision problem

Lane `db-design`, 2026-08-15. Companion to
[ADR-0463](../research/09-decisions/adr-0463-database-design-questions-are-answered-with-certificates.md).

## Why this domain, and why it fits

The ask was for the stack to be pointed at useful computation: "planning,
logistics, database design, or general numerical approximation / ode / pde
systems". Planning and logistics had the `infeasibility` lane. Database design
had nothing, and it is the best fit of the three for what this project actually
is, for a reason that has nothing to do with the gap.

Every central question of relational schema design is a **decidable logical
implication problem whose certificate is far smaller than its decision
procedure**. That is not an analogy for "untrusted fast search, trusted small
checking" — it is the same sentence in relational clothing. The extreme case is
conjunctive-query containment: finding the homomorphism is NP-complete, and the
certificate for `Q_terse ⊆ Q_verbose` is *four variable-to-element pairs*.

So the engineering interest was never "can we decide these". Attribute closure
is linear time and was published in 1979. The interest is entirely in **what
comes back**, and in whether the thing that checks it knows less than the thing
that found it.

## The four question types, and what each one hands back

| question | positive | negative |
|---|---|---|
| `F ⊨ X → Y` | Armstrong derivation, ≤ `3\|F\|+3` lines | two rows satisfying `F`, violating `X → Y` |
| candidate keys | derivation of `K → R` + one removal test per attribute | two rows agreeing on the subset |
| BCNF / 3NF | one derivation per dependency of `F` | the violating dependency + its two rows |
| lossless join | chase trace ending in an all-distinguished row | the final tableau, read as a relation, with a spurious tuple |
| `Q₁ ⊆ Q₂` | homomorphism `Q₂ → freeze(Q₁)` | `freeze(Q₁)` as a counterexample database |

The **checkers deliberately know less than the finders**. `check_derivation`
implements reflexivity, augmentation, transitivity and the citation of a
dependency of `F`, and refuses to implement the union rule, the decomposition
rule or pseudo-transitivity — a derivation that wants one must spell it out in
the three axioms. It does not know that attribute closure exists. That is what
makes the certificate checkable by someone who does not have our code, and it is
also why a bug in the closure fixpoint cannot produce a derivation the checker
accepts.

## Four things worth writing down

### 1. The negative direction rests on less than the positive one

This is the reverse of the usual asymmetry in this repository, where a `sat`
witness is cheap and an `unsat` needs a proof. Here:

- **Lossy** needs *no theorem*. The final tableau, read as an ordinary relation,
  satisfies `F`; every fragment still has a row projecting onto the all-`a`
  tuple, so the join produces it; and the relation does not contain it. Three
  array comparisons and the decomposition is refuted. **Lossless** needs the
  soundness of the chase (Aho, Beeri and Ullman 1979) — replaying
  identifications to an all-`a` row means anything at all only because that
  theorem says so.
- **Not contained** needs no theorem either, and specifically it never invokes
  Chandra–Merlin's *converse* — the direction that requires an **infinite**
  domain (AHV Exercise 6.12a). "No homomorphism was found, therefore no
  containment" would need it. "Here is a concrete two-fact database on which
  `Q_path2` returns its head and `Q_edge` does not" does not.
- **Not implied** does not need the **completeness** half of Armstrong's
  theorem. Completeness is what guarantees a two-row counterexample *exists*
  whenever the implication fails. Here one is exhibited, so the guarantee is
  spare. Only soundness of the three axioms is load-bearing, and that is on the
  other side of the ledger.

Each fact's `axiom_footprint` says which half it is leaning on. Smoothing this
over would have been the easy thing and would have made three routes look
equally strong when they are not.

### 2. The solver's model *is* the certificate

A dependency set is a Horn theory: `A B → C D` is `A ∧ B → C ∧ D` over one
Boolean per attribute. So `F ⊭ X → Y` is satisfiability of
`Horn(F) ∪ X ∪ {¬y}`, and the useful observation is that **any** model of that —
not only the least one — yields a valid counterexample relation. Take the set
`M` of attributes the model makes true and build two rows agreeing exactly on
`M`: for any dependency `L → R`, the rows agree on `L` iff `L ⊆ M`, in which
case `R ⊆ M` by the implication, so they agree on `R`. The relation satisfies
`F`, agrees on `X ⊆ M` and differs on some `y ∉ M`.

That closes a loop the stack rarely gets to close. The solver is not consulted
for an opinion that a checker then re-derives independently; it *produces the
object*, and the object goes through `check_model` (IR ground evaluator, against
the encoding) and then through `check_two_tuple_witness` (against all of `F`,
row by row, with no closure anywhere). A `sat` we cannot use is a `sat` we would
have had to trust.

Same shape for containment: homomorphism existence is a one-hot Boolean
encoding, the model decodes to a map, and the map goes through the same
`check_homomorphism` as the backtracking search's output. Search and solver
disagreeing is a reported **failure**, not a tie-break.

### 3. ADR-0455 and ADR-0460 are satisfied here for a structural reason

A candidate-key claim is two claims wearing one name: `K` determines everything,
and no proper subset does. The second is a claim about what is *not* derivable,
and both minimality ADRs exist because that is where systems get believed
without evidence.

ADR-0455 asks whether every removal test was *decided*. Attribute closure is a
total function on a finite lattice, so they always are — 3520 of 3520 on the
order-line schema — and `KeyAnalysis` reports the count rather than letting the
reader assume it.

ADR-0460 asks the sharper question: was the decided test a test of the *claim*,
or of a decomposition the producer picked for its own reasons? That failure mode
is structurally absent. Closure is defined by `F` alone; there is no monomial
order, no block decomposition, no budget and no heuristic anywhere in the test.
And the evidence for each negative verdict is not the closure computation at all
— it is a two-row relation, which refutes superkey-hood on its own terms.

The completeness of the key list ("these are **all** of them") is the only claim
of its shape here, and it is established the only way a finite claim of that
shape can be: all 1024 subsets, 640 containing a reported key, 384 issued a
counterexample relation, 384 of those checked. The sweep also fails if a subset
containing a reported key turns out not to be a superkey, or if a subset
containing none turns out to be one.

### 4. Where a sweep stops is an **error**, not a smaller answer

`analyze_keys` refuses above arity 24. `project_dependencies` refuses above
fragment arity 16 — and that one is not a performance guard: a truncated
projection sweep would produce a **smaller** `G` than the truth, which turns a
dependency-preservation question into a wrong `no`. The homomorphism search and
the complete evaluator refuse above 50 000 000 assignments and report the count
they did enumerate.

This is the repository's own lesson about empty results applied before it could
bite. An unsearched space and an exhausted one are the same output.

## What a designer can do with this that they could not before

Concretely, running `db_design_certify` on a schema they wrote:

- **Settle "is the natural key really a key?" with evidence.** The order-line
  instance answers that `{order_id, line_no}` and `{line_uuid}` are *both*
  candidate keys and there are no others — so the surrogate is not redundant and
  the natural key is not a convention. Both halves are certified.
- **Get the *reason* a schema is denormalised, not the verdict.** "Not in BCNF"
  is not actionable. "`f_order` has determinant `order_id`, which is not a
  superkey, and here are two rows that satisfy every one of your seven
  dependencies while agreeing on `order_id customer_id customer_email warehouse
  region` and differing" is a test fixture.
- **Tell the two failure modes of a split apart.** Splitting street/city/zip on
  `city` — the shape a designer reaches for on seeing `zip → city` — *loses
  information*, and the run prints the two-row database whose projections rejoin
  to a tuple that was never there. Splitting on `zip` is lossless and *loses the
  dependency* `street city → zip`, with two rows satisfying the projected set
  and violating it. A tool that only said "not in BCNF" gives no way to
  distinguish these, and they call for opposite decisions.
- **Decide whether a materialised view answers a query**, with a certificate the
  optimiser could carry: `Q_us_orders ⊆ Q_any_region` by a three-pair map, and
  the reverse refuted by a two-fact database. Constants are not mapped by a
  homomorphism, which is exactly why the pair is asymmetric — and why a rewrite
  rule that ignored the direction would be unsound.

## Traps hit, and one design regret

**The `wrong-notpreserving` control was nearly useless.** The first version
pinned `notpreserving` on a decomposition that did not exist, so the tool
rejected it at *parse* time. That measures the parser, not the preservation
test. Replaced with a decomposition that keeps the whole relation as one
fragment, where preservation trivially holds — so the rejection now comes from
the thing under test. A negative control that fails for the wrong reason is
worse than none, because it looks like coverage.

**`--verify-formal` needed its own negative control immediately.** A flag that
dispatches a committed SMT-LIB script and requires `unsat` will happily exit 0
on any script the parser accepts if nobody checks the other branch.
`negative-controls/wrong-formal.smt2` asserts the negation of a *false* claim,
so it is satisfiable and must be refused — and a second assertion covers a
`--verify-formal` target that asserts nothing at all.

**A `rustfmt` pass silently mangled a message.** A `\`-continued string literal
came back from `rustfmt` with the continuation flattened into fourteen literal
spaces mid-sentence. It was cosmetic, but it is the third time in this tree that
a tool has quietly rewritten something a human wrote and nobody noticed until
they read the output. Read what your tools produce.

**The regret: the instance format is a fifth parser.** `.dbd` and `.cq` are a
small line-based format with its own error messages, when SMT-LIB is right
there. The justification is that a relational schema is not an SMT-LIB script —
attributes, dependencies, named decompositions and *pinned expectations* have no
natural encoding there, and burying the expectations on a command line was the
thing that had to be avoided. But it is a parser, it will drift, and the
mitigation is that an unrecognised directive is an **error** rather than a
comment, so a typo cannot silently drop an expectation.

## What is deliberately not here

**Inclusion dependencies.** Implication for FDs and INDs together is
*undecidable* — proved independently by Chandra and Vardi (SIAM J. Comput.
14(3):671–677, 1985) and by Mitchell (Information and Control 56:154–173, 1983);
naming only the first, as most secondary sources do, is incomplete. A module
that quietly answered such a question would be answering a different one. The
decidable fragment to reach for first is unary INDs with FDs, which is
polynomial time (Cosmadakis, Kanellakis and Vardi, J. ACM 37:15–46, 1990), and
whoever adds it must say so in the ADR before it becomes public surface.

**Multivalued dependencies and 4NF**, and the general chase with tuple- and
equality-generating dependencies. The tableau machinery here is one `Symbol`
enum and a global replacement away from supporting them; the certificate story
would need re-deriving, since a chase with EGDs can fail rather than terminate.

**A 3NF synthesis algorithm.** The lane *decides* 3NF and *checks* a given
decomposition; it does not construct one. That is the obvious next slice, and
the attribution to get right is split: Bernstein 1976 delivers dependency
preservation, and the lossless-join guarantee comes from the extra key fragment
added by Biskup, Dayal and Bernstein in 1979. Citing Bernstein alone for both,
as is common, is wrong.

## Attribution notes

Everything proved here is instance-level; none of the mathematics is ours, and
the facts say so. Three corrections the literature pass produced, all of which
went into the `prior_art` rows:

1. **Armstrong's axioms may not be Armstrong's axioms.** Maier's bibliographic
   notes credit the three rules to Delobel and Casey (1973) and Armstrong with
   the soundness and completeness *proof*. AHV says only "the axiomatization is
   due to [Arm74]". Both agree completeness is his.
2. **BCNF is cited to Codd alone.** The 1974 IFIP paper has Codd as sole author
   in both bibliographies; "Boyce–Codd" is the eponym, not the byline, and
   Date's claim that Heath had the definition in 1971 is lore this lane could
   not verify to a primary source.
3. **The two-way lossless-join criterion is not Heath's theorem**, at least not
   according to the two scholarly sources: Maier credits the sufficient
   direction to Delobel and Casey (1973) and the necessary direction to Rissanen
   (1977).

Every `prior_art.attribution` field says what was actually read. In every case
it was a page of Abiteboul–Hull–Vianu or Maier, not the primary paper, and the
rows say that rather than implying otherwise.
