# Lane: binding-coverage — how much of the corpus's Lean evidence says anything

<!-- plan-section: lane-status -->

**The transcription check now covers three routes, and the denominator is
measured rather than estimated** (`WIP`, binding-coverage, 2026-08-18).

Lane `agent-transcription` closed the SMT-LIB → rendered-statement gap
(trust-surface item 3, *weaker than the kernel*) for the two Farkas routes and
declined the rest. This lane widened it and, more usefully, **measured what the
rest actually is**. Swept all **1404** committed `.smt2` files: **270** render a
Lean module at all, and those 270 split exactly three ways.

| verdict | n | what it means |
| --- | --- | --- |
| **bound** | 125 | every rendered hypothesis bound back to an `(assert …)` line |
| **attested** | 124 | the module transcribes **nothing**; verified content-free |

> **SUPERSEDED 2026-08-18 by lane `agent-attestation`.** The 124 were not one
> class. Decomposed per route, **89 `ArrayAxiom` modules said nothing because of
> how the emitter was written** — `array_axiom_term_expr` collapsed each whole
> term into a single opaque constant keyed by arena index, though the certificate
> carried the query's own `TermId`s all along, and the trees are 10 nodes at the
> median. A test now pins the defect that hid behind it: read-over-write and
> select-over-ite rendered **the same module, byte for byte**. Six more
> (`QfAbv`/`QfUf`) were structural all along and merely misfiled.
>
> Current gate line: `structural=95 attested=28 attested_vacuous=0`. The
> **self-refuting** instance was a real bug — `conflicting_bool_negation_equalities`
> returned the pair `(p, p)` for `(not (not (= p (not p))))`, a *Boolean*
> conflict where no honest pair exists — and the route now declines it, which
> re-running the search could never have caught. The query is still `unsat` via
> `TermLevelEnum`, `certified=1`.
>
> `structural` is deliberately weaker than `bound`: for 89 of 105 queries no
> assertion says `¬(lhs = rhs)`, because the hypothesis is a congruence
> *conclusion*. Binding those to an assert line would be a check with no true
> instance — so they get their own verdict, and an anti-absorption guard **fails**
> if an instance pinned `attested` can be related to its query, which is exactly
> the silent lie that had already happened to those six.
| **declined** | 21 | neither — named, not pinned, not checked |

**+20 bound (105 → 125), and the 124 are the finding.** The `ArrayAxiom`,
`QfAbv` and `Sos` reconstructions render an *opaque-skeleton attestation*: their
entire vocabulary is `α atom._N prop._N func._N Eq.{1} Not And`, with no
numeral, no `Int.*`/`Real.*` constructor and no carrier of any route. Lean checks
that `False` follows — and it would follow just as well if the `.smt2` file said
something else entirely, because the module's trusted base is a **fresh
vocabulary with no declared relationship to any symbol in the query.** Binding
them would be a check that cannot fail, so they are classified instead, in their
own manifest, reported as `attested=` and never as coverage. What *is* checked,
every run, is that each really is that shape: one smuggled `Int.one`, one
undeclared opaque name, one truncated type or one extra axiom takes a module out
of the class and fails the run. **One of the 124 is self-refuting** — its
`Not (Eq.{1} α atom._0 atom._0)` is an axiom Lean's own `rfl` refutes, so its
`False` needs none of the module's other axioms and not even the propositional
step is taken (`attested_vacuous=1`).

**Two prior claims were wrong, and both were measurements nobody had taken.**
The SOS route does **not** render `Real.mul` monomials on 10 QF_NRA instances:
9 of them render the content-free propositional skeleton above, and **exactly
one** file in the whole corpus (`nra-neg-square-d01.smt2`) renders a monomial at
all. `ArrayAxiom` is 102 instances in the corpus, not 14.

**The Diophantine route (`axeyum.reconstruct.dio.hyp._N`) is bound**: 18 of its
20 instances, the ground-linear ones. Its hypotheses are `Eq.{1} Int` equalities
with coefficients rendered as repeated `Int.add`. Adding it exposed a real defect
in the checker: the `=` canonical form sign-normalized on the **lexicographically
first variable**, which reads a name and so is *not rename-invariant* — the two
sides of this check use different names by construction, and four faithful
modules were being rejected. Both orientations of every equality go into the pool
instead, which needs no name ordering at all.

**The converse direction is now measured, not just admitted.** Binding proves
every rendered hypothesis comes *from* the query; it says nothing about the
query's rows that were never rendered. That shortfall is counted from the
accepted renaming (never from the search's own bookkeeping) and printed:
**286 of 531 spine assertions are represented** — barely half. Not a soundness
hole (a refutation of a subset refutes the whole) but the precise size of what
the subset check does not show, floored by `--min-represented` so a wholesale
drop cannot pass quietly.

**Two defects that made the checker lie rather than decline.** (1) A module with
no hypothesis in any bound route *bound vacuously* — the empty renaming satisfies
every requirement — so a pinned instance degrading to a content-free skeleton
would have stayed green. (2) `read_query` died with `Unsupported: arithmetic head
'forall'` on a `let`-bound quantifier and ended the run in a **traceback**, which
is neither a pass nor an honest decline; the name is now bound opaquely, and
referencing it contributes no atom rather than inventing a free variable a
hypothesis could match.

**24 guards, each driven to failure** in `scripts/tests/mutation_controls.py`
(12 → 24); 83 offline control tests. Every run corrupts each hypothesis six ways:
1210 caught, 427 accepted and each re-verified from its own binding.

**Next, in measured order.** (1) The 13 quantified LIA/BV instances whose
hypothesis is a pi-type `((x0 : Int) -> … Or/Not/Iff …)` — the largest declined
group, and the one needing a genuinely different binding argument. (2) Monomial
support, worth **one** instance, not ten: it means canonicalizing over monomials
rather than variables, which touches the matching code all 125 bound instances
rest on. (3) The 8 ground declines whose hypothesis is the *output* of an array
or BV abstraction step rather than a transcription of any assertion — these need
the abstraction itself bound, which is a different check.

<!-- plan-section: landed-changes -->

| 2026-08-18 | `pending` | binding coverage: +20 bound (105 → 125), 124 modules proved content-free, and the converse direction measured at 286/531 |
