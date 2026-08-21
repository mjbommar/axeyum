# Notes: 95-binding-coverage

Detail moved out of [`../status/95-binding-coverage.md`](../status/95-binding-coverage.md) so the
lane-status block stays inside the per-lane ceiling. Nothing here was
deleted; it was moved.

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
