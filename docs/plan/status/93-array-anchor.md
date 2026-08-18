# Lane: array-anchor — the disequality the module assumes must be one the query forces

<!-- plan-section: lane-status -->

**Ten of the thirteen bare-leaf attestations now carry a checked anchor; three
are declined with a named reason** (`WIP`, array-anchor, 2026-08-18).

Lane `agent-attestation` left 13 `ArrayAxiom`/`TermIdentity` instances whose
whole rendered module is

    axiom axeyum.reconstruct.hyp._2 : Eq.{1} α atom._0 atom._1
    axiom axeyum.reconstruct.hyp._3 : Not (Eq.{1} α atom._0 atom._1)

— one assumed schema conclusion and one assumed disequality, over two bare
constants. `bind_structural` refuses them and is **right to**: an injective map
onto two of the query's symbols exists for any query with two symbols, so a
structural match there would be a check with no true instance. That refusal is
the guard, not the gap.

**The gap is the second axiom.** The module *assumes* `¬(lhs = rhs)` and nothing
in Lean checks that the query says so. Anchoring checks exactly that, and asks a
different question from the structural one — not "is this term in the file" but
**"do the file's own assertions FORCE this equality to be false, and is it the
only one they force that this module could stand for?"**

`forced_disequalities` reads the `.smt2` text and propagates a required truth
value down each `(assert …)`: through `not`/`and`/`or`/`=>`, through `distinct`,
and through the one-bit-vector encoding a BTOR-derived file writes Booleans in
(`(= #b1 t)`, `bvand`/`bvor`/`bvnot`, `(ite c #b1 #b0)`). It stops wherever the
value is not forced — an `or` under a true polarity, an `xor`, an n-ary `=` under
a false polarity, an `ite` without the Boolean branch pair — because each of
those entails a disjunction, not a fact.

**Uniqueness is what makes it an anchor rather than a formality, and it bites on
the very set it was built for: 3 of the 13 are refused.**
`solver__array__ext27.btor.smt2` forces four leaf disequalities (`i0≠i1`,
`v5≠v6`, `i0≠i2`, `i1≠i2`) and a bare module does not say which it means; the two
`unsat__replace_all__not-first-only` rows force none at all, their one assertion
being a forced-**true** equality whose sides the arena constant-folded — the same
rewrite residue as `ext10` and `redand-eliminate`. Those three stay attested.

**The `TermIdentity` route was also rendering opaquely, and did not need to be.**
`term_identity_term_expr` keyed one constant per whole `TermId`, exactly the
pre-2026-08-18 `ArrayAxiom` mistake. It now uses the same budgeted
`query_term_expr`, so `(assert (not (= x (ite true x y))))` renders as
`Not (Eq α atom._0 (func._3 atom._1 atom._0 atom._2))` — a transcription of a
whole assert line. For those three the correspondence is pinned by structure and
not only by uniqueness, and a swapped `ite` argument names a term the file does
not contain.

**What anchoring does NOT show, stated because it is the honest half.** For the
seven bare-pair `ArrayAxiom` rows the correspondence is pinned *only* by
uniqueness: those seven modules are byte-identical to each other, so each anchors
against any of the others' queries. It rules out a module assuming a disequality
the query does not entail, and a query that entails none or several. It does not
say which symbol a bare `atom._0` means. Pinned as a driven test
(`test_the_bare_module_does_NOT_anchor_against_the_identity_query`) rather than
left in prose.

**Gate line**, `python3 scripts/check-lra-hypothesis-binding.py`, before → after:

    …|structural=95|…|attested=19|…|failures=0
    …|structural=95|…|anchored=10|anchored_nodes=29|anchored_caught=26|anchored_accepted=0|attested=9|…|failures=0

26 of 26 corruptions of an anchored module are caught, and 0 accepted — the
strongest ratio of the three checked classes, because the anchor is matched
against what the query *forces* rather than against every subterm it contains.
The anti-absorption guard now runs in both directions: an instance pinned
`attested` fails if the structural binder **or** the anchor can relate it to its
query.

**Two dead controls found and repaired.** `mutation_controls.py`'s
`injectivity of the renaming`, `sort-soundness of the renaming` and
`an unknown rendered leaf is not a fresh variable` had all gone to
`MUTATION DID NOT APPLY` when the degree-2 monomial work moved the guard text
under them — a mutation harness reporting three guards it never tested. And
adding the anchored anti-absorption guard *masked* the structural one: with
`bound_anyway` deleted the structural fixture was caught by the anchor instead,
so the older guard SURVIVED. Both are now driven by a case only they can catch.
All 43 guards kill at least one test.

**Also corrected**: `ArrayAxiomRefutationCertificate::assertion` was documented
as "the original top-level disequality assertion". On the read-congruence path
it is not a disequality at all — it is the whole bit-blasted assertion, and
`¬(lhs = rhs)` is something that assertion *entails*. That distinction is the
entire reason the checker propagates polarity instead of pattern-matching a
`not (= …)`.

**Measured aside for whoever takes the next slice.** 63 of the 95 rows pinned
`structural` also anchor — their query asserts the disequality outright rather
than leaving it a congruence conclusion. They are left `structural` because that
is the stronger statement about them, and because the manifests are currently
mutually exclusive.

**Next.** (1) The two rewrite-output instances (`redand-eliminate`, `ext10`) and
the two `replace_all` rows need a rewrite-step certificate; anchoring reaches
none of them and the reasons are now written down per instance. (2) `ext27` needs
the module to carry *which* pair — which needs the emitter to render the source
assertion, not just the pair, and an explicit assumed entailment step beside it.
(3) The 4 `FiniteArrayExtensionality` rows render `Not (And (Eq α a b) (Eq α c
d))`, which has no bare `Not (Eq …)` for either checked verdict to take hold of.
