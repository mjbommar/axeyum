# Fact atlas: the whole ledger

*341 facts, 155 depends_on edges*

[Pilot: the Fibonacci frontier](facts-pilot.html) / [Pilot: Euclid's lemma](facts-pilot-arith.html)

Every fact in `artifacts/facts/` (341 facts, 155 `depends_on` edges), both of its status axes, and the dependency graph they form. Every status here is copied from the ledger; nothing infers or upgrades one, and the badge column is a conservative mapping that can only weaken a ledger value. Facts established here but not settled in the literature are listed first: that disagreement is the output this project exists to produce.

EXCLUDED FROM THIS ATLAS: 2 fact file(s) in the ledger currently FAIL fact.schema.json and are not rendered here, because a card cannot be built from bytes the schema rejects. The exclusion is a finding about the ledger, not about the mathematics: F-lean-query-module-shrinks-by-a-shared-import.json; F-lean-query-module-shrinks-by-a-shared-import.json. Note that scripts/validate-facts.py currently ACCEPTS these files, so the schema and the gate disagree; reported to the ledger owners.

Established here, not settled in the literature

| fact | title | epistemic | external | card |
| --- | --- | --- | --- | --- |
| F:rado-r4-a5-b3 | The four-colour Rado number of 5(x-y) = 3z is 625 | computed | open | [`F-rado-r4-a5-b3`](cards/F-rado-r4-a5-b3.html) |
| F:rado-r4-a5-b4 | The four-colour Rado number of 5(x-y) = 4z is 741 | computed | open | [`F-rado-r4-a5-b4`](cards/F-rado-r4-a5-b4.html) |

Source: `python3 render/producers-py/facts_to_docir.py` (exit 0), 341 input(s) hashed.

The `depends_on` relation over these 341 facts has 155 edges and falls into 213 connected components: 38 with more than one fact (166 facts between them, the largest holding 43), and 175 single facts that nothing in the ledger depends on and that depend on nothing in it.

One drawing of all 341 would be 341 nodes wide and four layers deep -- a strip some thirty thousand pixels across, which at page width is a smear. So each component is drawn on its own below, largest first, and the 175 unconnected facts appear in the index table rather than as a row of dots. The index is the complete list either way: every fact is in it.

*Figure (Dependency graph of 43 facts with 67 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:complex-admits-no-compatible-order",
      "label": "depends_on",
      "to": "F:complex-ring-constructed-axiom-free"
    },
    {
      "from": "F:complex-ring-constructed-axiom-free",
      "label": "depends_on",
      "to": "F:real-axioms-modelled-by-constructed-setoid"
    },
    {
      "from": "F:farkas-refutation-over-constructed-reals",
      "label": "depends_on",
      "to": "F:ordered-ring-farkas-refutation"
    },
    {
      "from": "F:farkas-refutation-over-constructed-reals",
      "label": "depends_on",
      "to": "F:real-axioms-modelled-by-constructed-setoid"
    },
    {
      "from": "F:int-add-assoc",
      "label": "depends_on",
      "to": "F:nat-add-assoc"
    },
    {
      "from": "F:int-add-assoc",
      "label": "depends_on",
      "to": "F:nat-add-comm"
    },
    {
      "from": "F:int-add-assoc",
      "label": "depends_on",
      "to": "F:nat-succ-add"
    },
    {
      "from": "F:int-add-comm",
      "label": "depends_on",
      "to": "F:nat-add-comm"
    },
    {
      "from": "F:int-add-le-add",
      "label": "depends_on",
      "to": "F:int-add-assoc"
    },
    {
      "from": "F:int-add-le-add",
      "label": "depends_on",
      "to": "F:int-add-comm"
    },
    {
      "from": "F:int-add-lt-add-of-le-of-lt",
      "label": "depends_on",
      "to": "F:int-add-assoc"
    },
    {
      "from": "F:int-add-lt-add-of-le-of-lt",
      "label": "depends_on",
      "to": "F:int-add-comm"
    },
    {
      "from": "F:int-add-lt-add-of-le-of-lt",
      "label": "depends_on",
      "to": "F:int-add-le-add"
    },
    {
      "from": "F:int-categoricity",
      "label": "depends_on",
      "to": "F:int-characterization"
    },
    {
      "from": "F:int-categoricity",
      "label": "depends_on",
      "to": "F:nat-peano-categoricity"
    },
    {
      "from": "F:int-characterization",
      "label": "depends_on",
      "to": "F:int-add-assoc"
    },
    {
      "from": "F:int-characterization",
      "label": "depends_on",
      "to": "F:int-mul-assoc"
    },
    {
      "from": "F:int-euclidean-decomposition",
      "label": "depends_on",
      "to": "F:nat-div-mod-exists"
    },
    {
      "from": "F:int-euclidean-decomposition",
      "label": "depends_on",
      "to": "F:nat-div-mod-unique"
    },
    {
      "from": "F:int-euclidean-decomposition",
      "label": "depends_on",
      "to": "F:nat-zero-add"
    },
    {
      "from": "F:int-left-distrib",
      "label": "depends_on",
      "to": "F:int-add-assoc"
    },
    {
      "from": "F:int-left-distrib",
      "label": "depends_on",
      "to": "F:nat-left-distrib"
    },
    {
      "from": "F:int-left-distrib",
      "label": "depends_on",
      "to": "F:nat-succ-add"
    },
    {
      "from": "F:int-mul-assoc",
      "label": "depends_on",
      "to": "F:nat-mul-assoc"
    },
    {
      "from": "F:int-mul-comm",
      "label": "depends_on",
      "to": "F:nat-mul-comm"
    },
    {
      "from": "F:int-sq-nonneg",
      "label": "depends_on",
      "to": "F:int-mul-comm"
    },
    {
      "from": "F:nat-add-comm",
      "label": "depends_on",
      "to": "F:nat-succ-add"
    },
    {
      "from": "F:nat-add-comm",
      "label": "depends_on",
      "to": "F:nat-zero-add"
    },
    {
      "from": "F:nat-add-sub-cancel-left",
      "label": "depends_on",
      "to": "F:nat-add-comm"
    },
    {
      "from": "F:nat-div-mod-unique",
      "label": "depends_on",
      "to": "F:nat-div-mod-exists"
    },
    {
      "from": "F:nat-dvd-add",
      "label": "depends_on",
      "to": "F:nat-left-distrib"
    },
    {
      "from": "F:nat-euclid-lemma",
      "label": "depends_on",
      "to": "F:nat-add-assoc"
    },
    {
      "from": "F:nat-euclid-lemma",
      "label": "depends_on",
      "to": "F:nat-add-comm"
    },
    {
      "from": "F:nat-euclid-lemma",
      "label": "depends_on",
      "to": "F:nat-dvd-add"
    },
    {
      "from": "F:nat-euclid-lemma",
      "label": "depends_on",
      "to": "F:nat-dvd-gcd-iff"
    },
    {
      "from": "F:nat-euclid-lemma",
      "label": "depends_on",
      "to": "F:nat-gcd-bezout"
    },
    {
      "from": "F:nat-euclid-lemma",
      "label": "depends_on",
      "to": "F:nat-mul-assoc"
    },
    {
      "from": "F:nat-euclid-lemma",
      "label": "depends_on",
      "to": "F:nat-mul-comm"
    },
    {
      "from": "F:nat-exists-prime-dvd",
      "label": "depends_on",
      "to": "F:nat-div-mod-exists"
    },
    {
      "from": "F:nat-exists-prime-dvd",
      "label": "depends_on",
      "to": "F:nat-dvd-add"
    },
    {
      "from": "F:nat-exists-prime-gt",
      "label": "depends_on",
      "to": "F:nat-dvd-add"
    },
    {
      "from": "F:nat-exists-prime-gt",
      "label": "depends_on",
      "to": "F:nat-exists-prime-dvd"
    },
    {
      "from": "F:nat-gcd-bezout",
      "label": "depends_on",
      "to": "F:nat-add-assoc"
    },
    {
      "from": "F:nat-gcd-bezout",
      "label": "depends_on",
      "to": "F:nat-add-comm"
    },
    {
      "from": "F:nat-gcd-bezout",
      "label": "depends_on",
      "to": "F:nat-gcd-succ"
    },
    {
      "from": "F:nat-gcd-bezout",
      "label": "depends_on",
      "to": "F:nat-left-distrib"
    },
    {
      "from": "F:nat-gcd-bezout",
      "label": "depends_on",
      "to": "F:nat-mul-assoc"
    },
    {
      "from": "F:nat-gcd-bezout",
      "label": "depends_on",
      "to": "F:nat-mul-one"
    },
    {
      "from": "F:nat-gcd-bezout",
      "label": "depends_on",
      "to": "F:nat-zero-add"
    },
    {
      "from": "F:nat-left-distrib",
      "label": "depends_on",
      "to": "F:nat-add-assoc"
    },
    {
      "from": "F:nat-mul-assoc",
      "label": "depends_on",
      "to": "F:nat-left-distrib"
    },
    {
      "from": "F:nat-mul-one",
      "label": "depends_on",
      "to": "F:nat-zero-add"
    },
    {
      "from": "F:nat-pow-add",
      "label": "depends_on",
      "to": "F:nat-mul-assoc"
    },
    {
      "from": "F:nat-pow-add",
      "label": "depends_on",
      "to": "F:nat-mul-comm"
    },
    {
      "from": "F:nat-pow-add",
      "label": "depends_on",
      "to": "F:nat-mul-one"
    },
    {
      "from": "F:ordered-ring-interface-is-the-same-over-the-axiom-free-integers",
      "label": "depends_on",
      "to": "F:int-add-comm"
    },
    {
      "from": "F:ordered-ring-interface-is-the-same-over-the-axiom-free-integers",
      "label": "depends_on",
      "to": "F:int-sq-nonneg"
    },
    {
      "from": "F:rat-add-neg-inverse",
      "label": "depends_on",
      "to": "F:rat-mul-renormalises"
    },
    {
      "from": "F:rat-mul-renormalises",
      "label": "depends_on",
      "to": "F:rat-normalize-reduces"
    },
    {
      "from": "F:rat-normalize-reduces",
      "label": "depends_on",
      "to": "F:int-euclidean-decomposition"
    },
    {
      "from": "F:real-axioms-modelled-by-constructed-setoid",
      "label": "depends_on",
      "to": "F:rat-add-neg-inverse"
    },
    {
      "from": "F:real-axioms-modelled-by-constructed-setoid",
      "label": "depends_on",
      "to": "F:rat-mul-renormalises"
    },
    {
      "from": "F:real-axioms-modelled-by-constructed-setoid",
      "label": "depends_on",
      "to": "F:rat-normalize-reduces"
    },
    {
      "from": "F:real-lattice-is-constructed-axiom-free",
      "label": "depends_on",
      "to": "F:real-axioms-modelled-by-constructed-setoid"
    },
    {
      "from": "F:shipped-front-door-reaches-no-real-axiom",
      "label": "depends_on",
      "to": "F:shipped-front-door-refutes-over-constructed-reals"
    },
    {
      "from": "F:shipped-front-door-refutes-over-constructed-reals",
      "label": "depends_on",
      "to": "F:farkas-refutation-over-constructed-reals"
    },
    {
      "from": "F:shipped-front-door-refutes-over-constructed-reals",
      "label": "depends_on",
      "to": "F:real-axioms-modelled-by-constructed-setoid"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "kernel-lean",
      "href": "cards/F-complex-admits-no-compatible-order.doc.json",
      "id": "F:complex-admits-no-compatible-order",
      "label": "complex-admits-no-compatible-order",
      "status": "proved",
      "tooltip": "No relation on the constructed complex numbers satisfies seven of the Real package's ordered-ring laws"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-complex-ring-constructed-axiom-free.doc.json",
      "id": "F:complex-ring-constructed-axiom-free",
      "label": "complex-ring-constructed-axiom-free",
      "status": "proved",
      "tooltip": "The complex numbers are constructible in this kernel at zero trusted declarations, as a pair setoid over the constructed reals"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-farkas-refutation-over-constructed-reals.doc.json",
      "id": "F:farkas-refutation-over-constructed-reals",
      "label": "farkas-refutation-over-constructed-reals",
      "status": "proved",
      "tooltip": "A Farkas refutation closes over the constructed reals resting on zero carrier axioms, where the same refutation over the axiomatized AxReal package rests on 30"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-int-add-assoc.doc.json",
      "id": "F:int-add-assoc",
      "label": "int-add-assoc",
      "status": "proved",
      "tooltip": "Addition on the integers is associative"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-int-add-comm.doc.json",
      "id": "F:int-add-comm",
      "label": "int-add-comm",
      "status": "proved",
      "tooltip": "Addition on the integers is commutative"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-int-add-le-add.doc.json",
      "id": "F:int-add-le-add",
      "label": "int-add-le-add",
      "status": "proved",
      "tooltip": "The order on the integers is compatible with addition"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-int-add-lt-add-of-le-of-lt.doc.json",
      "id": "F:int-add-lt-add-of-le-of-lt",
      "label": "int-add-lt-add-of-le-of-lt",
      "status": "proved",
      "tooltip": "A strict integer inequality survives addition of a non-strict one"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-int-categoricity.doc.json",
      "id": "F:int-categoricity",
      "label": "int-categoricity",
      "status": "proved",
      "tooltip": "The constructed Int is THE integers: every generated aperiodic Z-structure is in structure-preserving bijection with it"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-int-characterization.doc.json",
      "id": "F:int-characterization",
      "label": "int-characterization",
      "status": "proved",
      "tooltip": "The constructed Int is a discretely ordered ring generated by 1, with unique maps out"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-int-euclidean-decomposition.doc.json",
      "id": "F:int-euclidean-decomposition",
      "label": "int-euclidean-decomposition",
      "status": "proved",
      "tooltip": "Euclidean decomposition over the integers is derived, not assumed"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-int-left-distrib.doc.json",
      "id": "F:int-left-distrib",
      "label": "int-left-distrib",
      "status": "proved",
      "tooltip": "Multiplication distributes over addition on the integers"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-int-mul-assoc.doc.json",
      "id": "F:int-mul-assoc",
      "label": "int-mul-assoc",
      "status": "proved",
      "tooltip": "Multiplication on the integers is associative"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-int-mul-comm.doc.json",
      "id": "F:int-mul-comm",
      "label": "int-mul-comm",
      "status": "proved",
      "tooltip": "Multiplication on the integers is commutative"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-int-sq-nonneg.doc.json",
      "id": "F:int-sq-nonneg",
      "label": "int-sq-nonneg",
      "status": "proved",
      "tooltip": "Every integer square is nonnegative"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-add-assoc.doc.json",
      "id": "F:nat-add-assoc",
      "label": "nat-add-assoc",
      "status": "proved",
      "tooltip": "Addition on the naturals is associative"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-add-comm.doc.json",
      "id": "F:nat-add-comm",
      "label": "nat-add-comm",
      "status": "proved",
      "tooltip": "Addition on the naturals is commutative"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-add-sub-cancel-left.doc.json",
      "id": "F:nat-add-sub-cancel-left",
      "label": "nat-add-sub-cancel-left",
      "status": "proved",
      "tooltip": "Subtraction undoes addition on the naturals"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-div-mod-exists.doc.json",
      "id": "F:nat-div-mod-exists",
      "label": "nat-div-mod-exists",
      "status": "proved",
      "tooltip": "Division with remainder always exists for a positive divisor"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-div-mod-unique.doc.json",
      "id": "F:nat-div-mod-unique",
      "label": "nat-div-mod-unique",
      "status": "proved",
      "tooltip": "The quotient and remainder of a division are unique"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-dvd-add.doc.json",
      "id": "F:nat-dvd-add",
      "label": "nat-dvd-add",
      "status": "proved",
      "tooltip": "A common divisor of two numbers divides their sum"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-dvd-gcd-iff.doc.json",
      "id": "F:nat-dvd-gcd-iff",
      "label": "nat-dvd-gcd-iff",
      "status": "proved",
      "tooltip": "The gcd is exactly the common divisors' upper bound"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-euclid-lemma.doc.json",
      "id": "F:nat-euclid-lemma",
      "label": "nat-euclid-lemma",
      "status": "proved",
      "tooltip": "Euclid's lemma: a prime dividing a product divides a factor"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-exists-prime-dvd.doc.json",
      "id": "F:nat-exists-prime-dvd",
      "label": "nat-exists-prime-dvd",
      "status": "proved",
      "tooltip": "Every natural number at least 2 has a prime divisor"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-exists-prime-gt.doc.json",
      "id": "F:nat-exists-prime-gt",
      "label": "nat-exists-prime-gt",
      "status": "proved",
      "tooltip": "There is no largest prime"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-gcd-bezout.doc.json",
      "id": "F:nat-gcd-bezout",
      "label": "nat-gcd-bezout",
      "status": "proved",
      "tooltip": "Bezout's identity holds for the natural gcd"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-gcd-succ.doc.json",
      "id": "F:nat-gcd-succ",
      "label": "nat-gcd-succ",
      "status": "proved",
      "tooltip": "The Euclidean algorithm's descent step is correct"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-left-distrib.doc.json",
      "id": "F:nat-left-distrib",
      "label": "nat-left-distrib",
      "status": "proved",
      "tooltip": "Multiplication distributes over addition on the left"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-mul-assoc.doc.json",
      "id": "F:nat-mul-assoc",
      "label": "nat-mul-assoc",
      "status": "proved",
      "tooltip": "Multiplication on the naturals is associative"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-mul-comm.doc.json",
      "id": "F:nat-mul-comm",
      "label": "nat-mul-comm",
      "status": "proved",
      "tooltip": "Multiplication on the naturals is commutative"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-mul-one.doc.json",
      "id": "F:nat-mul-one",
      "label": "nat-mul-one",
      "status": "proved",
      "tooltip": "One is a right identity for multiplication on the naturals"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-peano-categoricity.doc.json",
      "id": "F:nat-peano-categoricity",
      "label": "nat-peano-categoricity",
      "status": "proved",
      "tooltip": "The constructed Nat is THE natural numbers, up to unique isomorphism"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-pow-add.doc.json",
      "id": "F:nat-pow-add",
      "label": "nat-pow-add",
      "status": "proved",
      "tooltip": "The first index law: powers add over a product"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-succ-add.doc.json",
      "id": "F:nat-succ-add",
      "label": "nat-succ-add",
      "status": "proved",
      "tooltip": "Nat succ_add"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-zero-add.doc.json",
      "id": "F:nat-zero-add",
      "label": "nat-zero-add",
      "status": "proved",
      "tooltip": "Nat zero_add"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-ordered-ring-farkas-refutation.doc.json",
      "id": "F:ordered-ring-farkas-refutation",
      "label": "ordered-ring-farkas-refutation",
      "status": "proved",
      "tooltip": "A reconstructed Farkas refutation holds in every ordered commutative ring, and rests on no axiom"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-ordered-ring-interface-is-the-same-over-the-axiom-free-integers.doc.json",
      "id": "F:ordered-ring-interface-is-the-same-over-the-axiom-free-integers",
      "label": "ordered-ring-interface-is-the-same-over-the-axiom-free-integers",
      "status": "proved",
      "tooltip": "The ordered-ring interface telescope is byte-identical over Real and over the axiom-free Int development"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-rat-add-neg-inverse.doc.json",
      "id": "F:rat-add-neg-inverse",
      "label": "rat-add-neg-inverse",
      "status": "proved",
      "tooltip": "Rational addition renormalises and negation is an additive inverse"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-rat-mul-renormalises.doc.json",
      "id": "F:rat-mul-renormalises",
      "label": "rat-mul-renormalises",
      "status": "proved",
      "tooltip": "Rational multiplication renormalises"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-rat-normalize-reduces.doc.json",
      "id": "F:rat-normalize-reduces",
      "label": "rat-normalize-reduces",
      "status": "proved",
      "tooltip": "The rational smart constructor normalises"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-real-axioms-modelled-by-constructed-setoid.doc.json",
      "id": "F:real-axioms-modelled-by-constructed-setoid",
      "label": "real-axioms-modelled-by-constructed-setoid",
      "status": "proved",
      "tooltip": "The 30 AxReal axioms are satisfiable: a Bishop setoid over the constructed rationals models all 22 laws at zero trusted declarations"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-real-lattice-is-constructed-axiom-free.doc.json",
      "id": "F:real-lattice-is-constructed-axiom-free",
      "label": "real-lattice-is-constructed-axiom-free",
      "status": "proved",
      "tooltip": "The constructed reals carry max, min and a total absolute value, built with no index shift and no decision procedure"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-shipped-front-door-reaches-no-real-axiom.doc.json",
      "id": "F:shipped-front-door-reaches-no-real-axiom",
      "label": "shipped-front-door-reaches-no-real-axiom",
      "status": "proved",
      "tooltip": "No shipped reconstruction route BUILDS the AxReal axiom package: the trusted surface is declared but never reached"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-shipped-front-door-refutes-over-constructed-reals.doc.json",
      "id": "F:shipped-front-door-refutes-over-constructed-reals",
      "label": "shipped-front-door-refutes-over-constructed-reals",
      "status": "proved",
      "tooltip": "The shipped LRA/SOS front door reconstructs over the constructed reals, and the refutation it returns rests on zero carrier axioms"
    }
  ],
  "rankdir": "TB"
}
```

*Component 1 of 38: 43 facts, 67 edges. An edge runs from the dependent fact to the fact it rests on.*

*Figure (Dependency graph of 9 facts with 8 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-int-fib-add-one-33f1b748",
      "label": "depends_on",
      "to": "F:ml430-int-fib-add-two-739358dd"
    },
    {
      "from": "F:ml430-int-fib-add-two-739358dd",
      "label": "depends_on",
      "to": "F:ml430-int-fib-natcast-d5886be4"
    },
    {
      "from": "F:ml430-int-fib-add-two-739358dd",
      "label": "depends_on",
      "to": "F:ml430-nat-fib-add-two-b86e0c82"
    },
    {
      "from": "F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d",
      "label": "depends_on",
      "to": "F:ml430-int-fib-add-two-739358dd"
    },
    {
      "from": "F:ml430-nat-fib-coprime-fib-succ-162fc738",
      "label": "depends_on",
      "to": "F:ml430-nat-fib-add-two-b86e0c82"
    },
    {
      "from": "F:ml430-nat-fib-le-fib-succ-d1ef4a3d",
      "label": "depends_on",
      "to": "F:ml430-nat-fib-add-two-b86e0c82"
    },
    {
      "from": "F:ml430-nat-fib-mono-cc6afe09",
      "label": "depends_on",
      "to": "F:ml430-nat-fib-le-fib-succ-d1ef4a3d"
    },
    {
      "from": "F:ml430-nat-gcd-fib-add-self-5a92d5e3",
      "label": "depends_on",
      "to": "F:ml430-nat-fib-coprime-fib-succ-162fc738"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-fib-add-one-33f1b748.doc.json",
      "id": "F:ml430-int-fib-add-one-33f1b748",
      "label": "ml430-int-fib-add-one",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.fib_add_one"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-fib-add-two-739358dd.doc.json",
      "id": "F:ml430-int-fib-add-two-739358dd",
      "label": "ml430-int-fib-add-two",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.fib_add_two"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d.doc.json",
      "id": "F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d",
      "label": "ml430-int-fib-eq-fib-add-two-sub-fib-add-one",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.fib_eq_fib_add_two_sub_fib_add_one"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-fib-natcast-d5886be4.doc.json",
      "id": "F:ml430-int-fib-natcast-d5886be4",
      "label": "ml430-int-fib-natcast",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.fib_natCast"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-ml430-nat-fib-add-two-b86e0c82.doc.json",
      "id": "F:ml430-nat-fib-add-two-b86e0c82",
      "label": "ml430-nat-fib-add-two",
      "status": "proved",
      "tooltip": "Mathlib v4.30 source proposition Nat.fib_add_two"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-ml430-nat-fib-coprime-fib-succ-162fc738.doc.json",
      "id": "F:ml430-nat-fib-coprime-fib-succ-162fc738",
      "label": "ml430-nat-fib-coprime-fib-succ",
      "status": "proved",
      "tooltip": "Mathlib v4.30 source proposition Nat.fib_coprime_fib_succ"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-fib-le-fib-succ-d1ef4a3d.doc.json",
      "id": "F:ml430-nat-fib-le-fib-succ-d1ef4a3d",
      "label": "ml430-nat-fib-le-fib-succ",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.fib_le_fib_succ"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-fib-mono-cc6afe09.doc.json",
      "id": "F:ml430-nat-fib-mono-cc6afe09",
      "label": "ml430-nat-fib-mono",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.fib_mono"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-ml430-nat-gcd-fib-add-self-5a92d5e3.doc.json",
      "id": "F:ml430-nat-gcd-fib-add-self-5a92d5e3",
      "label": "ml430-nat-gcd-fib-add-self",
      "status": "proved",
      "tooltip": "Mathlib v4.30 source proposition Nat.gcd_fib_add_self"
    }
  ],
  "rankdir": "TB"
}
```

*Component 2 of 38: 9 facts, 8 edges. An edge runs from the dependent fact to the fact it rests on.*

*Figure (Dependency graph of 7 facts with 7 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-le-sqrt-e6996680",
      "label": "depends_on",
      "to": "F:ml430-nat-lt-succ-sqrt-39389df2"
    },
    {
      "from": "F:ml430-nat-le-sqrt-e6996680",
      "label": "depends_on",
      "to": "F:ml430-nat-sqrt-le-7918582b"
    },
    {
      "from": "F:ml430-nat-le-sqrt-of-eq-mul-503c5afe",
      "label": "depends_on",
      "to": "F:ml430-nat-le-sqrt-e6996680"
    },
    {
      "from": "F:ml430-nat-sqrt-le-self-1ed5eb85",
      "label": "depends_on",
      "to": "F:ml430-nat-sqrt-le-7918582b"
    },
    {
      "from": "F:ml430-nat-sqrt-le-sqrt-6e2bfc47",
      "label": "depends_on",
      "to": "F:ml430-nat-le-sqrt-e6996680"
    },
    {
      "from": "F:ml430-nat-sqrt-le-sqrt-6e2bfc47",
      "label": "depends_on",
      "to": "F:ml430-nat-sqrt-le-7918582b"
    },
    {
      "from": "F:ml430-nat-sqrt-pos-f75e5114",
      "label": "depends_on",
      "to": "F:ml430-nat-le-sqrt-e6996680"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-le-sqrt-e6996680.doc.json",
      "id": "F:ml430-nat-le-sqrt-e6996680",
      "label": "ml430-nat-le-sqrt",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.le_sqrt"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-le-sqrt-of-eq-mul-503c5afe.doc.json",
      "id": "F:ml430-nat-le-sqrt-of-eq-mul-503c5afe",
      "label": "ml430-nat-le-sqrt-of-eq-mul",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.le_sqrt_of_eq_mul"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-lt-succ-sqrt-39389df2.doc.json",
      "id": "F:ml430-nat-lt-succ-sqrt-39389df2",
      "label": "ml430-nat-lt-succ-sqrt",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.lt_succ_sqrt"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-sqrt-le-7918582b.doc.json",
      "id": "F:ml430-nat-sqrt-le-7918582b",
      "label": "ml430-nat-sqrt-le",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.sqrt_le"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-sqrt-le-self-1ed5eb85.doc.json",
      "id": "F:ml430-nat-sqrt-le-self-1ed5eb85",
      "label": "ml430-nat-sqrt-le-self",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.sqrt_le_self"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-sqrt-le-sqrt-6e2bfc47.doc.json",
      "id": "F:ml430-nat-sqrt-le-sqrt-6e2bfc47",
      "label": "ml430-nat-sqrt-le-sqrt",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.sqrt_le_sqrt"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-sqrt-pos-f75e5114.doc.json",
      "id": "F:ml430-nat-sqrt-pos-f75e5114",
      "label": "ml430-nat-sqrt-pos",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.sqrt_pos"
    }
  ],
  "rankdir": "TB"
}
```

*Component 3 of 38: 7 facts, 7 edges. An edge runs from the dependent fact to the fact it rests on.*

*Figure (Dependency graph of 6 facts with 5 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-modeq-comm-24b71e7a",
      "label": "depends_on",
      "to": "F:ml430-nat-modeq-symm-0a3d4d18"
    },
    {
      "from": "F:ml430-nat-modeq-dvd-iff-8f130450",
      "label": "depends_on",
      "to": "F:ml430-nat-modeq-of-dvd-d75cc374"
    },
    {
      "from": "F:ml430-nat-modeq-dvd-iff-8f130450",
      "label": "depends_on",
      "to": "F:ml430-nat-modeq-symm-0a3d4d18"
    },
    {
      "from": "F:ml430-nat-modeq-dvd-iff-8f130450",
      "label": "depends_on",
      "to": "F:ml430-nat-modeq-trans-ef9d1c46"
    },
    {
      "from": "F:ml430-nat-modeq-gcd-eq-5167ff4f",
      "label": "depends_on",
      "to": "F:ml430-nat-modeq-dvd-iff-8f130450"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-modeq-comm-24b71e7a.doc.json",
      "id": "F:ml430-nat-modeq-comm-24b71e7a",
      "label": "ml430-nat-modeq-comm",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.ModEq.comm"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-modeq-dvd-iff-8f130450.doc.json",
      "id": "F:ml430-nat-modeq-dvd-iff-8f130450",
      "label": "ml430-nat-modeq-dvd-iff",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.ModEq.dvd_iff"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-modeq-gcd-eq-5167ff4f.doc.json",
      "id": "F:ml430-nat-modeq-gcd-eq-5167ff4f",
      "label": "ml430-nat-modeq-gcd-eq",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.ModEq.gcd_eq"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-modeq-of-dvd-d75cc374.doc.json",
      "id": "F:ml430-nat-modeq-of-dvd-d75cc374",
      "label": "ml430-nat-modeq-of-dvd",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.ModEq.of_dvd"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-modeq-symm-0a3d4d18.doc.json",
      "id": "F:ml430-nat-modeq-symm-0a3d4d18",
      "label": "ml430-nat-modeq-symm",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.ModEq.symm"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-modeq-trans-ef9d1c46.doc.json",
      "id": "F:ml430-nat-modeq-trans-ef9d1c46",
      "label": "ml430-nat-modeq-trans",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.ModEq.trans"
    }
  ],
  "rankdir": "TB"
}
```

*Component 4 of 38: 6 facts, 5 edges. An edge runs from the dependent fact to the fact it rests on.*

*Figure (Dependency graph of 5 facts with 4 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-int-fib-gcd-3a8bfdec",
      "label": "depends_on",
      "to": "F:ml430-int-gcd-fib-73bdafc2"
    },
    {
      "from": "F:ml430-int-gcd-fib-73bdafc2",
      "label": "depends_on",
      "to": "F:ml430-int-fib-neg-b4021d37"
    },
    {
      "from": "F:ml430-int-gcd-fib-73bdafc2",
      "label": "depends_on",
      "to": "F:ml430-nat-fib-gcd-d1d98407"
    },
    {
      "from": "F:ml430-nat-fib-dvd-f80f3de1",
      "label": "depends_on",
      "to": "F:ml430-nat-fib-gcd-d1d98407"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-fib-gcd-3a8bfdec.doc.json",
      "id": "F:ml430-int-fib-gcd-3a8bfdec",
      "label": "ml430-int-fib-gcd",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.fib_gcd"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-fib-neg-b4021d37.doc.json",
      "id": "F:ml430-int-fib-neg-b4021d37",
      "label": "ml430-int-fib-neg",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.fib_neg"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-gcd-fib-73bdafc2.doc.json",
      "id": "F:ml430-int-gcd-fib-73bdafc2",
      "label": "ml430-int-gcd-fib",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.gcd_fib"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-ml430-nat-fib-dvd-f80f3de1.doc.json",
      "id": "F:ml430-nat-fib-dvd-f80f3de1",
      "label": "ml430-nat-fib-dvd",
      "status": "proved",
      "tooltip": "Mathlib v4.30 source proposition Nat.fib_dvd"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-ml430-nat-fib-gcd-d1d98407.doc.json",
      "id": "F:ml430-nat-fib-gcd-d1d98407",
      "label": "ml430-nat-fib-gcd",
      "status": "proved",
      "tooltip": "Mathlib v4.30 source proposition Nat.fib_gcd"
    }
  ],
  "rankdir": "TB"
}
```

*Component 5 of 38: 5 facts, 4 edges. An edge runs from the dependent fact to the fact it rests on.*

*Figure (Dependency graph of 5 facts with 4 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-int-modeq-comm-1e4bcc07",
      "label": "depends_on",
      "to": "F:ml430-int-modeq-symm-984a6e67"
    },
    {
      "from": "F:ml430-int-modeq-dvd-iff-b7ffeff8",
      "label": "depends_on",
      "to": "F:ml430-int-modeq-symm-984a6e67"
    },
    {
      "from": "F:ml430-int-modeq-dvd-iff-b7ffeff8",
      "label": "depends_on",
      "to": "F:ml430-int-modeq-trans-6d7863e0"
    },
    {
      "from": "F:ml430-int-modeq-sub-3148f130",
      "label": "depends_on",
      "to": "F:ml430-int-modeq-symm-984a6e67"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-modeq-comm-1e4bcc07.doc.json",
      "id": "F:ml430-int-modeq-comm-1e4bcc07",
      "label": "ml430-int-modeq-comm",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.modEq_comm"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-modeq-dvd-iff-b7ffeff8.doc.json",
      "id": "F:ml430-int-modeq-dvd-iff-b7ffeff8",
      "label": "ml430-int-modeq-dvd-iff",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.ModEq.dvd_iff"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-modeq-sub-3148f130.doc.json",
      "id": "F:ml430-int-modeq-sub-3148f130",
      "label": "ml430-int-modeq-sub",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.modEq_sub"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-modeq-symm-984a6e67.doc.json",
      "id": "F:ml430-int-modeq-symm-984a6e67",
      "label": "ml430-int-modeq-symm",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.ModEq.symm"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-modeq-trans-6d7863e0.doc.json",
      "id": "F:ml430-int-modeq-trans-6d7863e0",
      "label": "ml430-int-modeq-trans",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.ModEq.trans"
    }
  ],
  "rankdir": "TB"
}
```

*Component 6 of 38: 5 facts, 4 edges. An edge runs from the dependent fact to the fact it rests on.*

*Figure (Dependency graph of 5 facts with 4 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-bitwise-comm-1a273bae",
      "label": "depends_on",
      "to": "F:ml430-nat-bitwise-swap-7175e90e"
    },
    {
      "from": "F:ml430-nat-bitwise-swap-7175e90e",
      "label": "depends_on",
      "to": "F:ml430-nat-bitwise-bit-4c4b28a8"
    },
    {
      "from": "F:ml430-nat-land-comm-7e6ad72e",
      "label": "depends_on",
      "to": "F:ml430-nat-bitwise-comm-1a273bae"
    },
    {
      "from": "F:ml430-nat-lor-comm-2666d7ef",
      "label": "depends_on",
      "to": "F:ml430-nat-bitwise-comm-1a273bae"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-bitwise-bit-4c4b28a8.doc.json",
      "id": "F:ml430-nat-bitwise-bit-4c4b28a8",
      "label": "ml430-nat-bitwise-bit",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.bitwise_bit'"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-bitwise-comm-1a273bae.doc.json",
      "id": "F:ml430-nat-bitwise-comm-1a273bae",
      "label": "ml430-nat-bitwise-comm",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.bitwise_comm"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-bitwise-swap-7175e90e.doc.json",
      "id": "F:ml430-nat-bitwise-swap-7175e90e",
      "label": "ml430-nat-bitwise-swap",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.bitwise_swap"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-land-comm-7e6ad72e.doc.json",
      "id": "F:ml430-nat-land-comm-7e6ad72e",
      "label": "ml430-nat-land-comm",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.land_comm"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-lor-comm-2666d7ef.doc.json",
      "id": "F:ml430-nat-lor-comm-2666d7ef",
      "label": "ml430-nat-lor-comm",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.lor_comm"
    }
  ],
  "rankdir": "TB"
}
```

*Component 7 of 38: 5 facts, 4 edges. An edge runs from the dependent fact to the fact it rests on.*

*Figure (Dependency graph of 5 facts with 4 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-factorial-le-d0f4a912",
      "label": "depends_on",
      "to": "F:ml430-nat-factorial-dvd-factorial-e9d14845"
    },
    {
      "from": "F:ml430-nat-factorial-le-d0f4a912",
      "label": "depends_on",
      "to": "F:ml430-nat-factorial-pos-f1dd2405"
    },
    {
      "from": "F:ml430-nat-factorial-ne-zero-5fc0b0a1",
      "label": "depends_on",
      "to": "F:ml430-nat-factorial-pos-f1dd2405"
    },
    {
      "from": "F:ml430-nat-self-le-factorial-cfdffc69",
      "label": "depends_on",
      "to": "F:ml430-nat-factorial-pos-f1dd2405"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-factorial-dvd-factorial-e9d14845.doc.json",
      "id": "F:ml430-nat-factorial-dvd-factorial-e9d14845",
      "label": "ml430-nat-factorial-dvd-factorial",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.factorial_dvd_factorial"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-factorial-le-d0f4a912.doc.json",
      "id": "F:ml430-nat-factorial-le-d0f4a912",
      "label": "ml430-nat-factorial-le",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.factorial_le"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-factorial-ne-zero-5fc0b0a1.doc.json",
      "id": "F:ml430-nat-factorial-ne-zero-5fc0b0a1",
      "label": "ml430-nat-factorial-ne-zero",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.factorial_ne_zero"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-factorial-pos-f1dd2405.doc.json",
      "id": "F:ml430-nat-factorial-pos-f1dd2405",
      "label": "ml430-nat-factorial-pos",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.factorial_pos"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-self-le-factorial-cfdffc69.doc.json",
      "id": "F:ml430-nat-self-le-factorial-cfdffc69",
      "label": "ml430-nat-self-le-factorial",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.self_le_factorial"
    }
  ],
  "rankdir": "TB"
}
```

*Component 8 of 38: 5 facts, 4 edges. An edge runs from the dependent fact to the fact it rests on.*

*Figure (Dependency graph of 5 facts with 4 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-le-three-of-sqrt-eq-one-0c48a868",
      "label": "depends_on",
      "to": "F:ml430-nat-sqrt-lt-4909537f"
    },
    {
      "from": "F:ml430-nat-sqrt-eq-zero-53666a3b",
      "label": "depends_on",
      "to": "F:ml430-nat-sqrt-lt-4909537f"
    },
    {
      "from": "F:ml430-nat-sqrt-lt-self-ff7a155a",
      "label": "depends_on",
      "to": "F:ml430-nat-sqrt-lt-4909537f"
    },
    {
      "from": "F:ml430-nat-sqrt-succ-le-succ-sqrt-6b041183",
      "label": "depends_on",
      "to": "F:ml430-nat-sqrt-lt-4909537f"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-le-three-of-sqrt-eq-one-0c48a868.doc.json",
      "id": "F:ml430-nat-le-three-of-sqrt-eq-one-0c48a868",
      "label": "ml430-nat-le-three-of-sqrt-eq-one",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.le_three_of_sqrt_eq_one"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-sqrt-eq-zero-53666a3b.doc.json",
      "id": "F:ml430-nat-sqrt-eq-zero-53666a3b",
      "label": "ml430-nat-sqrt-eq-zero",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.sqrt_eq_zero"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-sqrt-lt-4909537f.doc.json",
      "id": "F:ml430-nat-sqrt-lt-4909537f",
      "label": "ml430-nat-sqrt-lt",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.sqrt_lt"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-sqrt-lt-self-ff7a155a.doc.json",
      "id": "F:ml430-nat-sqrt-lt-self-ff7a155a",
      "label": "ml430-nat-sqrt-lt-self",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.sqrt_lt_self"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-sqrt-succ-le-succ-sqrt-6b041183.doc.json",
      "id": "F:ml430-nat-sqrt-succ-le-succ-sqrt-6b041183",
      "label": "ml430-nat-sqrt-succ-le-succ-sqrt",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.sqrt_succ_le_succ_sqrt"
    }
  ],
  "rankdir": "TB"
}
```

*Component 9 of 38: 5 facts, 4 edges. An edge runs from the dependent fact to the fact it rests on.*

*Figure (Dependency graph of 5 facts with 4 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-log-le-clog-ac8ab2d4",
      "label": "depends_on",
      "to": "F:ml430-nat-log-zero-right-8ea186db"
    },
    {
      "from": "F:ml430-nat-log-le-self-da387172",
      "label": "depends_on",
      "to": "F:ml430-nat-log-lt-self-529f89fa"
    },
    {
      "from": "F:ml430-nat-log-le-self-da387172",
      "label": "depends_on",
      "to": "F:ml430-nat-log-zero-right-8ea186db"
    },
    {
      "from": "F:ml430-nat-log2-eq-log-two-28085932",
      "label": "depends_on",
      "to": "F:ml430-nat-log-zero-right-8ea186db"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-log-le-clog-ac8ab2d4.doc.json",
      "id": "F:ml430-nat-log-le-clog-ac8ab2d4",
      "label": "ml430-nat-log-le-clog",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.log_le_clog"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-log-le-self-da387172.doc.json",
      "id": "F:ml430-nat-log-le-self-da387172",
      "label": "ml430-nat-log-le-self",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.log_le_self"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-log-lt-self-529f89fa.doc.json",
      "id": "F:ml430-nat-log-lt-self-529f89fa",
      "label": "ml430-nat-log-lt-self",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.log_lt_self"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-log-zero-right-8ea186db.doc.json",
      "id": "F:ml430-nat-log-zero-right-8ea186db",
      "label": "ml430-nat-log-zero-right",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.log_zero_right"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-log2-eq-log-two-28085932.doc.json",
      "id": "F:ml430-nat-log2-eq-log-two-28085932",
      "label": "ml430-nat-log2-eq-log-two",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.log2_eq_log_two"
    }
  ],
  "rankdir": "TB"
}
```

*Component 10 of 38: 5 facts, 4 edges. An edge runs from the dependent fact to the fact it rests on.*

<details>
<summary>Component 11 (4 facts)</summary>

*Figure (Dependency graph of 4 facts with 3 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-choose-le-add-9c463139",
      "label": "depends_on",
      "to": "F:ml430-nat-choose-le-succ-62ae968b"
    },
    {
      "from": "F:ml430-nat-choose-le-choose-907b5042",
      "label": "depends_on",
      "to": "F:ml430-nat-choose-le-add-9c463139"
    },
    {
      "from": "F:ml430-nat-choose-mono-a1af9c18",
      "label": "depends_on",
      "to": "F:ml430-nat-choose-le-choose-907b5042"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-choose-le-add-9c463139.doc.json",
      "id": "F:ml430-nat-choose-le-add-9c463139",
      "label": "ml430-nat-choose-le-add",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.choose_le_add"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-choose-le-choose-907b5042.doc.json",
      "id": "F:ml430-nat-choose-le-choose-907b5042",
      "label": "ml430-nat-choose-le-choose",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.choose_le_choose"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-choose-le-succ-62ae968b.doc.json",
      "id": "F:ml430-nat-choose-le-succ-62ae968b",
      "label": "ml430-nat-choose-le-succ",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.choose_le_succ"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-choose-mono-a1af9c18.doc.json",
      "id": "F:ml430-nat-choose-mono-a1af9c18",
      "label": "ml430-nat-choose-mono",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.choose_mono"
    }
  ],
  "rankdir": "TB"
}
```

*Component 11 of 38: 4 facts, 3 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 12 (4 facts)</summary>

*Figure (Dependency graph of 4 facts with 3 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-coprime-odd-of-left-ed80ab44",
      "label": "depends_on",
      "to": "F:ml430-nat-coprime-two-left-1b47e7c4"
    },
    {
      "from": "F:ml430-nat-coprime-odd-of-right-8dc1decc",
      "label": "depends_on",
      "to": "F:ml430-nat-coprime-two-right-7c5a1850"
    },
    {
      "from": "F:ml430-nat-coprime-two-right-7c5a1850",
      "label": "depends_on",
      "to": "F:ml430-nat-coprime-two-left-1b47e7c4"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-coprime-odd-of-left-ed80ab44.doc.json",
      "id": "F:ml430-nat-coprime-odd-of-left-ed80ab44",
      "label": "ml430-nat-coprime-odd-of-left",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.Coprime.odd_of_left"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-coprime-odd-of-right-8dc1decc.doc.json",
      "id": "F:ml430-nat-coprime-odd-of-right-8dc1decc",
      "label": "ml430-nat-coprime-odd-of-right",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.Coprime.odd_of_right"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-coprime-two-left-1b47e7c4.doc.json",
      "id": "F:ml430-nat-coprime-two-left-1b47e7c4",
      "label": "ml430-nat-coprime-two-left",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.coprime_two_left"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-coprime-two-right-7c5a1850.doc.json",
      "id": "F:ml430-nat-coprime-two-right-7c5a1850",
      "label": "ml430-nat-coprime-two-right",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.coprime_two_right"
    }
  ],
  "rankdir": "TB"
}
```

*Component 12 of 38: 4 facts, 3 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 13 (3 facts)</summary>

*Figure (Dependency graph of 3 facts with 2 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:bcnf-decomposition-lossless-not-dependency-preserving",
      "label": "depends_on",
      "to": "F:orders-fd-implication-certified"
    },
    {
      "from": "F:orders-candidate-keys-and-normal-forms",
      "label": "depends_on",
      "to": "F:orders-fd-implication-certified"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "search-certificate",
      "href": "cards/F-bcnf-decomposition-lossless-not-dependency-preserving.doc.json",
      "id": "F:bcnf-decomposition-lossless-not-dependency-preserving",
      "label": "bcnf-decomposition-lossless-not-dependency-preserving",
      "status": "proved",
      "tooltip": "The BCNF repair of the street/city/zip schema rejoins exactly and cannot enforce its own dependency; two other splits lose information"
    },
    {
      "group": "search-certificate",
      "href": "cards/F-orders-candidate-keys-and-normal-forms.doc.json",
      "id": "F:orders-candidate-keys-and-normal-forms",
      "label": "orders-candidate-keys-and-normal-forms",
      "status": "proved",
      "tooltip": "An order-line schema has exactly two candidate keys, is not in BCNF, and is not in 3NF -- with every subset of the attributes examined"
    },
    {
      "group": "search-certificate",
      "href": "cards/F-orders-fd-implication-certified.doc.json",
      "id": "F:orders-fd-implication-certified",
      "label": "orders-fd-implication-certified",
      "status": "proved",
      "tooltip": "Two implied and two unimplied functional dependencies on a committed order-line schema, each with a replayable certificate"
    }
  ],
  "rankdir": "TB"
}
```

*Component 13 of 38: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 14 (3 facts)</summary>

*Figure (Dependency graph of 3 facts with 2 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:modus-tollens-valid",
      "label": "depends_on",
      "to": "F:contraposition"
    },
    {
      "from": "F:modus-tollens-valid",
      "label": "depends_on",
      "to": "F:modus-ponens-valid"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "smt-term-level",
      "href": "cards/F-contraposition.doc.json",
      "id": "F:contraposition",
      "label": "contraposition",
      "status": "proved",
      "tooltip": "A conditional is equivalent to its contrapositive"
    },
    {
      "group": "smt-term-level",
      "href": "cards/F-modus-ponens-valid.doc.json",
      "id": "F:modus-ponens-valid",
      "label": "modus-ponens-valid",
      "status": "proved",
      "tooltip": "Modus ponens is a valid inference"
    },
    {
      "group": "smt-term-level",
      "href": "cards/F-modus-tollens-valid.doc.json",
      "id": "F:modus-tollens-valid",
      "label": "modus-tollens-valid",
      "status": "proved",
      "tooltip": "Modus tollens is a valid inference"
    }
  ],
  "rankdir": "TB"
}
```

*Component 14 of 38: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 15 (3 facts)</summary>

*Figure (Dependency graph of 3 facts with 2 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:double-negation-elimination",
      "label": "depends_on",
      "to": "F:excluded-middle"
    },
    {
      "from": "F:excluded-middle-not-intuitionistic",
      "label": "depends_on",
      "to": "F:excluded-middle"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "smt-term-level",
      "href": "cards/F-double-negation-elimination.doc.json",
      "id": "F:double-negation-elimination",
      "label": "double-negation-elimination",
      "status": "proved",
      "tooltip": "Double negation elimination"
    },
    {
      "group": "smt-term-level",
      "href": "cards/F-excluded-middle.doc.json",
      "id": "F:excluded-middle",
      "label": "excluded-middle",
      "status": "proved",
      "tooltip": "Law of excluded middle"
    },
    {
      "group": "unproved",
      "href": "cards/F-excluded-middle-not-intuitionistic.doc.json",
      "id": "F:excluded-middle-not-intuitionistic",
      "label": "excluded-middle-not-intuitionistic",
      "status": "open",
      "tooltip": "Excluded middle is not derivable in intuitionistic propositional logic"
    }
  ],
  "rankdir": "TB"
}
```

*Component 15 of 38: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 16 (3 facts)</summary>

*Figure (Dependency graph of 3 facts with 3 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:int-sub-nat-nat-elim",
      "label": "depends_on",
      "to": "F:int-sub-nat-nat-shift"
    },
    {
      "from": "F:int-sub-nat-nat-elim",
      "label": "depends_on",
      "to": "F:nat-add-zero"
    },
    {
      "from": "F:int-sub-nat-nat-shift",
      "label": "depends_on",
      "to": "F:nat-add-zero"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "kernel-lean",
      "href": "cards/F-int-sub-nat-nat-elim.doc.json",
      "id": "F:int-sub-nat-nat-elim",
      "label": "int-sub-nat-nat-elim",
      "status": "proved",
      "tooltip": "The integer borrow has exactly two outcomes, and each is witnessed by a natural"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-int-sub-nat-nat-shift.doc.json",
      "id": "F:int-sub-nat-nat-shift",
      "label": "int-sub-nat-nat-shift",
      "status": "proved",
      "tooltip": "The normalized integer difference is invariant under a common shift"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-nat-add-zero.doc.json",
      "id": "F:nat-add-zero",
      "label": "nat-add-zero",
      "status": "proved",
      "tooltip": "Zero is a right identity for addition on the naturals"
    }
  ],
  "rankdir": "TB"
}
```

*Component 16 of 38: 3 facts, 3 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 17 (3 facts)</summary>

*Figure (Dependency graph of 3 facts with 2 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b",
      "label": "depends_on",
      "to": "F:ml430-int-gcd-eq-gcd-ab-63005aef"
    },
    {
      "from": "F:ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0",
      "label": "depends_on",
      "to": "F:ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b.doc.json",
      "id": "F:ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b",
      "label": "ml430-int-dvd-of-dvd-mul-left-of-gcd-one",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.dvd_of_dvd_mul_left_of_gcd_one"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0.doc.json",
      "id": "F:ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0",
      "label": "ml430-int-dvd-of-dvd-mul-right-of-gcd-one",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.dvd_of_dvd_mul_right_of_gcd_one"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-gcd-eq-gcd-ab-63005aef.doc.json",
      "id": "F:ml430-int-gcd-eq-gcd-ab-63005aef",
      "label": "ml430-int-gcd-eq-gcd-ab",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.gcd_eq_gcd_ab"
    }
  ],
  "rankdir": "TB"
}
```

*Component 17 of 38: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 18 (3 facts)</summary>

*Figure (Dependency graph of 3 facts with 2 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-int-fib-two-mul-0e70f3dd",
      "label": "depends_on",
      "to": "F:ml430-int-fib-add-181b6a2c"
    },
    {
      "from": "F:ml430-int-fib-two-mul-add-two-0ba4a948",
      "label": "depends_on",
      "to": "F:ml430-int-fib-two-mul-0e70f3dd"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-fib-add-181b6a2c.doc.json",
      "id": "F:ml430-int-fib-add-181b6a2c",
      "label": "ml430-int-fib-add",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.fib_add"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-fib-two-mul-0e70f3dd.doc.json",
      "id": "F:ml430-int-fib-two-mul-0e70f3dd",
      "label": "ml430-int-fib-two-mul",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.fib_two_mul"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-fib-two-mul-add-two-0ba4a948.doc.json",
      "id": "F:ml430-int-fib-two-mul-add-two-0ba4a948",
      "label": "ml430-int-fib-two-mul-add-two",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.fib_two_mul_add_two"
    }
  ],
  "rankdir": "TB"
}
```

*Component 18 of 38: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 19 (3 facts)</summary>

*Figure (Dependency graph of 3 facts with 2 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-coprime-of-dvd-18fcd09f",
      "label": "depends_on",
      "to": "F:ml430-nat-coprime-of-dvd-left-b0e2aa94"
    },
    {
      "from": "F:ml430-nat-coprime-of-dvd-18fcd09f",
      "label": "depends_on",
      "to": "F:ml430-nat-coprime-of-dvd-right-a640bd56"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-coprime-of-dvd-18fcd09f.doc.json",
      "id": "F:ml430-nat-coprime-of-dvd-18fcd09f",
      "label": "ml430-nat-coprime-of-dvd",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.Coprime.of_dvd"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-coprime-of-dvd-left-b0e2aa94.doc.json",
      "id": "F:ml430-nat-coprime-of-dvd-left-b0e2aa94",
      "label": "ml430-nat-coprime-of-dvd-left",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.Coprime.of_dvd_left"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-coprime-of-dvd-right-a640bd56.doc.json",
      "id": "F:ml430-nat-coprime-of-dvd-right-a640bd56",
      "label": "ml430-nat-coprime-of-dvd-right",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.Coprime.of_dvd_right"
    }
  ],
  "rankdir": "TB"
}
```

*Component 19 of 38: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 20 (3 facts)</summary>

*Figure (Dependency graph of 3 facts with 2 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-coprime-of-lt-prime-1978a919",
      "label": "depends_on",
      "to": "F:ml430-nat-coprime-or-dvd-of-prime-65f47114"
    },
    {
      "from": "F:ml430-nat-coprime-or-dvd-of-prime-65f47114",
      "label": "depends_on",
      "to": "F:ml430-nat-prime-dvd-iff-not-coprime-77854741"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-coprime-of-lt-prime-1978a919.doc.json",
      "id": "F:ml430-nat-coprime-of-lt-prime-1978a919",
      "label": "ml430-nat-coprime-of-lt-prime",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.coprime_of_lt_prime"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-coprime-or-dvd-of-prime-65f47114.doc.json",
      "id": "F:ml430-nat-coprime-or-dvd-of-prime-65f47114",
      "label": "ml430-nat-coprime-or-dvd-of-prime",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.coprime_or_dvd_of_prime"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-prime-dvd-iff-not-coprime-77854741.doc.json",
      "id": "F:ml430-nat-prime-dvd-iff-not-coprime-77854741",
      "label": "ml430-nat-prime-dvd-iff-not-coprime",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.Prime.dvd_iff_not_coprime"
    }
  ],
  "rankdir": "TB"
}
```

*Component 20 of 38: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 21 (3 facts)</summary>

*Figure (Dependency graph of 3 facts with 2 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-fib-lt-fib-3582b881",
      "label": "depends_on",
      "to": "F:ml430-nat-fib-strictmonoon-905810a9"
    },
    {
      "from": "F:ml430-nat-fib-strictmonoon-905810a9",
      "label": "depends_on",
      "to": "F:ml430-nat-fib-add-two-strictmono-c1e86d4d"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-fib-add-two-strictmono-c1e86d4d.doc.json",
      "id": "F:ml430-nat-fib-add-two-strictmono-c1e86d4d",
      "label": "ml430-nat-fib-add-two-strictmono",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.fib_add_two_strictMono"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-fib-lt-fib-3582b881.doc.json",
      "id": "F:ml430-nat-fib-lt-fib-3582b881",
      "label": "ml430-nat-fib-lt-fib",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.fib_lt_fib"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-fib-strictmonoon-905810a9.doc.json",
      "id": "F:ml430-nat-fib-strictmonoon-905810a9",
      "label": "ml430-nat-fib-strictmonoon",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.fib_strictMonoOn"
    }
  ],
  "rankdir": "TB"
}
```

*Component 21 of 38: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 22 (3 facts)</summary>

*Figure (Dependency graph of 3 facts with 2 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-multichoose-one-b210386a",
      "label": "depends_on",
      "to": "F:ml430-nat-multichoose-zero-right-6ef827c8"
    },
    {
      "from": "F:ml430-nat-multichoose-one-right-7755072d",
      "label": "depends_on",
      "to": "F:ml430-nat-multichoose-zero-right-6ef827c8"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-multichoose-one-b210386a.doc.json",
      "id": "F:ml430-nat-multichoose-one-b210386a",
      "label": "ml430-nat-multichoose-one",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.multichoose_one"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-multichoose-one-right-7755072d.doc.json",
      "id": "F:ml430-nat-multichoose-one-right-7755072d",
      "label": "ml430-nat-multichoose-one-right",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.multichoose_one_right"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-multichoose-zero-right-6ef827c8.doc.json",
      "id": "F:ml430-nat-multichoose-zero-right-6ef827c8",
      "label": "ml430-nat-multichoose-zero-right",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.multichoose_zero_right"
    }
  ],
  "rankdir": "TB"
}
```

*Component 22 of 38: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 23 (3 facts)</summary>

*Figure (Dependency graph of 3 facts with 2 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:real-inverse-is-built-and-well-defined",
      "label": "depends_on",
      "to": "F:real-inverse-is-partial-and-its-modulus-is-data"
    },
    {
      "from": "F:real-inverse-is-partial-and-its-modulus-is-data",
      "label": "depends_on",
      "to": "F:rationals-are-a-field-axiom-free"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "kernel-lean",
      "href": "cards/F-rationals-are-a-field-axiom-free.doc.json",
      "id": "F:rationals-are-a-field-axiom-free",
      "label": "rationals-are-a-field-axiom-free",
      "status": "proved",
      "tooltip": "ℚ is a field: Rat.inv is proved to invert, at zero trusted declarations"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-real-inverse-is-built-and-well-defined.doc.json",
      "id": "F:real-inverse-is-built-and-well-defined",
      "label": "real-inverse-is-built-and-well-defined",
      "status": "proved",
      "tooltip": "The constructed reals have a multiplicative inverse whose modulus is an explicit natural, and it is a function on the reals rather than on representatives"
    },
    {
      "group": "kernel-lean",
      "href": "cards/F-real-inverse-is-partial-and-its-modulus-is-data.doc.json",
      "id": "F:real-inverse-is-partial-and-its-modulus-is-data",
      "label": "real-inverse-is-partial-and-its-modulus-is-data",
      "status": "proved",
      "tooltip": "No function on all of the constructed reals is a multiplicative inverse, and the modulus that would make one possible cannot be extracted from positivity"
    }
  ],
  "rankdir": "TB"
}
```

*Component 23 of 38: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 24 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:chu-vandermonde-convolution",
      "label": "depends_on",
      "to": "F:chu-vandermonde-convolution-recurrence"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "cas-certificate",
      "href": "cards/F-chu-vandermonde-convolution.doc.json",
      "id": "F:chu-vandermonde-convolution",
      "label": "chu-vandermonde-convolution",
      "status": "proved",
      "tooltip": "Chu-Vandermonde convolution, closed form at symbolic parameters"
    },
    {
      "group": "cas-certificate",
      "href": "cards/F-chu-vandermonde-convolution-recurrence.doc.json",
      "id": "F:chu-vandermonde-convolution-recurrence",
      "label": "chu-vandermonde-convolution-recurrence",
      "status": "proved",
      "tooltip": "The Chu-Vandermonde convolution satisfies a first-order recurrence in p"
    }
  ],
  "rankdir": "TB"
}
```

*Component 24 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 25 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-int-modeq-of-mul-right-c92b7bf0",
      "label": "depends_on",
      "to": "F:ml430-int-modeq-of-mul-left-c4ccd51e"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-modeq-of-mul-left-c4ccd51e.doc.json",
      "id": "F:ml430-int-modeq-of-mul-left-c4ccd51e",
      "label": "ml430-int-modeq-of-mul-left",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.ModEq.of_mul_left"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-int-modeq-of-mul-right-c92b7bf0.doc.json",
      "id": "F:ml430-int-modeq-of-mul-right-c92b7bf0",
      "label": "ml430-int-modeq-of-mul-right",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Int.ModEq.of_mul_right"
    }
  ],
  "rankdir": "TB"
}
```

*Component 25 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 26 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-choose-succ-self-e396f6c2",
      "label": "depends_on",
      "to": "F:ml430-nat-choose-eq-zero-of-lt-92ebab29"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-choose-eq-zero-of-lt-92ebab29.doc.json",
      "id": "F:ml430-nat-choose-eq-zero-of-lt-92ebab29",
      "label": "ml430-nat-choose-eq-zero-of-lt",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.choose_eq_zero_of_lt"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-choose-succ-self-e396f6c2.doc.json",
      "id": "F:ml430-nat-choose-succ-self-e396f6c2",
      "label": "ml430-nat-choose-succ-self",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.choose_succ_self"
    }
  ],
  "rankdir": "TB"
}
```

*Component 26 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 27 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-choose-one-right-7eda8e39",
      "label": "depends_on",
      "to": "F:ml430-nat-choose-zero-right-1ed2802a"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-choose-one-right-7eda8e39.doc.json",
      "id": "F:ml430-nat-choose-one-right-7eda8e39",
      "label": "ml430-nat-choose-one-right",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.choose_one_right"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-choose-zero-right-1ed2802a.doc.json",
      "id": "F:ml430-nat-choose-zero-right-1ed2802a",
      "label": "ml430-nat-choose-zero-right",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.choose_zero_right"
    }
  ],
  "rankdir": "TB"
}
```

*Component 27 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 28 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-choose-symm-add-e4b68161",
      "label": "depends_on",
      "to": "F:ml430-nat-choose-symm-of-eq-add-9b5f9a20"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-choose-symm-add-e4b68161.doc.json",
      "id": "F:ml430-nat-choose-symm-add-e4b68161",
      "label": "ml430-nat-choose-symm-add",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.choose_symm_add"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-choose-symm-of-eq-add-9b5f9a20.doc.json",
      "id": "F:ml430-nat-choose-symm-of-eq-add-9b5f9a20",
      "label": "ml430-nat-choose-symm-of-eq-add",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.choose_symm_of_eq_add"
    }
  ],
  "rankdir": "TB"
}
```

*Component 28 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 29 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-clog-monotone-48fe50c6",
      "label": "depends_on",
      "to": "F:ml430-nat-clog-mono-right-8d87a410"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-clog-mono-right-8d87a410.doc.json",
      "id": "F:ml430-nat-clog-mono-right-8d87a410",
      "label": "ml430-nat-clog-mono-right",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.clog_mono_right"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-clog-monotone-48fe50c6.doc.json",
      "id": "F:ml430-nat-clog-monotone-48fe50c6",
      "label": "ml430-nat-clog-monotone",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.clog_monotone"
    }
  ],
  "rankdir": "TB"
}
```

*Component 29 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 30 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-coprime-self-add-right-966e5434",
      "label": "depends_on",
      "to": "F:ml430-nat-coprime-add-self-right-c3ed0f45"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-coprime-add-self-right-c3ed0f45.doc.json",
      "id": "F:ml430-nat-coprime-add-self-right-c3ed0f45",
      "label": "ml430-nat-coprime-add-self-right",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.coprime_add_self_right"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-coprime-self-add-right-966e5434.doc.json",
      "id": "F:ml430-nat-coprime-self-add-right-966e5434",
      "label": "ml430-nat-coprime-self-add-right",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.coprime_self_add_right"
    }
  ],
  "rankdir": "TB"
}
```

*Component 30 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 31 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439",
      "label": "depends_on",
      "to": "F:ml430-nat-coprime-primes-5769049f"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-coprime-primes-5769049f.doc.json",
      "id": "F:ml430-nat-coprime-primes-5769049f",
      "label": "ml430-nat-coprime-primes",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.coprime_primes"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439.doc.json",
      "id": "F:ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439",
      "label": "ml430-nat-prime-dvd-mul-of-dvd-ne",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.Prime.dvd_mul_of_dvd_ne"
    }
  ],
  "rankdir": "TB"
}
```

*Component 31 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 32 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-exists-mul-self-e73ca9fa",
      "label": "depends_on",
      "to": "F:ml430-nat-sqrt-eq-79ae8eae"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-exists-mul-self-e73ca9fa.doc.json",
      "id": "F:ml430-nat-exists-mul-self-e73ca9fa",
      "label": "ml430-nat-exists-mul-self",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.exists_mul_self"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-sqrt-eq-79ae8eae.doc.json",
      "id": "F:ml430-nat-sqrt-eq-79ae8eae",
      "label": "ml430-nat-sqrt-eq",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.sqrt_eq"
    }
  ],
  "rankdir": "TB"
}
```

*Component 32 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 33 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-land-assoc-ad4775b8",
      "label": "depends_on",
      "to": "F:ml430-nat-land-bit-b9ab7475"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-land-assoc-ad4775b8.doc.json",
      "id": "F:ml430-nat-land-assoc-ad4775b8",
      "label": "ml430-nat-land-assoc",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.land_assoc"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-land-bit-b9ab7475.doc.json",
      "id": "F:ml430-nat-land-bit-b9ab7475",
      "label": "ml430-nat-land-bit",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.land_bit"
    }
  ],
  "rankdir": "TB"
}
```

*Component 33 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 34 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-le-fib-add-one-5284f0bf",
      "label": "depends_on",
      "to": "F:ml430-nat-le-fib-self-0cbccb4d"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-le-fib-add-one-5284f0bf.doc.json",
      "id": "F:ml430-nat-le-fib-add-one-5284f0bf",
      "label": "ml430-nat-le-fib-add-one",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.le_fib_add_one"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-le-fib-self-0cbccb4d.doc.json",
      "id": "F:ml430-nat-le-fib-self-0cbccb4d",
      "label": "ml430-nat-le-fib-self",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.le_fib_self"
    }
  ],
  "rankdir": "TB"
}
```

*Component 34 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 35 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-log-mono-right-b8939fee",
      "label": "depends_on",
      "to": "F:ml430-nat-log-monotone-52fad774"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-log-mono-right-b8939fee.doc.json",
      "id": "F:ml430-nat-log-mono-right-b8939fee",
      "label": "ml430-nat-log-mono-right",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.log_mono_right"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-log-monotone-52fad774.doc.json",
      "id": "F:ml430-nat-log-monotone-52fad774",
      "label": "ml430-nat-log-monotone",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.log_monotone"
    }
  ],
  "rankdir": "TB"
}
```

*Component 35 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 36 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-lor-assoc-82c4d0fd",
      "label": "depends_on",
      "to": "F:ml430-nat-lor-bit-a2f98c7c"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-lor-assoc-82c4d0fd.doc.json",
      "id": "F:ml430-nat-lor-assoc-82c4d0fd",
      "label": "ml430-nat-lor-assoc",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.lor_assoc"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-lor-bit-a2f98c7c.doc.json",
      "id": "F:ml430-nat-lor-bit-a2f98c7c",
      "label": "ml430-nat-lor-bit",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.lor_bit"
    }
  ],
  "rankdir": "TB"
}
```

*Component 36 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 37 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:ml430-nat-modeq-of-mul-right-43078e1c",
      "label": "depends_on",
      "to": "F:ml430-nat-modeq-of-mul-left-88d20bca"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-modeq-of-mul-left-88d20bca.doc.json",
      "id": "F:ml430-nat-modeq-of-mul-left-88d20bca",
      "label": "ml430-nat-modeq-of-mul-left",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.ModEq.of_mul_left"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-modeq-of-mul-right-43078e1c.doc.json",
      "id": "F:ml430-nat-modeq-of-mul-right-43078e1c",
      "label": "ml430-nat-modeq-of-mul-right",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.ModEq.of_mul_right"
    }
  ],
  "rankdir": "TB"
}
```

*Component 37 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 38 (2 facts)</summary>

*Figure (Dependency graph of 2 facts with 1 edges) -- data:*

```json
{
  "edges": [
    {
      "from": "F:schedule-deadline-iis",
      "label": "depends_on",
      "to": "F:schedule-critical-chain-infeasible"
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
    {
      "group": "kernel-lean",
      "href": "cards/F-schedule-critical-chain-infeasible.doc.json",
      "id": "F:schedule-critical-chain-infeasible",
      "label": "schedule-critical-chain-infeasible",
      "status": "proved",
      "tooltip": "A five-constraint critical chain against a delivery deadline, refuted in the Lean kernel"
    },
    {
      "group": "search-certificate",
      "href": "cards/F-schedule-deadline-iis.doc.json",
      "id": "F:schedule-deadline-iis",
      "label": "schedule-deadline-iis",
      "status": "proved",
      "tooltip": "Five rows of a 60-row project schedule are an irreducible infeasible subsystem"
    }
  ],
  "rankdir": "TB"
}
```

*Component 38 of 38: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

Ledger spread over the documented facts

| axis | value | facts |
| --- | --- | --- |
| epistemic_status | computed | 2 |
| epistemic_status | conjectured | 3 |
| epistemic_status | open | 212 |
| epistemic_status | proved | 121 |
| epistemic_status | refuted | 3 |
| external_status | (absent) | 8 |
| external_status | open | 5 |
| external_status | proved | 308 |
| external_status | refuted | 3 |
| external_status | unknown | 17 |
| proof_route | (none) | 215 |
| proof_route | cas-certificate | 19 |
| proof_route | imported-kernel-lean | 5 |
| proof_route | kernel-lean | 64 |
| proof_route | search-certificate | 12 |
| proof_route | smt-clausal | 9 |
| proof_route | smt-term-level | 17 |
| formal.language | cas-term | 9 |
| formal.language | lean4 | 62 |
| formal.language | lean4-surface | 214 |
| formal.language | smtlib2 | 56 |

Source: `python3 render/producers-py/facts_to_docir.py` (exit 0), 341 input(s) hashed.

Fact index

| fact | title | language | fragment | proof_route | epistemic | external | badge | flag | evidence | checked | card |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| F:affirming-the-consequent | Affirming the consequent is a valid inference | smtlib2 | QF_UF | search-certificate | refuted | refuted | refuted | - | 1 | 1 | [`F-affirming-the-consequent`](cards/F-affirming-the-consequent.html) |
| F:alternating-binomial-row-sum-zero | The alternating binomial row sum vanishes | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-alternating-binomial-row-sum-zero`](cards/F-alternating-binomial-row-sum-zero.html) |
| F:apery-numbers-recurrence | The Apery numbers satisfy Apery's second-order recurrence | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-apery-numbers-recurrence`](cards/F-apery-numbers-recurrence.html) |
| F:barber-no-such-barber | No barber shaves exactly those who do not shave themselves | smtlib2 | UF | smt-clausal | proved | proved | proved | - | 1 | 1 | [`F-barber-no-such-barber`](cards/F-barber-no-such-barber.html) |
| F:bcnf-decomposition-lossless-not-dependency-preserving | The BCNF repair of the street/city/zip schema rejoins exactly and cannot enforce its own dependency; two other splits lose information | smtlib2 | QF_UF | search-certificate | proved | unclassified | proved | - | 3 | 3 | [`F-bcnf-decomposition-lossless-not-dependency-preserving`](cards/F-bcnf-decomposition-lossless-not-dependency-preserving.html) |
| F:binomial-row-sum-two-power | The binomial row sum is a power of two | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-binomial-row-sum-two-power`](cards/F-binomial-row-sum-two-power.html) |
| F:bool-and-comm | Boolean conjunction is commutative | lean4 | Bool | imported-kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-bool-and-comm`](cards/F-bool-and-comm.html) |
| F:chu-vandermonde-convolution | Chu-Vandermonde convolution, closed form at symbolic parameters | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-chu-vandermonde-convolution`](cards/F-chu-vandermonde-convolution.html) |
| F:chu-vandermonde-convolution-recurrence | The Chu-Vandermonde convolution satisfies a first-order recurrence in p | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-chu-vandermonde-convolution-recurrence`](cards/F-chu-vandermonde-convolution-recurrence.html) |
| F:collatz-reaches-one | Collatz conjecture | lean4 | none | - | conjectured | open | open | - | 0 | 0 | [`F-collatz-reaches-one`](cards/F-collatz-reaches-one.html) |
| F:complex-admits-no-compatible-order | No relation on the constructed complex numbers satisfies seven of the Real package's ordered-ring laws | lean4 | Complex | kernel-lean | proved | proved | proved | - | 3 | 3 | [`F-complex-admits-no-compatible-order`](cards/F-complex-admits-no-compatible-order.html) |
| F:complex-ring-constructed-axiom-free | The complex numbers are constructible in this kernel at zero trusted declarations, as a pair setoid over the constructed reals | lean4 | Complex | kernel-lean | proved | proved | proved | - | 4 | 4 | [`F-complex-ring-constructed-axiom-free`](cards/F-complex-ring-constructed-axiom-free.html) |
| F:conjunctive-query-containment-homomorphism-certified | Six conjunctive-query containment questions decided by homomorphism and by counterexample database, agreeing across three independent routes | smtlib2 | none | search-certificate | proved | unclassified | proved | - | 3 | 3 | [`F-conjunctive-query-containment-homomorphism-certified`](cards/F-conjunctive-query-containment-homomorphism-certified.html) |
| F:continuum-hypothesis-independent | The continuum hypothesis is independent of ZFC | smtlib2 | none | - | open | proved | open | import-backlog | 0 | 0 | [`F-continuum-hypothesis-independent`](cards/F-continuum-hypothesis-independent.html) |
| F:contraposition | A conditional is equivalent to its contrapositive | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-contraposition`](cards/F-contraposition.html) |
| F:cross-binomial-row-sum | The cross binomial row sum equals a central binomial coefficient | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-cross-binomial-row-sum`](cards/F-cross-binomial-row-sum.html) |
| F:de-morgan-laws | De Morgan's laws for conjunction and disjunction | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-de-morgan-laws`](cards/F-de-morgan-laws.html) |
| F:double-negation-elimination | Double negation elimination | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-double-negation-elimination`](cards/F-double-negation-elimination.html) |
| F:ex-falso-quodlibet | A contradiction entails everything | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-ex-falso-quodlibet`](cards/F-ex-falso-quodlibet.html) |
| F:excluded-middle | Law of excluded middle | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-excluded-middle`](cards/F-excluded-middle.html) |
| F:excluded-middle-not-intuitionistic | Excluded middle is not derivable in intuitionistic propositional logic | smtlib2 | none | - | open | proved | open | import-backlog | 0 | 0 | [`F-excluded-middle-not-intuitionistic`](cards/F-excluded-middle-not-intuitionistic.html) |
| F:exportation | Exportation: the propositional form of the deduction theorem | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-exportation`](cards/F-exportation.html) |
| F:farkas-refutation-over-constructed-reals | A Farkas refutation closes over the constructed reals resting on zero carrier axioms, where the same refutation over the axiomatized AxReal package rests on 30 | lean4 | QF_LRA | kernel-lean | proved | proved | proved | - | 4 | 4 | [`F-farkas-refutation-over-constructed-reals`](cards/F-farkas-refutation-over-constructed-reals.html) |
| F:fermat-last-theorem | Fermat's Last Theorem | smtlib2 | none | - | open | proved | open | import-backlog | 0 | 0 | [`F-fermat-last-theorem`](cards/F-fermat-last-theorem.html) |
| F:fol-validity-undecidable | Validity in first-order logic is undecidable | smtlib2 | none | - | open | proved | open | import-backlog | 0 | 0 | [`F-fol-validity-undecidable`](cards/F-fol-validity-undecidable.html) |
| F:fp16-add-monotone-rne | binary16 addition under roundNearestTiesToEven is monotone in its first argument | smtlib2 | QF_FP | - | open | proved | open | import-backlog | 0 | 0 | [`F-fp16-add-monotone-rne`](cards/F-fp16-add-monotone-rne.html) |
| F:fp16-bf16-roundtrip-not-identity | Narrowing binary16 to bfloat16 and back is the identity | smtlib2 | QF_FP | search-certificate | refuted | refuted | refuted | - | 3 | 3 | [`F-fp16-bf16-roundtrip-not-identity`](cards/F-fp16-bf16-roundtrip-not-identity.html) |
| F:fp16-doubling-add-equals-mul-two | In binary16 under roundNearestTiesToEven, x+x and 2*x are the same value | smtlib2 | QF_FP | smt-clausal | proved | proved | proved | - | 2 | 2 | [`F-fp16-doubling-add-equals-mul-two`](cards/F-fp16-doubling-add-equals-mul-two.html) |
| F:fp16-fp32-roundtrip-identity | Widening binary16 to binary32 and narrowing back is the identity | smtlib2 | QF_FP | smt-clausal | proved | proved | proved | - | 2 | 2 | [`F-fp16-fp32-roundtrip-identity`](cards/F-fp16-fp32-roundtrip-identity.html) |
| F:fp32-doubling-add-equals-mul-two | In binary32 under roundNearestTiesToEven, x+x and 2*x are the same value | smtlib2 | QF_FP | smt-clausal | proved | proved | proved | - | 2 | 2 | [`F-fp32-doubling-add-equals-mul-two`](cards/F-fp32-doubling-add-equals-mul-two.html) |
| F:fp8-add-monotone-rne | fp8 E5M2 addition under roundNearestTiesToEven is monotone in its first argument | smtlib2 | QF_FP | smt-clausal | proved | proved | proved | - | 2 | 2 | [`F-fp8-add-monotone-rne`](cards/F-fp8-add-monotone-rne.html) |
| F:fp8-add-not-associative | fp8 E5M2 addition under roundNearestTiesToEven is associative | smtlib2 | QF_FP | search-certificate | refuted | refuted | refuted | - | 3 | 3 | [`F-fp8-add-not-associative`](cards/F-fp8-add-not-associative.html) |
| F:franel-numbers-recurrence | The Franel numbers satisfy a second-order recurrence | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-franel-numbers-recurrence`](cards/F-franel-numbers-recurrence.html) |
| F:geometry-centroid-divides-medians | the medians of a non-degenerate triangle meet at (A+B+C)/3 | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-geometry-centroid-divides-medians`](cards/F-geometry-centroid-divides-medians.html) |
| F:geometry-euler-line | Euler's line: the circumcentre, the centroid and the orthocentre of a non-degenerate triangle are collinear | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 3 | 3 | [`F-geometry-euler-line`](cards/F-geometry-euler-line.html) |
| F:geometry-medians-concurrent | the medians of a triangle are concurrent | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-geometry-medians-concurrent`](cards/F-geometry-medians-concurrent.html) |
| F:geometry-orthocentre-altitudes-concurrent | the altitudes of a triangle are concurrent | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-geometry-orthocentre-altitudes-concurrent`](cards/F-geometry-orthocentre-altitudes-concurrent.html) |
| F:geometry-pappus-hexagon | Pappus's hexagon theorem: the three cross intersections are collinear, and ONE non-degeneracy condition suffices | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 3 | 3 | [`F-geometry-pappus-hexagon`](cards/F-geometry-pappus-hexagon.html) |
| F:geometry-parallelogram-diagonals-bisect | the diagonals of a non-flat parallelogram bisect each other | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-geometry-parallelogram-diagonals-bisect`](cards/F-geometry-parallelogram-diagonals-bisect.html) |
| F:geometry-rhombus-diagonals-perpendicular | the diagonals of a non-flat rhombus are perpendicular | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-geometry-rhombus-diagonals-perpendicular`](cards/F-geometry-rhombus-diagonals-perpendicular.html) |
| F:geometry-simson-line | Simson's line: the feet of the perpendiculars from a concyclic point are collinear, and the minimal condition set depends on the FIELD rather than on the budget | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 3 | 3 | [`F-geometry-simson-line`](cards/F-geometry-simson-line.html) |
| F:geometry-thales-right-angle-in-semicircle | Thales' theorem: an angle inscribed in a semicircle is right | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-geometry-thales-right-angle-in-semicircle`](cards/F-geometry-thales-right-angle-in-semicircle.html) |
| F:geometry-varignon-midpoint-parallelogram | Varignon's theorem: the midpoint quadrilateral is a parallelogram | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-geometry-varignon-midpoint-parallelogram`](cards/F-geometry-varignon-midpoint-parallelogram.html) |
| F:godel-first-incompleteness | Godel's first incompleteness theorem | smtlib2 | none | - | open | proved | open | import-backlog | 0 | 0 | [`F-godel-first-incompleteness`](cards/F-godel-first-incompleteness.html) |
| F:goldbach-strong | Strong Goldbach conjecture | lean4 | Nat | - | conjectured | open | open | - | 0 | 0 | [`F-goldbach-strong`](cards/F-goldbach-strong.html) |
| F:int-add-assoc | Addition on the integers is associative | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-int-add-assoc`](cards/F-int-add-assoc.html) |
| F:int-add-comm | Addition on the integers is commutative | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-int-add-comm`](cards/F-int-add-comm.html) |
| F:int-add-le-add | The order on the integers is compatible with addition | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-int-add-le-add`](cards/F-int-add-le-add.html) |
| F:int-add-lt-add-of-le-of-lt | A strict integer inequality survives addition of a non-strict one | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-int-add-lt-add-of-le-of-lt`](cards/F-int-add-lt-add-of-le-of-lt.html) |
| F:int-add-neg | Every integer has an additive inverse | lean4 | Int | kernel-lean | proved | proved | proved | - | 3 | 3 | [`F-int-add-neg`](cards/F-int-add-neg.html) |
| F:int-categoricity | The constructed Int is THE integers: every generated aperiodic Z-structure is in structure-preserving bijection with it | lean4 | Int | kernel-lean | proved | proved | proved | - | 5 | 5 | [`F-int-categoricity`](cards/F-int-categoricity.html) |
| F:int-characterization | The constructed Int is a discretely ordered ring generated by 1, with unique maps out | lean4 | Int | kernel-lean | proved | proved | proved | - | 5 | 5 | [`F-int-characterization`](cards/F-int-characterization.html) |
| F:int-equality-is-decidable | Equality of integers is decidable | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-int-equality-is-decidable`](cards/F-int-equality-is-decidable.html) |
| F:int-euclidean-decomposition | Euclidean decomposition over the integers is derived, not assumed | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-int-euclidean-decomposition`](cards/F-int-euclidean-decomposition.html) |
| F:int-left-distrib | Multiplication distributes over addition on the integers | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-int-left-distrib`](cards/F-int-left-distrib.html) |
| F:int-mul-assoc | Multiplication on the integers is associative | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-int-mul-assoc`](cards/F-int-mul-assoc.html) |
| F:int-mul-comm | Multiplication on the integers is commutative | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-int-mul-comm`](cards/F-int-mul-comm.html) |
| F:int-no-integer-strictly-between-zero-and-one | No integer lies strictly between zero and one | lean4 | Int | kernel-lean | proved | proved | proved | - | 3 | 3 | [`F-int-no-integer-strictly-between-zero-and-one`](cards/F-int-no-integer-strictly-between-zero-and-one.html) |
| F:int-sq-nonneg | Every integer square is nonnegative | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-int-sq-nonneg`](cards/F-int-sq-nonneg.html) |
| F:int-sub-nat-nat-elim | The integer borrow has exactly two outcomes, and each is witnessed by a natural | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-int-sub-nat-nat-elim`](cards/F-int-sub-nat-nat-elim.html) |
| F:int-sub-nat-nat-shift | The normalized integer difference is invariant under a common shift | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-int-sub-nat-nat-shift`](cards/F-int-sub-nat-nat-shift.html) |
| F:lean-kernel-accepts-the-whole-constructed-real-carrier | Official Lean's own kernel accepts every declaration of the constructed-real carrier | lean4 | lean4-kernel-declaration-stream | kernel-lean | proved | unknown | proved | - | 3 | 3 | [`F-lean-kernel-accepts-the-whole-constructed-real-carrier`](cards/F-lean-kernel-accepts-the-whole-constructed-real-carrier.html) |
| F:list-nil-append | The empty list is a left identity for append | lean4 | List | imported-kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-list-nil-append`](cards/F-list-nil-append.html) |
| F:loadplan-hazmat-iis | Fourteen rows of a 90-row outbound load plan are an irreducible infeasible subsystem | smtlib2 | LIA | search-certificate | proved | unclassified | proved | - | 2 | 2 | [`F-loadplan-hazmat-iis`](cards/F-loadplan-hazmat-iis.html) |
| F:ml430-int-add-modeq-left-ee732b5b | Mathlib v4.30 source proposition Int.add_modEq_left | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-add-modeq-left-ee732b5b`](cards/F-ml430-int-add-modeq-left-ee732b5b.html) |
| F:ml430-int-add-modeq-right-e58108ee | Mathlib v4.30 source proposition Int.add_modEq_right | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-add-modeq-right-e58108ee`](cards/F-ml430-int-add-modeq-right-e58108ee.html) |
| F:ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b | Mathlib v4.30 source proposition Int.dvd_of_dvd_mul_left_of_gcd_one | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b`](cards/F-ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b.html) |
| F:ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0 | Mathlib v4.30 source proposition Int.dvd_of_dvd_mul_right_of_gcd_one | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0`](cards/F-ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0.html) |
| F:ml430-int-fib-add-181b6a2c | Mathlib v4.30 source proposition Int.fib_add | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-fib-add-181b6a2c`](cards/F-ml430-int-fib-add-181b6a2c.html) |
| F:ml430-int-fib-add-one-33f1b748 | Mathlib v4.30 source proposition Int.fib_add_one | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-fib-add-one-33f1b748`](cards/F-ml430-int-fib-add-one-33f1b748.html) |
| F:ml430-int-fib-add-two-739358dd | Mathlib v4.30 source proposition Int.fib_add_two | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-fib-add-two-739358dd`](cards/F-ml430-int-fib-add-two-739358dd.html) |
| F:ml430-int-fib-dvd-ffb3c5c1 | Mathlib v4.30 source proposition Int.fib_dvd | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-fib-dvd-ffb3c5c1`](cards/F-ml430-int-fib-dvd-ffb3c5c1.html) |
| F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d | Mathlib v4.30 source proposition Int.fib_eq_fib_add_two_sub_fib_add_one | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d`](cards/F-ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d.html) |
| F:ml430-int-fib-eq-zero-8193c7cb | Mathlib v4.30 source proposition Int.fib_eq_zero | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-fib-eq-zero-8193c7cb`](cards/F-ml430-int-fib-eq-zero-8193c7cb.html) |
| F:ml430-int-fib-gcd-3a8bfdec | Mathlib v4.30 source proposition Int.fib_gcd | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-fib-gcd-3a8bfdec`](cards/F-ml430-int-fib-gcd-3a8bfdec.html) |
| F:ml430-int-fib-natcast-d5886be4 | Mathlib v4.30 source proposition Int.fib_natCast | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-fib-natcast-d5886be4`](cards/F-ml430-int-fib-natcast-d5886be4.html) |
| F:ml430-int-fib-neg-b4021d37 | Mathlib v4.30 source proposition Int.fib_neg | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-fib-neg-b4021d37`](cards/F-ml430-int-fib-neg-b4021d37.html) |
| F:ml430-int-fib-of-nonneg-438018c5 | Mathlib v4.30 source proposition Int.fib_of_nonneg | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-fib-of-nonneg-438018c5`](cards/F-ml430-int-fib-of-nonneg-438018c5.html) |
| F:ml430-int-fib-of-odd-66560495 | Mathlib v4.30 source proposition Int.fib_of_odd | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-fib-of-odd-66560495`](cards/F-ml430-int-fib-of-odd-66560495.html) |
| F:ml430-int-fib-two-mul-0e70f3dd | Mathlib v4.30 source proposition Int.fib_two_mul | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-fib-two-mul-0e70f3dd`](cards/F-ml430-int-fib-two-mul-0e70f3dd.html) |
| F:ml430-int-fib-two-mul-add-one-pos-8977f65f | Mathlib v4.30 source proposition Int.fib_two_mul_add_one_pos | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-fib-two-mul-add-one-pos-8977f65f`](cards/F-ml430-int-fib-two-mul-add-one-pos-8977f65f.html) |
| F:ml430-int-fib-two-mul-add-two-0ba4a948 | Mathlib v4.30 source proposition Int.fib_two_mul_add_two | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-fib-two-mul-add-two-0ba4a948`](cards/F-ml430-int-fib-two-mul-add-two-0ba4a948.html) |
| F:ml430-int-gcd-div-5e01872f | Mathlib v4.30 source proposition Int.gcd_div | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-gcd-div-5e01872f`](cards/F-ml430-int-gcd-div-5e01872f.html) |
| F:ml430-int-gcd-div-gcd-div-gcd-2db608dc | Mathlib v4.30 source proposition Int.gcd_div_gcd_div_gcd | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-gcd-div-gcd-div-gcd-2db608dc`](cards/F-ml430-int-gcd-div-gcd-div-gcd-2db608dc.html) |
| F:ml430-int-gcd-eq-gcd-ab-63005aef | Mathlib v4.30 source proposition Int.gcd_eq_gcd_ab | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-gcd-eq-gcd-ab-63005aef`](cards/F-ml430-int-gcd-eq-gcd-ab-63005aef.html) |
| F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-left-8533eb82 | Mathlib v4.30 source proposition Int.gcd_eq_one_of_gcd_mul_right_eq_one_left | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-left-8533eb82`](cards/F-ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-left-8533eb82.html) |
| F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-right-a9b19222 | Mathlib v4.30 source proposition Int.gcd_eq_one_of_gcd_mul_right_eq_one_right | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-right-a9b19222`](cards/F-ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-right-a9b19222.html) |
| F:ml430-int-gcd-fib-73bdafc2 | Mathlib v4.30 source proposition Int.gcd_fib | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-gcd-fib-73bdafc2`](cards/F-ml430-int-gcd-fib-73bdafc2.html) |
| F:ml430-int-gcd-greatest-5b31c5fe | Mathlib v4.30 source proposition Int.gcd_greatest | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-gcd-greatest-5b31c5fe`](cards/F-ml430-int-gcd-greatest-5b31c5fe.html) |
| F:ml430-int-mod-modeq-6bec7847 | Mathlib v4.30 source proposition Int.mod_modEq | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-mod-modeq-6bec7847`](cards/F-ml430-int-mod-modeq-6bec7847.html) |
| F:ml430-int-modeq-add-left-6e17c69a | Mathlib v4.30 source proposition Int.ModEq.add_left | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modeq-add-left-6e17c69a`](cards/F-ml430-int-modeq-add-left-6e17c69a.html) |
| F:ml430-int-modeq-add-left-cancel-062ad5fe | Mathlib v4.30 source proposition Int.ModEq.add_left_cancel' | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modeq-add-left-cancel-062ad5fe`](cards/F-ml430-int-modeq-add-left-cancel-062ad5fe.html) |
| F:ml430-int-modeq-comm-1e4bcc07 | Mathlib v4.30 source proposition Int.modEq_comm | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modeq-comm-1e4bcc07`](cards/F-ml430-int-modeq-comm-1e4bcc07.html) |
| F:ml430-int-modeq-dvd-iff-b7ffeff8 | Mathlib v4.30 source proposition Int.ModEq.dvd_iff | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modeq-dvd-iff-b7ffeff8`](cards/F-ml430-int-modeq-dvd-iff-b7ffeff8.html) |
| F:ml430-int-modeq-neg-d6ff57b6 | Mathlib v4.30 source proposition Int.modEq_neg | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modeq-neg-d6ff57b6`](cards/F-ml430-int-modeq-neg-d6ff57b6.html) |
| F:ml430-int-modeq-neg-f649f6c5 | Mathlib v4.30 source proposition Int.ModEq.neg | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modeq-neg-f649f6c5`](cards/F-ml430-int-modeq-neg-f649f6c5.html) |
| F:ml430-int-modeq-of-dvd-b9c41fce | Mathlib v4.30 source proposition Int.ModEq.of_dvd | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modeq-of-dvd-b9c41fce`](cards/F-ml430-int-modeq-of-dvd-b9c41fce.html) |
| F:ml430-int-modeq-of-mul-left-c4ccd51e | Mathlib v4.30 source proposition Int.ModEq.of_mul_left | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modeq-of-mul-left-c4ccd51e`](cards/F-ml430-int-modeq-of-mul-left-c4ccd51e.html) |
| F:ml430-int-modeq-of-mul-right-c92b7bf0 | Mathlib v4.30 source proposition Int.ModEq.of_mul_right | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modeq-of-mul-right-c92b7bf0`](cards/F-ml430-int-modeq-of-mul-right-c92b7bf0.html) |
| F:ml430-int-modeq-one-01d9de39 | Mathlib v4.30 source proposition Int.modEq_one | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modeq-one-01d9de39`](cards/F-ml430-int-modeq-one-01d9de39.html) |
| F:ml430-int-modeq-refl-30e15520 | Mathlib v4.30 source proposition Int.ModEq.refl | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modeq-refl-30e15520`](cards/F-ml430-int-modeq-refl-30e15520.html) |
| F:ml430-int-modeq-sub-3148f130 | Mathlib v4.30 source proposition Int.modEq_sub | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modeq-sub-3148f130`](cards/F-ml430-int-modeq-sub-3148f130.html) |
| F:ml430-int-modeq-symm-984a6e67 | Mathlib v4.30 source proposition Int.ModEq.symm | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modeq-symm-984a6e67`](cards/F-ml430-int-modeq-symm-984a6e67.html) |
| F:ml430-int-modeq-trans-6d7863e0 | Mathlib v4.30 source proposition Int.ModEq.trans | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modeq-trans-6d7863e0`](cards/F-ml430-int-modeq-trans-6d7863e0.html) |
| F:ml430-int-modulus-modeq-zero-5b57a898 | Mathlib v4.30 source proposition Int.modulus_modEq_zero | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-modulus-modeq-zero-5b57a898`](cards/F-ml430-int-modulus-modeq-zero-5b57a898.html) |
| F:ml430-int-ne-zero-of-gcd-f71f00df | Mathlib v4.30 source proposition Int.ne_zero_of_gcd | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-ne-zero-of-gcd-f71f00df`](cards/F-ml430-int-ne-zero-of-gcd-f71f00df.html) |
| F:ml430-int-neg-modeq-neg-30d98479 | Mathlib v4.30 source proposition Int.neg_modEq_neg | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-int-neg-modeq-neg-30d98479`](cards/F-ml430-int-neg-modeq-neg-30d98479.html) |
| F:ml430-mutation-1432b2277cf2cc26c1d11cd6 | Outcome-blind mutation of Nat.fib_eq_zero | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | [`F-ml430-mutation-1432b2277cf2cc26c1d11cd6`](cards/F-ml430-mutation-1432b2277cf2cc26c1d11cd6.html) |
| F:ml430-mutation-2086302b3a338591b3179871 | Outcome-blind mutation of Nat.sqrt_le_self | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | [`F-ml430-mutation-2086302b3a338591b3179871`](cards/F-ml430-mutation-2086302b3a338591b3179871.html) |
| F:ml430-mutation-48fe130e2b8eadb6f626b66f | Outcome-blind mutation of Int.ne_zero_of_gcd | lean4-surface | Int | - | open | unknown | open | - | 0 | 0 | [`F-ml430-mutation-48fe130e2b8eadb6f626b66f`](cards/F-ml430-mutation-48fe130e2b8eadb6f626b66f.html) |
| F:ml430-mutation-5179f333b8333ecff8adc223 | Outcome-blind mutation of Nat.Prime.pred_pos | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | [`F-ml430-mutation-5179f333b8333ecff8adc223`](cards/F-ml430-mutation-5179f333b8333ecff8adc223.html) |
| F:ml430-mutation-7afa5ec620720a1501bf349d | Outcome-blind mutation of Nat.factorial_ne_zero | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | [`F-ml430-mutation-7afa5ec620720a1501bf349d`](cards/F-ml430-mutation-7afa5ec620720a1501bf349d.html) |
| F:ml430-mutation-a6dd1759bce60d820292e107 | Outcome-blind mutation of Nat.lor_comm | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | [`F-ml430-mutation-a6dd1759bce60d820292e107`](cards/F-ml430-mutation-a6dd1759bce60d820292e107.html) |
| F:ml430-mutation-aabb80b1f89f0c5847364692 | Outcome-blind mutation of Int.fib_eq_zero | lean4-surface | Int | - | open | unknown | open | - | 0 | 0 | [`F-ml430-mutation-aabb80b1f89f0c5847364692`](cards/F-ml430-mutation-aabb80b1f89f0c5847364692.html) |
| F:ml430-mutation-aca37b68d3cdf06f0127def9 | Outcome-blind mutation of Int.ModEq.symm | lean4-surface | Int | - | open | unknown | open | - | 0 | 0 | [`F-ml430-mutation-aca37b68d3cdf06f0127def9`](cards/F-ml430-mutation-aca37b68d3cdf06f0127def9.html) |
| F:ml430-mutation-c20db9b4c60b816ce738bdf2 | Outcome-blind mutation of Nat.not_coprime_zero_zero | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | [`F-ml430-mutation-c20db9b4c60b816ce738bdf2`](cards/F-ml430-mutation-c20db9b4c60b816ce738bdf2.html) |
| F:ml430-mutation-c86940b52af8159ca9b381d6 | Outcome-blind mutation of Nat.ModEq.symm | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | [`F-ml430-mutation-c86940b52af8159ca9b381d6`](cards/F-ml430-mutation-c86940b52af8159ca9b381d6.html) |
| F:ml430-mutation-e8583599cfae2d40cefae3f0 | Outcome-blind mutation of Nat.log_le_self | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | [`F-ml430-mutation-e8583599cfae2d40cefae3f0`](cards/F-ml430-mutation-e8583599cfae2d40cefae3f0.html) |
| F:ml430-mutation-edb05acf07d9ef3f9f8232fc | Outcome-blind mutation of Nat.choose_self | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | [`F-ml430-mutation-edb05acf07d9ef3f9f8232fc`](cards/F-ml430-mutation-edb05acf07d9ef3f9f8232fc.html) |
| F:ml430-nat-add-modeq-left-e3b1fba9 | Mathlib v4.30 source proposition Nat.add_modEq_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-add-modeq-left-e3b1fba9`](cards/F-ml430-nat-add-modeq-left-e3b1fba9.html) |
| F:ml430-nat-add-modeq-right-e2f11f21 | Mathlib v4.30 source proposition Nat.add_modEq_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-add-modeq-right-e2f11f21`](cards/F-ml430-nat-add-modeq-right-e2f11f21.html) |
| F:ml430-nat-ascfactorial-zero-fd183202 | Mathlib v4.30 source proposition Nat.ascFactorial_zero | lean4-surface | Nat | kernel-lean | proved | proved | proved | - | 1 | 1 | [`F-ml430-nat-ascfactorial-zero-fd183202`](cards/F-ml430-nat-ascfactorial-zero-fd183202.html) |
| F:ml430-nat-bitwise-bit-4c4b28a8 | Mathlib v4.30 source proposition Nat.bitwise_bit' | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-bitwise-bit-4c4b28a8`](cards/F-ml430-nat-bitwise-bit-4c4b28a8.html) |
| F:ml430-nat-bitwise-comm-1a273bae | Mathlib v4.30 source proposition Nat.bitwise_comm | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-bitwise-comm-1a273bae`](cards/F-ml430-nat-bitwise-comm-1a273bae.html) |
| F:ml430-nat-bitwise-swap-7175e90e | Mathlib v4.30 source proposition Nat.bitwise_swap | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-bitwise-swap-7175e90e`](cards/F-ml430-nat-bitwise-swap-7175e90e.html) |
| F:ml430-nat-choose-eq-zero-of-lt-92ebab29 | Mathlib v4.30 source proposition Nat.choose_eq_zero_of_lt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-choose-eq-zero-of-lt-92ebab29`](cards/F-ml430-nat-choose-eq-zero-of-lt-92ebab29.html) |
| F:ml430-nat-choose-le-add-9c463139 | Mathlib v4.30 source proposition Nat.choose_le_add | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-choose-le-add-9c463139`](cards/F-ml430-nat-choose-le-add-9c463139.html) |
| F:ml430-nat-choose-le-choose-907b5042 | Mathlib v4.30 source proposition Nat.choose_le_choose | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-choose-le-choose-907b5042`](cards/F-ml430-nat-choose-le-choose-907b5042.html) |
| F:ml430-nat-choose-le-succ-62ae968b | Mathlib v4.30 source proposition Nat.choose_le_succ | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-choose-le-succ-62ae968b`](cards/F-ml430-nat-choose-le-succ-62ae968b.html) |
| F:ml430-nat-choose-mono-a1af9c18 | Mathlib v4.30 source proposition Nat.choose_mono | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-choose-mono-a1af9c18`](cards/F-ml430-nat-choose-mono-a1af9c18.html) |
| F:ml430-nat-choose-ne-zero-49c3d3cb | Mathlib v4.30 source proposition Nat.choose_ne_zero | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-choose-ne-zero-49c3d3cb`](cards/F-ml430-nat-choose-ne-zero-49c3d3cb.html) |
| F:ml430-nat-choose-one-right-7eda8e39 | Mathlib v4.30 source proposition Nat.choose_one_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-choose-one-right-7eda8e39`](cards/F-ml430-nat-choose-one-right-7eda8e39.html) |
| F:ml430-nat-choose-self-25bb9fb8 | Mathlib v4.30 source proposition Nat.choose_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-choose-self-25bb9fb8`](cards/F-ml430-nat-choose-self-25bb9fb8.html) |
| F:ml430-nat-choose-succ-self-e396f6c2 | Mathlib v4.30 source proposition Nat.choose_succ_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-choose-succ-self-e396f6c2`](cards/F-ml430-nat-choose-succ-self-e396f6c2.html) |
| F:ml430-nat-choose-succ-succ-671856b6 | Mathlib v4.30 source proposition Nat.choose_succ_succ | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-choose-succ-succ-671856b6`](cards/F-ml430-nat-choose-succ-succ-671856b6.html) |
| F:ml430-nat-choose-symm-add-e4b68161 | Mathlib v4.30 source proposition Nat.choose_symm_add | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-choose-symm-add-e4b68161`](cards/F-ml430-nat-choose-symm-add-e4b68161.html) |
| F:ml430-nat-choose-symm-of-eq-add-9b5f9a20 | Mathlib v4.30 source proposition Nat.choose_symm_of_eq_add | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-choose-symm-of-eq-add-9b5f9a20`](cards/F-ml430-nat-choose-symm-of-eq-add-9b5f9a20.html) |
| F:ml430-nat-choose-zero-right-1ed2802a | Mathlib v4.30 source proposition Nat.choose_zero_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-choose-zero-right-1ed2802a`](cards/F-ml430-nat-choose-zero-right-1ed2802a.html) |
| F:ml430-nat-choose-zero-succ-62c6520b | Mathlib v4.30 source proposition Nat.choose_zero_succ | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-choose-zero-succ-62c6520b`](cards/F-ml430-nat-choose-zero-succ-62c6520b.html) |
| F:ml430-nat-clog-antitone-left-44a87771 | Mathlib v4.30 source proposition Nat.clog_antitone_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-clog-antitone-left-44a87771`](cards/F-ml430-nat-clog-antitone-left-44a87771.html) |
| F:ml430-nat-clog-mono-right-8d87a410 | Mathlib v4.30 source proposition Nat.clog_mono_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-clog-mono-right-8d87a410`](cards/F-ml430-nat-clog-mono-right-8d87a410.html) |
| F:ml430-nat-clog-monotone-48fe50c6 | Mathlib v4.30 source proposition Nat.clog_monotone | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-clog-monotone-48fe50c6`](cards/F-ml430-nat-clog-monotone-48fe50c6.html) |
| F:ml430-nat-clog-one-left-b496af12 | Mathlib v4.30 source proposition Nat.clog_one_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-clog-one-left-b496af12`](cards/F-ml430-nat-clog-one-left-b496af12.html) |
| F:ml430-nat-clog-one-right-1ce3d52f | Mathlib v4.30 source proposition Nat.clog_one_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-clog-one-right-1ce3d52f`](cards/F-ml430-nat-clog-one-right-1ce3d52f.html) |
| F:ml430-nat-clog-pos-00852cb8 | Mathlib v4.30 source proposition Nat.clog_pos | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-clog-pos-00852cb8`](cards/F-ml430-nat-clog-pos-00852cb8.html) |
| F:ml430-nat-clog-zero-left-1c61a5bf | Mathlib v4.30 source proposition Nat.clog_zero_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-clog-zero-left-1c61a5bf`](cards/F-ml430-nat-clog-zero-left-1c61a5bf.html) |
| F:ml430-nat-clog-zero-right-d42d47b1 | Mathlib v4.30 source proposition Nat.clog_zero_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-clog-zero-right-d42d47b1`](cards/F-ml430-nat-clog-zero-right-d42d47b1.html) |
| F:ml430-nat-coprime-add-self-left-5e93448c | Mathlib v4.30 source proposition Nat.coprime_add_self_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-add-self-left-5e93448c`](cards/F-ml430-nat-coprime-add-self-left-5e93448c.html) |
| F:ml430-nat-coprime-add-self-right-c3ed0f45 | Mathlib v4.30 source proposition Nat.coprime_add_self_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-add-self-right-c3ed0f45`](cards/F-ml430-nat-coprime-add-self-right-c3ed0f45.html) |
| F:ml430-nat-coprime-iff-isrelprime-0c08eb25 | Mathlib v4.30 source proposition Nat.coprime_iff_isRelPrime | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-iff-isrelprime-0c08eb25`](cards/F-ml430-nat-coprime-iff-isrelprime-0c08eb25.html) |
| F:ml430-nat-coprime-odd-of-left-ed80ab44 | Mathlib v4.30 source proposition Nat.Coprime.odd_of_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-odd-of-left-ed80ab44`](cards/F-ml430-nat-coprime-odd-of-left-ed80ab44.html) |
| F:ml430-nat-coprime-odd-of-right-8dc1decc | Mathlib v4.30 source proposition Nat.Coprime.odd_of_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-odd-of-right-8dc1decc`](cards/F-ml430-nat-coprime-odd-of-right-8dc1decc.html) |
| F:ml430-nat-coprime-of-dvd-18fcd09f | Mathlib v4.30 source proposition Nat.Coprime.of_dvd | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-of-dvd-18fcd09f`](cards/F-ml430-nat-coprime-of-dvd-18fcd09f.html) |
| F:ml430-nat-coprime-of-dvd-6f652673 | Mathlib v4.30 source proposition Nat.coprime_of_dvd' | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-of-dvd-6f652673`](cards/F-ml430-nat-coprime-of-dvd-6f652673.html) |
| F:ml430-nat-coprime-of-dvd-left-b0e2aa94 | Mathlib v4.30 source proposition Nat.Coprime.of_dvd_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-of-dvd-left-b0e2aa94`](cards/F-ml430-nat-coprime-of-dvd-left-b0e2aa94.html) |
| F:ml430-nat-coprime-of-dvd-right-a640bd56 | Mathlib v4.30 source proposition Nat.Coprime.of_dvd_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-of-dvd-right-a640bd56`](cards/F-ml430-nat-coprime-of-dvd-right-a640bd56.html) |
| F:ml430-nat-coprime-of-lt-minfac-0f79bdba | Mathlib v4.30 source proposition Nat.coprime_of_lt_minFac | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-of-lt-minfac-0f79bdba`](cards/F-ml430-nat-coprime-of-lt-minfac-0f79bdba.html) |
| F:ml430-nat-coprime-of-lt-prime-1978a919 | Mathlib v4.30 source proposition Nat.coprime_of_lt_prime | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-of-lt-prime-1978a919`](cards/F-ml430-nat-coprime-of-lt-prime-1978a919.html) |
| F:ml430-nat-coprime-one-left-iff-45945e80 | Mathlib v4.30 source proposition Nat.coprime_one_left_iff | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-one-left-iff-45945e80`](cards/F-ml430-nat-coprime-one-left-iff-45945e80.html) |
| F:ml430-nat-coprime-one-right-iff-42fed4ce | Mathlib v4.30 source proposition Nat.coprime_one_right_iff | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-one-right-iff-42fed4ce`](cards/F-ml430-nat-coprime-one-right-iff-42fed4ce.html) |
| F:ml430-nat-coprime-or-dvd-of-prime-65f47114 | Mathlib v4.30 source proposition Nat.coprime_or_dvd_of_prime | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-or-dvd-of-prime-65f47114`](cards/F-ml430-nat-coprime-or-dvd-of-prime-65f47114.html) |
| F:ml430-nat-coprime-primes-5769049f | Mathlib v4.30 source proposition Nat.coprime_primes | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-primes-5769049f`](cards/F-ml430-nat-coprime-primes-5769049f.html) |
| F:ml430-nat-coprime-self-add-left-51351fa1 | Mathlib v4.30 source proposition Nat.coprime_self_add_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-self-add-left-51351fa1`](cards/F-ml430-nat-coprime-self-add-left-51351fa1.html) |
| F:ml430-nat-coprime-self-add-right-966e5434 | Mathlib v4.30 source proposition Nat.coprime_self_add_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-self-add-right-966e5434`](cards/F-ml430-nat-coprime-self-add-right-966e5434.html) |
| F:ml430-nat-coprime-symmetric-9b5cfa12 | Mathlib v4.30 source proposition Nat.Coprime.symmetric | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-symmetric-9b5cfa12`](cards/F-ml430-nat-coprime-symmetric-9b5cfa12.html) |
| F:ml430-nat-coprime-two-left-1b47e7c4 | Mathlib v4.30 source proposition Nat.coprime_two_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-two-left-1b47e7c4`](cards/F-ml430-nat-coprime-two-left-1b47e7c4.html) |
| F:ml430-nat-coprime-two-right-7c5a1850 | Mathlib v4.30 source proposition Nat.coprime_two_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-coprime-two-right-7c5a1850`](cards/F-ml430-nat-coprime-two-right-7c5a1850.html) |
| F:ml430-nat-descfactorial-le-2b8cc09a | Mathlib v4.30 source proposition Nat.descFactorial_le | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-descfactorial-le-2b8cc09a`](cards/F-ml430-nat-descfactorial-le-2b8cc09a.html) |
| F:ml430-nat-descfactorial-of-lt-fbcf5d26 | Mathlib v4.30 source proposition Nat.descFactorial_of_lt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-descfactorial-of-lt-fbcf5d26`](cards/F-ml430-nat-descfactorial-of-lt-fbcf5d26.html) |
| F:ml430-nat-descfactorial-one-d4856d4a | Mathlib v4.30 source proposition Nat.descFactorial_one | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-descfactorial-one-d4856d4a`](cards/F-ml430-nat-descfactorial-one-d4856d4a.html) |
| F:ml430-nat-descfactorial-self-899fc0e0 | Mathlib v4.30 source proposition Nat.descFactorial_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-descfactorial-self-899fc0e0`](cards/F-ml430-nat-descfactorial-self-899fc0e0.html) |
| F:ml430-nat-descfactorial-zero-966b01df | Mathlib v4.30 source proposition Nat.descFactorial_zero | lean4-surface | Nat | kernel-lean | proved | proved | proved | - | 1 | 1 | [`F-ml430-nat-descfactorial-zero-966b01df`](cards/F-ml430-nat-descfactorial-zero-966b01df.html) |
| F:ml430-nat-div-dvd-div-left-b56f6f7c | Mathlib v4.30 source proposition Nat.div_dvd_div_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-div-dvd-div-left-b56f6f7c`](cards/F-ml430-nat-div-dvd-div-left-b56f6f7c.html) |
| F:ml430-nat-dvd-lcm-of-dvd-left-141a64bb | Mathlib v4.30 source proposition Nat.dvd_lcm_of_dvd_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-dvd-lcm-of-dvd-left-141a64bb`](cards/F-ml430-nat-dvd-lcm-of-dvd-left-141a64bb.html) |
| F:ml430-nat-dvd-lcm-of-dvd-right-61a50fc3 | Mathlib v4.30 source proposition Nat.dvd_lcm_of_dvd_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-dvd-lcm-of-dvd-right-61a50fc3`](cards/F-ml430-nat-dvd-lcm-of-dvd-right-61a50fc3.html) |
| F:ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b | Mathlib v4.30 source proposition Nat.dvd_of_forall_prime_mul_dvd | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b`](cards/F-ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b.html) |
| F:ml430-nat-dvd-of-lcm-left-dvd-d6b2407c | Mathlib v4.30 source proposition Nat.dvd_of_lcm_left_dvd | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-dvd-of-lcm-left-dvd-d6b2407c`](cards/F-ml430-nat-dvd-of-lcm-left-dvd-d6b2407c.html) |
| F:ml430-nat-dvd-of-lcm-right-dvd-61bd1a60 | Mathlib v4.30 source proposition Nat.dvd_of_lcm_right_dvd | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-dvd-of-lcm-right-dvd-61bd1a60`](cards/F-ml430-nat-dvd-of-lcm-right-dvd-61bd1a60.html) |
| F:ml430-nat-even-xor-78a39432 | Mathlib v4.30 source proposition Nat.even_xor | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-even-xor-78a39432`](cards/F-ml430-nat-even-xor-78a39432.html) |
| F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e | Mathlib v4.30 source proposition Nat.exists_mul_mod_eq_gcd | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e`](cards/F-ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e.html) |
| F:ml430-nat-exists-mul-self-e73ca9fa | Mathlib v4.30 source proposition Nat.exists_mul_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-exists-mul-self-e73ca9fa`](cards/F-ml430-nat-exists-mul-self-e73ca9fa.html) |
| F:ml430-nat-factorial-dvd-ascfactorial-44a4e641 | Mathlib v4.30 source proposition Nat.factorial_dvd_ascFactorial | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-factorial-dvd-ascfactorial-44a4e641`](cards/F-ml430-nat-factorial-dvd-ascfactorial-44a4e641.html) |
| F:ml430-nat-factorial-dvd-descfactorial-bbf6124f | Mathlib v4.30 source proposition Nat.factorial_dvd_descFactorial | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-factorial-dvd-descfactorial-bbf6124f`](cards/F-ml430-nat-factorial-dvd-descfactorial-bbf6124f.html) |
| F:ml430-nat-factorial-dvd-factorial-e9d14845 | Mathlib v4.30 source proposition Nat.factorial_dvd_factorial | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-factorial-dvd-factorial-e9d14845`](cards/F-ml430-nat-factorial-dvd-factorial-e9d14845.html) |
| F:ml430-nat-factorial-le-d0f4a912 | Mathlib v4.30 source proposition Nat.factorial_le | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-factorial-le-d0f4a912`](cards/F-ml430-nat-factorial-le-d0f4a912.html) |
| F:ml430-nat-factorial-lt-of-lt-d6c2125d | Mathlib v4.30 source proposition Nat.factorial_lt_of_lt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-factorial-lt-of-lt-d6c2125d`](cards/F-ml430-nat-factorial-lt-of-lt-d6c2125d.html) |
| F:ml430-nat-factorial-ne-zero-5fc0b0a1 | Mathlib v4.30 source proposition Nat.factorial_ne_zero | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-factorial-ne-zero-5fc0b0a1`](cards/F-ml430-nat-factorial-ne-zero-5fc0b0a1.html) |
| F:ml430-nat-factorial-pos-f1dd2405 | Mathlib v4.30 source proposition Nat.factorial_pos | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-factorial-pos-f1dd2405`](cards/F-ml430-nat-factorial-pos-f1dd2405.html) |
| F:ml430-nat-fastfib-eq-cde11774 | Mathlib v4.30 source proposition Nat.fastFib_eq | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-fastfib-eq-cde11774`](cards/F-ml430-nat-fastfib-eq-cde11774.html) |
| F:ml430-nat-fib-add-two-b86e0c82 | Mathlib v4.30 source proposition Nat.fib_add_two | lean4-surface | Nat | kernel-lean | proved | proved | proved | - | 1 | 1 | [`F-ml430-nat-fib-add-two-b86e0c82`](cards/F-ml430-nat-fib-add-two-b86e0c82.html) |
| F:ml430-nat-fib-add-two-strictmono-c1e86d4d | Mathlib v4.30 source proposition Nat.fib_add_two_strictMono | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-fib-add-two-strictmono-c1e86d4d`](cards/F-ml430-nat-fib-add-two-strictmono-c1e86d4d.html) |
| F:ml430-nat-fib-coprime-fib-succ-162fc738 | Mathlib v4.30 source proposition Nat.fib_coprime_fib_succ | lean4-surface | Nat | kernel-lean | proved | proved | proved | - | 1 | 1 | [`F-ml430-nat-fib-coprime-fib-succ-162fc738`](cards/F-ml430-nat-fib-coprime-fib-succ-162fc738.html) |
| F:ml430-nat-fib-dvd-f80f3de1 | Mathlib v4.30 source proposition Nat.fib_dvd | lean4-surface | Nat | kernel-lean | proved | proved | proved | - | 1 | 1 | [`F-ml430-nat-fib-dvd-f80f3de1`](cards/F-ml430-nat-fib-dvd-f80f3de1.html) |
| F:ml430-nat-fib-eq-zero-61879073 | Mathlib v4.30 source proposition Nat.fib_eq_zero | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-fib-eq-zero-61879073`](cards/F-ml430-nat-fib-eq-zero-61879073.html) |
| F:ml430-nat-fib-gcd-d1d98407 | Mathlib v4.30 source proposition Nat.fib_gcd | lean4-surface | Nat | kernel-lean | proved | proved | proved | - | 1 | 1 | [`F-ml430-nat-fib-gcd-d1d98407`](cards/F-ml430-nat-fib-gcd-d1d98407.html) |
| F:ml430-nat-fib-le-fib-succ-d1ef4a3d | Mathlib v4.30 source proposition Nat.fib_le_fib_succ | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-fib-le-fib-succ-d1ef4a3d`](cards/F-ml430-nat-fib-le-fib-succ-d1ef4a3d.html) |
| F:ml430-nat-fib-lt-fib-3582b881 | Mathlib v4.30 source proposition Nat.fib_lt_fib | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-fib-lt-fib-3582b881`](cards/F-ml430-nat-fib-lt-fib-3582b881.html) |
| F:ml430-nat-fib-mono-cc6afe09 | Mathlib v4.30 source proposition Nat.fib_mono | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-fib-mono-cc6afe09`](cards/F-ml430-nat-fib-mono-cc6afe09.html) |
| F:ml430-nat-fib-pos-9e67bd8e | Mathlib v4.30 source proposition Nat.fib_pos | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-fib-pos-9e67bd8e`](cards/F-ml430-nat-fib-pos-9e67bd8e.html) |
| F:ml430-nat-fib-strictmonoon-905810a9 | Mathlib v4.30 source proposition Nat.fib_strictMonoOn | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-fib-strictmonoon-905810a9`](cards/F-ml430-nat-fib-strictmonoon-905810a9.html) |
| F:ml430-nat-gcd-fib-add-self-5a92d5e3 | Mathlib v4.30 source proposition Nat.gcd_fib_add_self | lean4-surface | Nat | kernel-lean | proved | proved | proved | - | 1 | 1 | [`F-ml430-nat-gcd-fib-add-self-5a92d5e3`](cards/F-ml430-nat-gcd-fib-add-self-5a92d5e3.html) |
| F:ml430-nat-gcd-greatest-0a04214a | Mathlib v4.30 source proposition Nat.gcd_greatest | lean4-surface | Nat | kernel-lean | proved | proved | proved | - | 1 | 1 | [`F-ml430-nat-gcd-greatest-0a04214a`](cards/F-ml430-nat-gcd-greatest-0a04214a.html) |
| F:ml430-nat-land-assoc-ad4775b8 | Mathlib v4.30 source proposition Nat.land_assoc | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-land-assoc-ad4775b8`](cards/F-ml430-nat-land-assoc-ad4775b8.html) |
| F:ml430-nat-land-bit-b9ab7475 | Mathlib v4.30 source proposition Nat.land_bit | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-land-bit-b9ab7475`](cards/F-ml430-nat-land-bit-b9ab7475.html) |
| F:ml430-nat-land-comm-7e6ad72e | Mathlib v4.30 source proposition Nat.land_comm | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-land-comm-7e6ad72e`](cards/F-ml430-nat-land-comm-7e6ad72e.html) |
| F:ml430-nat-ldiff-bit-6be49bb8 | Mathlib v4.30 source proposition Nat.ldiff_bit | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-ldiff-bit-6be49bb8`](cards/F-ml430-nat-ldiff-bit-6be49bb8.html) |
| F:ml430-nat-le-fib-add-one-5284f0bf | Mathlib v4.30 source proposition Nat.le_fib_add_one | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-le-fib-add-one-5284f0bf`](cards/F-ml430-nat-le-fib-add-one-5284f0bf.html) |
| F:ml430-nat-le-fib-self-0cbccb4d | Mathlib v4.30 source proposition Nat.le_fib_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-le-fib-self-0cbccb4d`](cards/F-ml430-nat-le-fib-self-0cbccb4d.html) |
| F:ml430-nat-le-sqrt-e6996680 | Mathlib v4.30 source proposition Nat.le_sqrt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-le-sqrt-e6996680`](cards/F-ml430-nat-le-sqrt-e6996680.html) |
| F:ml430-nat-le-sqrt-of-eq-mul-503c5afe | Mathlib v4.30 source proposition Nat.le_sqrt_of_eq_mul | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-le-sqrt-of-eq-mul-503c5afe`](cards/F-ml430-nat-le-sqrt-of-eq-mul-503c5afe.html) |
| F:ml430-nat-le-three-of-sqrt-eq-one-0c48a868 | Mathlib v4.30 source proposition Nat.le_three_of_sqrt_eq_one | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-le-three-of-sqrt-eq-one-0c48a868`](cards/F-ml430-nat-le-three-of-sqrt-eq-one-0c48a868.html) |
| F:ml430-nat-log-antitone-left-20d1326c | Mathlib v4.30 source proposition Nat.log_antitone_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-log-antitone-left-20d1326c`](cards/F-ml430-nat-log-antitone-left-20d1326c.html) |
| F:ml430-nat-log-le-clog-ac8ab2d4 | Mathlib v4.30 source proposition Nat.log_le_clog | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-log-le-clog-ac8ab2d4`](cards/F-ml430-nat-log-le-clog-ac8ab2d4.html) |
| F:ml430-nat-log-le-self-da387172 | Mathlib v4.30 source proposition Nat.log_le_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-log-le-self-da387172`](cards/F-ml430-nat-log-le-self-da387172.html) |
| F:ml430-nat-log-lt-self-529f89fa | Mathlib v4.30 source proposition Nat.log_lt_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-log-lt-self-529f89fa`](cards/F-ml430-nat-log-lt-self-529f89fa.html) |
| F:ml430-nat-log-mono-right-b8939fee | Mathlib v4.30 source proposition Nat.log_mono_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-log-mono-right-b8939fee`](cards/F-ml430-nat-log-mono-right-b8939fee.html) |
| F:ml430-nat-log-monotone-52fad774 | Mathlib v4.30 source proposition Nat.log_monotone | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-log-monotone-52fad774`](cards/F-ml430-nat-log-monotone-52fad774.html) |
| F:ml430-nat-log-of-lt-89eaf42e | Mathlib v4.30 source proposition Nat.log_of_lt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-log-of-lt-89eaf42e`](cards/F-ml430-nat-log-of-lt-89eaf42e.html) |
| F:ml430-nat-log-one-left-73efc119 | Mathlib v4.30 source proposition Nat.log_one_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-log-one-left-73efc119`](cards/F-ml430-nat-log-one-left-73efc119.html) |
| F:ml430-nat-log-one-right-282332ef | Mathlib v4.30 source proposition Nat.log_one_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-log-one-right-282332ef`](cards/F-ml430-nat-log-one-right-282332ef.html) |
| F:ml430-nat-log-zero-left-9ec8541e | Mathlib v4.30 source proposition Nat.log_zero_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-log-zero-left-9ec8541e`](cards/F-ml430-nat-log-zero-left-9ec8541e.html) |
| F:ml430-nat-log-zero-right-8ea186db | Mathlib v4.30 source proposition Nat.log_zero_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-log-zero-right-8ea186db`](cards/F-ml430-nat-log-zero-right-8ea186db.html) |
| F:ml430-nat-log2-eq-log-two-28085932 | Mathlib v4.30 source proposition Nat.log2_eq_log_two | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-log2-eq-log-two-28085932`](cards/F-ml430-nat-log2-eq-log-two-28085932.html) |
| F:ml430-nat-lor-assoc-82c4d0fd | Mathlib v4.30 source proposition Nat.lor_assoc | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-lor-assoc-82c4d0fd`](cards/F-ml430-nat-lor-assoc-82c4d0fd.html) |
| F:ml430-nat-lor-bit-a2f98c7c | Mathlib v4.30 source proposition Nat.lor_bit | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-lor-bit-a2f98c7c`](cards/F-ml430-nat-lor-bit-a2f98c7c.html) |
| F:ml430-nat-lor-comm-2666d7ef | Mathlib v4.30 source proposition Nat.lor_comm | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-lor-comm-2666d7ef`](cards/F-ml430-nat-lor-comm-2666d7ef.html) |
| F:ml430-nat-lt-of-testbit-72f64ab8 | Mathlib v4.30 source proposition Nat.lt_of_testBit | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-lt-of-testbit-72f64ab8`](cards/F-ml430-nat-lt-of-testbit-72f64ab8.html) |
| F:ml430-nat-lt-succ-sqrt-39389df2 | Mathlib v4.30 source proposition Nat.lt_succ_sqrt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-lt-succ-sqrt-39389df2`](cards/F-ml430-nat-lt-succ-sqrt-39389df2.html) |
| F:ml430-nat-lt-xor-cases-c43a1e85 | Mathlib v4.30 source proposition Nat.lt_xor_cases | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-lt-xor-cases-c43a1e85`](cards/F-ml430-nat-lt-xor-cases-c43a1e85.html) |
| F:ml430-nat-mod-lcm-ee6bdd41 | Mathlib v4.30 source proposition Nat.mod_lcm | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-mod-lcm-ee6bdd41`](cards/F-ml430-nat-mod-lcm-ee6bdd41.html) |
| F:ml430-nat-mod-modeq-436e4c10 | Mathlib v4.30 source proposition Nat.mod_modEq | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-mod-modeq-436e4c10`](cards/F-ml430-nat-mod-modeq-436e4c10.html) |
| F:ml430-nat-modeq-add-left-cancel-e5287cf6 | Mathlib v4.30 source proposition Nat.ModEq.add_left_cancel' | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modeq-add-left-cancel-e5287cf6`](cards/F-ml430-nat-modeq-add-left-cancel-e5287cf6.html) |
| F:ml430-nat-modeq-add-left-e83f0700 | Mathlib v4.30 source proposition Nat.ModEq.add_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modeq-add-left-e83f0700`](cards/F-ml430-nat-modeq-add-left-e83f0700.html) |
| F:ml430-nat-modeq-add-right-8e2ca0cc | Mathlib v4.30 source proposition Nat.ModEq.add_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modeq-add-right-8e2ca0cc`](cards/F-ml430-nat-modeq-add-right-8e2ca0cc.html) |
| F:ml430-nat-modeq-add-right-cancel-e871facf | Mathlib v4.30 source proposition Nat.ModEq.add_right_cancel' | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modeq-add-right-cancel-e871facf`](cards/F-ml430-nat-modeq-add-right-cancel-e871facf.html) |
| F:ml430-nat-modeq-comm-24b71e7a | Mathlib v4.30 source proposition Nat.ModEq.comm | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modeq-comm-24b71e7a`](cards/F-ml430-nat-modeq-comm-24b71e7a.html) |
| F:ml430-nat-modeq-dvd-iff-8f130450 | Mathlib v4.30 source proposition Nat.ModEq.dvd_iff | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modeq-dvd-iff-8f130450`](cards/F-ml430-nat-modeq-dvd-iff-8f130450.html) |
| F:ml430-nat-modeq-gcd-eq-5167ff4f | Mathlib v4.30 source proposition Nat.ModEq.gcd_eq | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modeq-gcd-eq-5167ff4f`](cards/F-ml430-nat-modeq-gcd-eq-5167ff4f.html) |
| F:ml430-nat-modeq-of-dvd-d75cc374 | Mathlib v4.30 source proposition Nat.ModEq.of_dvd | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modeq-of-dvd-d75cc374`](cards/F-ml430-nat-modeq-of-dvd-d75cc374.html) |
| F:ml430-nat-modeq-of-mul-left-88d20bca | Mathlib v4.30 source proposition Nat.ModEq.of_mul_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modeq-of-mul-left-88d20bca`](cards/F-ml430-nat-modeq-of-mul-left-88d20bca.html) |
| F:ml430-nat-modeq-of-mul-right-43078e1c | Mathlib v4.30 source proposition Nat.ModEq.of_mul_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modeq-of-mul-right-43078e1c`](cards/F-ml430-nat-modeq-of-mul-right-43078e1c.html) |
| F:ml430-nat-modeq-one-516d46e8 | Mathlib v4.30 source proposition Nat.modEq_one | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modeq-one-516d46e8`](cards/F-ml430-nat-modeq-one-516d46e8.html) |
| F:ml430-nat-modeq-refl-d870c8f5 | Mathlib v4.30 source proposition Nat.ModEq.refl | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modeq-refl-d870c8f5`](cards/F-ml430-nat-modeq-refl-d870c8f5.html) |
| F:ml430-nat-modeq-symm-0a3d4d18 | Mathlib v4.30 source proposition Nat.ModEq.symm | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modeq-symm-0a3d4d18`](cards/F-ml430-nat-modeq-symm-0a3d4d18.html) |
| F:ml430-nat-modeq-trans-ef9d1c46 | Mathlib v4.30 source proposition Nat.ModEq.trans | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modeq-trans-ef9d1c46`](cards/F-ml430-nat-modeq-trans-ef9d1c46.html) |
| F:ml430-nat-modulus-modeq-zero-fd9af096 | Mathlib v4.30 source proposition Nat.modulus_modEq_zero | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-modulus-modeq-zero-fd9af096`](cards/F-ml430-nat-modulus-modeq-zero-fd9af096.html) |
| F:ml430-nat-multichoose-one-b210386a | Mathlib v4.30 source proposition Nat.multichoose_one | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-multichoose-one-b210386a`](cards/F-ml430-nat-multichoose-one-b210386a.html) |
| F:ml430-nat-multichoose-one-right-7755072d | Mathlib v4.30 source proposition Nat.multichoose_one_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-multichoose-one-right-7755072d`](cards/F-ml430-nat-multichoose-one-right-7755072d.html) |
| F:ml430-nat-multichoose-zero-right-6ef827c8 | Mathlib v4.30 source proposition Nat.multichoose_zero_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-multichoose-zero-right-6ef827c8`](cards/F-ml430-nat-multichoose-zero-right-6ef827c8.html) |
| F:ml430-nat-not-coprime-zero-zero-6c4e8dd8 | Mathlib v4.30 source proposition Nat.not_coprime_zero_zero | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-not-coprime-zero-zero-6c4e8dd8`](cards/F-ml430-nat-not-coprime-zero-zero-6c4e8dd8.html) |
| F:ml430-nat-not-prime-of-dvd-of-ne-4ff592c0 | Mathlib v4.30 source proposition Nat.not_prime_of_dvd_of_ne | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-not-prime-of-dvd-of-ne-4ff592c0`](cards/F-ml430-nat-not-prime-of-dvd-of-ne-4ff592c0.html) |
| F:ml430-nat-one-ascfactorial-8bacb017 | Mathlib v4.30 source proposition Nat.one_ascFactorial | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-one-ascfactorial-8bacb017`](cards/F-ml430-nat-one-ascfactorial-8bacb017.html) |
| F:ml430-nat-prime-dvd-iff-not-coprime-77854741 | Mathlib v4.30 source proposition Nat.Prime.dvd_iff_not_coprime | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-prime-dvd-iff-not-coprime-77854741`](cards/F-ml430-nat-prime-dvd-iff-not-coprime-77854741.html) |
| F:ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439 | Mathlib v4.30 source proposition Nat.Prime.dvd_mul_of_dvd_ne | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439`](cards/F-ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439.html) |
| F:ml430-nat-prime-dvd-of-dvd-pow-e76f834a | Mathlib v4.30 source proposition Nat.Prime.dvd_of_dvd_pow | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-prime-dvd-of-dvd-pow-e76f834a`](cards/F-ml430-nat-prime-dvd-of-dvd-pow-e76f834a.html) |
| F:ml430-nat-prime-even-iff-d068ec82 | Mathlib v4.30 source proposition Nat.Prime.even_iff | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-prime-even-iff-d068ec82`](cards/F-ml430-nat-prime-even-iff-d068ec82.html) |
| F:ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786 | Mathlib v4.30 source proposition Nat.Prime.five_le_of_ne_two_of_ne_three | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786`](cards/F-ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786.html) |
| F:ml430-nat-prime-not-dvd-mul-cb3a915e | Mathlib v4.30 source proposition Nat.Prime.not_dvd_mul | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-prime-not-dvd-mul-cb3a915e`](cards/F-ml430-nat-prime-not-dvd-mul-cb3a915e.html) |
| F:ml430-nat-prime-odd-of-ne-two-91e1195f | Mathlib v4.30 source proposition Nat.Prime.odd_of_ne_two | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-prime-odd-of-ne-two-91e1195f`](cards/F-ml430-nat-prime-odd-of-ne-two-91e1195f.html) |
| F:ml430-nat-prime-pred-pos-4e67ac4c | Mathlib v4.30 source proposition Nat.Prime.pred_pos | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-prime-pred-pos-4e67ac4c`](cards/F-ml430-nat-prime-pred-pos-4e67ac4c.html) |
| F:ml430-nat-self-le-factorial-cfdffc69 | Mathlib v4.30 source proposition Nat.self_le_factorial | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-self-le-factorial-cfdffc69`](cards/F-ml430-nat-self-le-factorial-cfdffc69.html) |
| F:ml430-nat-sqrt-eq-79ae8eae | Mathlib v4.30 source proposition Nat.sqrt_eq | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-sqrt-eq-79ae8eae`](cards/F-ml430-nat-sqrt-eq-79ae8eae.html) |
| F:ml430-nat-sqrt-eq-c036815b | Mathlib v4.30 source proposition Nat.sqrt_eq' | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-sqrt-eq-c036815b`](cards/F-ml430-nat-sqrt-eq-c036815b.html) |
| F:ml430-nat-sqrt-eq-zero-53666a3b | Mathlib v4.30 source proposition Nat.sqrt_eq_zero | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-sqrt-eq-zero-53666a3b`](cards/F-ml430-nat-sqrt-eq-zero-53666a3b.html) |
| F:ml430-nat-sqrt-le-7918582b | Mathlib v4.30 source proposition Nat.sqrt_le | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-sqrt-le-7918582b`](cards/F-ml430-nat-sqrt-le-7918582b.html) |
| F:ml430-nat-sqrt-le-self-1ed5eb85 | Mathlib v4.30 source proposition Nat.sqrt_le_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-sqrt-le-self-1ed5eb85`](cards/F-ml430-nat-sqrt-le-self-1ed5eb85.html) |
| F:ml430-nat-sqrt-le-sqrt-6e2bfc47 | Mathlib v4.30 source proposition Nat.sqrt_le_sqrt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-sqrt-le-sqrt-6e2bfc47`](cards/F-ml430-nat-sqrt-le-sqrt-6e2bfc47.html) |
| F:ml430-nat-sqrt-lt-4909537f | Mathlib v4.30 source proposition Nat.sqrt_lt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-sqrt-lt-4909537f`](cards/F-ml430-nat-sqrt-lt-4909537f.html) |
| F:ml430-nat-sqrt-lt-self-ff7a155a | Mathlib v4.30 source proposition Nat.sqrt_lt_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-sqrt-lt-self-ff7a155a`](cards/F-ml430-nat-sqrt-lt-self-ff7a155a.html) |
| F:ml430-nat-sqrt-pos-f75e5114 | Mathlib v4.30 source proposition Nat.sqrt_pos | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-sqrt-pos-f75e5114`](cards/F-ml430-nat-sqrt-pos-f75e5114.html) |
| F:ml430-nat-sqrt-succ-le-succ-sqrt-6b041183 | Mathlib v4.30 source proposition Nat.sqrt_succ_le_succ_sqrt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-sqrt-succ-le-succ-sqrt-6b041183`](cards/F-ml430-nat-sqrt-succ-le-succ-sqrt-6b041183.html) |
| F:ml430-nat-succ-pred-prime-4feb123f | Mathlib v4.30 source proposition Nat.succ_pred_prime | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-succ-pred-prime-4feb123f`](cards/F-ml430-nat-succ-pred-prime-4feb123f.html) |
| F:ml430-nat-testbit-eq-inth-ffa07392 | Mathlib v4.30 source proposition Nat.testBit_eq_inth | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-testbit-eq-inth-ffa07392`](cards/F-ml430-nat-testbit-eq-inth-ffa07392.html) |
| F:ml430-nat-testbit-land-dfef7ca4 | Mathlib v4.30 source proposition Nat.testBit_land | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-testbit-land-dfef7ca4`](cards/F-ml430-nat-testbit-land-dfef7ca4.html) |
| F:ml430-nat-testbit-ldiff-16f94162 | Mathlib v4.30 source proposition Nat.testBit_ldiff | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-testbit-ldiff-16f94162`](cards/F-ml430-nat-testbit-ldiff-16f94162.html) |
| F:ml430-nat-testbit-lor-7644e067 | Mathlib v4.30 source proposition Nat.testBit_lor | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-testbit-lor-7644e067`](cards/F-ml430-nat-testbit-lor-7644e067.html) |
| F:ml430-nat-zero-ascfactorial-af4fcdca | Mathlib v4.30 source proposition Nat.zero_ascFactorial | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-zero-ascfactorial-af4fcdca`](cards/F-ml430-nat-zero-ascfactorial-af4fcdca.html) |
| F:ml430-nat-zero-of-testbit-eq-false-e244c9a1 | Mathlib v4.30 source proposition Nat.zero_of_testBit_eq_false | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | [`F-ml430-nat-zero-of-testbit-eq-false-e244c9a1`](cards/F-ml430-nat-zero-of-testbit-eq-false-e244c9a1.html) |
| F:modus-ponens-valid | Modus ponens is a valid inference | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-modus-ponens-valid`](cards/F-modus-ponens-valid.html) |
| F:modus-tollens-valid | Modus tollens is a valid inference | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-modus-tollens-valid`](cards/F-modus-tollens-valid.html) |
| F:nand-functional-completeness | NAND defines negation, conjunction and disjunction | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-nand-functional-completeness`](cards/F-nand-functional-completeness.html) |
| F:nat-add-assoc | Addition on the naturals is associative | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-add-assoc`](cards/F-nat-add-assoc.html) |
| F:nat-add-comm | Addition on the naturals is commutative | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-add-comm`](cards/F-nat-add-comm.html) |
| F:nat-add-sub-cancel-left | Subtraction undoes addition on the naturals | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-add-sub-cancel-left`](cards/F-nat-add-sub-cancel-left.html) |
| F:nat-add-zero | Zero is a right identity for addition on the naturals | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-add-zero`](cards/F-nat-add-zero.html) |
| F:nat-div-mod-exists | Division with remainder always exists for a positive divisor | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-div-mod-exists`](cards/F-nat-div-mod-exists.html) |
| F:nat-div-mod-unique | The quotient and remainder of a division are unique | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-div-mod-unique`](cards/F-nat-div-mod-unique.html) |
| F:nat-dvd-add | A common divisor of two numbers divides their sum | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-dvd-add`](cards/F-nat-dvd-add.html) |
| F:nat-dvd-gcd-iff | The gcd is exactly the common divisors' upper bound | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-dvd-gcd-iff`](cards/F-nat-dvd-gcd-iff.html) |
| F:nat-euclid-lemma | Euclid's lemma: a prime dividing a product divides a factor | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-euclid-lemma`](cards/F-nat-euclid-lemma.html) |
| F:nat-exists-prime-dvd | Every natural number at least 2 has a prime divisor | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-exists-prime-dvd`](cards/F-nat-exists-prime-dvd.html) |
| F:nat-exists-prime-gt | There is no largest prime | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-exists-prime-gt`](cards/F-nat-exists-prime-gt.html) |
| F:nat-gcd-bezout | Bezout's identity holds for the natural gcd | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-gcd-bezout`](cards/F-nat-gcd-bezout.html) |
| F:nat-gcd-succ | The Euclidean algorithm's descent step is correct | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-gcd-succ`](cards/F-nat-gcd-succ.html) |
| F:nat-le-refl | The order on the naturals is reflexive | lean4 | Nat | imported-kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-le-refl`](cards/F-nat-le-refl.html) |
| F:nat-le-succ | Every natural number is below its successor | lean4 | Nat | imported-kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-le-succ`](cards/F-nat-le-succ.html) |
| F:nat-left-distrib | Multiplication distributes over addition on the left | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-left-distrib`](cards/F-nat-left-distrib.html) |
| F:nat-mod-eq-mul | Congruences may be multiplied | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-mod-eq-mul`](cards/F-nat-mod-eq-mul.html) |
| F:nat-mul-assoc | Multiplication on the naturals is associative | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-mul-assoc`](cards/F-nat-mul-assoc.html) |
| F:nat-mul-comm | Multiplication on the naturals is commutative | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-mul-comm`](cards/F-nat-mul-comm.html) |
| F:nat-mul-one | One is a right identity for multiplication on the naturals | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-mul-one`](cards/F-nat-mul-one.html) |
| F:nat-peano-categoricity | The constructed Nat is THE natural numbers, up to unique isomorphism | lean4 | Nat | kernel-lean | proved | proved | proved | - | 4 | 4 | [`F-nat-peano-categoricity`](cards/F-nat-peano-categoricity.html) |
| F:nat-pow-add | The first index law: powers add over a product | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-pow-add`](cards/F-nat-pow-add.html) |
| F:nat-succ-add | Nat succ_add | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-succ-add`](cards/F-nat-succ-add.html) |
| F:nat-zero-add | Nat zero_add | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-nat-zero-add`](cards/F-nat-zero-add.html) |
| F:no-integer-square-is-minus-one | No integer squares to minus one | smtlib2 | QF_NIA | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-no-integer-square-is-minus-one`](cards/F-no-integer-square-is-minus-one.html) |
| F:no-self-negating-proposition | No proposition is equivalent to its own negation | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-no-self-negating-proposition`](cards/F-no-self-negating-proposition.html) |
| F:nra-refutations-reconstruct-over-constructed-reals | Two QF_NRA refutation certificates reconstruct to a kernel-checked Lean False over the CONSTRUCTED reals | smtlib2 | QF_NRA | kernel-lean | proved | unknown | proved | - | 2 | 2 | [`F-nra-refutations-reconstruct-over-constructed-reals`](cards/F-nra-refutations-reconstruct-over-constructed-reals.html) |
| F:ordered-ring-farkas-refutation | A reconstructed Farkas refutation holds in every ordered commutative ring, and rests on no axiom | lean4 | QF_LRA | kernel-lean | proved | proved | proved | - | 4 | 4 | [`F-ordered-ring-farkas-refutation`](cards/F-ordered-ring-farkas-refutation.html) |
| F:ordered-ring-interface-is-the-same-over-the-axiom-free-integers | The ordered-ring interface telescope is byte-identical over Real and over the axiom-free Int development | lean4 | kernel-metatheory | kernel-lean | proved | unknown | proved | - | 3 | 3 | [`F-ordered-ring-interface-is-the-same-over-the-axiom-free-integers`](cards/F-ordered-ring-interface-is-the-same-over-the-axiom-free-integers.html) |
| F:orders-candidate-keys-and-normal-forms | An order-line schema has exactly two candidate keys, is not in BCNF, and is not in 3NF -- with every subset of the attributes examined | smtlib2 | QF_UF | search-certificate | proved | unclassified | proved | - | 3 | 3 | [`F-orders-candidate-keys-and-normal-forms`](cards/F-orders-candidate-keys-and-normal-forms.html) |
| F:orders-fd-implication-certified | Two implied and two unimplied functional dependencies on a committed order-line schema, each with a replayable certificate | smtlib2 | QF_UF | search-certificate | proved | unclassified | proved | - | 3 | 3 | [`F-orders-fd-implication-certified`](cards/F-orders-fd-implication-certified.html) |
| F:peirce-law | Peirce's law | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-peirce-law`](cards/F-peirce-law.html) |
| F:prop-excluded-middle-classical | Excluded middle for propositions, as Lean proves it | lean4 | Prop | imported-kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-prop-excluded-middle-classical`](cards/F-prop-excluded-middle-classical.html) |
| F:qf-nia-univariate-unsat-is-certified | QF_NIA single-variable polynomial UNSAT carries an independently re-derivable refutation | smtlib2 | QF_NIA | smt-term-level | proved | unknown | proved | - | 3 | 3 | [`F-qf-nia-univariate-unsat-is-certified`](cards/F-qf-nia-univariate-unsat-is-certified.html) |
| F:quantifier-negation-duality | Negation exchanges the two quantifiers | smtlib2 | UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-quantifier-negation-duality`](cards/F-quantifier-negation-duality.html) |
| F:rado-r4-a5-b3 | The four-colour Rado number of 5(x-y) = 3z is 625 | smtlib2 | QF_BV | search-certificate | computed | open | evidence | novel | 3 | 3 | [`F-rado-r4-a5-b3`](cards/F-rado-r4-a5-b3.html) |
| F:rado-r4-a5-b4 | The four-colour Rado number of 5(x-y) = 4z is 741 | smtlib2 | QF_BV | search-certificate | computed | open | evidence | novel | 1 | 1 | [`F-rado-r4-a5-b4`](cards/F-rado-r4-a5-b4.html) |
| F:rat-add-neg-inverse | Rational addition renormalises and negation is an additive inverse | lean4 | Rat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-rat-add-neg-inverse`](cards/F-rat-add-neg-inverse.html) |
| F:rat-mul-renormalises | Rational multiplication renormalises | lean4 | Rat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-rat-mul-renormalises`](cards/F-rat-mul-renormalises.html) |
| F:rat-normalize-reduces | The rational smart constructor normalises | lean4 | Rat | kernel-lean | proved | proved | proved | - | 2 | 2 | [`F-rat-normalize-reduces`](cards/F-rat-normalize-reduces.html) |
| F:rationals-are-a-field-axiom-free | ℚ is a field: Rat.inv is proved to invert, at zero trusted declarations | lean4 | Rat | kernel-lean | proved | proved | proved | - | 3 | 3 | [`F-rationals-are-a-field-axiom-free`](cards/F-rationals-are-a-field-axiom-free.html) |
| F:real-axioms-modelled-by-constructed-setoid | The 30 AxReal axioms are satisfiable: a Bishop setoid over the constructed rationals models all 22 laws at zero trusted declarations | lean4 | Real | kernel-lean | proved | proved | proved | - | 3 | 3 | [`F-real-axioms-modelled-by-constructed-setoid`](cards/F-real-axioms-modelled-by-constructed-setoid.html) |
| F:real-inverse-is-built-and-well-defined | The constructed reals have a multiplicative inverse whose modulus is an explicit natural, and it is a function on the reals rather than on representatives | lean4 | CReal | kernel-lean | proved | proved | proved | - | 4 | 4 | [`F-real-inverse-is-built-and-well-defined`](cards/F-real-inverse-is-built-and-well-defined.html) |
| F:real-inverse-is-partial-and-its-modulus-is-data | No function on all of the constructed reals is a multiplicative inverse, and the modulus that would make one possible cannot be extracted from positivity | lean4 | CReal | kernel-lean | proved | proved | proved | - | 4 | 4 | [`F-real-inverse-is-partial-and-its-modulus-is-data`](cards/F-real-inverse-is-partial-and-its-modulus-is-data.html) |
| F:real-lattice-is-constructed-axiom-free | The constructed reals carry max, min and a total absolute value, built with no index shift and no decision procedure | lean4 | CReal | kernel-lean | proved | proved | proved | - | 5 | 5 | [`F-real-lattice-is-constructed-axiom-free`](cards/F-real-lattice-is-constructed-axiom-free.html) |
| F:resolution-rule-sound | The binary propositional resolution rule is sound | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-resolution-rule-sound`](cards/F-resolution-rule-sound.html) |
| F:roster-icu-night-iis | Five rows of a 102-row ICU night roster are an irreducible infeasible subsystem | smtlib2 | LIA | search-certificate | proved | unclassified | proved | - | 2 | 2 | [`F-roster-icu-night-iis`](cards/F-roster-icu-night-iis.html) |
| F:schedule-critical-chain-infeasible | A five-constraint critical chain against a delivery deadline, refuted in the Lean kernel | smtlib2 | QF_LRA | kernel-lean | proved | unclassified | proved | - | 2 | 2 | [`F-schedule-critical-chain-infeasible`](cards/F-schedule-critical-chain-infeasible.html) |
| F:schedule-deadline-iis | Five rows of a 60-row project schedule are an irreducible infeasible subsystem | smtlib2 | LRA | search-certificate | proved | unclassified | proved | - | 2 | 2 | [`F-schedule-deadline-iis`](cards/F-schedule-deadline-iis.html) |
| F:shipped-front-door-reaches-no-real-axiom | No shipped reconstruction route BUILDS the AxReal axiom package: the trusted surface is declared but never reached | lean4 | QF_LRA | kernel-lean | proved | unknown | proved | - | 7 | 7 | [`F-shipped-front-door-reaches-no-real-axiom`](cards/F-shipped-front-door-reaches-no-real-axiom.html) |
| F:shipped-front-door-refutes-over-constructed-reals | The shipped LRA/SOS front door reconstructs over the constructed reals, and the refutation it returns rests on zero carrier axioms | lean4 | QF_LRA | kernel-lean | proved | proved | proved | - | 6 | 6 | [`F-shipped-front-door-refutes-over-constructed-reals`](cards/F-shipped-front-door-refutes-over-constructed-reals.html) |
| F:sorting-network-optimal-size-n3 | The optimal sorting network on 3 channels has exactly 3 comparators | smtlib2 | QF_BV | smt-clausal | proved | proved | proved | - | 2 | 2 | [`F-sorting-network-optimal-size-n3`](cards/F-sorting-network-optimal-size-n3.html) |
| F:sorting-network-optimal-size-n4 | The optimal sorting network on 4 channels has exactly 5 comparators | smtlib2 | QF_BV | smt-clausal | proved | proved | proved | - | 2 | 2 | [`F-sorting-network-optimal-size-n4`](cards/F-sorting-network-optimal-size-n4.html) |
| F:sorting-network-optimal-size-n5 | The optimal sorting network on 5 channels has exactly 9 comparators | smtlib2 | QF_BV | smt-clausal | proved | proved | proved | - | 2 | 2 | [`F-sorting-network-optimal-size-n5`](cards/F-sorting-network-optimal-size-n5.html) |
| F:sorting-network-optimal-size-n6 | The optimal sorting network on 6 channels has exactly 12 comparators | smtlib2 | QF_BV | smt-clausal | proved | proved | proved | - | 2 | 2 | [`F-sorting-network-optimal-size-n6`](cards/F-sorting-network-optimal-size-n6.html) |
| F:squared-binomial-row-sum-central | The sum of squared binomial coefficients is the central binomial coefficient | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-squared-binomial-row-sum-central`](cards/F-squared-binomial-row-sum-central.html) |
| F:tseitin-and-gate | The Tseitin clauses for an AND gate define the gate | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-tseitin-and-gate`](cards/F-tseitin-and-gate.html) |
| F:twin-prime-unbounded | Twin prime conjecture | lean4 | Nat | - | conjectured | open | open | - | 0 | 0 | [`F-twin-prime-unbounded`](cards/F-twin-prime-unbounded.html) |
| F:weighted-binomial-row-sum | The k-weighted binomial row sum | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | [`F-weighted-binomial-row-sum`](cards/F-weighted-binomial-row-sum.html) |
| F:xor-associative | Exclusive-or is associative | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | [`F-xor-associative`](cards/F-xor-associative.html) |

Source: `python3 render/producers-py/facts_to_docir.py` (exit 0), 341 input(s) hashed.

<details>
<summary>Import backlog</summary>

Settled in the literature, open here (import backlog)

| fact | title | card |
| --- | --- | --- |
| F:continuum-hypothesis-independent | The continuum hypothesis is independent of ZFC | [`F-continuum-hypothesis-independent`](cards/F-continuum-hypothesis-independent.html) |
| F:excluded-middle-not-intuitionistic | Excluded middle is not derivable in intuitionistic propositional logic | [`F-excluded-middle-not-intuitionistic`](cards/F-excluded-middle-not-intuitionistic.html) |
| F:fermat-last-theorem | Fermat's Last Theorem | [`F-fermat-last-theorem`](cards/F-fermat-last-theorem.html) |
| F:fol-validity-undecidable | Validity in first-order logic is undecidable | [`F-fol-validity-undecidable`](cards/F-fol-validity-undecidable.html) |
| F:fp16-add-monotone-rne | binary16 addition under roundNearestTiesToEven is monotone in its first argument | [`F-fp16-add-monotone-rne`](cards/F-fp16-add-monotone-rne.html) |
| F:godel-first-incompleteness | Godel's first incompleteness theorem | [`F-godel-first-incompleteness`](cards/F-godel-first-incompleteness.html) |
| F:ml430-int-add-modeq-left-ee732b5b | Mathlib v4.30 source proposition Int.add_modEq_left | [`F-ml430-int-add-modeq-left-ee732b5b`](cards/F-ml430-int-add-modeq-left-ee732b5b.html) |
| F:ml430-int-add-modeq-right-e58108ee | Mathlib v4.30 source proposition Int.add_modEq_right | [`F-ml430-int-add-modeq-right-e58108ee`](cards/F-ml430-int-add-modeq-right-e58108ee.html) |
| F:ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b | Mathlib v4.30 source proposition Int.dvd_of_dvd_mul_left_of_gcd_one | [`F-ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b`](cards/F-ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b.html) |
| F:ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0 | Mathlib v4.30 source proposition Int.dvd_of_dvd_mul_right_of_gcd_one | [`F-ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0`](cards/F-ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0.html) |
| F:ml430-int-fib-add-181b6a2c | Mathlib v4.30 source proposition Int.fib_add | [`F-ml430-int-fib-add-181b6a2c`](cards/F-ml430-int-fib-add-181b6a2c.html) |
| F:ml430-int-fib-add-one-33f1b748 | Mathlib v4.30 source proposition Int.fib_add_one | [`F-ml430-int-fib-add-one-33f1b748`](cards/F-ml430-int-fib-add-one-33f1b748.html) |
| F:ml430-int-fib-add-two-739358dd | Mathlib v4.30 source proposition Int.fib_add_two | [`F-ml430-int-fib-add-two-739358dd`](cards/F-ml430-int-fib-add-two-739358dd.html) |
| F:ml430-int-fib-dvd-ffb3c5c1 | Mathlib v4.30 source proposition Int.fib_dvd | [`F-ml430-int-fib-dvd-ffb3c5c1`](cards/F-ml430-int-fib-dvd-ffb3c5c1.html) |
| F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d | Mathlib v4.30 source proposition Int.fib_eq_fib_add_two_sub_fib_add_one | [`F-ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d`](cards/F-ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d.html) |
| F:ml430-int-fib-eq-zero-8193c7cb | Mathlib v4.30 source proposition Int.fib_eq_zero | [`F-ml430-int-fib-eq-zero-8193c7cb`](cards/F-ml430-int-fib-eq-zero-8193c7cb.html) |
| F:ml430-int-fib-gcd-3a8bfdec | Mathlib v4.30 source proposition Int.fib_gcd | [`F-ml430-int-fib-gcd-3a8bfdec`](cards/F-ml430-int-fib-gcd-3a8bfdec.html) |
| F:ml430-int-fib-natcast-d5886be4 | Mathlib v4.30 source proposition Int.fib_natCast | [`F-ml430-int-fib-natcast-d5886be4`](cards/F-ml430-int-fib-natcast-d5886be4.html) |
| F:ml430-int-fib-neg-b4021d37 | Mathlib v4.30 source proposition Int.fib_neg | [`F-ml430-int-fib-neg-b4021d37`](cards/F-ml430-int-fib-neg-b4021d37.html) |
| F:ml430-int-fib-of-nonneg-438018c5 | Mathlib v4.30 source proposition Int.fib_of_nonneg | [`F-ml430-int-fib-of-nonneg-438018c5`](cards/F-ml430-int-fib-of-nonneg-438018c5.html) |
| F:ml430-int-fib-of-odd-66560495 | Mathlib v4.30 source proposition Int.fib_of_odd | [`F-ml430-int-fib-of-odd-66560495`](cards/F-ml430-int-fib-of-odd-66560495.html) |
| F:ml430-int-fib-two-mul-0e70f3dd | Mathlib v4.30 source proposition Int.fib_two_mul | [`F-ml430-int-fib-two-mul-0e70f3dd`](cards/F-ml430-int-fib-two-mul-0e70f3dd.html) |
| F:ml430-int-fib-two-mul-add-one-pos-8977f65f | Mathlib v4.30 source proposition Int.fib_two_mul_add_one_pos | [`F-ml430-int-fib-two-mul-add-one-pos-8977f65f`](cards/F-ml430-int-fib-two-mul-add-one-pos-8977f65f.html) |
| F:ml430-int-fib-two-mul-add-two-0ba4a948 | Mathlib v4.30 source proposition Int.fib_two_mul_add_two | [`F-ml430-int-fib-two-mul-add-two-0ba4a948`](cards/F-ml430-int-fib-two-mul-add-two-0ba4a948.html) |
| F:ml430-int-gcd-div-5e01872f | Mathlib v4.30 source proposition Int.gcd_div | [`F-ml430-int-gcd-div-5e01872f`](cards/F-ml430-int-gcd-div-5e01872f.html) |
| F:ml430-int-gcd-div-gcd-div-gcd-2db608dc | Mathlib v4.30 source proposition Int.gcd_div_gcd_div_gcd | [`F-ml430-int-gcd-div-gcd-div-gcd-2db608dc`](cards/F-ml430-int-gcd-div-gcd-div-gcd-2db608dc.html) |
| F:ml430-int-gcd-eq-gcd-ab-63005aef | Mathlib v4.30 source proposition Int.gcd_eq_gcd_ab | [`F-ml430-int-gcd-eq-gcd-ab-63005aef`](cards/F-ml430-int-gcd-eq-gcd-ab-63005aef.html) |
| F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-left-8533eb82 | Mathlib v4.30 source proposition Int.gcd_eq_one_of_gcd_mul_right_eq_one_left | [`F-ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-left-8533eb82`](cards/F-ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-left-8533eb82.html) |
| F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-right-a9b19222 | Mathlib v4.30 source proposition Int.gcd_eq_one_of_gcd_mul_right_eq_one_right | [`F-ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-right-a9b19222`](cards/F-ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-right-a9b19222.html) |
| F:ml430-int-gcd-fib-73bdafc2 | Mathlib v4.30 source proposition Int.gcd_fib | [`F-ml430-int-gcd-fib-73bdafc2`](cards/F-ml430-int-gcd-fib-73bdafc2.html) |
| F:ml430-int-gcd-greatest-5b31c5fe | Mathlib v4.30 source proposition Int.gcd_greatest | [`F-ml430-int-gcd-greatest-5b31c5fe`](cards/F-ml430-int-gcd-greatest-5b31c5fe.html) |
| F:ml430-int-mod-modeq-6bec7847 | Mathlib v4.30 source proposition Int.mod_modEq | [`F-ml430-int-mod-modeq-6bec7847`](cards/F-ml430-int-mod-modeq-6bec7847.html) |
| F:ml430-int-modeq-add-left-6e17c69a | Mathlib v4.30 source proposition Int.ModEq.add_left | [`F-ml430-int-modeq-add-left-6e17c69a`](cards/F-ml430-int-modeq-add-left-6e17c69a.html) |
| F:ml430-int-modeq-add-left-cancel-062ad5fe | Mathlib v4.30 source proposition Int.ModEq.add_left_cancel' | [`F-ml430-int-modeq-add-left-cancel-062ad5fe`](cards/F-ml430-int-modeq-add-left-cancel-062ad5fe.html) |
| F:ml430-int-modeq-comm-1e4bcc07 | Mathlib v4.30 source proposition Int.modEq_comm | [`F-ml430-int-modeq-comm-1e4bcc07`](cards/F-ml430-int-modeq-comm-1e4bcc07.html) |
| F:ml430-int-modeq-dvd-iff-b7ffeff8 | Mathlib v4.30 source proposition Int.ModEq.dvd_iff | [`F-ml430-int-modeq-dvd-iff-b7ffeff8`](cards/F-ml430-int-modeq-dvd-iff-b7ffeff8.html) |
| F:ml430-int-modeq-neg-d6ff57b6 | Mathlib v4.30 source proposition Int.modEq_neg | [`F-ml430-int-modeq-neg-d6ff57b6`](cards/F-ml430-int-modeq-neg-d6ff57b6.html) |
| F:ml430-int-modeq-neg-f649f6c5 | Mathlib v4.30 source proposition Int.ModEq.neg | [`F-ml430-int-modeq-neg-f649f6c5`](cards/F-ml430-int-modeq-neg-f649f6c5.html) |
| F:ml430-int-modeq-of-dvd-b9c41fce | Mathlib v4.30 source proposition Int.ModEq.of_dvd | [`F-ml430-int-modeq-of-dvd-b9c41fce`](cards/F-ml430-int-modeq-of-dvd-b9c41fce.html) |
| F:ml430-int-modeq-of-mul-left-c4ccd51e | Mathlib v4.30 source proposition Int.ModEq.of_mul_left | [`F-ml430-int-modeq-of-mul-left-c4ccd51e`](cards/F-ml430-int-modeq-of-mul-left-c4ccd51e.html) |
| F:ml430-int-modeq-of-mul-right-c92b7bf0 | Mathlib v4.30 source proposition Int.ModEq.of_mul_right | [`F-ml430-int-modeq-of-mul-right-c92b7bf0`](cards/F-ml430-int-modeq-of-mul-right-c92b7bf0.html) |
| F:ml430-int-modeq-one-01d9de39 | Mathlib v4.30 source proposition Int.modEq_one | [`F-ml430-int-modeq-one-01d9de39`](cards/F-ml430-int-modeq-one-01d9de39.html) |
| F:ml430-int-modeq-refl-30e15520 | Mathlib v4.30 source proposition Int.ModEq.refl | [`F-ml430-int-modeq-refl-30e15520`](cards/F-ml430-int-modeq-refl-30e15520.html) |
| F:ml430-int-modeq-sub-3148f130 | Mathlib v4.30 source proposition Int.modEq_sub | [`F-ml430-int-modeq-sub-3148f130`](cards/F-ml430-int-modeq-sub-3148f130.html) |
| F:ml430-int-modeq-symm-984a6e67 | Mathlib v4.30 source proposition Int.ModEq.symm | [`F-ml430-int-modeq-symm-984a6e67`](cards/F-ml430-int-modeq-symm-984a6e67.html) |
| F:ml430-int-modeq-trans-6d7863e0 | Mathlib v4.30 source proposition Int.ModEq.trans | [`F-ml430-int-modeq-trans-6d7863e0`](cards/F-ml430-int-modeq-trans-6d7863e0.html) |
| F:ml430-int-modulus-modeq-zero-5b57a898 | Mathlib v4.30 source proposition Int.modulus_modEq_zero | [`F-ml430-int-modulus-modeq-zero-5b57a898`](cards/F-ml430-int-modulus-modeq-zero-5b57a898.html) |
| F:ml430-int-ne-zero-of-gcd-f71f00df | Mathlib v4.30 source proposition Int.ne_zero_of_gcd | [`F-ml430-int-ne-zero-of-gcd-f71f00df`](cards/F-ml430-int-ne-zero-of-gcd-f71f00df.html) |
| F:ml430-int-neg-modeq-neg-30d98479 | Mathlib v4.30 source proposition Int.neg_modEq_neg | [`F-ml430-int-neg-modeq-neg-30d98479`](cards/F-ml430-int-neg-modeq-neg-30d98479.html) |
| F:ml430-nat-add-modeq-left-e3b1fba9 | Mathlib v4.30 source proposition Nat.add_modEq_left | [`F-ml430-nat-add-modeq-left-e3b1fba9`](cards/F-ml430-nat-add-modeq-left-e3b1fba9.html) |
| F:ml430-nat-add-modeq-right-e2f11f21 | Mathlib v4.30 source proposition Nat.add_modEq_right | [`F-ml430-nat-add-modeq-right-e2f11f21`](cards/F-ml430-nat-add-modeq-right-e2f11f21.html) |
| F:ml430-nat-bitwise-bit-4c4b28a8 | Mathlib v4.30 source proposition Nat.bitwise_bit' | [`F-ml430-nat-bitwise-bit-4c4b28a8`](cards/F-ml430-nat-bitwise-bit-4c4b28a8.html) |
| F:ml430-nat-bitwise-comm-1a273bae | Mathlib v4.30 source proposition Nat.bitwise_comm | [`F-ml430-nat-bitwise-comm-1a273bae`](cards/F-ml430-nat-bitwise-comm-1a273bae.html) |
| F:ml430-nat-bitwise-swap-7175e90e | Mathlib v4.30 source proposition Nat.bitwise_swap | [`F-ml430-nat-bitwise-swap-7175e90e`](cards/F-ml430-nat-bitwise-swap-7175e90e.html) |
| F:ml430-nat-choose-eq-zero-of-lt-92ebab29 | Mathlib v4.30 source proposition Nat.choose_eq_zero_of_lt | [`F-ml430-nat-choose-eq-zero-of-lt-92ebab29`](cards/F-ml430-nat-choose-eq-zero-of-lt-92ebab29.html) |
| F:ml430-nat-choose-le-add-9c463139 | Mathlib v4.30 source proposition Nat.choose_le_add | [`F-ml430-nat-choose-le-add-9c463139`](cards/F-ml430-nat-choose-le-add-9c463139.html) |
| F:ml430-nat-choose-le-choose-907b5042 | Mathlib v4.30 source proposition Nat.choose_le_choose | [`F-ml430-nat-choose-le-choose-907b5042`](cards/F-ml430-nat-choose-le-choose-907b5042.html) |
| F:ml430-nat-choose-le-succ-62ae968b | Mathlib v4.30 source proposition Nat.choose_le_succ | [`F-ml430-nat-choose-le-succ-62ae968b`](cards/F-ml430-nat-choose-le-succ-62ae968b.html) |
| F:ml430-nat-choose-mono-a1af9c18 | Mathlib v4.30 source proposition Nat.choose_mono | [`F-ml430-nat-choose-mono-a1af9c18`](cards/F-ml430-nat-choose-mono-a1af9c18.html) |
| F:ml430-nat-choose-ne-zero-49c3d3cb | Mathlib v4.30 source proposition Nat.choose_ne_zero | [`F-ml430-nat-choose-ne-zero-49c3d3cb`](cards/F-ml430-nat-choose-ne-zero-49c3d3cb.html) |
| F:ml430-nat-choose-one-right-7eda8e39 | Mathlib v4.30 source proposition Nat.choose_one_right | [`F-ml430-nat-choose-one-right-7eda8e39`](cards/F-ml430-nat-choose-one-right-7eda8e39.html) |
| F:ml430-nat-choose-self-25bb9fb8 | Mathlib v4.30 source proposition Nat.choose_self | [`F-ml430-nat-choose-self-25bb9fb8`](cards/F-ml430-nat-choose-self-25bb9fb8.html) |
| F:ml430-nat-choose-succ-self-e396f6c2 | Mathlib v4.30 source proposition Nat.choose_succ_self | [`F-ml430-nat-choose-succ-self-e396f6c2`](cards/F-ml430-nat-choose-succ-self-e396f6c2.html) |
| F:ml430-nat-choose-succ-succ-671856b6 | Mathlib v4.30 source proposition Nat.choose_succ_succ | [`F-ml430-nat-choose-succ-succ-671856b6`](cards/F-ml430-nat-choose-succ-succ-671856b6.html) |
| F:ml430-nat-choose-symm-add-e4b68161 | Mathlib v4.30 source proposition Nat.choose_symm_add | [`F-ml430-nat-choose-symm-add-e4b68161`](cards/F-ml430-nat-choose-symm-add-e4b68161.html) |
| F:ml430-nat-choose-symm-of-eq-add-9b5f9a20 | Mathlib v4.30 source proposition Nat.choose_symm_of_eq_add | [`F-ml430-nat-choose-symm-of-eq-add-9b5f9a20`](cards/F-ml430-nat-choose-symm-of-eq-add-9b5f9a20.html) |
| F:ml430-nat-choose-zero-right-1ed2802a | Mathlib v4.30 source proposition Nat.choose_zero_right | [`F-ml430-nat-choose-zero-right-1ed2802a`](cards/F-ml430-nat-choose-zero-right-1ed2802a.html) |
| F:ml430-nat-choose-zero-succ-62c6520b | Mathlib v4.30 source proposition Nat.choose_zero_succ | [`F-ml430-nat-choose-zero-succ-62c6520b`](cards/F-ml430-nat-choose-zero-succ-62c6520b.html) |
| F:ml430-nat-clog-antitone-left-44a87771 | Mathlib v4.30 source proposition Nat.clog_antitone_left | [`F-ml430-nat-clog-antitone-left-44a87771`](cards/F-ml430-nat-clog-antitone-left-44a87771.html) |
| F:ml430-nat-clog-mono-right-8d87a410 | Mathlib v4.30 source proposition Nat.clog_mono_right | [`F-ml430-nat-clog-mono-right-8d87a410`](cards/F-ml430-nat-clog-mono-right-8d87a410.html) |
| F:ml430-nat-clog-monotone-48fe50c6 | Mathlib v4.30 source proposition Nat.clog_monotone | [`F-ml430-nat-clog-monotone-48fe50c6`](cards/F-ml430-nat-clog-monotone-48fe50c6.html) |
| F:ml430-nat-clog-one-left-b496af12 | Mathlib v4.30 source proposition Nat.clog_one_left | [`F-ml430-nat-clog-one-left-b496af12`](cards/F-ml430-nat-clog-one-left-b496af12.html) |
| F:ml430-nat-clog-one-right-1ce3d52f | Mathlib v4.30 source proposition Nat.clog_one_right | [`F-ml430-nat-clog-one-right-1ce3d52f`](cards/F-ml430-nat-clog-one-right-1ce3d52f.html) |
| F:ml430-nat-clog-pos-00852cb8 | Mathlib v4.30 source proposition Nat.clog_pos | [`F-ml430-nat-clog-pos-00852cb8`](cards/F-ml430-nat-clog-pos-00852cb8.html) |
| F:ml430-nat-clog-zero-left-1c61a5bf | Mathlib v4.30 source proposition Nat.clog_zero_left | [`F-ml430-nat-clog-zero-left-1c61a5bf`](cards/F-ml430-nat-clog-zero-left-1c61a5bf.html) |
| F:ml430-nat-clog-zero-right-d42d47b1 | Mathlib v4.30 source proposition Nat.clog_zero_right | [`F-ml430-nat-clog-zero-right-d42d47b1`](cards/F-ml430-nat-clog-zero-right-d42d47b1.html) |
| F:ml430-nat-coprime-add-self-left-5e93448c | Mathlib v4.30 source proposition Nat.coprime_add_self_left | [`F-ml430-nat-coprime-add-self-left-5e93448c`](cards/F-ml430-nat-coprime-add-self-left-5e93448c.html) |
| F:ml430-nat-coprime-add-self-right-c3ed0f45 | Mathlib v4.30 source proposition Nat.coprime_add_self_right | [`F-ml430-nat-coprime-add-self-right-c3ed0f45`](cards/F-ml430-nat-coprime-add-self-right-c3ed0f45.html) |
| F:ml430-nat-coprime-iff-isrelprime-0c08eb25 | Mathlib v4.30 source proposition Nat.coprime_iff_isRelPrime | [`F-ml430-nat-coprime-iff-isrelprime-0c08eb25`](cards/F-ml430-nat-coprime-iff-isrelprime-0c08eb25.html) |
| F:ml430-nat-coprime-odd-of-left-ed80ab44 | Mathlib v4.30 source proposition Nat.Coprime.odd_of_left | [`F-ml430-nat-coprime-odd-of-left-ed80ab44`](cards/F-ml430-nat-coprime-odd-of-left-ed80ab44.html) |
| F:ml430-nat-coprime-odd-of-right-8dc1decc | Mathlib v4.30 source proposition Nat.Coprime.odd_of_right | [`F-ml430-nat-coprime-odd-of-right-8dc1decc`](cards/F-ml430-nat-coprime-odd-of-right-8dc1decc.html) |
| F:ml430-nat-coprime-of-dvd-18fcd09f | Mathlib v4.30 source proposition Nat.Coprime.of_dvd | [`F-ml430-nat-coprime-of-dvd-18fcd09f`](cards/F-ml430-nat-coprime-of-dvd-18fcd09f.html) |
| F:ml430-nat-coprime-of-dvd-6f652673 | Mathlib v4.30 source proposition Nat.coprime_of_dvd' | [`F-ml430-nat-coprime-of-dvd-6f652673`](cards/F-ml430-nat-coprime-of-dvd-6f652673.html) |
| F:ml430-nat-coprime-of-dvd-left-b0e2aa94 | Mathlib v4.30 source proposition Nat.Coprime.of_dvd_left | [`F-ml430-nat-coprime-of-dvd-left-b0e2aa94`](cards/F-ml430-nat-coprime-of-dvd-left-b0e2aa94.html) |
| F:ml430-nat-coprime-of-dvd-right-a640bd56 | Mathlib v4.30 source proposition Nat.Coprime.of_dvd_right | [`F-ml430-nat-coprime-of-dvd-right-a640bd56`](cards/F-ml430-nat-coprime-of-dvd-right-a640bd56.html) |
| F:ml430-nat-coprime-of-lt-minfac-0f79bdba | Mathlib v4.30 source proposition Nat.coprime_of_lt_minFac | [`F-ml430-nat-coprime-of-lt-minfac-0f79bdba`](cards/F-ml430-nat-coprime-of-lt-minfac-0f79bdba.html) |
| F:ml430-nat-coprime-of-lt-prime-1978a919 | Mathlib v4.30 source proposition Nat.coprime_of_lt_prime | [`F-ml430-nat-coprime-of-lt-prime-1978a919`](cards/F-ml430-nat-coprime-of-lt-prime-1978a919.html) |
| F:ml430-nat-coprime-one-left-iff-45945e80 | Mathlib v4.30 source proposition Nat.coprime_one_left_iff | [`F-ml430-nat-coprime-one-left-iff-45945e80`](cards/F-ml430-nat-coprime-one-left-iff-45945e80.html) |
| F:ml430-nat-coprime-one-right-iff-42fed4ce | Mathlib v4.30 source proposition Nat.coprime_one_right_iff | [`F-ml430-nat-coprime-one-right-iff-42fed4ce`](cards/F-ml430-nat-coprime-one-right-iff-42fed4ce.html) |
| F:ml430-nat-coprime-or-dvd-of-prime-65f47114 | Mathlib v4.30 source proposition Nat.coprime_or_dvd_of_prime | [`F-ml430-nat-coprime-or-dvd-of-prime-65f47114`](cards/F-ml430-nat-coprime-or-dvd-of-prime-65f47114.html) |
| F:ml430-nat-coprime-primes-5769049f | Mathlib v4.30 source proposition Nat.coprime_primes | [`F-ml430-nat-coprime-primes-5769049f`](cards/F-ml430-nat-coprime-primes-5769049f.html) |
| F:ml430-nat-coprime-self-add-left-51351fa1 | Mathlib v4.30 source proposition Nat.coprime_self_add_left | [`F-ml430-nat-coprime-self-add-left-51351fa1`](cards/F-ml430-nat-coprime-self-add-left-51351fa1.html) |
| F:ml430-nat-coprime-self-add-right-966e5434 | Mathlib v4.30 source proposition Nat.coprime_self_add_right | [`F-ml430-nat-coprime-self-add-right-966e5434`](cards/F-ml430-nat-coprime-self-add-right-966e5434.html) |
| F:ml430-nat-coprime-symmetric-9b5cfa12 | Mathlib v4.30 source proposition Nat.Coprime.symmetric | [`F-ml430-nat-coprime-symmetric-9b5cfa12`](cards/F-ml430-nat-coprime-symmetric-9b5cfa12.html) |
| F:ml430-nat-coprime-two-left-1b47e7c4 | Mathlib v4.30 source proposition Nat.coprime_two_left | [`F-ml430-nat-coprime-two-left-1b47e7c4`](cards/F-ml430-nat-coprime-two-left-1b47e7c4.html) |
| F:ml430-nat-coprime-two-right-7c5a1850 | Mathlib v4.30 source proposition Nat.coprime_two_right | [`F-ml430-nat-coprime-two-right-7c5a1850`](cards/F-ml430-nat-coprime-two-right-7c5a1850.html) |
| F:ml430-nat-descfactorial-le-2b8cc09a | Mathlib v4.30 source proposition Nat.descFactorial_le | [`F-ml430-nat-descfactorial-le-2b8cc09a`](cards/F-ml430-nat-descfactorial-le-2b8cc09a.html) |
| F:ml430-nat-descfactorial-of-lt-fbcf5d26 | Mathlib v4.30 source proposition Nat.descFactorial_of_lt | [`F-ml430-nat-descfactorial-of-lt-fbcf5d26`](cards/F-ml430-nat-descfactorial-of-lt-fbcf5d26.html) |
| F:ml430-nat-descfactorial-one-d4856d4a | Mathlib v4.30 source proposition Nat.descFactorial_one | [`F-ml430-nat-descfactorial-one-d4856d4a`](cards/F-ml430-nat-descfactorial-one-d4856d4a.html) |
| F:ml430-nat-descfactorial-self-899fc0e0 | Mathlib v4.30 source proposition Nat.descFactorial_self | [`F-ml430-nat-descfactorial-self-899fc0e0`](cards/F-ml430-nat-descfactorial-self-899fc0e0.html) |
| F:ml430-nat-div-dvd-div-left-b56f6f7c | Mathlib v4.30 source proposition Nat.div_dvd_div_left | [`F-ml430-nat-div-dvd-div-left-b56f6f7c`](cards/F-ml430-nat-div-dvd-div-left-b56f6f7c.html) |
| F:ml430-nat-dvd-lcm-of-dvd-left-141a64bb | Mathlib v4.30 source proposition Nat.dvd_lcm_of_dvd_left | [`F-ml430-nat-dvd-lcm-of-dvd-left-141a64bb`](cards/F-ml430-nat-dvd-lcm-of-dvd-left-141a64bb.html) |
| F:ml430-nat-dvd-lcm-of-dvd-right-61a50fc3 | Mathlib v4.30 source proposition Nat.dvd_lcm_of_dvd_right | [`F-ml430-nat-dvd-lcm-of-dvd-right-61a50fc3`](cards/F-ml430-nat-dvd-lcm-of-dvd-right-61a50fc3.html) |
| F:ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b | Mathlib v4.30 source proposition Nat.dvd_of_forall_prime_mul_dvd | [`F-ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b`](cards/F-ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b.html) |
| F:ml430-nat-dvd-of-lcm-left-dvd-d6b2407c | Mathlib v4.30 source proposition Nat.dvd_of_lcm_left_dvd | [`F-ml430-nat-dvd-of-lcm-left-dvd-d6b2407c`](cards/F-ml430-nat-dvd-of-lcm-left-dvd-d6b2407c.html) |
| F:ml430-nat-dvd-of-lcm-right-dvd-61bd1a60 | Mathlib v4.30 source proposition Nat.dvd_of_lcm_right_dvd | [`F-ml430-nat-dvd-of-lcm-right-dvd-61bd1a60`](cards/F-ml430-nat-dvd-of-lcm-right-dvd-61bd1a60.html) |
| F:ml430-nat-even-xor-78a39432 | Mathlib v4.30 source proposition Nat.even_xor | [`F-ml430-nat-even-xor-78a39432`](cards/F-ml430-nat-even-xor-78a39432.html) |
| F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e | Mathlib v4.30 source proposition Nat.exists_mul_mod_eq_gcd | [`F-ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e`](cards/F-ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e.html) |
| F:ml430-nat-exists-mul-self-e73ca9fa | Mathlib v4.30 source proposition Nat.exists_mul_self | [`F-ml430-nat-exists-mul-self-e73ca9fa`](cards/F-ml430-nat-exists-mul-self-e73ca9fa.html) |
| F:ml430-nat-factorial-dvd-ascfactorial-44a4e641 | Mathlib v4.30 source proposition Nat.factorial_dvd_ascFactorial | [`F-ml430-nat-factorial-dvd-ascfactorial-44a4e641`](cards/F-ml430-nat-factorial-dvd-ascfactorial-44a4e641.html) |
| F:ml430-nat-factorial-dvd-descfactorial-bbf6124f | Mathlib v4.30 source proposition Nat.factorial_dvd_descFactorial | [`F-ml430-nat-factorial-dvd-descfactorial-bbf6124f`](cards/F-ml430-nat-factorial-dvd-descfactorial-bbf6124f.html) |
| F:ml430-nat-factorial-dvd-factorial-e9d14845 | Mathlib v4.30 source proposition Nat.factorial_dvd_factorial | [`F-ml430-nat-factorial-dvd-factorial-e9d14845`](cards/F-ml430-nat-factorial-dvd-factorial-e9d14845.html) |
| F:ml430-nat-factorial-le-d0f4a912 | Mathlib v4.30 source proposition Nat.factorial_le | [`F-ml430-nat-factorial-le-d0f4a912`](cards/F-ml430-nat-factorial-le-d0f4a912.html) |
| F:ml430-nat-factorial-lt-of-lt-d6c2125d | Mathlib v4.30 source proposition Nat.factorial_lt_of_lt | [`F-ml430-nat-factorial-lt-of-lt-d6c2125d`](cards/F-ml430-nat-factorial-lt-of-lt-d6c2125d.html) |
| F:ml430-nat-factorial-ne-zero-5fc0b0a1 | Mathlib v4.30 source proposition Nat.factorial_ne_zero | [`F-ml430-nat-factorial-ne-zero-5fc0b0a1`](cards/F-ml430-nat-factorial-ne-zero-5fc0b0a1.html) |
| F:ml430-nat-factorial-pos-f1dd2405 | Mathlib v4.30 source proposition Nat.factorial_pos | [`F-ml430-nat-factorial-pos-f1dd2405`](cards/F-ml430-nat-factorial-pos-f1dd2405.html) |
| F:ml430-nat-fastfib-eq-cde11774 | Mathlib v4.30 source proposition Nat.fastFib_eq | [`F-ml430-nat-fastfib-eq-cde11774`](cards/F-ml430-nat-fastfib-eq-cde11774.html) |
| F:ml430-nat-fib-add-two-strictmono-c1e86d4d | Mathlib v4.30 source proposition Nat.fib_add_two_strictMono | [`F-ml430-nat-fib-add-two-strictmono-c1e86d4d`](cards/F-ml430-nat-fib-add-two-strictmono-c1e86d4d.html) |
| F:ml430-nat-fib-eq-zero-61879073 | Mathlib v4.30 source proposition Nat.fib_eq_zero | [`F-ml430-nat-fib-eq-zero-61879073`](cards/F-ml430-nat-fib-eq-zero-61879073.html) |
| F:ml430-nat-fib-le-fib-succ-d1ef4a3d | Mathlib v4.30 source proposition Nat.fib_le_fib_succ | [`F-ml430-nat-fib-le-fib-succ-d1ef4a3d`](cards/F-ml430-nat-fib-le-fib-succ-d1ef4a3d.html) |
| F:ml430-nat-fib-lt-fib-3582b881 | Mathlib v4.30 source proposition Nat.fib_lt_fib | [`F-ml430-nat-fib-lt-fib-3582b881`](cards/F-ml430-nat-fib-lt-fib-3582b881.html) |
| F:ml430-nat-fib-mono-cc6afe09 | Mathlib v4.30 source proposition Nat.fib_mono | [`F-ml430-nat-fib-mono-cc6afe09`](cards/F-ml430-nat-fib-mono-cc6afe09.html) |
| F:ml430-nat-fib-pos-9e67bd8e | Mathlib v4.30 source proposition Nat.fib_pos | [`F-ml430-nat-fib-pos-9e67bd8e`](cards/F-ml430-nat-fib-pos-9e67bd8e.html) |
| F:ml430-nat-fib-strictmonoon-905810a9 | Mathlib v4.30 source proposition Nat.fib_strictMonoOn | [`F-ml430-nat-fib-strictmonoon-905810a9`](cards/F-ml430-nat-fib-strictmonoon-905810a9.html) |
| F:ml430-nat-land-assoc-ad4775b8 | Mathlib v4.30 source proposition Nat.land_assoc | [`F-ml430-nat-land-assoc-ad4775b8`](cards/F-ml430-nat-land-assoc-ad4775b8.html) |
| F:ml430-nat-land-bit-b9ab7475 | Mathlib v4.30 source proposition Nat.land_bit | [`F-ml430-nat-land-bit-b9ab7475`](cards/F-ml430-nat-land-bit-b9ab7475.html) |
| F:ml430-nat-land-comm-7e6ad72e | Mathlib v4.30 source proposition Nat.land_comm | [`F-ml430-nat-land-comm-7e6ad72e`](cards/F-ml430-nat-land-comm-7e6ad72e.html) |
| F:ml430-nat-ldiff-bit-6be49bb8 | Mathlib v4.30 source proposition Nat.ldiff_bit | [`F-ml430-nat-ldiff-bit-6be49bb8`](cards/F-ml430-nat-ldiff-bit-6be49bb8.html) |
| F:ml430-nat-le-fib-add-one-5284f0bf | Mathlib v4.30 source proposition Nat.le_fib_add_one | [`F-ml430-nat-le-fib-add-one-5284f0bf`](cards/F-ml430-nat-le-fib-add-one-5284f0bf.html) |
| F:ml430-nat-le-fib-self-0cbccb4d | Mathlib v4.30 source proposition Nat.le_fib_self | [`F-ml430-nat-le-fib-self-0cbccb4d`](cards/F-ml430-nat-le-fib-self-0cbccb4d.html) |
| F:ml430-nat-le-sqrt-e6996680 | Mathlib v4.30 source proposition Nat.le_sqrt | [`F-ml430-nat-le-sqrt-e6996680`](cards/F-ml430-nat-le-sqrt-e6996680.html) |
| F:ml430-nat-le-sqrt-of-eq-mul-503c5afe | Mathlib v4.30 source proposition Nat.le_sqrt_of_eq_mul | [`F-ml430-nat-le-sqrt-of-eq-mul-503c5afe`](cards/F-ml430-nat-le-sqrt-of-eq-mul-503c5afe.html) |
| F:ml430-nat-le-three-of-sqrt-eq-one-0c48a868 | Mathlib v4.30 source proposition Nat.le_three_of_sqrt_eq_one | [`F-ml430-nat-le-three-of-sqrt-eq-one-0c48a868`](cards/F-ml430-nat-le-three-of-sqrt-eq-one-0c48a868.html) |
| F:ml430-nat-log-antitone-left-20d1326c | Mathlib v4.30 source proposition Nat.log_antitone_left | [`F-ml430-nat-log-antitone-left-20d1326c`](cards/F-ml430-nat-log-antitone-left-20d1326c.html) |
| F:ml430-nat-log-le-clog-ac8ab2d4 | Mathlib v4.30 source proposition Nat.log_le_clog | [`F-ml430-nat-log-le-clog-ac8ab2d4`](cards/F-ml430-nat-log-le-clog-ac8ab2d4.html) |
| F:ml430-nat-log-le-self-da387172 | Mathlib v4.30 source proposition Nat.log_le_self | [`F-ml430-nat-log-le-self-da387172`](cards/F-ml430-nat-log-le-self-da387172.html) |
| F:ml430-nat-log-lt-self-529f89fa | Mathlib v4.30 source proposition Nat.log_lt_self | [`F-ml430-nat-log-lt-self-529f89fa`](cards/F-ml430-nat-log-lt-self-529f89fa.html) |
| F:ml430-nat-log-mono-right-b8939fee | Mathlib v4.30 source proposition Nat.log_mono_right | [`F-ml430-nat-log-mono-right-b8939fee`](cards/F-ml430-nat-log-mono-right-b8939fee.html) |
| F:ml430-nat-log-monotone-52fad774 | Mathlib v4.30 source proposition Nat.log_monotone | [`F-ml430-nat-log-monotone-52fad774`](cards/F-ml430-nat-log-monotone-52fad774.html) |
| F:ml430-nat-log-of-lt-89eaf42e | Mathlib v4.30 source proposition Nat.log_of_lt | [`F-ml430-nat-log-of-lt-89eaf42e`](cards/F-ml430-nat-log-of-lt-89eaf42e.html) |
| F:ml430-nat-log-one-left-73efc119 | Mathlib v4.30 source proposition Nat.log_one_left | [`F-ml430-nat-log-one-left-73efc119`](cards/F-ml430-nat-log-one-left-73efc119.html) |
| F:ml430-nat-log-one-right-282332ef | Mathlib v4.30 source proposition Nat.log_one_right | [`F-ml430-nat-log-one-right-282332ef`](cards/F-ml430-nat-log-one-right-282332ef.html) |
| F:ml430-nat-log-zero-left-9ec8541e | Mathlib v4.30 source proposition Nat.log_zero_left | [`F-ml430-nat-log-zero-left-9ec8541e`](cards/F-ml430-nat-log-zero-left-9ec8541e.html) |
| F:ml430-nat-log-zero-right-8ea186db | Mathlib v4.30 source proposition Nat.log_zero_right | [`F-ml430-nat-log-zero-right-8ea186db`](cards/F-ml430-nat-log-zero-right-8ea186db.html) |
| F:ml430-nat-log2-eq-log-two-28085932 | Mathlib v4.30 source proposition Nat.log2_eq_log_two | [`F-ml430-nat-log2-eq-log-two-28085932`](cards/F-ml430-nat-log2-eq-log-two-28085932.html) |
| F:ml430-nat-lor-assoc-82c4d0fd | Mathlib v4.30 source proposition Nat.lor_assoc | [`F-ml430-nat-lor-assoc-82c4d0fd`](cards/F-ml430-nat-lor-assoc-82c4d0fd.html) |
| F:ml430-nat-lor-bit-a2f98c7c | Mathlib v4.30 source proposition Nat.lor_bit | [`F-ml430-nat-lor-bit-a2f98c7c`](cards/F-ml430-nat-lor-bit-a2f98c7c.html) |
| F:ml430-nat-lor-comm-2666d7ef | Mathlib v4.30 source proposition Nat.lor_comm | [`F-ml430-nat-lor-comm-2666d7ef`](cards/F-ml430-nat-lor-comm-2666d7ef.html) |
| F:ml430-nat-lt-of-testbit-72f64ab8 | Mathlib v4.30 source proposition Nat.lt_of_testBit | [`F-ml430-nat-lt-of-testbit-72f64ab8`](cards/F-ml430-nat-lt-of-testbit-72f64ab8.html) |
| F:ml430-nat-lt-succ-sqrt-39389df2 | Mathlib v4.30 source proposition Nat.lt_succ_sqrt | [`F-ml430-nat-lt-succ-sqrt-39389df2`](cards/F-ml430-nat-lt-succ-sqrt-39389df2.html) |
| F:ml430-nat-lt-xor-cases-c43a1e85 | Mathlib v4.30 source proposition Nat.lt_xor_cases | [`F-ml430-nat-lt-xor-cases-c43a1e85`](cards/F-ml430-nat-lt-xor-cases-c43a1e85.html) |
| F:ml430-nat-mod-lcm-ee6bdd41 | Mathlib v4.30 source proposition Nat.mod_lcm | [`F-ml430-nat-mod-lcm-ee6bdd41`](cards/F-ml430-nat-mod-lcm-ee6bdd41.html) |
| F:ml430-nat-mod-modeq-436e4c10 | Mathlib v4.30 source proposition Nat.mod_modEq | [`F-ml430-nat-mod-modeq-436e4c10`](cards/F-ml430-nat-mod-modeq-436e4c10.html) |
| F:ml430-nat-modeq-add-left-cancel-e5287cf6 | Mathlib v4.30 source proposition Nat.ModEq.add_left_cancel' | [`F-ml430-nat-modeq-add-left-cancel-e5287cf6`](cards/F-ml430-nat-modeq-add-left-cancel-e5287cf6.html) |
| F:ml430-nat-modeq-add-left-e83f0700 | Mathlib v4.30 source proposition Nat.ModEq.add_left | [`F-ml430-nat-modeq-add-left-e83f0700`](cards/F-ml430-nat-modeq-add-left-e83f0700.html) |
| F:ml430-nat-modeq-add-right-8e2ca0cc | Mathlib v4.30 source proposition Nat.ModEq.add_right | [`F-ml430-nat-modeq-add-right-8e2ca0cc`](cards/F-ml430-nat-modeq-add-right-8e2ca0cc.html) |
| F:ml430-nat-modeq-add-right-cancel-e871facf | Mathlib v4.30 source proposition Nat.ModEq.add_right_cancel' | [`F-ml430-nat-modeq-add-right-cancel-e871facf`](cards/F-ml430-nat-modeq-add-right-cancel-e871facf.html) |
| F:ml430-nat-modeq-comm-24b71e7a | Mathlib v4.30 source proposition Nat.ModEq.comm | [`F-ml430-nat-modeq-comm-24b71e7a`](cards/F-ml430-nat-modeq-comm-24b71e7a.html) |
| F:ml430-nat-modeq-dvd-iff-8f130450 | Mathlib v4.30 source proposition Nat.ModEq.dvd_iff | [`F-ml430-nat-modeq-dvd-iff-8f130450`](cards/F-ml430-nat-modeq-dvd-iff-8f130450.html) |
| F:ml430-nat-modeq-gcd-eq-5167ff4f | Mathlib v4.30 source proposition Nat.ModEq.gcd_eq | [`F-ml430-nat-modeq-gcd-eq-5167ff4f`](cards/F-ml430-nat-modeq-gcd-eq-5167ff4f.html) |
| F:ml430-nat-modeq-of-dvd-d75cc374 | Mathlib v4.30 source proposition Nat.ModEq.of_dvd | [`F-ml430-nat-modeq-of-dvd-d75cc374`](cards/F-ml430-nat-modeq-of-dvd-d75cc374.html) |
| F:ml430-nat-modeq-of-mul-left-88d20bca | Mathlib v4.30 source proposition Nat.ModEq.of_mul_left | [`F-ml430-nat-modeq-of-mul-left-88d20bca`](cards/F-ml430-nat-modeq-of-mul-left-88d20bca.html) |
| F:ml430-nat-modeq-of-mul-right-43078e1c | Mathlib v4.30 source proposition Nat.ModEq.of_mul_right | [`F-ml430-nat-modeq-of-mul-right-43078e1c`](cards/F-ml430-nat-modeq-of-mul-right-43078e1c.html) |
| F:ml430-nat-modeq-one-516d46e8 | Mathlib v4.30 source proposition Nat.modEq_one | [`F-ml430-nat-modeq-one-516d46e8`](cards/F-ml430-nat-modeq-one-516d46e8.html) |
| F:ml430-nat-modeq-refl-d870c8f5 | Mathlib v4.30 source proposition Nat.ModEq.refl | [`F-ml430-nat-modeq-refl-d870c8f5`](cards/F-ml430-nat-modeq-refl-d870c8f5.html) |
| F:ml430-nat-modeq-symm-0a3d4d18 | Mathlib v4.30 source proposition Nat.ModEq.symm | [`F-ml430-nat-modeq-symm-0a3d4d18`](cards/F-ml430-nat-modeq-symm-0a3d4d18.html) |
| F:ml430-nat-modeq-trans-ef9d1c46 | Mathlib v4.30 source proposition Nat.ModEq.trans | [`F-ml430-nat-modeq-trans-ef9d1c46`](cards/F-ml430-nat-modeq-trans-ef9d1c46.html) |
| F:ml430-nat-modulus-modeq-zero-fd9af096 | Mathlib v4.30 source proposition Nat.modulus_modEq_zero | [`F-ml430-nat-modulus-modeq-zero-fd9af096`](cards/F-ml430-nat-modulus-modeq-zero-fd9af096.html) |
| F:ml430-nat-multichoose-one-b210386a | Mathlib v4.30 source proposition Nat.multichoose_one | [`F-ml430-nat-multichoose-one-b210386a`](cards/F-ml430-nat-multichoose-one-b210386a.html) |
| F:ml430-nat-multichoose-one-right-7755072d | Mathlib v4.30 source proposition Nat.multichoose_one_right | [`F-ml430-nat-multichoose-one-right-7755072d`](cards/F-ml430-nat-multichoose-one-right-7755072d.html) |
| F:ml430-nat-multichoose-zero-right-6ef827c8 | Mathlib v4.30 source proposition Nat.multichoose_zero_right | [`F-ml430-nat-multichoose-zero-right-6ef827c8`](cards/F-ml430-nat-multichoose-zero-right-6ef827c8.html) |
| F:ml430-nat-not-coprime-zero-zero-6c4e8dd8 | Mathlib v4.30 source proposition Nat.not_coprime_zero_zero | [`F-ml430-nat-not-coprime-zero-zero-6c4e8dd8`](cards/F-ml430-nat-not-coprime-zero-zero-6c4e8dd8.html) |
| F:ml430-nat-not-prime-of-dvd-of-ne-4ff592c0 | Mathlib v4.30 source proposition Nat.not_prime_of_dvd_of_ne | [`F-ml430-nat-not-prime-of-dvd-of-ne-4ff592c0`](cards/F-ml430-nat-not-prime-of-dvd-of-ne-4ff592c0.html) |
| F:ml430-nat-one-ascfactorial-8bacb017 | Mathlib v4.30 source proposition Nat.one_ascFactorial | [`F-ml430-nat-one-ascfactorial-8bacb017`](cards/F-ml430-nat-one-ascfactorial-8bacb017.html) |
| F:ml430-nat-prime-dvd-iff-not-coprime-77854741 | Mathlib v4.30 source proposition Nat.Prime.dvd_iff_not_coprime | [`F-ml430-nat-prime-dvd-iff-not-coprime-77854741`](cards/F-ml430-nat-prime-dvd-iff-not-coprime-77854741.html) |
| F:ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439 | Mathlib v4.30 source proposition Nat.Prime.dvd_mul_of_dvd_ne | [`F-ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439`](cards/F-ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439.html) |
| F:ml430-nat-prime-dvd-of-dvd-pow-e76f834a | Mathlib v4.30 source proposition Nat.Prime.dvd_of_dvd_pow | [`F-ml430-nat-prime-dvd-of-dvd-pow-e76f834a`](cards/F-ml430-nat-prime-dvd-of-dvd-pow-e76f834a.html) |
| F:ml430-nat-prime-even-iff-d068ec82 | Mathlib v4.30 source proposition Nat.Prime.even_iff | [`F-ml430-nat-prime-even-iff-d068ec82`](cards/F-ml430-nat-prime-even-iff-d068ec82.html) |
| F:ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786 | Mathlib v4.30 source proposition Nat.Prime.five_le_of_ne_two_of_ne_three | [`F-ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786`](cards/F-ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786.html) |
| F:ml430-nat-prime-not-dvd-mul-cb3a915e | Mathlib v4.30 source proposition Nat.Prime.not_dvd_mul | [`F-ml430-nat-prime-not-dvd-mul-cb3a915e`](cards/F-ml430-nat-prime-not-dvd-mul-cb3a915e.html) |
| F:ml430-nat-prime-odd-of-ne-two-91e1195f | Mathlib v4.30 source proposition Nat.Prime.odd_of_ne_two | [`F-ml430-nat-prime-odd-of-ne-two-91e1195f`](cards/F-ml430-nat-prime-odd-of-ne-two-91e1195f.html) |
| F:ml430-nat-prime-pred-pos-4e67ac4c | Mathlib v4.30 source proposition Nat.Prime.pred_pos | [`F-ml430-nat-prime-pred-pos-4e67ac4c`](cards/F-ml430-nat-prime-pred-pos-4e67ac4c.html) |
| F:ml430-nat-self-le-factorial-cfdffc69 | Mathlib v4.30 source proposition Nat.self_le_factorial | [`F-ml430-nat-self-le-factorial-cfdffc69`](cards/F-ml430-nat-self-le-factorial-cfdffc69.html) |
| F:ml430-nat-sqrt-eq-79ae8eae | Mathlib v4.30 source proposition Nat.sqrt_eq | [`F-ml430-nat-sqrt-eq-79ae8eae`](cards/F-ml430-nat-sqrt-eq-79ae8eae.html) |
| F:ml430-nat-sqrt-eq-c036815b | Mathlib v4.30 source proposition Nat.sqrt_eq' | [`F-ml430-nat-sqrt-eq-c036815b`](cards/F-ml430-nat-sqrt-eq-c036815b.html) |
| F:ml430-nat-sqrt-eq-zero-53666a3b | Mathlib v4.30 source proposition Nat.sqrt_eq_zero | [`F-ml430-nat-sqrt-eq-zero-53666a3b`](cards/F-ml430-nat-sqrt-eq-zero-53666a3b.html) |
| F:ml430-nat-sqrt-le-7918582b | Mathlib v4.30 source proposition Nat.sqrt_le | [`F-ml430-nat-sqrt-le-7918582b`](cards/F-ml430-nat-sqrt-le-7918582b.html) |
| F:ml430-nat-sqrt-le-self-1ed5eb85 | Mathlib v4.30 source proposition Nat.sqrt_le_self | [`F-ml430-nat-sqrt-le-self-1ed5eb85`](cards/F-ml430-nat-sqrt-le-self-1ed5eb85.html) |
| F:ml430-nat-sqrt-le-sqrt-6e2bfc47 | Mathlib v4.30 source proposition Nat.sqrt_le_sqrt | [`F-ml430-nat-sqrt-le-sqrt-6e2bfc47`](cards/F-ml430-nat-sqrt-le-sqrt-6e2bfc47.html) |
| F:ml430-nat-sqrt-lt-4909537f | Mathlib v4.30 source proposition Nat.sqrt_lt | [`F-ml430-nat-sqrt-lt-4909537f`](cards/F-ml430-nat-sqrt-lt-4909537f.html) |
| F:ml430-nat-sqrt-lt-self-ff7a155a | Mathlib v4.30 source proposition Nat.sqrt_lt_self | [`F-ml430-nat-sqrt-lt-self-ff7a155a`](cards/F-ml430-nat-sqrt-lt-self-ff7a155a.html) |
| F:ml430-nat-sqrt-pos-f75e5114 | Mathlib v4.30 source proposition Nat.sqrt_pos | [`F-ml430-nat-sqrt-pos-f75e5114`](cards/F-ml430-nat-sqrt-pos-f75e5114.html) |
| F:ml430-nat-sqrt-succ-le-succ-sqrt-6b041183 | Mathlib v4.30 source proposition Nat.sqrt_succ_le_succ_sqrt | [`F-ml430-nat-sqrt-succ-le-succ-sqrt-6b041183`](cards/F-ml430-nat-sqrt-succ-le-succ-sqrt-6b041183.html) |
| F:ml430-nat-succ-pred-prime-4feb123f | Mathlib v4.30 source proposition Nat.succ_pred_prime | [`F-ml430-nat-succ-pred-prime-4feb123f`](cards/F-ml430-nat-succ-pred-prime-4feb123f.html) |
| F:ml430-nat-testbit-eq-inth-ffa07392 | Mathlib v4.30 source proposition Nat.testBit_eq_inth | [`F-ml430-nat-testbit-eq-inth-ffa07392`](cards/F-ml430-nat-testbit-eq-inth-ffa07392.html) |
| F:ml430-nat-testbit-land-dfef7ca4 | Mathlib v4.30 source proposition Nat.testBit_land | [`F-ml430-nat-testbit-land-dfef7ca4`](cards/F-ml430-nat-testbit-land-dfef7ca4.html) |
| F:ml430-nat-testbit-ldiff-16f94162 | Mathlib v4.30 source proposition Nat.testBit_ldiff | [`F-ml430-nat-testbit-ldiff-16f94162`](cards/F-ml430-nat-testbit-ldiff-16f94162.html) |
| F:ml430-nat-testbit-lor-7644e067 | Mathlib v4.30 source proposition Nat.testBit_lor | [`F-ml430-nat-testbit-lor-7644e067`](cards/F-ml430-nat-testbit-lor-7644e067.html) |
| F:ml430-nat-zero-ascfactorial-af4fcdca | Mathlib v4.30 source proposition Nat.zero_ascFactorial | [`F-ml430-nat-zero-ascfactorial-af4fcdca`](cards/F-ml430-nat-zero-ascfactorial-af4fcdca.html) |
| F:ml430-nat-zero-of-testbit-eq-false-e244c9a1 | Mathlib v4.30 source proposition Nat.zero_of_testBit_eq_false | [`F-ml430-nat-zero-of-testbit-eq-false-e244c9a1`](cards/F-ml430-nat-zero-of-testbit-eq-false-e244c9a1.html) |

Source: `python3 render/producers-py/facts_to_docir.py` (exit 0), 341 input(s) hashed.

</details>

---

Rendered from Doc-IR by `axeyum-render`. Epoch 1787338967 (2026-08-21T19:02:47Z, source `commit`), commit `733126c0f351f0931f7eaf0b4f5f9f569f3aef44`.
