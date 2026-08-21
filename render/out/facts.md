# Fact atlas: the whole ledger

*324 facts, 135 depends_on edges*

Every fact in `artifacts/facts/` (324 facts, 135 `depends_on` edges), both of its status axes, and the dependency graph they form. Every status here is copied from the ledger; nothing infers or upgrades one, and the badge column is a conservative mapping that can only weaken a ledger value. Facts established here but not settled in the literature are listed first: that disagreement is the output this project exists to produce.

Established here, not settled in the literature

| fact | title | epistemic | external | card |
| --- | --- | --- | --- | --- |
| F:rado-r4-a5-b3 | The four-colour Rado number of 5(x-y) = 3z is 625 | computed | open | cards/F-rado-r4-a5-b3.doc.json |
| F:rado-r4-a5-b4 | The four-colour Rado number of 5(x-y) = 4z is 741 | computed | open | cards/F-rado-r4-a5-b4.doc.json |

Source: `python3 render/producers-py/facts_to_docir.py` (exit 0), 324 input(s) hashed.

The `depends_on` relation over these 324 facts has 135 edges and falls into 210 connected components: 37 with more than one fact (151 facts between them, the largest holding 31), and 173 single facts that nothing in the ledger depends on and that depend on nothing in it.

One drawing of all 324 would be 324 nodes wide and four layers deep -- a strip some thirty thousand pixels across, which at page width is a smear. So each component is drawn on its own below, largest first, and the 173 unconnected facts appear in the index table rather than as a row of dots. The index is the complete list either way: every fact is in it.

*Figure (Dependency graph of 31 facts with 49 edges) -- data:*

```json
{
  "edges": [
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
    }
  ],
  "figure_type": "dep-graph",
  "nodes": [
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
    }
  ],
  "rankdir": "TB"
}
```

*Component 1 of 37: 31 facts, 49 edges. An edge runs from the dependent fact to the fact it rests on.*

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
      "group": "unproved",
      "href": "cards/F-ml430-nat-fib-coprime-fib-succ-162fc738.doc.json",
      "id": "F:ml430-nat-fib-coprime-fib-succ-162fc738",
      "label": "ml430-nat-fib-coprime-fib-succ",
      "status": "open",
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
      "group": "unproved",
      "href": "cards/F-ml430-nat-gcd-fib-add-self-5a92d5e3.doc.json",
      "id": "F:ml430-nat-gcd-fib-add-self-5a92d5e3",
      "label": "ml430-nat-gcd-fib-add-self",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.gcd_fib_add_self"
    }
  ],
  "rankdir": "TB"
}
```

*Component 2 of 37: 9 facts, 8 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 3 of 37: 7 facts, 7 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 4 of 37: 6 facts, 5 edges. An edge runs from the dependent fact to the fact it rests on.*

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
      "group": "unproved",
      "href": "cards/F-ml430-nat-fib-dvd-f80f3de1.doc.json",
      "id": "F:ml430-nat-fib-dvd-f80f3de1",
      "label": "ml430-nat-fib-dvd",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.fib_dvd"
    },
    {
      "group": "unproved",
      "href": "cards/F-ml430-nat-fib-gcd-d1d98407.doc.json",
      "id": "F:ml430-nat-fib-gcd-d1d98407",
      "label": "ml430-nat-fib-gcd",
      "status": "open",
      "tooltip": "Mathlib v4.30 source proposition Nat.fib_gcd"
    }
  ],
  "rankdir": "TB"
}
```

*Component 5 of 37: 5 facts, 4 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 6 of 37: 5 facts, 4 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 7 of 37: 5 facts, 4 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 8 of 37: 5 facts, 4 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 9 of 37: 5 facts, 4 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 10 of 37: 5 facts, 4 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 11 of 37: 4 facts, 3 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 12 of 37: 4 facts, 3 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 13 of 37: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 14 of 37: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 15 of 37: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 16 of 37: 3 facts, 3 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 17 of 37: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 18 of 37: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 19 of 37: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 20 of 37: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 21 of 37: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

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

*Component 22 of 37: 3 facts, 2 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 23 (2 facts)</summary>

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

*Component 23 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 24 (2 facts)</summary>

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

*Component 24 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 25 (2 facts)</summary>

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

*Component 25 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 26 (2 facts)</summary>

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

*Component 26 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 27 (2 facts)</summary>

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

*Component 27 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 28 (2 facts)</summary>

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

*Component 28 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 29 (2 facts)</summary>

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

*Component 29 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 30 (2 facts)</summary>

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

*Component 30 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 31 (2 facts)</summary>

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

*Component 31 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 32 (2 facts)</summary>

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

*Component 32 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 33 (2 facts)</summary>

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

*Component 33 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 34 (2 facts)</summary>

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

*Component 34 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 35 (2 facts)</summary>

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

*Component 35 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 36 (2 facts)</summary>

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

*Component 36 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

<details>
<summary>Component 37 (2 facts)</summary>

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

*Component 37 of 37: 2 facts, 1 edges. An edge runs from the dependent fact to the fact it rests on.*

</details>

Ledger spread over the documented facts

| axis | value | facts |
| --- | --- | --- |
| epistemic_status | computed | 2 |
| epistemic_status | conjectured | 3 |
| epistemic_status | open | 217 |
| epistemic_status | proved | 99 |
| epistemic_status | refuted | 3 |
| external_status | (absent) | 8 |
| external_status | open | 5 |
| external_status | proved | 296 |
| external_status | refuted | 3 |
| external_status | unknown | 12 |
| proof_route | (none) | 220 |
| proof_route | cas-certificate | 19 |
| proof_route | imported-kernel-lean | 5 |
| proof_route | kernel-lean | 43 |
| proof_route | search-certificate | 12 |
| proof_route | smt-clausal | 9 |
| proof_route | smt-term-level | 16 |
| formal.language | cas-term | 9 |
| formal.language | lean4 | 47 |
| formal.language | lean4-surface | 214 |
| formal.language | smtlib2 | 54 |

Source: `python3 render/producers-py/facts_to_docir.py` (exit 0), 324 input(s) hashed.

Fact index

| fact | title | language | fragment | proof_route | epistemic | external | badge | flag | evidence | checked | card |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| F:affirming-the-consequent | Affirming the consequent is a valid inference | smtlib2 | QF_UF | search-certificate | refuted | refuted | refuted | - | 1 | 1 | cards/F-affirming-the-consequent.doc.json |
| F:alternating-binomial-row-sum-zero | The alternating binomial row sum vanishes | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-alternating-binomial-row-sum-zero.doc.json |
| F:apery-numbers-recurrence | The Apery numbers satisfy Apery's second-order recurrence | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-apery-numbers-recurrence.doc.json |
| F:barber-no-such-barber | No barber shaves exactly those who do not shave themselves | smtlib2 | UF | smt-clausal | proved | proved | proved | - | 1 | 1 | cards/F-barber-no-such-barber.doc.json |
| F:bcnf-decomposition-lossless-not-dependency-preserving | The BCNF repair of the street/city/zip schema rejoins exactly and cannot enforce its own dependency; two other splits lose information | smtlib2 | QF_UF | search-certificate | proved | unclassified | proved | - | 3 | 3 | cards/F-bcnf-decomposition-lossless-not-dependency-preserving.doc.json |
| F:binomial-row-sum-two-power | The binomial row sum is a power of two | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-binomial-row-sum-two-power.doc.json |
| F:bool-and-comm | Boolean conjunction is commutative | lean4 | Bool | imported-kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-bool-and-comm.doc.json |
| F:chu-vandermonde-convolution | Chu-Vandermonde convolution, closed form at symbolic parameters | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-chu-vandermonde-convolution.doc.json |
| F:chu-vandermonde-convolution-recurrence | The Chu-Vandermonde convolution satisfies a first-order recurrence in p | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-chu-vandermonde-convolution-recurrence.doc.json |
| F:collatz-reaches-one | Collatz conjecture | lean4 | none | - | conjectured | open | open | - | 0 | 0 | cards/F-collatz-reaches-one.doc.json |
| F:conjunctive-query-containment-homomorphism-certified | Six conjunctive-query containment questions decided by homomorphism and by counterexample database, agreeing across three independent routes | smtlib2 | none | search-certificate | proved | unclassified | proved | - | 3 | 3 | cards/F-conjunctive-query-containment-homomorphism-certified.doc.json |
| F:continuum-hypothesis-independent | The continuum hypothesis is independent of ZFC | smtlib2 | none | - | open | proved | open | import-backlog | 0 | 0 | cards/F-continuum-hypothesis-independent.doc.json |
| F:contraposition | A conditional is equivalent to its contrapositive | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-contraposition.doc.json |
| F:cross-binomial-row-sum | The cross binomial row sum equals a central binomial coefficient | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-cross-binomial-row-sum.doc.json |
| F:de-morgan-laws | De Morgan's laws for conjunction and disjunction | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-de-morgan-laws.doc.json |
| F:double-negation-elimination | Double negation elimination | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-double-negation-elimination.doc.json |
| F:ex-falso-quodlibet | A contradiction entails everything | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-ex-falso-quodlibet.doc.json |
| F:excluded-middle | Law of excluded middle | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-excluded-middle.doc.json |
| F:excluded-middle-not-intuitionistic | Excluded middle is not derivable in intuitionistic propositional logic | smtlib2 | none | - | open | proved | open | import-backlog | 0 | 0 | cards/F-excluded-middle-not-intuitionistic.doc.json |
| F:exportation | Exportation: the propositional form of the deduction theorem | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-exportation.doc.json |
| F:fermat-last-theorem | Fermat's Last Theorem | smtlib2 | none | - | open | proved | open | import-backlog | 0 | 0 | cards/F-fermat-last-theorem.doc.json |
| F:fol-validity-undecidable | Validity in first-order logic is undecidable | smtlib2 | none | - | open | proved | open | import-backlog | 0 | 0 | cards/F-fol-validity-undecidable.doc.json |
| F:fp16-add-monotone-rne | binary16 addition under roundNearestTiesToEven is monotone in its first argument | smtlib2 | QF_FP | - | open | proved | open | import-backlog | 0 | 0 | cards/F-fp16-add-monotone-rne.doc.json |
| F:fp16-bf16-roundtrip-not-identity | Narrowing binary16 to bfloat16 and back is the identity | smtlib2 | QF_FP | search-certificate | refuted | refuted | refuted | - | 3 | 3 | cards/F-fp16-bf16-roundtrip-not-identity.doc.json |
| F:fp16-doubling-add-equals-mul-two | In binary16 under roundNearestTiesToEven, x+x and 2*x are the same value | smtlib2 | QF_FP | smt-clausal | proved | proved | proved | - | 2 | 2 | cards/F-fp16-doubling-add-equals-mul-two.doc.json |
| F:fp16-fp32-roundtrip-identity | Widening binary16 to binary32 and narrowing back is the identity | smtlib2 | QF_FP | smt-clausal | proved | proved | proved | - | 2 | 2 | cards/F-fp16-fp32-roundtrip-identity.doc.json |
| F:fp32-doubling-add-equals-mul-two | In binary32 under roundNearestTiesToEven, x+x and 2*x are the same value | smtlib2 | QF_FP | smt-clausal | proved | proved | proved | - | 2 | 2 | cards/F-fp32-doubling-add-equals-mul-two.doc.json |
| F:fp8-add-monotone-rne | fp8 E5M2 addition under roundNearestTiesToEven is monotone in its first argument | smtlib2 | QF_FP | smt-clausal | proved | proved | proved | - | 2 | 2 | cards/F-fp8-add-monotone-rne.doc.json |
| F:fp8-add-not-associative | fp8 E5M2 addition under roundNearestTiesToEven is associative | smtlib2 | QF_FP | search-certificate | refuted | refuted | refuted | - | 3 | 3 | cards/F-fp8-add-not-associative.doc.json |
| F:franel-numbers-recurrence | The Franel numbers satisfy a second-order recurrence | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-franel-numbers-recurrence.doc.json |
| F:geometry-centroid-divides-medians | the medians of a non-degenerate triangle meet at (A+B+C)/3 | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-geometry-centroid-divides-medians.doc.json |
| F:geometry-euler-line | Euler's line: the circumcentre, the centroid and the orthocentre of a non-degenerate triangle are collinear | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 3 | 3 | cards/F-geometry-euler-line.doc.json |
| F:geometry-medians-concurrent | the medians of a triangle are concurrent | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-geometry-medians-concurrent.doc.json |
| F:geometry-orthocentre-altitudes-concurrent | the altitudes of a triangle are concurrent | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-geometry-orthocentre-altitudes-concurrent.doc.json |
| F:geometry-pappus-hexagon | Pappus's hexagon theorem: the three cross intersections are collinear, and ONE non-degeneracy condition suffices | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 3 | 3 | cards/F-geometry-pappus-hexagon.doc.json |
| F:geometry-parallelogram-diagonals-bisect | the diagonals of a non-flat parallelogram bisect each other | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-geometry-parallelogram-diagonals-bisect.doc.json |
| F:geometry-rhombus-diagonals-perpendicular | the diagonals of a non-flat rhombus are perpendicular | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-geometry-rhombus-diagonals-perpendicular.doc.json |
| F:geometry-simson-line | Simson's line: the feet of the perpendiculars from a concyclic point are collinear, and the minimal condition set depends on the FIELD rather than on the budget | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 3 | 3 | cards/F-geometry-simson-line.doc.json |
| F:geometry-thales-right-angle-in-semicircle | Thales' theorem: an angle inscribed in a semicircle is right | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-geometry-thales-right-angle-in-semicircle.doc.json |
| F:geometry-varignon-midpoint-parallelogram | Varignon's theorem: the midpoint quadrilateral is a parallelogram | smtlib2 | NRA | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-geometry-varignon-midpoint-parallelogram.doc.json |
| F:godel-first-incompleteness | Godel's first incompleteness theorem | smtlib2 | none | - | open | proved | open | import-backlog | 0 | 0 | cards/F-godel-first-incompleteness.doc.json |
| F:goldbach-strong | Strong Goldbach conjecture | lean4 | Nat | - | conjectured | open | open | - | 0 | 0 | cards/F-goldbach-strong.doc.json |
| F:int-add-assoc | Addition on the integers is associative | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-int-add-assoc.doc.json |
| F:int-add-comm | Addition on the integers is commutative | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-int-add-comm.doc.json |
| F:int-add-le-add | The order on the integers is compatible with addition | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-int-add-le-add.doc.json |
| F:int-add-lt-add-of-le-of-lt | A strict integer inequality survives addition of a non-strict one | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-int-add-lt-add-of-le-of-lt.doc.json |
| F:int-add-neg | Every integer has an additive inverse | lean4 | Int | kernel-lean | proved | proved | proved | - | 3 | 3 | cards/F-int-add-neg.doc.json |
| F:int-equality-is-decidable | Equality of integers is decidable | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-int-equality-is-decidable.doc.json |
| F:int-euclidean-decomposition | Euclidean decomposition over the integers is derived, not assumed | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-int-euclidean-decomposition.doc.json |
| F:int-left-distrib | Multiplication distributes over addition on the integers | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-int-left-distrib.doc.json |
| F:int-mul-assoc | Multiplication on the integers is associative | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-int-mul-assoc.doc.json |
| F:int-mul-comm | Multiplication on the integers is commutative | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-int-mul-comm.doc.json |
| F:int-no-integer-strictly-between-zero-and-one | No integer lies strictly between zero and one | lean4 | Int | kernel-lean | proved | proved | proved | - | 3 | 3 | cards/F-int-no-integer-strictly-between-zero-and-one.doc.json |
| F:int-sq-nonneg | Every integer square is nonnegative | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-int-sq-nonneg.doc.json |
| F:int-sub-nat-nat-elim | The integer borrow has exactly two outcomes, and each is witnessed by a natural | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-int-sub-nat-nat-elim.doc.json |
| F:int-sub-nat-nat-shift | The normalized integer difference is invariant under a common shift | lean4 | Int | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-int-sub-nat-nat-shift.doc.json |
| F:list-nil-append | The empty list is a left identity for append | lean4 | List | imported-kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-list-nil-append.doc.json |
| F:loadplan-hazmat-iis | Fourteen rows of a 90-row outbound load plan are an irreducible infeasible subsystem | smtlib2 | LIA | search-certificate | proved | unclassified | proved | - | 2 | 2 | cards/F-loadplan-hazmat-iis.doc.json |
| F:ml430-int-add-modeq-left-ee732b5b | Mathlib v4.30 source proposition Int.add_modEq_left | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-add-modeq-left-ee732b5b.doc.json |
| F:ml430-int-add-modeq-right-e58108ee | Mathlib v4.30 source proposition Int.add_modEq_right | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-add-modeq-right-e58108ee.doc.json |
| F:ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b | Mathlib v4.30 source proposition Int.dvd_of_dvd_mul_left_of_gcd_one | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b.doc.json |
| F:ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0 | Mathlib v4.30 source proposition Int.dvd_of_dvd_mul_right_of_gcd_one | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0.doc.json |
| F:ml430-int-fib-add-181b6a2c | Mathlib v4.30 source proposition Int.fib_add | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-fib-add-181b6a2c.doc.json |
| F:ml430-int-fib-add-one-33f1b748 | Mathlib v4.30 source proposition Int.fib_add_one | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-fib-add-one-33f1b748.doc.json |
| F:ml430-int-fib-add-two-739358dd | Mathlib v4.30 source proposition Int.fib_add_two | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-fib-add-two-739358dd.doc.json |
| F:ml430-int-fib-dvd-ffb3c5c1 | Mathlib v4.30 source proposition Int.fib_dvd | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-fib-dvd-ffb3c5c1.doc.json |
| F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d | Mathlib v4.30 source proposition Int.fib_eq_fib_add_two_sub_fib_add_one | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d.doc.json |
| F:ml430-int-fib-eq-zero-8193c7cb | Mathlib v4.30 source proposition Int.fib_eq_zero | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-fib-eq-zero-8193c7cb.doc.json |
| F:ml430-int-fib-gcd-3a8bfdec | Mathlib v4.30 source proposition Int.fib_gcd | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-fib-gcd-3a8bfdec.doc.json |
| F:ml430-int-fib-natcast-d5886be4 | Mathlib v4.30 source proposition Int.fib_natCast | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-fib-natcast-d5886be4.doc.json |
| F:ml430-int-fib-neg-b4021d37 | Mathlib v4.30 source proposition Int.fib_neg | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-fib-neg-b4021d37.doc.json |
| F:ml430-int-fib-of-nonneg-438018c5 | Mathlib v4.30 source proposition Int.fib_of_nonneg | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-fib-of-nonneg-438018c5.doc.json |
| F:ml430-int-fib-of-odd-66560495 | Mathlib v4.30 source proposition Int.fib_of_odd | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-fib-of-odd-66560495.doc.json |
| F:ml430-int-fib-two-mul-0e70f3dd | Mathlib v4.30 source proposition Int.fib_two_mul | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-fib-two-mul-0e70f3dd.doc.json |
| F:ml430-int-fib-two-mul-add-one-pos-8977f65f | Mathlib v4.30 source proposition Int.fib_two_mul_add_one_pos | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-fib-two-mul-add-one-pos-8977f65f.doc.json |
| F:ml430-int-fib-two-mul-add-two-0ba4a948 | Mathlib v4.30 source proposition Int.fib_two_mul_add_two | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-fib-two-mul-add-two-0ba4a948.doc.json |
| F:ml430-int-gcd-div-5e01872f | Mathlib v4.30 source proposition Int.gcd_div | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-gcd-div-5e01872f.doc.json |
| F:ml430-int-gcd-div-gcd-div-gcd-2db608dc | Mathlib v4.30 source proposition Int.gcd_div_gcd_div_gcd | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-gcd-div-gcd-div-gcd-2db608dc.doc.json |
| F:ml430-int-gcd-eq-gcd-ab-63005aef | Mathlib v4.30 source proposition Int.gcd_eq_gcd_ab | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-gcd-eq-gcd-ab-63005aef.doc.json |
| F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-left-8533eb82 | Mathlib v4.30 source proposition Int.gcd_eq_one_of_gcd_mul_right_eq_one_left | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-left-8533eb82.doc.json |
| F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-right-a9b19222 | Mathlib v4.30 source proposition Int.gcd_eq_one_of_gcd_mul_right_eq_one_right | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-right-a9b19222.doc.json |
| F:ml430-int-gcd-fib-73bdafc2 | Mathlib v4.30 source proposition Int.gcd_fib | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-gcd-fib-73bdafc2.doc.json |
| F:ml430-int-gcd-greatest-5b31c5fe | Mathlib v4.30 source proposition Int.gcd_greatest | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-gcd-greatest-5b31c5fe.doc.json |
| F:ml430-int-mod-modeq-6bec7847 | Mathlib v4.30 source proposition Int.mod_modEq | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-mod-modeq-6bec7847.doc.json |
| F:ml430-int-modeq-add-left-6e17c69a | Mathlib v4.30 source proposition Int.ModEq.add_left | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modeq-add-left-6e17c69a.doc.json |
| F:ml430-int-modeq-add-left-cancel-062ad5fe | Mathlib v4.30 source proposition Int.ModEq.add_left_cancel' | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modeq-add-left-cancel-062ad5fe.doc.json |
| F:ml430-int-modeq-comm-1e4bcc07 | Mathlib v4.30 source proposition Int.modEq_comm | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modeq-comm-1e4bcc07.doc.json |
| F:ml430-int-modeq-dvd-iff-b7ffeff8 | Mathlib v4.30 source proposition Int.ModEq.dvd_iff | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modeq-dvd-iff-b7ffeff8.doc.json |
| F:ml430-int-modeq-neg-d6ff57b6 | Mathlib v4.30 source proposition Int.modEq_neg | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modeq-neg-d6ff57b6.doc.json |
| F:ml430-int-modeq-neg-f649f6c5 | Mathlib v4.30 source proposition Int.ModEq.neg | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modeq-neg-f649f6c5.doc.json |
| F:ml430-int-modeq-of-dvd-b9c41fce | Mathlib v4.30 source proposition Int.ModEq.of_dvd | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modeq-of-dvd-b9c41fce.doc.json |
| F:ml430-int-modeq-of-mul-left-c4ccd51e | Mathlib v4.30 source proposition Int.ModEq.of_mul_left | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modeq-of-mul-left-c4ccd51e.doc.json |
| F:ml430-int-modeq-of-mul-right-c92b7bf0 | Mathlib v4.30 source proposition Int.ModEq.of_mul_right | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modeq-of-mul-right-c92b7bf0.doc.json |
| F:ml430-int-modeq-one-01d9de39 | Mathlib v4.30 source proposition Int.modEq_one | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modeq-one-01d9de39.doc.json |
| F:ml430-int-modeq-refl-30e15520 | Mathlib v4.30 source proposition Int.ModEq.refl | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modeq-refl-30e15520.doc.json |
| F:ml430-int-modeq-sub-3148f130 | Mathlib v4.30 source proposition Int.modEq_sub | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modeq-sub-3148f130.doc.json |
| F:ml430-int-modeq-symm-984a6e67 | Mathlib v4.30 source proposition Int.ModEq.symm | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modeq-symm-984a6e67.doc.json |
| F:ml430-int-modeq-trans-6d7863e0 | Mathlib v4.30 source proposition Int.ModEq.trans | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modeq-trans-6d7863e0.doc.json |
| F:ml430-int-modulus-modeq-zero-5b57a898 | Mathlib v4.30 source proposition Int.modulus_modEq_zero | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-modulus-modeq-zero-5b57a898.doc.json |
| F:ml430-int-ne-zero-of-gcd-f71f00df | Mathlib v4.30 source proposition Int.ne_zero_of_gcd | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-ne-zero-of-gcd-f71f00df.doc.json |
| F:ml430-int-neg-modeq-neg-30d98479 | Mathlib v4.30 source proposition Int.neg_modEq_neg | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-int-neg-modeq-neg-30d98479.doc.json |
| F:ml430-mutation-1432b2277cf2cc26c1d11cd6 | Outcome-blind mutation of Nat.fib_eq_zero | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | cards/F-ml430-mutation-1432b2277cf2cc26c1d11cd6.doc.json |
| F:ml430-mutation-2086302b3a338591b3179871 | Outcome-blind mutation of Nat.sqrt_le_self | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | cards/F-ml430-mutation-2086302b3a338591b3179871.doc.json |
| F:ml430-mutation-48fe130e2b8eadb6f626b66f | Outcome-blind mutation of Int.ne_zero_of_gcd | lean4-surface | Int | - | open | unknown | open | - | 0 | 0 | cards/F-ml430-mutation-48fe130e2b8eadb6f626b66f.doc.json |
| F:ml430-mutation-5179f333b8333ecff8adc223 | Outcome-blind mutation of Nat.Prime.pred_pos | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | cards/F-ml430-mutation-5179f333b8333ecff8adc223.doc.json |
| F:ml430-mutation-7afa5ec620720a1501bf349d | Outcome-blind mutation of Nat.factorial_ne_zero | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | cards/F-ml430-mutation-7afa5ec620720a1501bf349d.doc.json |
| F:ml430-mutation-a6dd1759bce60d820292e107 | Outcome-blind mutation of Nat.lor_comm | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | cards/F-ml430-mutation-a6dd1759bce60d820292e107.doc.json |
| F:ml430-mutation-aabb80b1f89f0c5847364692 | Outcome-blind mutation of Int.fib_eq_zero | lean4-surface | Int | - | open | unknown | open | - | 0 | 0 | cards/F-ml430-mutation-aabb80b1f89f0c5847364692.doc.json |
| F:ml430-mutation-aca37b68d3cdf06f0127def9 | Outcome-blind mutation of Int.ModEq.symm | lean4-surface | Int | - | open | unknown | open | - | 0 | 0 | cards/F-ml430-mutation-aca37b68d3cdf06f0127def9.doc.json |
| F:ml430-mutation-c20db9b4c60b816ce738bdf2 | Outcome-blind mutation of Nat.not_coprime_zero_zero | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | cards/F-ml430-mutation-c20db9b4c60b816ce738bdf2.doc.json |
| F:ml430-mutation-c86940b52af8159ca9b381d6 | Outcome-blind mutation of Nat.ModEq.symm | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | cards/F-ml430-mutation-c86940b52af8159ca9b381d6.doc.json |
| F:ml430-mutation-e8583599cfae2d40cefae3f0 | Outcome-blind mutation of Nat.log_le_self | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | cards/F-ml430-mutation-e8583599cfae2d40cefae3f0.doc.json |
| F:ml430-mutation-edb05acf07d9ef3f9f8232fc | Outcome-blind mutation of Nat.choose_self | lean4-surface | Nat | - | open | unknown | open | - | 0 | 0 | cards/F-ml430-mutation-edb05acf07d9ef3f9f8232fc.doc.json |
| F:ml430-nat-add-modeq-left-e3b1fba9 | Mathlib v4.30 source proposition Nat.add_modEq_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-add-modeq-left-e3b1fba9.doc.json |
| F:ml430-nat-add-modeq-right-e2f11f21 | Mathlib v4.30 source proposition Nat.add_modEq_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-add-modeq-right-e2f11f21.doc.json |
| F:ml430-nat-ascfactorial-zero-fd183202 | Mathlib v4.30 source proposition Nat.ascFactorial_zero | lean4-surface | Nat | kernel-lean | proved | proved | proved | - | 1 | 1 | cards/F-ml430-nat-ascfactorial-zero-fd183202.doc.json |
| F:ml430-nat-bitwise-bit-4c4b28a8 | Mathlib v4.30 source proposition Nat.bitwise_bit' | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-bitwise-bit-4c4b28a8.doc.json |
| F:ml430-nat-bitwise-comm-1a273bae | Mathlib v4.30 source proposition Nat.bitwise_comm | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-bitwise-comm-1a273bae.doc.json |
| F:ml430-nat-bitwise-swap-7175e90e | Mathlib v4.30 source proposition Nat.bitwise_swap | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-bitwise-swap-7175e90e.doc.json |
| F:ml430-nat-choose-eq-zero-of-lt-92ebab29 | Mathlib v4.30 source proposition Nat.choose_eq_zero_of_lt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-choose-eq-zero-of-lt-92ebab29.doc.json |
| F:ml430-nat-choose-le-add-9c463139 | Mathlib v4.30 source proposition Nat.choose_le_add | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-choose-le-add-9c463139.doc.json |
| F:ml430-nat-choose-le-choose-907b5042 | Mathlib v4.30 source proposition Nat.choose_le_choose | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-choose-le-choose-907b5042.doc.json |
| F:ml430-nat-choose-le-succ-62ae968b | Mathlib v4.30 source proposition Nat.choose_le_succ | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-choose-le-succ-62ae968b.doc.json |
| F:ml430-nat-choose-mono-a1af9c18 | Mathlib v4.30 source proposition Nat.choose_mono | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-choose-mono-a1af9c18.doc.json |
| F:ml430-nat-choose-ne-zero-49c3d3cb | Mathlib v4.30 source proposition Nat.choose_ne_zero | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-choose-ne-zero-49c3d3cb.doc.json |
| F:ml430-nat-choose-one-right-7eda8e39 | Mathlib v4.30 source proposition Nat.choose_one_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-choose-one-right-7eda8e39.doc.json |
| F:ml430-nat-choose-self-25bb9fb8 | Mathlib v4.30 source proposition Nat.choose_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-choose-self-25bb9fb8.doc.json |
| F:ml430-nat-choose-succ-self-e396f6c2 | Mathlib v4.30 source proposition Nat.choose_succ_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-choose-succ-self-e396f6c2.doc.json |
| F:ml430-nat-choose-succ-succ-671856b6 | Mathlib v4.30 source proposition Nat.choose_succ_succ | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-choose-succ-succ-671856b6.doc.json |
| F:ml430-nat-choose-symm-add-e4b68161 | Mathlib v4.30 source proposition Nat.choose_symm_add | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-choose-symm-add-e4b68161.doc.json |
| F:ml430-nat-choose-symm-of-eq-add-9b5f9a20 | Mathlib v4.30 source proposition Nat.choose_symm_of_eq_add | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-choose-symm-of-eq-add-9b5f9a20.doc.json |
| F:ml430-nat-choose-zero-right-1ed2802a | Mathlib v4.30 source proposition Nat.choose_zero_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-choose-zero-right-1ed2802a.doc.json |
| F:ml430-nat-choose-zero-succ-62c6520b | Mathlib v4.30 source proposition Nat.choose_zero_succ | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-choose-zero-succ-62c6520b.doc.json |
| F:ml430-nat-clog-antitone-left-44a87771 | Mathlib v4.30 source proposition Nat.clog_antitone_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-clog-antitone-left-44a87771.doc.json |
| F:ml430-nat-clog-mono-right-8d87a410 | Mathlib v4.30 source proposition Nat.clog_mono_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-clog-mono-right-8d87a410.doc.json |
| F:ml430-nat-clog-monotone-48fe50c6 | Mathlib v4.30 source proposition Nat.clog_monotone | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-clog-monotone-48fe50c6.doc.json |
| F:ml430-nat-clog-one-left-b496af12 | Mathlib v4.30 source proposition Nat.clog_one_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-clog-one-left-b496af12.doc.json |
| F:ml430-nat-clog-one-right-1ce3d52f | Mathlib v4.30 source proposition Nat.clog_one_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-clog-one-right-1ce3d52f.doc.json |
| F:ml430-nat-clog-pos-00852cb8 | Mathlib v4.30 source proposition Nat.clog_pos | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-clog-pos-00852cb8.doc.json |
| F:ml430-nat-clog-zero-left-1c61a5bf | Mathlib v4.30 source proposition Nat.clog_zero_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-clog-zero-left-1c61a5bf.doc.json |
| F:ml430-nat-clog-zero-right-d42d47b1 | Mathlib v4.30 source proposition Nat.clog_zero_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-clog-zero-right-d42d47b1.doc.json |
| F:ml430-nat-coprime-add-self-left-5e93448c | Mathlib v4.30 source proposition Nat.coprime_add_self_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-add-self-left-5e93448c.doc.json |
| F:ml430-nat-coprime-add-self-right-c3ed0f45 | Mathlib v4.30 source proposition Nat.coprime_add_self_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-add-self-right-c3ed0f45.doc.json |
| F:ml430-nat-coprime-iff-isrelprime-0c08eb25 | Mathlib v4.30 source proposition Nat.coprime_iff_isRelPrime | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-iff-isrelprime-0c08eb25.doc.json |
| F:ml430-nat-coprime-odd-of-left-ed80ab44 | Mathlib v4.30 source proposition Nat.Coprime.odd_of_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-odd-of-left-ed80ab44.doc.json |
| F:ml430-nat-coprime-odd-of-right-8dc1decc | Mathlib v4.30 source proposition Nat.Coprime.odd_of_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-odd-of-right-8dc1decc.doc.json |
| F:ml430-nat-coprime-of-dvd-18fcd09f | Mathlib v4.30 source proposition Nat.Coprime.of_dvd | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-of-dvd-18fcd09f.doc.json |
| F:ml430-nat-coprime-of-dvd-6f652673 | Mathlib v4.30 source proposition Nat.coprime_of_dvd' | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-of-dvd-6f652673.doc.json |
| F:ml430-nat-coprime-of-dvd-left-b0e2aa94 | Mathlib v4.30 source proposition Nat.Coprime.of_dvd_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-of-dvd-left-b0e2aa94.doc.json |
| F:ml430-nat-coprime-of-dvd-right-a640bd56 | Mathlib v4.30 source proposition Nat.Coprime.of_dvd_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-of-dvd-right-a640bd56.doc.json |
| F:ml430-nat-coprime-of-lt-minfac-0f79bdba | Mathlib v4.30 source proposition Nat.coprime_of_lt_minFac | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-of-lt-minfac-0f79bdba.doc.json |
| F:ml430-nat-coprime-of-lt-prime-1978a919 | Mathlib v4.30 source proposition Nat.coprime_of_lt_prime | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-of-lt-prime-1978a919.doc.json |
| F:ml430-nat-coprime-one-left-iff-45945e80 | Mathlib v4.30 source proposition Nat.coprime_one_left_iff | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-one-left-iff-45945e80.doc.json |
| F:ml430-nat-coprime-one-right-iff-42fed4ce | Mathlib v4.30 source proposition Nat.coprime_one_right_iff | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-one-right-iff-42fed4ce.doc.json |
| F:ml430-nat-coprime-or-dvd-of-prime-65f47114 | Mathlib v4.30 source proposition Nat.coprime_or_dvd_of_prime | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-or-dvd-of-prime-65f47114.doc.json |
| F:ml430-nat-coprime-primes-5769049f | Mathlib v4.30 source proposition Nat.coprime_primes | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-primes-5769049f.doc.json |
| F:ml430-nat-coprime-self-add-left-51351fa1 | Mathlib v4.30 source proposition Nat.coprime_self_add_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-self-add-left-51351fa1.doc.json |
| F:ml430-nat-coprime-self-add-right-966e5434 | Mathlib v4.30 source proposition Nat.coprime_self_add_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-self-add-right-966e5434.doc.json |
| F:ml430-nat-coprime-symmetric-9b5cfa12 | Mathlib v4.30 source proposition Nat.Coprime.symmetric | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-symmetric-9b5cfa12.doc.json |
| F:ml430-nat-coprime-two-left-1b47e7c4 | Mathlib v4.30 source proposition Nat.coprime_two_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-two-left-1b47e7c4.doc.json |
| F:ml430-nat-coprime-two-right-7c5a1850 | Mathlib v4.30 source proposition Nat.coprime_two_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-coprime-two-right-7c5a1850.doc.json |
| F:ml430-nat-descfactorial-le-2b8cc09a | Mathlib v4.30 source proposition Nat.descFactorial_le | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-descfactorial-le-2b8cc09a.doc.json |
| F:ml430-nat-descfactorial-of-lt-fbcf5d26 | Mathlib v4.30 source proposition Nat.descFactorial_of_lt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-descfactorial-of-lt-fbcf5d26.doc.json |
| F:ml430-nat-descfactorial-one-d4856d4a | Mathlib v4.30 source proposition Nat.descFactorial_one | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-descfactorial-one-d4856d4a.doc.json |
| F:ml430-nat-descfactorial-self-899fc0e0 | Mathlib v4.30 source proposition Nat.descFactorial_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-descfactorial-self-899fc0e0.doc.json |
| F:ml430-nat-descfactorial-zero-966b01df | Mathlib v4.30 source proposition Nat.descFactorial_zero | lean4-surface | Nat | kernel-lean | proved | proved | proved | - | 1 | 1 | cards/F-ml430-nat-descfactorial-zero-966b01df.doc.json |
| F:ml430-nat-div-dvd-div-left-b56f6f7c | Mathlib v4.30 source proposition Nat.div_dvd_div_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-div-dvd-div-left-b56f6f7c.doc.json |
| F:ml430-nat-dvd-lcm-of-dvd-left-141a64bb | Mathlib v4.30 source proposition Nat.dvd_lcm_of_dvd_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-dvd-lcm-of-dvd-left-141a64bb.doc.json |
| F:ml430-nat-dvd-lcm-of-dvd-right-61a50fc3 | Mathlib v4.30 source proposition Nat.dvd_lcm_of_dvd_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-dvd-lcm-of-dvd-right-61a50fc3.doc.json |
| F:ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b | Mathlib v4.30 source proposition Nat.dvd_of_forall_prime_mul_dvd | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b.doc.json |
| F:ml430-nat-dvd-of-lcm-left-dvd-d6b2407c | Mathlib v4.30 source proposition Nat.dvd_of_lcm_left_dvd | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-dvd-of-lcm-left-dvd-d6b2407c.doc.json |
| F:ml430-nat-dvd-of-lcm-right-dvd-61bd1a60 | Mathlib v4.30 source proposition Nat.dvd_of_lcm_right_dvd | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-dvd-of-lcm-right-dvd-61bd1a60.doc.json |
| F:ml430-nat-even-xor-78a39432 | Mathlib v4.30 source proposition Nat.even_xor | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-even-xor-78a39432.doc.json |
| F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e | Mathlib v4.30 source proposition Nat.exists_mul_mod_eq_gcd | lean4-surface | Int | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e.doc.json |
| F:ml430-nat-exists-mul-self-e73ca9fa | Mathlib v4.30 source proposition Nat.exists_mul_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-exists-mul-self-e73ca9fa.doc.json |
| F:ml430-nat-factorial-dvd-ascfactorial-44a4e641 | Mathlib v4.30 source proposition Nat.factorial_dvd_ascFactorial | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-factorial-dvd-ascfactorial-44a4e641.doc.json |
| F:ml430-nat-factorial-dvd-descfactorial-bbf6124f | Mathlib v4.30 source proposition Nat.factorial_dvd_descFactorial | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-factorial-dvd-descfactorial-bbf6124f.doc.json |
| F:ml430-nat-factorial-dvd-factorial-e9d14845 | Mathlib v4.30 source proposition Nat.factorial_dvd_factorial | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-factorial-dvd-factorial-e9d14845.doc.json |
| F:ml430-nat-factorial-le-d0f4a912 | Mathlib v4.30 source proposition Nat.factorial_le | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-factorial-le-d0f4a912.doc.json |
| F:ml430-nat-factorial-lt-of-lt-d6c2125d | Mathlib v4.30 source proposition Nat.factorial_lt_of_lt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-factorial-lt-of-lt-d6c2125d.doc.json |
| F:ml430-nat-factorial-ne-zero-5fc0b0a1 | Mathlib v4.30 source proposition Nat.factorial_ne_zero | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-factorial-ne-zero-5fc0b0a1.doc.json |
| F:ml430-nat-factorial-pos-f1dd2405 | Mathlib v4.30 source proposition Nat.factorial_pos | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-factorial-pos-f1dd2405.doc.json |
| F:ml430-nat-fastfib-eq-cde11774 | Mathlib v4.30 source proposition Nat.fastFib_eq | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-fastfib-eq-cde11774.doc.json |
| F:ml430-nat-fib-add-two-b86e0c82 | Mathlib v4.30 source proposition Nat.fib_add_two | lean4-surface | Nat | kernel-lean | proved | proved | proved | - | 1 | 1 | cards/F-ml430-nat-fib-add-two-b86e0c82.doc.json |
| F:ml430-nat-fib-add-two-strictmono-c1e86d4d | Mathlib v4.30 source proposition Nat.fib_add_two_strictMono | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-fib-add-two-strictmono-c1e86d4d.doc.json |
| F:ml430-nat-fib-coprime-fib-succ-162fc738 | Mathlib v4.30 source proposition Nat.fib_coprime_fib_succ | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-fib-coprime-fib-succ-162fc738.doc.json |
| F:ml430-nat-fib-dvd-f80f3de1 | Mathlib v4.30 source proposition Nat.fib_dvd | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-fib-dvd-f80f3de1.doc.json |
| F:ml430-nat-fib-eq-zero-61879073 | Mathlib v4.30 source proposition Nat.fib_eq_zero | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-fib-eq-zero-61879073.doc.json |
| F:ml430-nat-fib-gcd-d1d98407 | Mathlib v4.30 source proposition Nat.fib_gcd | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-fib-gcd-d1d98407.doc.json |
| F:ml430-nat-fib-le-fib-succ-d1ef4a3d | Mathlib v4.30 source proposition Nat.fib_le_fib_succ | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-fib-le-fib-succ-d1ef4a3d.doc.json |
| F:ml430-nat-fib-lt-fib-3582b881 | Mathlib v4.30 source proposition Nat.fib_lt_fib | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-fib-lt-fib-3582b881.doc.json |
| F:ml430-nat-fib-mono-cc6afe09 | Mathlib v4.30 source proposition Nat.fib_mono | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-fib-mono-cc6afe09.doc.json |
| F:ml430-nat-fib-pos-9e67bd8e | Mathlib v4.30 source proposition Nat.fib_pos | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-fib-pos-9e67bd8e.doc.json |
| F:ml430-nat-fib-strictmonoon-905810a9 | Mathlib v4.30 source proposition Nat.fib_strictMonoOn | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-fib-strictmonoon-905810a9.doc.json |
| F:ml430-nat-gcd-fib-add-self-5a92d5e3 | Mathlib v4.30 source proposition Nat.gcd_fib_add_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-gcd-fib-add-self-5a92d5e3.doc.json |
| F:ml430-nat-gcd-greatest-0a04214a | Mathlib v4.30 source proposition Nat.gcd_greatest | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-gcd-greatest-0a04214a.doc.json |
| F:ml430-nat-land-assoc-ad4775b8 | Mathlib v4.30 source proposition Nat.land_assoc | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-land-assoc-ad4775b8.doc.json |
| F:ml430-nat-land-bit-b9ab7475 | Mathlib v4.30 source proposition Nat.land_bit | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-land-bit-b9ab7475.doc.json |
| F:ml430-nat-land-comm-7e6ad72e | Mathlib v4.30 source proposition Nat.land_comm | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-land-comm-7e6ad72e.doc.json |
| F:ml430-nat-ldiff-bit-6be49bb8 | Mathlib v4.30 source proposition Nat.ldiff_bit | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-ldiff-bit-6be49bb8.doc.json |
| F:ml430-nat-le-fib-add-one-5284f0bf | Mathlib v4.30 source proposition Nat.le_fib_add_one | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-le-fib-add-one-5284f0bf.doc.json |
| F:ml430-nat-le-fib-self-0cbccb4d | Mathlib v4.30 source proposition Nat.le_fib_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-le-fib-self-0cbccb4d.doc.json |
| F:ml430-nat-le-sqrt-e6996680 | Mathlib v4.30 source proposition Nat.le_sqrt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-le-sqrt-e6996680.doc.json |
| F:ml430-nat-le-sqrt-of-eq-mul-503c5afe | Mathlib v4.30 source proposition Nat.le_sqrt_of_eq_mul | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-le-sqrt-of-eq-mul-503c5afe.doc.json |
| F:ml430-nat-le-three-of-sqrt-eq-one-0c48a868 | Mathlib v4.30 source proposition Nat.le_three_of_sqrt_eq_one | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-le-three-of-sqrt-eq-one-0c48a868.doc.json |
| F:ml430-nat-log-antitone-left-20d1326c | Mathlib v4.30 source proposition Nat.log_antitone_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-log-antitone-left-20d1326c.doc.json |
| F:ml430-nat-log-le-clog-ac8ab2d4 | Mathlib v4.30 source proposition Nat.log_le_clog | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-log-le-clog-ac8ab2d4.doc.json |
| F:ml430-nat-log-le-self-da387172 | Mathlib v4.30 source proposition Nat.log_le_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-log-le-self-da387172.doc.json |
| F:ml430-nat-log-lt-self-529f89fa | Mathlib v4.30 source proposition Nat.log_lt_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-log-lt-self-529f89fa.doc.json |
| F:ml430-nat-log-mono-right-b8939fee | Mathlib v4.30 source proposition Nat.log_mono_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-log-mono-right-b8939fee.doc.json |
| F:ml430-nat-log-monotone-52fad774 | Mathlib v4.30 source proposition Nat.log_monotone | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-log-monotone-52fad774.doc.json |
| F:ml430-nat-log-of-lt-89eaf42e | Mathlib v4.30 source proposition Nat.log_of_lt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-log-of-lt-89eaf42e.doc.json |
| F:ml430-nat-log-one-left-73efc119 | Mathlib v4.30 source proposition Nat.log_one_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-log-one-left-73efc119.doc.json |
| F:ml430-nat-log-one-right-282332ef | Mathlib v4.30 source proposition Nat.log_one_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-log-one-right-282332ef.doc.json |
| F:ml430-nat-log-zero-left-9ec8541e | Mathlib v4.30 source proposition Nat.log_zero_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-log-zero-left-9ec8541e.doc.json |
| F:ml430-nat-log-zero-right-8ea186db | Mathlib v4.30 source proposition Nat.log_zero_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-log-zero-right-8ea186db.doc.json |
| F:ml430-nat-log2-eq-log-two-28085932 | Mathlib v4.30 source proposition Nat.log2_eq_log_two | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-log2-eq-log-two-28085932.doc.json |
| F:ml430-nat-lor-assoc-82c4d0fd | Mathlib v4.30 source proposition Nat.lor_assoc | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-lor-assoc-82c4d0fd.doc.json |
| F:ml430-nat-lor-bit-a2f98c7c | Mathlib v4.30 source proposition Nat.lor_bit | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-lor-bit-a2f98c7c.doc.json |
| F:ml430-nat-lor-comm-2666d7ef | Mathlib v4.30 source proposition Nat.lor_comm | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-lor-comm-2666d7ef.doc.json |
| F:ml430-nat-lt-of-testbit-72f64ab8 | Mathlib v4.30 source proposition Nat.lt_of_testBit | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-lt-of-testbit-72f64ab8.doc.json |
| F:ml430-nat-lt-succ-sqrt-39389df2 | Mathlib v4.30 source proposition Nat.lt_succ_sqrt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-lt-succ-sqrt-39389df2.doc.json |
| F:ml430-nat-lt-xor-cases-c43a1e85 | Mathlib v4.30 source proposition Nat.lt_xor_cases | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-lt-xor-cases-c43a1e85.doc.json |
| F:ml430-nat-mod-lcm-ee6bdd41 | Mathlib v4.30 source proposition Nat.mod_lcm | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-mod-lcm-ee6bdd41.doc.json |
| F:ml430-nat-mod-modeq-436e4c10 | Mathlib v4.30 source proposition Nat.mod_modEq | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-mod-modeq-436e4c10.doc.json |
| F:ml430-nat-modeq-add-left-cancel-e5287cf6 | Mathlib v4.30 source proposition Nat.ModEq.add_left_cancel' | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modeq-add-left-cancel-e5287cf6.doc.json |
| F:ml430-nat-modeq-add-left-e83f0700 | Mathlib v4.30 source proposition Nat.ModEq.add_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modeq-add-left-e83f0700.doc.json |
| F:ml430-nat-modeq-add-right-8e2ca0cc | Mathlib v4.30 source proposition Nat.ModEq.add_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modeq-add-right-8e2ca0cc.doc.json |
| F:ml430-nat-modeq-add-right-cancel-e871facf | Mathlib v4.30 source proposition Nat.ModEq.add_right_cancel' | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modeq-add-right-cancel-e871facf.doc.json |
| F:ml430-nat-modeq-comm-24b71e7a | Mathlib v4.30 source proposition Nat.ModEq.comm | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modeq-comm-24b71e7a.doc.json |
| F:ml430-nat-modeq-dvd-iff-8f130450 | Mathlib v4.30 source proposition Nat.ModEq.dvd_iff | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modeq-dvd-iff-8f130450.doc.json |
| F:ml430-nat-modeq-gcd-eq-5167ff4f | Mathlib v4.30 source proposition Nat.ModEq.gcd_eq | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modeq-gcd-eq-5167ff4f.doc.json |
| F:ml430-nat-modeq-of-dvd-d75cc374 | Mathlib v4.30 source proposition Nat.ModEq.of_dvd | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modeq-of-dvd-d75cc374.doc.json |
| F:ml430-nat-modeq-of-mul-left-88d20bca | Mathlib v4.30 source proposition Nat.ModEq.of_mul_left | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modeq-of-mul-left-88d20bca.doc.json |
| F:ml430-nat-modeq-of-mul-right-43078e1c | Mathlib v4.30 source proposition Nat.ModEq.of_mul_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modeq-of-mul-right-43078e1c.doc.json |
| F:ml430-nat-modeq-one-516d46e8 | Mathlib v4.30 source proposition Nat.modEq_one | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modeq-one-516d46e8.doc.json |
| F:ml430-nat-modeq-refl-d870c8f5 | Mathlib v4.30 source proposition Nat.ModEq.refl | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modeq-refl-d870c8f5.doc.json |
| F:ml430-nat-modeq-symm-0a3d4d18 | Mathlib v4.30 source proposition Nat.ModEq.symm | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modeq-symm-0a3d4d18.doc.json |
| F:ml430-nat-modeq-trans-ef9d1c46 | Mathlib v4.30 source proposition Nat.ModEq.trans | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modeq-trans-ef9d1c46.doc.json |
| F:ml430-nat-modulus-modeq-zero-fd9af096 | Mathlib v4.30 source proposition Nat.modulus_modEq_zero | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-modulus-modeq-zero-fd9af096.doc.json |
| F:ml430-nat-multichoose-one-b210386a | Mathlib v4.30 source proposition Nat.multichoose_one | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-multichoose-one-b210386a.doc.json |
| F:ml430-nat-multichoose-one-right-7755072d | Mathlib v4.30 source proposition Nat.multichoose_one_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-multichoose-one-right-7755072d.doc.json |
| F:ml430-nat-multichoose-zero-right-6ef827c8 | Mathlib v4.30 source proposition Nat.multichoose_zero_right | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-multichoose-zero-right-6ef827c8.doc.json |
| F:ml430-nat-not-coprime-zero-zero-6c4e8dd8 | Mathlib v4.30 source proposition Nat.not_coprime_zero_zero | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-not-coprime-zero-zero-6c4e8dd8.doc.json |
| F:ml430-nat-not-prime-of-dvd-of-ne-4ff592c0 | Mathlib v4.30 source proposition Nat.not_prime_of_dvd_of_ne | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-not-prime-of-dvd-of-ne-4ff592c0.doc.json |
| F:ml430-nat-one-ascfactorial-8bacb017 | Mathlib v4.30 source proposition Nat.one_ascFactorial | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-one-ascfactorial-8bacb017.doc.json |
| F:ml430-nat-prime-dvd-iff-not-coprime-77854741 | Mathlib v4.30 source proposition Nat.Prime.dvd_iff_not_coprime | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-prime-dvd-iff-not-coprime-77854741.doc.json |
| F:ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439 | Mathlib v4.30 source proposition Nat.Prime.dvd_mul_of_dvd_ne | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439.doc.json |
| F:ml430-nat-prime-dvd-of-dvd-pow-e76f834a | Mathlib v4.30 source proposition Nat.Prime.dvd_of_dvd_pow | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-prime-dvd-of-dvd-pow-e76f834a.doc.json |
| F:ml430-nat-prime-even-iff-d068ec82 | Mathlib v4.30 source proposition Nat.Prime.even_iff | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-prime-even-iff-d068ec82.doc.json |
| F:ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786 | Mathlib v4.30 source proposition Nat.Prime.five_le_of_ne_two_of_ne_three | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786.doc.json |
| F:ml430-nat-prime-not-dvd-mul-cb3a915e | Mathlib v4.30 source proposition Nat.Prime.not_dvd_mul | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-prime-not-dvd-mul-cb3a915e.doc.json |
| F:ml430-nat-prime-odd-of-ne-two-91e1195f | Mathlib v4.30 source proposition Nat.Prime.odd_of_ne_two | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-prime-odd-of-ne-two-91e1195f.doc.json |
| F:ml430-nat-prime-pred-pos-4e67ac4c | Mathlib v4.30 source proposition Nat.Prime.pred_pos | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-prime-pred-pos-4e67ac4c.doc.json |
| F:ml430-nat-self-le-factorial-cfdffc69 | Mathlib v4.30 source proposition Nat.self_le_factorial | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-self-le-factorial-cfdffc69.doc.json |
| F:ml430-nat-sqrt-eq-79ae8eae | Mathlib v4.30 source proposition Nat.sqrt_eq | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-sqrt-eq-79ae8eae.doc.json |
| F:ml430-nat-sqrt-eq-c036815b | Mathlib v4.30 source proposition Nat.sqrt_eq' | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-sqrt-eq-c036815b.doc.json |
| F:ml430-nat-sqrt-eq-zero-53666a3b | Mathlib v4.30 source proposition Nat.sqrt_eq_zero | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-sqrt-eq-zero-53666a3b.doc.json |
| F:ml430-nat-sqrt-le-7918582b | Mathlib v4.30 source proposition Nat.sqrt_le | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-sqrt-le-7918582b.doc.json |
| F:ml430-nat-sqrt-le-self-1ed5eb85 | Mathlib v4.30 source proposition Nat.sqrt_le_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-sqrt-le-self-1ed5eb85.doc.json |
| F:ml430-nat-sqrt-le-sqrt-6e2bfc47 | Mathlib v4.30 source proposition Nat.sqrt_le_sqrt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-sqrt-le-sqrt-6e2bfc47.doc.json |
| F:ml430-nat-sqrt-lt-4909537f | Mathlib v4.30 source proposition Nat.sqrt_lt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-sqrt-lt-4909537f.doc.json |
| F:ml430-nat-sqrt-lt-self-ff7a155a | Mathlib v4.30 source proposition Nat.sqrt_lt_self | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-sqrt-lt-self-ff7a155a.doc.json |
| F:ml430-nat-sqrt-pos-f75e5114 | Mathlib v4.30 source proposition Nat.sqrt_pos | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-sqrt-pos-f75e5114.doc.json |
| F:ml430-nat-sqrt-succ-le-succ-sqrt-6b041183 | Mathlib v4.30 source proposition Nat.sqrt_succ_le_succ_sqrt | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-sqrt-succ-le-succ-sqrt-6b041183.doc.json |
| F:ml430-nat-succ-pred-prime-4feb123f | Mathlib v4.30 source proposition Nat.succ_pred_prime | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-succ-pred-prime-4feb123f.doc.json |
| F:ml430-nat-testbit-eq-inth-ffa07392 | Mathlib v4.30 source proposition Nat.testBit_eq_inth | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-testbit-eq-inth-ffa07392.doc.json |
| F:ml430-nat-testbit-land-dfef7ca4 | Mathlib v4.30 source proposition Nat.testBit_land | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-testbit-land-dfef7ca4.doc.json |
| F:ml430-nat-testbit-ldiff-16f94162 | Mathlib v4.30 source proposition Nat.testBit_ldiff | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-testbit-ldiff-16f94162.doc.json |
| F:ml430-nat-testbit-lor-7644e067 | Mathlib v4.30 source proposition Nat.testBit_lor | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-testbit-lor-7644e067.doc.json |
| F:ml430-nat-zero-ascfactorial-af4fcdca | Mathlib v4.30 source proposition Nat.zero_ascFactorial | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-zero-ascfactorial-af4fcdca.doc.json |
| F:ml430-nat-zero-of-testbit-eq-false-e244c9a1 | Mathlib v4.30 source proposition Nat.zero_of_testBit_eq_false | lean4-surface | Nat | - | open | proved | open | import-backlog | 0 | 0 | cards/F-ml430-nat-zero-of-testbit-eq-false-e244c9a1.doc.json |
| F:modus-ponens-valid | Modus ponens is a valid inference | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-modus-ponens-valid.doc.json |
| F:modus-tollens-valid | Modus tollens is a valid inference | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-modus-tollens-valid.doc.json |
| F:nand-functional-completeness | NAND defines negation, conjunction and disjunction | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-nand-functional-completeness.doc.json |
| F:nat-add-assoc | Addition on the naturals is associative | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-add-assoc.doc.json |
| F:nat-add-comm | Addition on the naturals is commutative | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-add-comm.doc.json |
| F:nat-add-sub-cancel-left | Subtraction undoes addition on the naturals | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-add-sub-cancel-left.doc.json |
| F:nat-add-zero | Zero is a right identity for addition on the naturals | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-add-zero.doc.json |
| F:nat-div-mod-exists | Division with remainder always exists for a positive divisor | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-div-mod-exists.doc.json |
| F:nat-div-mod-unique | The quotient and remainder of a division are unique | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-div-mod-unique.doc.json |
| F:nat-dvd-add | A common divisor of two numbers divides their sum | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-dvd-add.doc.json |
| F:nat-dvd-gcd-iff | The gcd is exactly the common divisors' upper bound | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-dvd-gcd-iff.doc.json |
| F:nat-euclid-lemma | Euclid's lemma: a prime dividing a product divides a factor | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-euclid-lemma.doc.json |
| F:nat-exists-prime-dvd | Every natural number at least 2 has a prime divisor | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-exists-prime-dvd.doc.json |
| F:nat-exists-prime-gt | There is no largest prime | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-exists-prime-gt.doc.json |
| F:nat-gcd-bezout | Bezout's identity holds for the natural gcd | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-gcd-bezout.doc.json |
| F:nat-gcd-succ | The Euclidean algorithm's descent step is correct | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-gcd-succ.doc.json |
| F:nat-le-refl | The order on the naturals is reflexive | lean4 | Nat | imported-kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-le-refl.doc.json |
| F:nat-le-succ | Every natural number is below its successor | lean4 | Nat | imported-kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-le-succ.doc.json |
| F:nat-left-distrib | Multiplication distributes over addition on the left | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-left-distrib.doc.json |
| F:nat-mod-eq-mul | Congruences may be multiplied | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-mod-eq-mul.doc.json |
| F:nat-mul-assoc | Multiplication on the naturals is associative | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-mul-assoc.doc.json |
| F:nat-mul-comm | Multiplication on the naturals is commutative | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-mul-comm.doc.json |
| F:nat-mul-one | One is a right identity for multiplication on the naturals | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-mul-one.doc.json |
| F:nat-pow-add | The first index law: powers add over a product | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-pow-add.doc.json |
| F:nat-succ-add | Nat succ_add | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-succ-add.doc.json |
| F:nat-zero-add | Nat zero_add | lean4 | Nat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-nat-zero-add.doc.json |
| F:no-integer-square-is-minus-one | No integer squares to minus one | smtlib2 | QF_NIA | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-no-integer-square-is-minus-one.doc.json |
| F:no-self-negating-proposition | No proposition is equivalent to its own negation | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-no-self-negating-proposition.doc.json |
| F:ordered-ring-farkas-refutation | A reconstructed Farkas refutation holds in every ordered commutative ring, and rests on no axiom | lean4 | QF_LRA | kernel-lean | proved | proved | proved | - | 4 | 4 | cards/F-ordered-ring-farkas-refutation.doc.json |
| F:orders-candidate-keys-and-normal-forms | An order-line schema has exactly two candidate keys, is not in BCNF, and is not in 3NF -- with every subset of the attributes examined | smtlib2 | QF_UF | search-certificate | proved | unclassified | proved | - | 3 | 3 | cards/F-orders-candidate-keys-and-normal-forms.doc.json |
| F:orders-fd-implication-certified | Two implied and two unimplied functional dependencies on a committed order-line schema, each with a replayable certificate | smtlib2 | QF_UF | search-certificate | proved | unclassified | proved | - | 3 | 3 | cards/F-orders-fd-implication-certified.doc.json |
| F:peirce-law | Peirce's law | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-peirce-law.doc.json |
| F:prop-excluded-middle-classical | Excluded middle for propositions, as Lean proves it | lean4 | Prop | imported-kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-prop-excluded-middle-classical.doc.json |
| F:quantifier-negation-duality | Negation exchanges the two quantifiers | smtlib2 | UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-quantifier-negation-duality.doc.json |
| F:rado-r4-a5-b3 | The four-colour Rado number of 5(x-y) = 3z is 625 | smtlib2 | QF_BV | search-certificate | computed | open | evidence | novel | 3 | 3 | cards/F-rado-r4-a5-b3.doc.json |
| F:rado-r4-a5-b4 | The four-colour Rado number of 5(x-y) = 4z is 741 | smtlib2 | QF_BV | search-certificate | computed | open | evidence | novel | 1 | 1 | cards/F-rado-r4-a5-b4.doc.json |
| F:rat-add-neg-inverse | Rational addition renormalises and negation is an additive inverse | lean4 | Rat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-rat-add-neg-inverse.doc.json |
| F:rat-mul-renormalises | Rational multiplication renormalises | lean4 | Rat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-rat-mul-renormalises.doc.json |
| F:rat-normalize-reduces | The rational smart constructor normalises | lean4 | Rat | kernel-lean | proved | proved | proved | - | 2 | 2 | cards/F-rat-normalize-reduces.doc.json |
| F:resolution-rule-sound | The binary propositional resolution rule is sound | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-resolution-rule-sound.doc.json |
| F:roster-icu-night-iis | Five rows of a 102-row ICU night roster are an irreducible infeasible subsystem | smtlib2 | LIA | search-certificate | proved | unclassified | proved | - | 2 | 2 | cards/F-roster-icu-night-iis.doc.json |
| F:schedule-critical-chain-infeasible | A five-constraint critical chain against a delivery deadline, refuted in the Lean kernel | smtlib2 | QF_LRA | kernel-lean | proved | unclassified | proved | - | 2 | 2 | cards/F-schedule-critical-chain-infeasible.doc.json |
| F:schedule-deadline-iis | Five rows of a 60-row project schedule are an irreducible infeasible subsystem | smtlib2 | LRA | search-certificate | proved | unclassified | proved | - | 2 | 2 | cards/F-schedule-deadline-iis.doc.json |
| F:sorting-network-optimal-size-n3 | The optimal sorting network on 3 channels has exactly 3 comparators | smtlib2 | QF_BV | smt-clausal | proved | proved | proved | - | 2 | 2 | cards/F-sorting-network-optimal-size-n3.doc.json |
| F:sorting-network-optimal-size-n4 | The optimal sorting network on 4 channels has exactly 5 comparators | smtlib2 | QF_BV | smt-clausal | proved | proved | proved | - | 2 | 2 | cards/F-sorting-network-optimal-size-n4.doc.json |
| F:sorting-network-optimal-size-n5 | The optimal sorting network on 5 channels has exactly 9 comparators | smtlib2 | QF_BV | smt-clausal | proved | proved | proved | - | 2 | 2 | cards/F-sorting-network-optimal-size-n5.doc.json |
| F:sorting-network-optimal-size-n6 | The optimal sorting network on 6 channels has exactly 12 comparators | smtlib2 | QF_BV | smt-clausal | proved | proved | proved | - | 2 | 2 | cards/F-sorting-network-optimal-size-n6.doc.json |
| F:squared-binomial-row-sum-central | The sum of squared binomial coefficients is the central binomial coefficient | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-squared-binomial-row-sum-central.doc.json |
| F:tseitin-and-gate | The Tseitin clauses for an AND gate define the gate | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-tseitin-and-gate.doc.json |
| F:twin-prime-unbounded | Twin prime conjecture | lean4 | Nat | - | conjectured | open | open | - | 0 | 0 | cards/F-twin-prime-unbounded.doc.json |
| F:weighted-binomial-row-sum | The k-weighted binomial row sum | cas-term | hypergeometric-summation | cas-certificate | proved | proved | proved | - | 2 | 2 | cards/F-weighted-binomial-row-sum.doc.json |
| F:xor-associative | Exclusive-or is associative | smtlib2 | QF_UF | smt-term-level | proved | proved | proved | - | 1 | 1 | cards/F-xor-associative.doc.json |

Source: `python3 render/producers-py/facts_to_docir.py` (exit 0), 324 input(s) hashed.

<details>
<summary>Import backlog</summary>

Settled in the literature, open here (import backlog)

| fact | title | card |
| --- | --- | --- |
| F:continuum-hypothesis-independent | The continuum hypothesis is independent of ZFC | cards/F-continuum-hypothesis-independent.doc.json |
| F:excluded-middle-not-intuitionistic | Excluded middle is not derivable in intuitionistic propositional logic | cards/F-excluded-middle-not-intuitionistic.doc.json |
| F:fermat-last-theorem | Fermat's Last Theorem | cards/F-fermat-last-theorem.doc.json |
| F:fol-validity-undecidable | Validity in first-order logic is undecidable | cards/F-fol-validity-undecidable.doc.json |
| F:fp16-add-monotone-rne | binary16 addition under roundNearestTiesToEven is monotone in its first argument | cards/F-fp16-add-monotone-rne.doc.json |
| F:godel-first-incompleteness | Godel's first incompleteness theorem | cards/F-godel-first-incompleteness.doc.json |
| F:ml430-int-add-modeq-left-ee732b5b | Mathlib v4.30 source proposition Int.add_modEq_left | cards/F-ml430-int-add-modeq-left-ee732b5b.doc.json |
| F:ml430-int-add-modeq-right-e58108ee | Mathlib v4.30 source proposition Int.add_modEq_right | cards/F-ml430-int-add-modeq-right-e58108ee.doc.json |
| F:ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b | Mathlib v4.30 source proposition Int.dvd_of_dvd_mul_left_of_gcd_one | cards/F-ml430-int-dvd-of-dvd-mul-left-of-gcd-one-649e349b.doc.json |
| F:ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0 | Mathlib v4.30 source proposition Int.dvd_of_dvd_mul_right_of_gcd_one | cards/F-ml430-int-dvd-of-dvd-mul-right-of-gcd-one-77817ff0.doc.json |
| F:ml430-int-fib-add-181b6a2c | Mathlib v4.30 source proposition Int.fib_add | cards/F-ml430-int-fib-add-181b6a2c.doc.json |
| F:ml430-int-fib-add-one-33f1b748 | Mathlib v4.30 source proposition Int.fib_add_one | cards/F-ml430-int-fib-add-one-33f1b748.doc.json |
| F:ml430-int-fib-add-two-739358dd | Mathlib v4.30 source proposition Int.fib_add_two | cards/F-ml430-int-fib-add-two-739358dd.doc.json |
| F:ml430-int-fib-dvd-ffb3c5c1 | Mathlib v4.30 source proposition Int.fib_dvd | cards/F-ml430-int-fib-dvd-ffb3c5c1.doc.json |
| F:ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d | Mathlib v4.30 source proposition Int.fib_eq_fib_add_two_sub_fib_add_one | cards/F-ml430-int-fib-eq-fib-add-two-sub-fib-add-one-0dab3f6d.doc.json |
| F:ml430-int-fib-eq-zero-8193c7cb | Mathlib v4.30 source proposition Int.fib_eq_zero | cards/F-ml430-int-fib-eq-zero-8193c7cb.doc.json |
| F:ml430-int-fib-gcd-3a8bfdec | Mathlib v4.30 source proposition Int.fib_gcd | cards/F-ml430-int-fib-gcd-3a8bfdec.doc.json |
| F:ml430-int-fib-natcast-d5886be4 | Mathlib v4.30 source proposition Int.fib_natCast | cards/F-ml430-int-fib-natcast-d5886be4.doc.json |
| F:ml430-int-fib-neg-b4021d37 | Mathlib v4.30 source proposition Int.fib_neg | cards/F-ml430-int-fib-neg-b4021d37.doc.json |
| F:ml430-int-fib-of-nonneg-438018c5 | Mathlib v4.30 source proposition Int.fib_of_nonneg | cards/F-ml430-int-fib-of-nonneg-438018c5.doc.json |
| F:ml430-int-fib-of-odd-66560495 | Mathlib v4.30 source proposition Int.fib_of_odd | cards/F-ml430-int-fib-of-odd-66560495.doc.json |
| F:ml430-int-fib-two-mul-0e70f3dd | Mathlib v4.30 source proposition Int.fib_two_mul | cards/F-ml430-int-fib-two-mul-0e70f3dd.doc.json |
| F:ml430-int-fib-two-mul-add-one-pos-8977f65f | Mathlib v4.30 source proposition Int.fib_two_mul_add_one_pos | cards/F-ml430-int-fib-two-mul-add-one-pos-8977f65f.doc.json |
| F:ml430-int-fib-two-mul-add-two-0ba4a948 | Mathlib v4.30 source proposition Int.fib_two_mul_add_two | cards/F-ml430-int-fib-two-mul-add-two-0ba4a948.doc.json |
| F:ml430-int-gcd-div-5e01872f | Mathlib v4.30 source proposition Int.gcd_div | cards/F-ml430-int-gcd-div-5e01872f.doc.json |
| F:ml430-int-gcd-div-gcd-div-gcd-2db608dc | Mathlib v4.30 source proposition Int.gcd_div_gcd_div_gcd | cards/F-ml430-int-gcd-div-gcd-div-gcd-2db608dc.doc.json |
| F:ml430-int-gcd-eq-gcd-ab-63005aef | Mathlib v4.30 source proposition Int.gcd_eq_gcd_ab | cards/F-ml430-int-gcd-eq-gcd-ab-63005aef.doc.json |
| F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-left-8533eb82 | Mathlib v4.30 source proposition Int.gcd_eq_one_of_gcd_mul_right_eq_one_left | cards/F-ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-left-8533eb82.doc.json |
| F:ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-right-a9b19222 | Mathlib v4.30 source proposition Int.gcd_eq_one_of_gcd_mul_right_eq_one_right | cards/F-ml430-int-gcd-eq-one-of-gcd-mul-right-eq-one-right-a9b19222.doc.json |
| F:ml430-int-gcd-fib-73bdafc2 | Mathlib v4.30 source proposition Int.gcd_fib | cards/F-ml430-int-gcd-fib-73bdafc2.doc.json |
| F:ml430-int-gcd-greatest-5b31c5fe | Mathlib v4.30 source proposition Int.gcd_greatest | cards/F-ml430-int-gcd-greatest-5b31c5fe.doc.json |
| F:ml430-int-mod-modeq-6bec7847 | Mathlib v4.30 source proposition Int.mod_modEq | cards/F-ml430-int-mod-modeq-6bec7847.doc.json |
| F:ml430-int-modeq-add-left-6e17c69a | Mathlib v4.30 source proposition Int.ModEq.add_left | cards/F-ml430-int-modeq-add-left-6e17c69a.doc.json |
| F:ml430-int-modeq-add-left-cancel-062ad5fe | Mathlib v4.30 source proposition Int.ModEq.add_left_cancel' | cards/F-ml430-int-modeq-add-left-cancel-062ad5fe.doc.json |
| F:ml430-int-modeq-comm-1e4bcc07 | Mathlib v4.30 source proposition Int.modEq_comm | cards/F-ml430-int-modeq-comm-1e4bcc07.doc.json |
| F:ml430-int-modeq-dvd-iff-b7ffeff8 | Mathlib v4.30 source proposition Int.ModEq.dvd_iff | cards/F-ml430-int-modeq-dvd-iff-b7ffeff8.doc.json |
| F:ml430-int-modeq-neg-d6ff57b6 | Mathlib v4.30 source proposition Int.modEq_neg | cards/F-ml430-int-modeq-neg-d6ff57b6.doc.json |
| F:ml430-int-modeq-neg-f649f6c5 | Mathlib v4.30 source proposition Int.ModEq.neg | cards/F-ml430-int-modeq-neg-f649f6c5.doc.json |
| F:ml430-int-modeq-of-dvd-b9c41fce | Mathlib v4.30 source proposition Int.ModEq.of_dvd | cards/F-ml430-int-modeq-of-dvd-b9c41fce.doc.json |
| F:ml430-int-modeq-of-mul-left-c4ccd51e | Mathlib v4.30 source proposition Int.ModEq.of_mul_left | cards/F-ml430-int-modeq-of-mul-left-c4ccd51e.doc.json |
| F:ml430-int-modeq-of-mul-right-c92b7bf0 | Mathlib v4.30 source proposition Int.ModEq.of_mul_right | cards/F-ml430-int-modeq-of-mul-right-c92b7bf0.doc.json |
| F:ml430-int-modeq-one-01d9de39 | Mathlib v4.30 source proposition Int.modEq_one | cards/F-ml430-int-modeq-one-01d9de39.doc.json |
| F:ml430-int-modeq-refl-30e15520 | Mathlib v4.30 source proposition Int.ModEq.refl | cards/F-ml430-int-modeq-refl-30e15520.doc.json |
| F:ml430-int-modeq-sub-3148f130 | Mathlib v4.30 source proposition Int.modEq_sub | cards/F-ml430-int-modeq-sub-3148f130.doc.json |
| F:ml430-int-modeq-symm-984a6e67 | Mathlib v4.30 source proposition Int.ModEq.symm | cards/F-ml430-int-modeq-symm-984a6e67.doc.json |
| F:ml430-int-modeq-trans-6d7863e0 | Mathlib v4.30 source proposition Int.ModEq.trans | cards/F-ml430-int-modeq-trans-6d7863e0.doc.json |
| F:ml430-int-modulus-modeq-zero-5b57a898 | Mathlib v4.30 source proposition Int.modulus_modEq_zero | cards/F-ml430-int-modulus-modeq-zero-5b57a898.doc.json |
| F:ml430-int-ne-zero-of-gcd-f71f00df | Mathlib v4.30 source proposition Int.ne_zero_of_gcd | cards/F-ml430-int-ne-zero-of-gcd-f71f00df.doc.json |
| F:ml430-int-neg-modeq-neg-30d98479 | Mathlib v4.30 source proposition Int.neg_modEq_neg | cards/F-ml430-int-neg-modeq-neg-30d98479.doc.json |
| F:ml430-nat-add-modeq-left-e3b1fba9 | Mathlib v4.30 source proposition Nat.add_modEq_left | cards/F-ml430-nat-add-modeq-left-e3b1fba9.doc.json |
| F:ml430-nat-add-modeq-right-e2f11f21 | Mathlib v4.30 source proposition Nat.add_modEq_right | cards/F-ml430-nat-add-modeq-right-e2f11f21.doc.json |
| F:ml430-nat-bitwise-bit-4c4b28a8 | Mathlib v4.30 source proposition Nat.bitwise_bit' | cards/F-ml430-nat-bitwise-bit-4c4b28a8.doc.json |
| F:ml430-nat-bitwise-comm-1a273bae | Mathlib v4.30 source proposition Nat.bitwise_comm | cards/F-ml430-nat-bitwise-comm-1a273bae.doc.json |
| F:ml430-nat-bitwise-swap-7175e90e | Mathlib v4.30 source proposition Nat.bitwise_swap | cards/F-ml430-nat-bitwise-swap-7175e90e.doc.json |
| F:ml430-nat-choose-eq-zero-of-lt-92ebab29 | Mathlib v4.30 source proposition Nat.choose_eq_zero_of_lt | cards/F-ml430-nat-choose-eq-zero-of-lt-92ebab29.doc.json |
| F:ml430-nat-choose-le-add-9c463139 | Mathlib v4.30 source proposition Nat.choose_le_add | cards/F-ml430-nat-choose-le-add-9c463139.doc.json |
| F:ml430-nat-choose-le-choose-907b5042 | Mathlib v4.30 source proposition Nat.choose_le_choose | cards/F-ml430-nat-choose-le-choose-907b5042.doc.json |
| F:ml430-nat-choose-le-succ-62ae968b | Mathlib v4.30 source proposition Nat.choose_le_succ | cards/F-ml430-nat-choose-le-succ-62ae968b.doc.json |
| F:ml430-nat-choose-mono-a1af9c18 | Mathlib v4.30 source proposition Nat.choose_mono | cards/F-ml430-nat-choose-mono-a1af9c18.doc.json |
| F:ml430-nat-choose-ne-zero-49c3d3cb | Mathlib v4.30 source proposition Nat.choose_ne_zero | cards/F-ml430-nat-choose-ne-zero-49c3d3cb.doc.json |
| F:ml430-nat-choose-one-right-7eda8e39 | Mathlib v4.30 source proposition Nat.choose_one_right | cards/F-ml430-nat-choose-one-right-7eda8e39.doc.json |
| F:ml430-nat-choose-self-25bb9fb8 | Mathlib v4.30 source proposition Nat.choose_self | cards/F-ml430-nat-choose-self-25bb9fb8.doc.json |
| F:ml430-nat-choose-succ-self-e396f6c2 | Mathlib v4.30 source proposition Nat.choose_succ_self | cards/F-ml430-nat-choose-succ-self-e396f6c2.doc.json |
| F:ml430-nat-choose-succ-succ-671856b6 | Mathlib v4.30 source proposition Nat.choose_succ_succ | cards/F-ml430-nat-choose-succ-succ-671856b6.doc.json |
| F:ml430-nat-choose-symm-add-e4b68161 | Mathlib v4.30 source proposition Nat.choose_symm_add | cards/F-ml430-nat-choose-symm-add-e4b68161.doc.json |
| F:ml430-nat-choose-symm-of-eq-add-9b5f9a20 | Mathlib v4.30 source proposition Nat.choose_symm_of_eq_add | cards/F-ml430-nat-choose-symm-of-eq-add-9b5f9a20.doc.json |
| F:ml430-nat-choose-zero-right-1ed2802a | Mathlib v4.30 source proposition Nat.choose_zero_right | cards/F-ml430-nat-choose-zero-right-1ed2802a.doc.json |
| F:ml430-nat-choose-zero-succ-62c6520b | Mathlib v4.30 source proposition Nat.choose_zero_succ | cards/F-ml430-nat-choose-zero-succ-62c6520b.doc.json |
| F:ml430-nat-clog-antitone-left-44a87771 | Mathlib v4.30 source proposition Nat.clog_antitone_left | cards/F-ml430-nat-clog-antitone-left-44a87771.doc.json |
| F:ml430-nat-clog-mono-right-8d87a410 | Mathlib v4.30 source proposition Nat.clog_mono_right | cards/F-ml430-nat-clog-mono-right-8d87a410.doc.json |
| F:ml430-nat-clog-monotone-48fe50c6 | Mathlib v4.30 source proposition Nat.clog_monotone | cards/F-ml430-nat-clog-monotone-48fe50c6.doc.json |
| F:ml430-nat-clog-one-left-b496af12 | Mathlib v4.30 source proposition Nat.clog_one_left | cards/F-ml430-nat-clog-one-left-b496af12.doc.json |
| F:ml430-nat-clog-one-right-1ce3d52f | Mathlib v4.30 source proposition Nat.clog_one_right | cards/F-ml430-nat-clog-one-right-1ce3d52f.doc.json |
| F:ml430-nat-clog-pos-00852cb8 | Mathlib v4.30 source proposition Nat.clog_pos | cards/F-ml430-nat-clog-pos-00852cb8.doc.json |
| F:ml430-nat-clog-zero-left-1c61a5bf | Mathlib v4.30 source proposition Nat.clog_zero_left | cards/F-ml430-nat-clog-zero-left-1c61a5bf.doc.json |
| F:ml430-nat-clog-zero-right-d42d47b1 | Mathlib v4.30 source proposition Nat.clog_zero_right | cards/F-ml430-nat-clog-zero-right-d42d47b1.doc.json |
| F:ml430-nat-coprime-add-self-left-5e93448c | Mathlib v4.30 source proposition Nat.coprime_add_self_left | cards/F-ml430-nat-coprime-add-self-left-5e93448c.doc.json |
| F:ml430-nat-coprime-add-self-right-c3ed0f45 | Mathlib v4.30 source proposition Nat.coprime_add_self_right | cards/F-ml430-nat-coprime-add-self-right-c3ed0f45.doc.json |
| F:ml430-nat-coprime-iff-isrelprime-0c08eb25 | Mathlib v4.30 source proposition Nat.coprime_iff_isRelPrime | cards/F-ml430-nat-coprime-iff-isrelprime-0c08eb25.doc.json |
| F:ml430-nat-coprime-odd-of-left-ed80ab44 | Mathlib v4.30 source proposition Nat.Coprime.odd_of_left | cards/F-ml430-nat-coprime-odd-of-left-ed80ab44.doc.json |
| F:ml430-nat-coprime-odd-of-right-8dc1decc | Mathlib v4.30 source proposition Nat.Coprime.odd_of_right | cards/F-ml430-nat-coprime-odd-of-right-8dc1decc.doc.json |
| F:ml430-nat-coprime-of-dvd-18fcd09f | Mathlib v4.30 source proposition Nat.Coprime.of_dvd | cards/F-ml430-nat-coprime-of-dvd-18fcd09f.doc.json |
| F:ml430-nat-coprime-of-dvd-6f652673 | Mathlib v4.30 source proposition Nat.coprime_of_dvd' | cards/F-ml430-nat-coprime-of-dvd-6f652673.doc.json |
| F:ml430-nat-coprime-of-dvd-left-b0e2aa94 | Mathlib v4.30 source proposition Nat.Coprime.of_dvd_left | cards/F-ml430-nat-coprime-of-dvd-left-b0e2aa94.doc.json |
| F:ml430-nat-coprime-of-dvd-right-a640bd56 | Mathlib v4.30 source proposition Nat.Coprime.of_dvd_right | cards/F-ml430-nat-coprime-of-dvd-right-a640bd56.doc.json |
| F:ml430-nat-coprime-of-lt-minfac-0f79bdba | Mathlib v4.30 source proposition Nat.coprime_of_lt_minFac | cards/F-ml430-nat-coprime-of-lt-minfac-0f79bdba.doc.json |
| F:ml430-nat-coprime-of-lt-prime-1978a919 | Mathlib v4.30 source proposition Nat.coprime_of_lt_prime | cards/F-ml430-nat-coprime-of-lt-prime-1978a919.doc.json |
| F:ml430-nat-coprime-one-left-iff-45945e80 | Mathlib v4.30 source proposition Nat.coprime_one_left_iff | cards/F-ml430-nat-coprime-one-left-iff-45945e80.doc.json |
| F:ml430-nat-coprime-one-right-iff-42fed4ce | Mathlib v4.30 source proposition Nat.coprime_one_right_iff | cards/F-ml430-nat-coprime-one-right-iff-42fed4ce.doc.json |
| F:ml430-nat-coprime-or-dvd-of-prime-65f47114 | Mathlib v4.30 source proposition Nat.coprime_or_dvd_of_prime | cards/F-ml430-nat-coprime-or-dvd-of-prime-65f47114.doc.json |
| F:ml430-nat-coprime-primes-5769049f | Mathlib v4.30 source proposition Nat.coprime_primes | cards/F-ml430-nat-coprime-primes-5769049f.doc.json |
| F:ml430-nat-coprime-self-add-left-51351fa1 | Mathlib v4.30 source proposition Nat.coprime_self_add_left | cards/F-ml430-nat-coprime-self-add-left-51351fa1.doc.json |
| F:ml430-nat-coprime-self-add-right-966e5434 | Mathlib v4.30 source proposition Nat.coprime_self_add_right | cards/F-ml430-nat-coprime-self-add-right-966e5434.doc.json |
| F:ml430-nat-coprime-symmetric-9b5cfa12 | Mathlib v4.30 source proposition Nat.Coprime.symmetric | cards/F-ml430-nat-coprime-symmetric-9b5cfa12.doc.json |
| F:ml430-nat-coprime-two-left-1b47e7c4 | Mathlib v4.30 source proposition Nat.coprime_two_left | cards/F-ml430-nat-coprime-two-left-1b47e7c4.doc.json |
| F:ml430-nat-coprime-two-right-7c5a1850 | Mathlib v4.30 source proposition Nat.coprime_two_right | cards/F-ml430-nat-coprime-two-right-7c5a1850.doc.json |
| F:ml430-nat-descfactorial-le-2b8cc09a | Mathlib v4.30 source proposition Nat.descFactorial_le | cards/F-ml430-nat-descfactorial-le-2b8cc09a.doc.json |
| F:ml430-nat-descfactorial-of-lt-fbcf5d26 | Mathlib v4.30 source proposition Nat.descFactorial_of_lt | cards/F-ml430-nat-descfactorial-of-lt-fbcf5d26.doc.json |
| F:ml430-nat-descfactorial-one-d4856d4a | Mathlib v4.30 source proposition Nat.descFactorial_one | cards/F-ml430-nat-descfactorial-one-d4856d4a.doc.json |
| F:ml430-nat-descfactorial-self-899fc0e0 | Mathlib v4.30 source proposition Nat.descFactorial_self | cards/F-ml430-nat-descfactorial-self-899fc0e0.doc.json |
| F:ml430-nat-div-dvd-div-left-b56f6f7c | Mathlib v4.30 source proposition Nat.div_dvd_div_left | cards/F-ml430-nat-div-dvd-div-left-b56f6f7c.doc.json |
| F:ml430-nat-dvd-lcm-of-dvd-left-141a64bb | Mathlib v4.30 source proposition Nat.dvd_lcm_of_dvd_left | cards/F-ml430-nat-dvd-lcm-of-dvd-left-141a64bb.doc.json |
| F:ml430-nat-dvd-lcm-of-dvd-right-61a50fc3 | Mathlib v4.30 source proposition Nat.dvd_lcm_of_dvd_right | cards/F-ml430-nat-dvd-lcm-of-dvd-right-61a50fc3.doc.json |
| F:ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b | Mathlib v4.30 source proposition Nat.dvd_of_forall_prime_mul_dvd | cards/F-ml430-nat-dvd-of-forall-prime-mul-dvd-5898723b.doc.json |
| F:ml430-nat-dvd-of-lcm-left-dvd-d6b2407c | Mathlib v4.30 source proposition Nat.dvd_of_lcm_left_dvd | cards/F-ml430-nat-dvd-of-lcm-left-dvd-d6b2407c.doc.json |
| F:ml430-nat-dvd-of-lcm-right-dvd-61bd1a60 | Mathlib v4.30 source proposition Nat.dvd_of_lcm_right_dvd | cards/F-ml430-nat-dvd-of-lcm-right-dvd-61bd1a60.doc.json |
| F:ml430-nat-even-xor-78a39432 | Mathlib v4.30 source proposition Nat.even_xor | cards/F-ml430-nat-even-xor-78a39432.doc.json |
| F:ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e | Mathlib v4.30 source proposition Nat.exists_mul_mod_eq_gcd | cards/F-ml430-nat-exists-mul-mod-eq-gcd-8bf9ec7e.doc.json |
| F:ml430-nat-exists-mul-self-e73ca9fa | Mathlib v4.30 source proposition Nat.exists_mul_self | cards/F-ml430-nat-exists-mul-self-e73ca9fa.doc.json |
| F:ml430-nat-factorial-dvd-ascfactorial-44a4e641 | Mathlib v4.30 source proposition Nat.factorial_dvd_ascFactorial | cards/F-ml430-nat-factorial-dvd-ascfactorial-44a4e641.doc.json |
| F:ml430-nat-factorial-dvd-descfactorial-bbf6124f | Mathlib v4.30 source proposition Nat.factorial_dvd_descFactorial | cards/F-ml430-nat-factorial-dvd-descfactorial-bbf6124f.doc.json |
| F:ml430-nat-factorial-dvd-factorial-e9d14845 | Mathlib v4.30 source proposition Nat.factorial_dvd_factorial | cards/F-ml430-nat-factorial-dvd-factorial-e9d14845.doc.json |
| F:ml430-nat-factorial-le-d0f4a912 | Mathlib v4.30 source proposition Nat.factorial_le | cards/F-ml430-nat-factorial-le-d0f4a912.doc.json |
| F:ml430-nat-factorial-lt-of-lt-d6c2125d | Mathlib v4.30 source proposition Nat.factorial_lt_of_lt | cards/F-ml430-nat-factorial-lt-of-lt-d6c2125d.doc.json |
| F:ml430-nat-factorial-ne-zero-5fc0b0a1 | Mathlib v4.30 source proposition Nat.factorial_ne_zero | cards/F-ml430-nat-factorial-ne-zero-5fc0b0a1.doc.json |
| F:ml430-nat-factorial-pos-f1dd2405 | Mathlib v4.30 source proposition Nat.factorial_pos | cards/F-ml430-nat-factorial-pos-f1dd2405.doc.json |
| F:ml430-nat-fastfib-eq-cde11774 | Mathlib v4.30 source proposition Nat.fastFib_eq | cards/F-ml430-nat-fastfib-eq-cde11774.doc.json |
| F:ml430-nat-fib-add-two-strictmono-c1e86d4d | Mathlib v4.30 source proposition Nat.fib_add_two_strictMono | cards/F-ml430-nat-fib-add-two-strictmono-c1e86d4d.doc.json |
| F:ml430-nat-fib-coprime-fib-succ-162fc738 | Mathlib v4.30 source proposition Nat.fib_coprime_fib_succ | cards/F-ml430-nat-fib-coprime-fib-succ-162fc738.doc.json |
| F:ml430-nat-fib-dvd-f80f3de1 | Mathlib v4.30 source proposition Nat.fib_dvd | cards/F-ml430-nat-fib-dvd-f80f3de1.doc.json |
| F:ml430-nat-fib-eq-zero-61879073 | Mathlib v4.30 source proposition Nat.fib_eq_zero | cards/F-ml430-nat-fib-eq-zero-61879073.doc.json |
| F:ml430-nat-fib-gcd-d1d98407 | Mathlib v4.30 source proposition Nat.fib_gcd | cards/F-ml430-nat-fib-gcd-d1d98407.doc.json |
| F:ml430-nat-fib-le-fib-succ-d1ef4a3d | Mathlib v4.30 source proposition Nat.fib_le_fib_succ | cards/F-ml430-nat-fib-le-fib-succ-d1ef4a3d.doc.json |
| F:ml430-nat-fib-lt-fib-3582b881 | Mathlib v4.30 source proposition Nat.fib_lt_fib | cards/F-ml430-nat-fib-lt-fib-3582b881.doc.json |
| F:ml430-nat-fib-mono-cc6afe09 | Mathlib v4.30 source proposition Nat.fib_mono | cards/F-ml430-nat-fib-mono-cc6afe09.doc.json |
| F:ml430-nat-fib-pos-9e67bd8e | Mathlib v4.30 source proposition Nat.fib_pos | cards/F-ml430-nat-fib-pos-9e67bd8e.doc.json |
| F:ml430-nat-fib-strictmonoon-905810a9 | Mathlib v4.30 source proposition Nat.fib_strictMonoOn | cards/F-ml430-nat-fib-strictmonoon-905810a9.doc.json |
| F:ml430-nat-gcd-fib-add-self-5a92d5e3 | Mathlib v4.30 source proposition Nat.gcd_fib_add_self | cards/F-ml430-nat-gcd-fib-add-self-5a92d5e3.doc.json |
| F:ml430-nat-gcd-greatest-0a04214a | Mathlib v4.30 source proposition Nat.gcd_greatest | cards/F-ml430-nat-gcd-greatest-0a04214a.doc.json |
| F:ml430-nat-land-assoc-ad4775b8 | Mathlib v4.30 source proposition Nat.land_assoc | cards/F-ml430-nat-land-assoc-ad4775b8.doc.json |
| F:ml430-nat-land-bit-b9ab7475 | Mathlib v4.30 source proposition Nat.land_bit | cards/F-ml430-nat-land-bit-b9ab7475.doc.json |
| F:ml430-nat-land-comm-7e6ad72e | Mathlib v4.30 source proposition Nat.land_comm | cards/F-ml430-nat-land-comm-7e6ad72e.doc.json |
| F:ml430-nat-ldiff-bit-6be49bb8 | Mathlib v4.30 source proposition Nat.ldiff_bit | cards/F-ml430-nat-ldiff-bit-6be49bb8.doc.json |
| F:ml430-nat-le-fib-add-one-5284f0bf | Mathlib v4.30 source proposition Nat.le_fib_add_one | cards/F-ml430-nat-le-fib-add-one-5284f0bf.doc.json |
| F:ml430-nat-le-fib-self-0cbccb4d | Mathlib v4.30 source proposition Nat.le_fib_self | cards/F-ml430-nat-le-fib-self-0cbccb4d.doc.json |
| F:ml430-nat-le-sqrt-e6996680 | Mathlib v4.30 source proposition Nat.le_sqrt | cards/F-ml430-nat-le-sqrt-e6996680.doc.json |
| F:ml430-nat-le-sqrt-of-eq-mul-503c5afe | Mathlib v4.30 source proposition Nat.le_sqrt_of_eq_mul | cards/F-ml430-nat-le-sqrt-of-eq-mul-503c5afe.doc.json |
| F:ml430-nat-le-three-of-sqrt-eq-one-0c48a868 | Mathlib v4.30 source proposition Nat.le_three_of_sqrt_eq_one | cards/F-ml430-nat-le-three-of-sqrt-eq-one-0c48a868.doc.json |
| F:ml430-nat-log-antitone-left-20d1326c | Mathlib v4.30 source proposition Nat.log_antitone_left | cards/F-ml430-nat-log-antitone-left-20d1326c.doc.json |
| F:ml430-nat-log-le-clog-ac8ab2d4 | Mathlib v4.30 source proposition Nat.log_le_clog | cards/F-ml430-nat-log-le-clog-ac8ab2d4.doc.json |
| F:ml430-nat-log-le-self-da387172 | Mathlib v4.30 source proposition Nat.log_le_self | cards/F-ml430-nat-log-le-self-da387172.doc.json |
| F:ml430-nat-log-lt-self-529f89fa | Mathlib v4.30 source proposition Nat.log_lt_self | cards/F-ml430-nat-log-lt-self-529f89fa.doc.json |
| F:ml430-nat-log-mono-right-b8939fee | Mathlib v4.30 source proposition Nat.log_mono_right | cards/F-ml430-nat-log-mono-right-b8939fee.doc.json |
| F:ml430-nat-log-monotone-52fad774 | Mathlib v4.30 source proposition Nat.log_monotone | cards/F-ml430-nat-log-monotone-52fad774.doc.json |
| F:ml430-nat-log-of-lt-89eaf42e | Mathlib v4.30 source proposition Nat.log_of_lt | cards/F-ml430-nat-log-of-lt-89eaf42e.doc.json |
| F:ml430-nat-log-one-left-73efc119 | Mathlib v4.30 source proposition Nat.log_one_left | cards/F-ml430-nat-log-one-left-73efc119.doc.json |
| F:ml430-nat-log-one-right-282332ef | Mathlib v4.30 source proposition Nat.log_one_right | cards/F-ml430-nat-log-one-right-282332ef.doc.json |
| F:ml430-nat-log-zero-left-9ec8541e | Mathlib v4.30 source proposition Nat.log_zero_left | cards/F-ml430-nat-log-zero-left-9ec8541e.doc.json |
| F:ml430-nat-log-zero-right-8ea186db | Mathlib v4.30 source proposition Nat.log_zero_right | cards/F-ml430-nat-log-zero-right-8ea186db.doc.json |
| F:ml430-nat-log2-eq-log-two-28085932 | Mathlib v4.30 source proposition Nat.log2_eq_log_two | cards/F-ml430-nat-log2-eq-log-two-28085932.doc.json |
| F:ml430-nat-lor-assoc-82c4d0fd | Mathlib v4.30 source proposition Nat.lor_assoc | cards/F-ml430-nat-lor-assoc-82c4d0fd.doc.json |
| F:ml430-nat-lor-bit-a2f98c7c | Mathlib v4.30 source proposition Nat.lor_bit | cards/F-ml430-nat-lor-bit-a2f98c7c.doc.json |
| F:ml430-nat-lor-comm-2666d7ef | Mathlib v4.30 source proposition Nat.lor_comm | cards/F-ml430-nat-lor-comm-2666d7ef.doc.json |
| F:ml430-nat-lt-of-testbit-72f64ab8 | Mathlib v4.30 source proposition Nat.lt_of_testBit | cards/F-ml430-nat-lt-of-testbit-72f64ab8.doc.json |
| F:ml430-nat-lt-succ-sqrt-39389df2 | Mathlib v4.30 source proposition Nat.lt_succ_sqrt | cards/F-ml430-nat-lt-succ-sqrt-39389df2.doc.json |
| F:ml430-nat-lt-xor-cases-c43a1e85 | Mathlib v4.30 source proposition Nat.lt_xor_cases | cards/F-ml430-nat-lt-xor-cases-c43a1e85.doc.json |
| F:ml430-nat-mod-lcm-ee6bdd41 | Mathlib v4.30 source proposition Nat.mod_lcm | cards/F-ml430-nat-mod-lcm-ee6bdd41.doc.json |
| F:ml430-nat-mod-modeq-436e4c10 | Mathlib v4.30 source proposition Nat.mod_modEq | cards/F-ml430-nat-mod-modeq-436e4c10.doc.json |
| F:ml430-nat-modeq-add-left-cancel-e5287cf6 | Mathlib v4.30 source proposition Nat.ModEq.add_left_cancel' | cards/F-ml430-nat-modeq-add-left-cancel-e5287cf6.doc.json |
| F:ml430-nat-modeq-add-left-e83f0700 | Mathlib v4.30 source proposition Nat.ModEq.add_left | cards/F-ml430-nat-modeq-add-left-e83f0700.doc.json |
| F:ml430-nat-modeq-add-right-8e2ca0cc | Mathlib v4.30 source proposition Nat.ModEq.add_right | cards/F-ml430-nat-modeq-add-right-8e2ca0cc.doc.json |
| F:ml430-nat-modeq-add-right-cancel-e871facf | Mathlib v4.30 source proposition Nat.ModEq.add_right_cancel' | cards/F-ml430-nat-modeq-add-right-cancel-e871facf.doc.json |
| F:ml430-nat-modeq-comm-24b71e7a | Mathlib v4.30 source proposition Nat.ModEq.comm | cards/F-ml430-nat-modeq-comm-24b71e7a.doc.json |
| F:ml430-nat-modeq-dvd-iff-8f130450 | Mathlib v4.30 source proposition Nat.ModEq.dvd_iff | cards/F-ml430-nat-modeq-dvd-iff-8f130450.doc.json |
| F:ml430-nat-modeq-gcd-eq-5167ff4f | Mathlib v4.30 source proposition Nat.ModEq.gcd_eq | cards/F-ml430-nat-modeq-gcd-eq-5167ff4f.doc.json |
| F:ml430-nat-modeq-of-dvd-d75cc374 | Mathlib v4.30 source proposition Nat.ModEq.of_dvd | cards/F-ml430-nat-modeq-of-dvd-d75cc374.doc.json |
| F:ml430-nat-modeq-of-mul-left-88d20bca | Mathlib v4.30 source proposition Nat.ModEq.of_mul_left | cards/F-ml430-nat-modeq-of-mul-left-88d20bca.doc.json |
| F:ml430-nat-modeq-of-mul-right-43078e1c | Mathlib v4.30 source proposition Nat.ModEq.of_mul_right | cards/F-ml430-nat-modeq-of-mul-right-43078e1c.doc.json |
| F:ml430-nat-modeq-one-516d46e8 | Mathlib v4.30 source proposition Nat.modEq_one | cards/F-ml430-nat-modeq-one-516d46e8.doc.json |
| F:ml430-nat-modeq-refl-d870c8f5 | Mathlib v4.30 source proposition Nat.ModEq.refl | cards/F-ml430-nat-modeq-refl-d870c8f5.doc.json |
| F:ml430-nat-modeq-symm-0a3d4d18 | Mathlib v4.30 source proposition Nat.ModEq.symm | cards/F-ml430-nat-modeq-symm-0a3d4d18.doc.json |
| F:ml430-nat-modeq-trans-ef9d1c46 | Mathlib v4.30 source proposition Nat.ModEq.trans | cards/F-ml430-nat-modeq-trans-ef9d1c46.doc.json |
| F:ml430-nat-modulus-modeq-zero-fd9af096 | Mathlib v4.30 source proposition Nat.modulus_modEq_zero | cards/F-ml430-nat-modulus-modeq-zero-fd9af096.doc.json |
| F:ml430-nat-multichoose-one-b210386a | Mathlib v4.30 source proposition Nat.multichoose_one | cards/F-ml430-nat-multichoose-one-b210386a.doc.json |
| F:ml430-nat-multichoose-one-right-7755072d | Mathlib v4.30 source proposition Nat.multichoose_one_right | cards/F-ml430-nat-multichoose-one-right-7755072d.doc.json |
| F:ml430-nat-multichoose-zero-right-6ef827c8 | Mathlib v4.30 source proposition Nat.multichoose_zero_right | cards/F-ml430-nat-multichoose-zero-right-6ef827c8.doc.json |
| F:ml430-nat-not-coprime-zero-zero-6c4e8dd8 | Mathlib v4.30 source proposition Nat.not_coprime_zero_zero | cards/F-ml430-nat-not-coprime-zero-zero-6c4e8dd8.doc.json |
| F:ml430-nat-not-prime-of-dvd-of-ne-4ff592c0 | Mathlib v4.30 source proposition Nat.not_prime_of_dvd_of_ne | cards/F-ml430-nat-not-prime-of-dvd-of-ne-4ff592c0.doc.json |
| F:ml430-nat-one-ascfactorial-8bacb017 | Mathlib v4.30 source proposition Nat.one_ascFactorial | cards/F-ml430-nat-one-ascfactorial-8bacb017.doc.json |
| F:ml430-nat-prime-dvd-iff-not-coprime-77854741 | Mathlib v4.30 source proposition Nat.Prime.dvd_iff_not_coprime | cards/F-ml430-nat-prime-dvd-iff-not-coprime-77854741.doc.json |
| F:ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439 | Mathlib v4.30 source proposition Nat.Prime.dvd_mul_of_dvd_ne | cards/F-ml430-nat-prime-dvd-mul-of-dvd-ne-6c253439.doc.json |
| F:ml430-nat-prime-dvd-of-dvd-pow-e76f834a | Mathlib v4.30 source proposition Nat.Prime.dvd_of_dvd_pow | cards/F-ml430-nat-prime-dvd-of-dvd-pow-e76f834a.doc.json |
| F:ml430-nat-prime-even-iff-d068ec82 | Mathlib v4.30 source proposition Nat.Prime.even_iff | cards/F-ml430-nat-prime-even-iff-d068ec82.doc.json |
| F:ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786 | Mathlib v4.30 source proposition Nat.Prime.five_le_of_ne_two_of_ne_three | cards/F-ml430-nat-prime-five-le-of-ne-two-of-ne-three-c069e786.doc.json |
| F:ml430-nat-prime-not-dvd-mul-cb3a915e | Mathlib v4.30 source proposition Nat.Prime.not_dvd_mul | cards/F-ml430-nat-prime-not-dvd-mul-cb3a915e.doc.json |
| F:ml430-nat-prime-odd-of-ne-two-91e1195f | Mathlib v4.30 source proposition Nat.Prime.odd_of_ne_two | cards/F-ml430-nat-prime-odd-of-ne-two-91e1195f.doc.json |
| F:ml430-nat-prime-pred-pos-4e67ac4c | Mathlib v4.30 source proposition Nat.Prime.pred_pos | cards/F-ml430-nat-prime-pred-pos-4e67ac4c.doc.json |
| F:ml430-nat-self-le-factorial-cfdffc69 | Mathlib v4.30 source proposition Nat.self_le_factorial | cards/F-ml430-nat-self-le-factorial-cfdffc69.doc.json |
| F:ml430-nat-sqrt-eq-79ae8eae | Mathlib v4.30 source proposition Nat.sqrt_eq | cards/F-ml430-nat-sqrt-eq-79ae8eae.doc.json |
| F:ml430-nat-sqrt-eq-c036815b | Mathlib v4.30 source proposition Nat.sqrt_eq' | cards/F-ml430-nat-sqrt-eq-c036815b.doc.json |
| F:ml430-nat-sqrt-eq-zero-53666a3b | Mathlib v4.30 source proposition Nat.sqrt_eq_zero | cards/F-ml430-nat-sqrt-eq-zero-53666a3b.doc.json |
| F:ml430-nat-sqrt-le-7918582b | Mathlib v4.30 source proposition Nat.sqrt_le | cards/F-ml430-nat-sqrt-le-7918582b.doc.json |
| F:ml430-nat-sqrt-le-self-1ed5eb85 | Mathlib v4.30 source proposition Nat.sqrt_le_self | cards/F-ml430-nat-sqrt-le-self-1ed5eb85.doc.json |
| F:ml430-nat-sqrt-le-sqrt-6e2bfc47 | Mathlib v4.30 source proposition Nat.sqrt_le_sqrt | cards/F-ml430-nat-sqrt-le-sqrt-6e2bfc47.doc.json |
| F:ml430-nat-sqrt-lt-4909537f | Mathlib v4.30 source proposition Nat.sqrt_lt | cards/F-ml430-nat-sqrt-lt-4909537f.doc.json |
| F:ml430-nat-sqrt-lt-self-ff7a155a | Mathlib v4.30 source proposition Nat.sqrt_lt_self | cards/F-ml430-nat-sqrt-lt-self-ff7a155a.doc.json |
| F:ml430-nat-sqrt-pos-f75e5114 | Mathlib v4.30 source proposition Nat.sqrt_pos | cards/F-ml430-nat-sqrt-pos-f75e5114.doc.json |
| F:ml430-nat-sqrt-succ-le-succ-sqrt-6b041183 | Mathlib v4.30 source proposition Nat.sqrt_succ_le_succ_sqrt | cards/F-ml430-nat-sqrt-succ-le-succ-sqrt-6b041183.doc.json |
| F:ml430-nat-succ-pred-prime-4feb123f | Mathlib v4.30 source proposition Nat.succ_pred_prime | cards/F-ml430-nat-succ-pred-prime-4feb123f.doc.json |
| F:ml430-nat-testbit-eq-inth-ffa07392 | Mathlib v4.30 source proposition Nat.testBit_eq_inth | cards/F-ml430-nat-testbit-eq-inth-ffa07392.doc.json |
| F:ml430-nat-testbit-land-dfef7ca4 | Mathlib v4.30 source proposition Nat.testBit_land | cards/F-ml430-nat-testbit-land-dfef7ca4.doc.json |
| F:ml430-nat-testbit-ldiff-16f94162 | Mathlib v4.30 source proposition Nat.testBit_ldiff | cards/F-ml430-nat-testbit-ldiff-16f94162.doc.json |
| F:ml430-nat-testbit-lor-7644e067 | Mathlib v4.30 source proposition Nat.testBit_lor | cards/F-ml430-nat-testbit-lor-7644e067.doc.json |
| F:ml430-nat-zero-ascfactorial-af4fcdca | Mathlib v4.30 source proposition Nat.zero_ascFactorial | cards/F-ml430-nat-zero-ascfactorial-af4fcdca.doc.json |
| F:ml430-nat-zero-of-testbit-eq-false-e244c9a1 | Mathlib v4.30 source proposition Nat.zero_of_testBit_eq_false | cards/F-ml430-nat-zero-of-testbit-eq-false-e244c9a1.doc.json |

Source: `python3 render/producers-py/facts_to_docir.py` (exit 0), 324 input(s) hashed.

</details>

---

Rendered from Doc-IR by `axeyum-render`. Epoch 1787144076 (2026-08-19T12:54:36Z, source `commit`), commit `d637d83f77dbfa43c98eee4ab0ad78d235099006`.
