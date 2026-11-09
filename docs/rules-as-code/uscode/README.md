# Lifting the U.S. Code

A rule model is only as trustworthy as its link to the text it encodes. This
directory holds the first step of that link: a U.S. Code section lifted from its
published rendering into a computable object that a rule model can be checked
against.

```text
sources/USCODE-2023-title18-partI-chap47-sec1030.htm   GovInfo rendering (input, committed)
lifted/usc-t18-s1030.json                              lifted section (generated, committed)
```

Regenerate and check:

```sh
python3 scripts/uscode_lift.py \
  docs/rules-as-code/uscode/sources/USCODE-2023-title18-partI-chap47-sec1030.htm \
  docs/rules-as-code/uscode/lifted/usc-t18-s1030.json [--check]
```

## What is lifted

The input is the GPO HTML rendering that GovInfo publishes for each section
(here 18 U.S.C. § 1030, United States Code 2023 Edition, current through
2024-01-03; SHA-256 recorded in the output). The lift records only structure the
text states explicitly. It does not interpret the law.

| Component | § 1030 | What it is |
|---|---:|---|
| `provisions` | 104 | The outline: 10 subsections, 32 paragraphs, 39 subparagraphs, 15 clauses, 8 subclauses, each with a USLM-style identifier (`/us/usc/t18/s1030/c/4/A/i/VI`), its citation, its own text, any trailing flush text, and editorial footnotes. |
| `cross_references` | 29 internal, 14 external | Internal references resolved to 49 provision targets, including relative ("subparagraph (B)"), anchored ("subparagraphs (A) or (B) of subsection (a)(5)"), and ranged ("subclauses (I) through (VI) of subparagraph (A)(i)") forms. External references keep their citation (`15 U.S.C. § 1602(n)`, `Federal Reserve Act § 25(a)`). |
| `definitions`, `term_uses` | 13 terms | Each "the term X means" in (e), and every provision whose text uses the term (longest match first, so "protected computer" is not also counted as "computer"). |
| `quantities` | 20 | Dollar thresholds with their comparator, imprisonment maxima, periods, and counts, each attached to the provision that states it. |

## Using the lifted section

[`scripts/uscode_query.py`](../../../scripts/uscode_query.py) answers questions
directly from the lifted object. Three that matter for § 1030:

```text
$ python3 scripts/uscode_query.py docs/rules-as-code/uscode/lifted/usc-t18-s1030.json quantities --kind money_usd
18 U.S.C. § 1030(a)(4): money_usd <= 5000   "not more than $5,000"
18 U.S.C. § 1030(c)(2)(B)(iii): money_usd > 5000   "exceeds $5,000"
18 U.S.C. § 1030(c)(4)(A)(i)(I): money_usd >= 5000   "aggregating at least $5,000"
```

One section states the same amount with three comparators. A rule author who
transcribes "$5,000" without its comparator is wrong at exactly $5,000 in at
least one of the three places.

```text
$ python3 scripts/uscode_query.py docs/rules-as-code/uscode/lifted/usc-t18-s1030.json cited-by c/4/A/i
18 U.S.C. § 1030(c)(4)(A)(i) and its descendants are cited 3 times:
  18 U.S.C. § 1030(c)(4)(B)(i)  "subclauses (I) through (VI) of subparagraph (A)(i)"  -> …(I), …(II), …(III), …(IV), …(V), …(VI)
  18 U.S.C. § 1030(g)  "subclauses (I), (II), (III), (IV), or (V) of subsection (c)(4)(A)(i)"  -> …(I), …(II), …(III), …(IV), …(V)
  18 U.S.C. § 1030(g)  "subsection (c)(4)(A)(i)(I)"  -> …(I)
```

The six harm factors are defined once and reused twice, by the felony maximum
for (a)(5)(A) and by the civil action, and the two reuses take different subsets.
A rule model can encode the factors once and let both consumers depend on that
encoding; the lifted references are what make the dependency checkable.

```text
$ python3 scripts/uscode_query.py docs/rules-as-code/uscode/lifted/usc-t18-s1030.json term "protected computer"
defined: 18 U.S.C. § 1030(e)(2) ("protected computer" means)
used in 10 provisions:
  18 U.S.C. § 1030(a)(2)(C)
  …
```

The rule compiler [`scripts/rules_ir.py`](../../../scripts/rules_ir.py) uses the
same object to gate a rule model: anchors must occur in their provision, numeric
literals must match the provision's quantities and comparators, dependencies
must follow structure, references, or defined terms, and every reference leaving
a modeled provision must be consumed or scoped out. The worked example is
[Computer Fraud and Abuse Act V0](../examples/cfaa-1030-v0/README.md).

## Extraction hazards met in § 1030

Each of these produced a wrong lift on the first attempt and is now handled and
documented in `uscode_lift.py`:

- **Footnote markers inline with text.** GovInfo places superscript footnote
  anchors in the text ("subclauses⁵ (I), (II)…"); stripped naively they become
  "subclauses 5 (I)". The lift removes the markers and keeps the footnote bodies
  ("So in original. Probably should be 'subclause'.") as editorial metadata on
  the provision: 7 such notes in § 1030.
- **Ambiguous enumerators.** "(i)" is a subsection in § 1030(i) and a clause in
  § 1030(c)(2)(B)(i); "(I)" is a subparagraph in § 1030(e)(4)(I) and a subclause
  in § 1030(c)(4)(A)(i)(I). The lift assigns each enumerator by whether it
  continues an open sequence or opens the first child of the deepest open level,
  and fails on any enumerator that fits more than one level.
- **Combined enumerators.** "(5)(A) knowingly causes…" opens paragraph (5) and
  subparagraph (A) in one line; (5) has no text of its own.
- **Flush text.** "shall be punished as provided in subsection (c)" follows the
  list in (a) and belongs to (a), not to (a)(7)(C).
- **References into other laws.** "paragraphs (1) and (3) of section 1(b) of
  the International Banking Act of 1978" names paragraphs of another statute and
  must not resolve inside § 1030; "section 25 or section 25(a) of the Federal
  Reserve Act" coordinates two sections of the same Act, so the bare "section 25"
  is not 18 U.S.C. § 25.
- **Capitalized terms.** The defined term "State" must not match inside
  "United States".

## Scope and next steps

The lifter handles one GovInfo section rendering at a time. The next inputs are
the USLM XML releases of the Office of the Law Revision Counsel, which carry the
outline and identifiers explicitly and would replace the enumerator inference
above, and the eCFR XML, whose outline has the same shape. The point-in-time
question (which edition, current through which public law) is recorded in the
lifted object and is part of every generated obligation's header.

## Related work

The representation of the Code as a hierarchy with a citation network follows
earlier empirical work on the U.S. Code:

- M. J. Bommarito II and D. M. Katz, "Properties of the United States Code
  citation network," arXiv:0911.1751 (2009).
- M. J. Bommarito II and D. M. Katz, "A mathematical approach to the study of
  the United States Code," *Physica A* 389(19):4195–4200 (2010),
  arXiv:1003.4146.
- D. M. Katz and M. J. Bommarito II, "Measuring the complexity of the law: the
  United States Code," *Artificial Intelligence and Law* 22(4):337–374 (2014).
- J. B. Ruhl, D. M. Katz, and M. J. Bommarito II, "Harnessing legal
  complexity," *Science* 355(6332):1377–1378 (2017).
- C. Coupette, J. Beckedorf, D. Hartung, M. Bommarito, and D. M. Katz,
  "Measuring law over time: A network analytical framework with an application
  to statutes and regulations in the United States and Germany," *Frontiers in
  Physics* 9:658463 (2021), arXiv:2101.11284.

Those papers measure structure across the whole Code. This directory uses the
same structure at the level of one section, as the reference a formal rule model
is checked against.
