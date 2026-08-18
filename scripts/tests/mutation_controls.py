#!/usr/bin/env python3
"""Delete one guard at a time and require each deletion to kill a test.

A guard nobody can remove is decoration.  This harness copies a generator into
a scratch tree, applies one textual mutation (each of which removes exactly one
guard), runs that generator's unittest module, and reports which tests died.

Usage::

    python3 scripts/tests/mutation_controls.py            # both generators
    python3 scripts/tests/mutation_controls.py adr-index  # one of them

Exit status is 0 only when every mutation killed at least one test.  It prints
the surviving mutations, which are the guards you have not actually tested.

This is a control, not a gate: it rewrites a scratch copy of the repository, so
it is run deliberately rather than from `scripts/check.sh`.
"""

from __future__ import annotations

import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

# (generator, test module, [(mutation name, find, replace), ...])
SUITES: dict[str, tuple[str, str, list[tuple[str, str, str]]]] = {
    "adr-index": (
        "scripts/gen-adr-index.py",
        "scripts.tests.test_gen_adr_index",
        [
            (
                "heading-shape guard",
                "    if heading is None:\n        raise AdrError(",
                "    if False:\n        raise AdrError(",
            ),
            (
                "front-matter stop",
                "        if field is None:\n            break",
                "        if field is None:\n            index += 1\n            continue",
            ),
            (
                "Status-required guard",
                '    if "Status" not in front:\n        raise AdrError(f"{path.name}: no \'Status:\' line in its front matter")',
                '    if "Status" not in front:\n        front["Status"] = ""',
            ),
            (
                "pipe-in-cell guard",
                '        if "|" in cell:',
                "        if False:",
            ),
            (
                "empty-directory guard",
                "    if not adrs:",
                "    if False and not adrs:",
            ),
            (
                "filename sort tiebreak",
                '    return (adr["number"], adr["path"])',
                '    return (adr["number"], "")',
            ),
            (
                "preamble own-index guard",
                '    if "## Index" in preamble:',
                "    if False:",
            ),
            (
                "preamble h1 guard",
                '    if not body or not body[0].startswith("# "):',
                "    if False:",
            ),
            (
                "--check staleness guard",
                "        if current != rendered:",
                "        if False:",
            ),
        ],
    ),
    "plan": (
        "scripts/gen-plan.py",
        "scripts.tests.test_gen_plan",
        [
            (
                "lane-heading guard",
                '    if not heading.startswith("# "):',
                "    if False:",
            ),
            (
                "lane unknown-section guard",
                "            if name not in SECTIONS:",
                "            if False:",
            ),
            (
                "lane repeated-section guard",
                "            if name in contributions:",
                "            if False:",
            ),
            (
                "text-before-first-marker guard",
                "            if line.strip():",
                "            if False:",
            ),
            (
                "landed-row shape guard",
                "            if row is None:",
                "            if False:",
            ),
            (
                "landed-row ordering tiebreak",
                '    return (_negated_date(str(row["date"])), str(row["lane"]), int(row["ordinal"]))',
                '    return (_negated_date(str(row["date"])), "", 0)',
            ),
            (
                "empty-global guard",
                "    if not global_parts:",
                "    if False:",
            ),
            (
                "unknown-placeholder guard",
                "            if section not in SECTIONS:",
                "            if False:",
            ),
            (
                "repeated-placeholder guard",
                "            if section in seen:",
                "            if False:",
            ),
            (
                "missing-placeholder guard",
                "        if name not in seen:",
                "        if False:",
            ),
            (
                "plan-heading guard",
                '    if not body or not body[0].startswith("# "):',
                "    if False:",
            ),
            (
                "required-plan-marker guard",
                "        if marker not in rendered:",
                "        if False:",
            ),
            (
                "--check staleness guard",
                "        if current != rendered:",
                "        if False:",
            ),
        ],
    ),
    "fact-derived-numbers": (
        "scripts/check-fact-derived-numbers.py",
        "scripts.tests.test_check_fact_derived_numbers",
        [
            (
                "empty-literal claim vs a non-empty array",
                'if c.kind == "empty-literal" and total != 0:',
                "if False:",
            ),
            (
                "no-axiom prose vs a named declaration",
                'if c.kind == "no-axiom" and decls != 0:',
                "if False:",
            ),
            (
                "count in `supports` vs the array",
                'if c.kind == "count" and c.where.endswith(".supports") and c.asserted != decls:',
                "if False:",
            ),
            (
                "count in `notes` vs the array",
                'if c.kind == "count" and c.where.endswith(".notes") and c.asserted != decls:',
                "if False:",
            ),
            (
                "--expect-axioms flag vs the array",
                'if c.kind == "expect-axioms" and c.asserted != total:',
                "if False:",
            ),
            (
                "unchecked-claim ceiling",
                "if len(unchecked) > ceiling:",
                "if False:",
            ),
            (
                "anchored-slot floor (reader liveness)",
                "if reading.anchored_slots < floor:",
                "if False:",
            ),
        ],
    ),
    "lra-hypothesis-binding": (
        "scripts/check-lra-hypothesis-binding.py",
        "scripts.tests.test_check_lra_hypothesis_binding",
        [
            (
                # `bind`'s search moved into `_bind_monomial` when the degree-2
                # fragment landed; the guard is the same one, and the find-string
                # carries the two lines after it so it cannot drift onto the
                # sort check immediately below.
                "injectivity of the renaming",
                "            if target in next_used:\n                ok = False\n                break\n            if not sort_compatible",
                "            if False:\n                ok = False\n                break\n            if not sort_compatible",
            ),
            (
                "sort-soundness of the renaming",
                "            if not sort_compatible(carriers.get(factor), sorts.get(target)):\n                ok = False\n                break\n            next_phi = {**next_phi, factor: target}",
                "            if False:\n                ok = False\n                break\n            next_phi = {**next_phi, factor: target}",
            ),
            (
                "search completeness (all permutations, not the first)",
                "                found = extend(index + 1, next_phi, next_used, origins + (origin,))\n                if found is not None:\n                    return found",
                "                return extend(index + 1, next_phi, next_used, origins + (origin,))",
            ),
            (
                "unaccounted-axiom guard",
                "    if unaccounted:\n        return (None, [], set(), \"; \".join(unaccounted))",
                "    if False:\n        return (None, [], set(), \"; \".join(unaccounted))",
            ),
            (
                "carrier is an opaque constant of the right sort",
                "            if ty != carrier_hit:",
                "            if False:",
            ),
            (
                "re-check of whatever the search returned",
                "    problems = verify_binding(phi, hypotheses, allowed, carriers, sorts)\n    if problems:",
                "    problems = verify_binding(phi, hypotheses, allowed, carriers, sorts)\n    if False:",
            ),
            (
                "re-check: every renamed hypothesis is a query atom",
                "        if _rename(atom, phi) not in allowed:",
                "        if False:",
            ),
            (
                "re-check: injectivity",
                "        if target in seen:",
                "        if False:",
            ),
            (
                "both orientations of an equality reach the pool",
                '            out.append(canonical("=", flipped, -const))',
                "            pass",
            ),
            (
                "an equality is not sign-normalized by variable NAME",
                "    return (rel, tuple(sorted(ints.items())), k)",
                '    if rel == "=":\n'
                "        _ordered = sorted(ints.items())\n"
                "        _lead = _ordered[0][1] if _ordered else k\n"
                "        if _lead < 0:\n"
                "            ints = {v: -c for v, c in ints.items()}\n"
                "            k = -k\n"
                "    return (rel, tuple(sorted(ints.items())), k)",
            ),
            (
                "a disjunction entails neither disjunct",
                '    if (head == "and" and polarity) or (head == "or" and not polarity):',
                '    if head in ("and", "or"):',
            ),
            (
                "a disequality entails neither bound",
                '    if head == "=" and polarity and len(args) >= 2:',
                '    if head == "=" and len(args) >= 2:',
            ),
            (
                "an unknown rendered leaf is not a fresh variable",
                "        if expr.startswith(QUERY_NAMESPACE):\n            return ({(expr,): Fraction(1)}, Fraction(0))",
                "        if True:\n            return ({(expr,): Fraction(1)}, Fraction(0))",
            ),
            (
                "an `Eq` at the wrong sort is not an equality between query terms",
                "        if expr[1] != carrier:\n            raise Unsupported(",
                "        if False:\n            raise Unsupported(",
            ),
            (
                "a `let`-bound non-arithmetic name is not a fresh variable",
                "            if bound is OPAQUE:\n                raise Unsupported(",
                "            if False:\n                raise Unsupported(",
            ),
            (
                "attestation: the hypothesis vocabulary is closed",
                "            if token not in allowed:",
                "            if False:",
            ),
            (
                # Both this guard and the next are duplicated in
                # `bind_structural`, so the find-string carries the following
                # line: without it `str.replace` hits whichever copy comes first
                # in the file and the mutation silently controls the wrong one.
                "attestation: no axiom beyond the opaque sort",
                "            if (name, ty) != ATTESTATION_SORT_AXIOM:\n                return (\n                    False,",
                "            if False:\n                return (\n                    False,",
            ),
            (
                "attestation: a truncated multi-line type is refused",
                'if ty.count("(") != ty.count(")"):\n            # A type that spilled',
                "if False:\n            # A type that spilled",
            ),
            (
                "attestation: an `atom`/`prop` declares the opaque type it claims",
                "            if ty != declared:",
                "            if False:",
            ),
            (
                "attestation: a `func` is a function over the opaque sort",
                "            if not _is_opaque_function_type(ty):",
                "            if False:",
            ),
            (
                "attestation: a module with no hypothesis is not one",
                '    if not hypotheses:\n        return (False, "the module declares no hypothesis axiom at all", 0)',
                "    if False:\n        pass",
            ),
            (
                "attestation: a denied reflexivity is counted as self-refuting",
                "    return inner[2] == inner[3]",
                "    return False",
            ),
            (
                "a bound instance with no hypothesis binds vacuously",
                "        if not hypotheses:\n            # A module with no hypothesis",
                "        if False:\n            # A module with no hypothesis",
            ),
            (
                "a self-refuting attestation FAILS rather than being counted",
                "            attested_vacuous += vacuous\n            if vacuous:",
                "            attested_vacuous += vacuous\n            if False:",
            ),
            (
                "structural: the renaming is injective",
                "    if smt in phi.values():\n        return None",
                "    if False:\n        return None",
            ),
            (
                "structural: the renaming is a function",
                "        return phi if phi[lean] == smt else None",
                "        return phi",
            ),
            (
                "structural: a rendered application must match one of the same arity",
                "    if isinstance(smt, str) or len(smt) - 1 != len(lean) - 1:",
                "    if isinstance(smt, str):",
            ),
            (
                "structural: a bare pair of constants carries no structure",
                "    if not any(isinstance(side, list) for side in sides):",
                "    if False:",
            ),
            (
                "structural: a declared constant no rendered term uses is refused",
                "        if name not in phi:",
                "        if False:",
            ),
            (
                "structural: an indexed identifier is a literal, not an application",
                '    if head == "_":',
                "    if False:",
            ),
            (
                "an attestation that CAN be bound structurally is not an attestation",
                "            bound_anyway, _why, nodes = bind_structural(source, path)\n            if bound_anyway:",
                "            bound_anyway, _why, nodes = bind_structural(source, path)\n            if False:",
            ),
            (
                # Keyed on the adjacency, not on the old overlap test: the
                # converse count became a maximum matching on 2026-08-18 and this
                # control's find-string went with it. A control whose text has
                # drifted reports MUTATION DID NOT APPLY, which is how three
                # guards in this file went dead once already.
                "the converse direction counts UNrendered rows as unrepresented",
                "        [index for index in spine if atom in assertions[index]] for atom in renamed",
                "        [index for index in spine] for atom in renamed",
            ),
            (
                # A maximum MATCHING, not an overlap: let one hypothesis claim
                # every row it appears in and three assertions entailing a common
                # atom are all credited to a module that rendered it once. The
                # measured shortfall shrinks, in the direction nobody checks.
                "the converse direction gives each row its OWN hypothesis",
                "                owner[index] = hypothesis\n                return True",
                "                owner[index] = hypothesis\n                continue",
            ),
            (
                # A row this parser cannot decompose is unrepresentable whatever
                # the module renders. Without the ceiling it arrives as a lower
                # `represented_assertions` and reads as the refutations resting
                # on less of the query -- one number shrinking for two opposite
                # reasons, with no way to tell which.
                "an undecomposable spine row FAILS rather than lowering the number",
                "    if undecomposable_spine > args.max_undecomposable_spine:",
                "    if False:",
            ),
            (
                # `_AND_HEADS` / `_OR_HEADS` are propagated under OPPOSITE
                # polarities on purpose. Making the `or` rule fire under a true
                # polarity turns a disjunction into a fact, which is the whole
                # class of bug anchoring exists to refuse.
                "anchor: an `or` under a true polarity is not a fact",
                "        elif head in _OR_HEADS and not value:",
                "        elif head in _OR_HEADS:",
            ),
            (
                "anchor: an `ite` needs the Boolean branch pair to be descended",
                "            if then_bit is True and else_bit is False:\n                stack.append((args[0], value))",
                "            if True:\n                stack.append((args[0], value))",
            ),
            (
                "anchor: an asserted EQUALITY is not a disequality",
                "            if not value:\n                record(args[0], args[1])",
                "            if True:\n                record(args[0], args[1])",
            ),
            (
                "anchor: `distinct` is only a disequality under a true polarity",
                'elif head == "distinct" and value:',
                'elif head == "distinct":',
            ),
            (
                "anchor: the module must state a DISEQUALITY",
                "    if not disequality:",
                "    if False:",
            ),
            (
                "anchor: every hypothesis equates the same pair",
                "            elif pair != sides:",
                "            elif False:",
            ),
            (
                "anchor: the forced disequality must be UNIQUE",
                "    if len(matches) > 1:",
                "    if False:",
            ),
            (
                "anchor: a module the query forces nothing for is refused",
                "    if not matches:",
                "    if False and not matches:",
            ),
            (
                # Duplicated in `bind_structural` and `classify_attestation`, so
                # the find-string carries the following line to pin WHICH copy.
                "anchor: a declared constant no rendered term uses is refused",
                "    phi = matches[0]\n    for name in declared:\n        if name not in phi:",
                "    phi = matches[0]\n    for name in declared:\n        if False:",
            ),
            (
                # Same shape as the structural/attestation copies above; the
                # find-string carries the `bind_anchored` message that follows it.
                "anchor: no axiom beyond the opaque sort",
                "            if (name, ty) != ATTESTATION_SORT_AXIOM:\n                return (\n                    False,\n                    f\"`{name} : {ty}` is not the opaque sort `α : Sort (1)`\",\n                    0,\n                )",
                "            if False:\n                return (\n                    False,\n                    f\"`{name} : {ty}` is not the opaque sort `α : Sort (1)`\",\n                    0,\n                )",
            ),
            (
                "an attestation the query ENTAILS is not an attestation",
                "            anchored_anyway, _why, _nodes = bind_anchored(source, path)\n            if anchored_anyway:",
                "            anchored_anyway, _why, _nodes = bind_anchored(source, path)\n            if False:",
            ),
            (
                # The conjunction walker must reach BOTH conjuncts. Short-circuit
                # it and a `¬(r₁ ∧ … ∧ rₙ)` module binds on r₁ alone, with the
                # other n−1 rendered terms never compared to the file at all.
                "structural: every conjunct's terms are collected, not just the first",
                "            return walk(node[1]) and walk(node[2])",
                "            return walk(node[1]) or walk(node[2])",
            ),
            (
                # A backtracking matcher that runs forever is a gate that never
                # reports; one that gives up quietly is a gate that passes. The
                # budget must exist AND its verdict must be distinct from a
                # refusal.
                "structural: the search budget is enforced",
                '            state["nodes"] += 1\n            if state["nodes"] > budget:',
                '            state["nodes"] += 1\n            if False:',
            ),
            (
                # The anti-absorption guard in the direction that only appeared
                # once the four verdicts became a PARTITION: a row pinned
                # `structural` that also anchors must be refused, or the stronger
                # of two true statements stays unrecorded forever. 66 instances
                # sat in exactly that state until it was measured.
                "a structural-ONLY pin is refused when the query also anchors",
                "            if not wants_anchored and a_ok:",
                "            if False and a_ok:",
            ),
            (
                # And the same from the other side. `anchored` alone claims the
                # structural binder cannot grip the module -- for the 7 bare-pair
                # rows left in that class that admission IS the class, so it has
                # to be checked rather than asserted in a comment.
                "an anchored-ONLY pin is refused when the module binds structurally",
                "            if not wants_structural and s_ok:",
                "            if False and s_ok:",
            ),
        ],
    ),
}


def baseline_and_mutants(name: str) -> int:
    generator, test_module, mutations = SUITES[name]
    survivors: list[str] = []

    with tempfile.TemporaryDirectory(prefix=f"mutation-{name}-") as tmp:
        work = Path(tmp) / "repo"
        shutil.copytree(
            ROOT,
            work,
            ignore=shutil.ignore_patterns(
                ".git", "target", "references", "corpus", "bench-results", "__pycache__"
            ),
            symlinks=True,
        )
        source = work / generator
        original = source.read_text(encoding="utf-8")

        def run() -> tuple[int, str]:
            done = subprocess.run(
                [sys.executable, "-m", "unittest", test_module],
                cwd=work,
                capture_output=True,
                text=True,
            )
            return done.returncode, done.stderr

        code, _ = run()
        if code != 0:
            print(f"{name}: BASELINE IS RED; fix the tests before mutating")
            return 1
        print(f"{name}: baseline green")

        for label, find, replace in mutations:
            if find not in original:
                print(f"  {label:34s} MUTATION DID NOT APPLY (guard text moved)")
                survivors.append(label)
                continue
            source.write_text(original.replace(find, replace, 1), encoding="utf-8")
            code, stderr = run()
            source.write_text(original, encoding="utf-8")
            killed = [
                line.split(" ", 2)[1]
                for line in stderr.splitlines()
                if line.startswith(("FAIL: ", "ERROR: "))
            ]
            if code == 0:
                print(f"  {label:34s} SURVIVED — no test depends on this guard")
                survivors.append(label)
            else:
                print(f"  {label:34s} killed {len(killed)}: {', '.join(killed) or 'see output'}")

    if survivors:
        print(f"{name}: {len(survivors)} guard(s) not covered by any test")
        return 1
    return 0


def main(argv: list[str]) -> int:
    names = argv[1:] or sorted(SUITES)
    failed = 0
    for name in names:
        if name not in SUITES:
            print(f"unknown suite {name!r}; known: {', '.join(sorted(SUITES))}")
            return 2
        failed |= baseline_and_mutants(name)
    return failed


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
