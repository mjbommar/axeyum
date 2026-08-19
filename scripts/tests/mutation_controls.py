#!/usr/bin/env python3
"""Delete one guard at a time and require each deletion to kill a test.

A guard nobody can remove is decoration.  This harness copies a generator into
a scratch tree, applies one textual mutation (each of which removes exactly one
guard), runs that generator's test module, and reports which tests died.

Usage::

    python3 scripts/tests/mutation_controls.py            # every gated suite
    python3 scripts/tests/mutation_controls.py adr-index  # one of them
    python3 scripts/tests/mutation_controls.py self-demo  # all four outcomes, live

# A mutation check must not report a result it did not measure

Measured 2026-08-18 against the harness as it stood: a mutation that makes the
subject *fail to compile* was reported as ``killed 0``, and counted toward
coverage.  So was a suite that executed **zero** tests -- the
``#![cfg(feature = "full")]`` trap, which is `already documented in CLAUDE.md
<../../CLAUDE.md>`_ as printing ``running 0 tests ... ok`` and exiting 0.  Both
present as "the run was not clean", which the old classifier read as "a test
died".  Every ``exactly one test died`` in this repository's history rests on the
mutant having been built and run, and nothing checked either.

So the outcome of a mutation is now one of a closed set, and only the first two
are *measurements*:

``killed N``
    built, ran the baseline's tests, N of them died.  The only outcome that
    supports a coverage claim.
``SURVIVED``
    built, ran the baseline's tests, none died.  A real finding: the guard is
    not load-bearing.  Previously indistinguishable from the two below.
``DID NOT BUILD``
    the mutation broke the subject.  Not a result.
``DID NOT RUN``
    it built, but the suite executed zero tests -- or a different number from
    the baseline, which means the mutation changed *collection* rather than
    behaviour.  Not a result.
``NOT APPLIED`` / ``AMBIGUOUS ANCHOR``
    the anchor text is absent, matches nothing new, or matches in more than one
    place so nobody can say which copy was mutated.  Not a result.
``INCONSISTENT``
    the run's two independent kill counts -- the ``FAIL:``/``ERROR:`` headers and
    the summary line -- disagree, or the exit status contradicts both.  The
    harness cannot say what happened, so it says that.

Exit status is 0 only when every mutation is ``killed N``.  Survivors and
unmeasured mutations are counted and printed **separately**: "the guard is not
tested" and "the harness could not tell" are different failures and the fix for
one is not the fix for the other.

The subject is never mutated in place.  Every run works on a scratch copy in a
``TemporaryDirectory``, so a killed process cannot leave a mutated tree behind,
and the restore after each mutation is verified byte-for-byte rather than
assumed.

This is a control, not a gate: it rewrites a scratch copy of the repository, so
it is run deliberately rather than from `scripts/check.sh`.
"""

from __future__ import annotations

import importlib.util
import os
import re
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass, field
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]

# (subject path, runner, [(mutation name, find, replace[, file mutated]), ...])
#
# The runner is either a test-module name -- `python3 -m unittest <module>` --
# or a `Cargo(...)`.  A mutation's optional FOURTH element names the file it
# edits when that is not the subject, which is how a control can be mutated to
# check the control.
SUITES: dict[str, tuple[str, "str | Unittest | Cargo", list[tuple[str, ...]]]] = {
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
            (
                "remote-collision: non-numbered filename is skipped, not crashed",
                "        if match is None:\n            continue",
                "        if False:\n            continue",
            ),
            (
                "remote-collision: BOTH sides must have a file the other lacks",
                "        if local_only and remote_only:",
                "        if True:",
            ),
            (
                "check-remote: unresolvable ref is SKIPPED before comparing",
                "    if commit is None:",
                "    if False:",
            ),
            (
                "check-remote: staleness is measured, not assumed fresh",
                "    stale = age is None or age > max_staleness_hours * 3600.0",
                "    stale = False",
            ),
            (
                "check-remote: a found collision fails the gate",
                "    if collisions:",
                "    if False:",
            ),
            (
                "--check-remote CLI flag actually routes to check_remote",
                "    if args.check_remote:\n        return check_remote(",
                "    if False:\n        return check_remote(",
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
    # Cargo-backed: every run rebuilds the isolated kernel preludes, so the
    # first `run()` in the scratch tree pays a cold build and the rest reuse it.
    # Slower than the pure-Python suites and worth it -- the guards here are what
    # stop the project's headline trust number from moving unobserved.
    "lean-axiom-ledger": (
        "scripts/gen-lean-axiom-ledger.py",
        "scripts.tests.test_lean_axiom_ledger",
        [
            ("EXPECTED_PRELUDES drops creal", '    "creal",\n', ""),
            ("EXPECTED_PRELUDES drops complex", '    "complex",\n', ""),
            ("EXPECTED_PRELUDES drops rat", '    "rat",\n', ""),
            (
                "rise reported as REGRESSION",
                "if isinstance(was, int) and now > was:",
                "if False:",
            ),
            (
                "fall reported as IMPROVEMENT",
                "elif isinstance(was, int) and now < was:",
                "elif False:",
            ),
            ("coverage-lost branch", "if after is None:", "if False:"),
            ("coverage-added branch", "if before is None:", "if False:"),
            (
                "kind-reshape branch",
                '            else:\n                failures.append(\n'
                '                    f"{STALE} -- RESHAPED: `{prelude}` trusted surface is still "',
                '            elif False:\n                failures.append(\n'
                '                    f"{STALE} -- RESHAPED: `{prelude}` trusted surface is still "',
            ),
            (
                "unexplained-drift catch-all",
                "    if not failures:\n        failures.append(\n"
                '            f"{STALE}; committed {json.dumps(committed, sort_keys=True)} vs "\n'
                '            f"measured {json.dumps(derived, sort_keys=True)}"\n        )\n',
                "",
            ),
            (
                "non-object measurement guard",
                "if not isinstance(committed, dict):",
                "if False:",
            ),
            # Not independently isolable: without the flag `measure()` fails
            # cross-check and the whole suite dies at setUpClass. Listed so the
            # control records that, rather than leaving it untested-looking.
            (
                "--include-constructed on the coverage command",
                ' -- --include-constructed"',
                '"',
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
                # THREE copies exist -- `bind_structural`, `bind_anchored`,
                # `classify_attestation` -- and the context above matched TWO, so
                # `replace(…, 1)` silently mutated `bind_anchored`: the same copy
                # the `anchor:` control below already drives, leaving
                # `classify_attestation`'s untested under a label that claimed
                # otherwise. Found 2026-08-18 by AMBIGUOUS ANCHOR. The message
                # text is what makes this one unique.
                "attestation: no axiom beyond the opaque sort",
                '            if (name, ty) != ATTESTATION_SORT_AXIOM:\n                return (\n                    False,\n                    f"`{name} : {ty}` is not the opaque sort `\u03b1 : Sort (1)`, so this "',
                '            if False:\n                return (\n                    False,\n                    f"`{name} : {ty}` is not the opaque sort `\u03b1 : Sort (1)`, so this "',
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
                # Was `_is_self_refuting`'s own `inner[2] == inner[3]`; the
                # predicate moved into `_is_refl_provable` when it was widened
                # past the one shape anybody had looked at, and the guard is the
                # same one: `Not (Eq τ t t)` is `rfl`, `Not (Eq τ a b)` is not.
                "self-refutation: a reflexive EQUALITY is recognized",
                '    if head in EQ_HEADS and len(expr) == 4:\n        return expr[2] == expr[3]',
                "    if head in EQ_HEADS and len(expr) == 4:\n        return False",
            ),
            (
                "a bound instance with no hypothesis binds vacuously",
                "        if not hypotheses:\n            # A module with no hypothesis",
                "        if False:\n            # A module with no hypothesis",
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
                # Also duplicated in `bind_anchored`; the bare guard matched both.
                # It happened to hit the right copy -- first in file order -- but
                # nothing said so, which is the same silence as hitting the wrong
                # one. The three preceding lines pin `bind_structural`.
                "structural: a declared constant no rendered term uses is refused",
                "            0,\n        )\n    for name in declared:\n        if name not in phi:",
                "            0,\n        )\n    for name in declared:\n        if False:",
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
            (
                # The predicate that found the corpus's SECOND self-refuting
                # module. Stop walking the `And`-tree and only the one shape
                # anybody had already looked at is recognized -- which is exactly
                # the state this was in before 2026-08-18.
                "self-refutation: the whole And-tree is walked",
                "    if head == \"And\" and len(expr) == 3:\n"
                "        return _is_refl_provable(expr[1]) and _is_refl_provable(expr[2])",
                "    if head == \"And\" and len(expr) == 3:\n        return False",
            ),
            (
                # ...and the discriminating half: a conjunct relating two
                # DIFFERENT props is a real assumption. Weaken the comparison and
                # the predicate condemns honest modules.
                "self-refutation: the two sides must be IDENTICAL",
                '    if head == "Iff" and len(expr) == 3:\n        return expr[1] == expr[2]',
                '    if head == "Iff" and len(expr) == 3:\n        return True',
            ),
            (
                # The check runs on EVERY class, before any verdict.
                # `classify_attestation` could only see the class it was already
                # looking at, and the second self-refuting module was in the
                # DECLINED list where nothing ran at all.
                "self-refutation is checked on every rendered module",
                "        vacuous_here = self_refuting_axioms(source)\n        if vacuous_here:",
                "        vacuous_here = self_refuting_axioms(source)\n        if False:",
            ),
            (
                "declined: an instance that binds structurally must move",
                "            s_ok, _why, s_nodes = bind_structural(source, path)\n            if s_ok:",
                "            s_ok, _why, s_nodes = bind_structural(source, path)\n            if False:",
            ),
            (
                "declined: an instance that is an attestation must move",
                "            att_ok, _why, _vacuous = classify_attestation(source)\n            if att_ok:",
                "            att_ok, _why, _vacuous = classify_attestation(source)\n            if False:",
            ),
        ],
    ),
}


# --------------------------------------------------------------------------
# Outcomes.  Exactly two of these are measurements; the rest say so out loud.
# --------------------------------------------------------------------------

KILLED = "killed"
SURVIVED = "SURVIVED"
NO_BUILD = "DID NOT BUILD"
NO_RUN = "DID NOT RUN"
NOT_APPLIED = "NOT APPLIED"
AMBIGUOUS = "AMBIGUOUS ANCHOR"
INCONSISTENT = "INCONSISTENT"

#: The only outcomes a coverage claim may rest on.
MEASUREMENTS = (KILLED, SURVIVED)


@dataclass(frozen=True)
class Report:
    """What one mutation actually produced.

    ``outcome`` is one of the constants above.  ``tests_run`` is ``None`` when
    the runner never said, which is itself a finding rather than a zero.
    """

    outcome: str
    tests_run: int | None = None
    deaths: tuple[str, ...] = ()
    detail: str = ""

    @property
    def measured(self) -> bool:
        return self.outcome in MEASUREMENTS

    def line(self) -> str:
        if self.outcome == KILLED:
            names = ", ".join(self.deaths)
            return f"killed {len(self.deaths)}: {names}"
        if self.outcome == SURVIVED:
            return f"SURVIVED — {self.tests_run} tests ran, none depend on this guard"
        return f"{self.outcome} — {self.detail}" if self.detail else self.outcome


# --------------------------------------------------------------------------
# Classifiers.  Pure functions over (exit status, output, baseline test count),
# so `scripts/tests/test_mutation_controls.py` can drive every branch without
# building anything.
# --------------------------------------------------------------------------

_UNITTEST_RAN = re.compile(r"^Ran (\d+) tests? in ", re.M)
_UNITTEST_OK = re.compile(r"^OK(?: \([^)]*\))?[ \t]*$", re.M)
_UNITTEST_FAILED = re.compile(r"^FAILED \(([^)]*)\)[ \t]*$", re.M)
_UNITTEST_DEATH = re.compile(r"^(?:FAIL|ERROR): (\S+)", re.M)


def _collection_report(tests_run: int | None, baseline_tests: int | None) -> Report | None:
    """The half of classification that is the same for every runner."""
    if tests_run is None:
        return Report(NO_RUN, None, (), "the runner never reported how many tests ran")
    if tests_run == 0:
        return Report(NO_RUN, 0, (), "the suite built and then executed zero tests")
    if baseline_tests is not None and tests_run != baseline_tests:
        return Report(
            NO_RUN,
            tests_run,
            (),
            f"collection changed: {tests_run} tests ran, the baseline ran {baseline_tests}",
        )
    return None


def _verdict(
    tests_run: int,
    deaths: tuple[str, ...],
    counted: int,
    returncode: int,
) -> Report:
    """Cross-check the two independent kill counts against the exit status."""
    if counted != len(deaths):
        return Report(
            INCONSISTENT,
            tests_run,
            deaths,
            f"the summary line says {counted} died but {len(deaths)} were named",
        )
    if counted == 0:
        if returncode != 0:
            return Report(
                INCONSISTENT,
                tests_run,
                deaths,
                f"no test died but the exit status is {returncode}",
            )
        return Report(SURVIVED, tests_run, (), "")
    if returncode == 0:
        return Report(
            INCONSISTENT,
            tests_run,
            deaths,
            f"{counted} test(s) died but the exit status is 0",
        )
    return Report(KILLED, tests_run, deaths, "")


def classify_unittest(returncode: int, output: str, baseline_tests: int | None) -> Report:
    """Read a `python -m unittest` run without believing its exit status alone."""
    ran = _UNITTEST_RAN.search(output)
    early = _collection_report(int(ran.group(1)) if ran else None, baseline_tests)
    if early is not None:
        return early
    tests_run = int(ran.group(1))  # type: ignore[union-attr]
    deaths = tuple(match.group(1) for match in _UNITTEST_DEATH.finditer(output))
    failed = _UNITTEST_FAILED.search(output)
    ok = _UNITTEST_OK.search(output)
    if failed is not None and ok is not None:
        return Report(INCONSISTENT, tests_run, deaths, "both an OK and a FAILED summary line")
    if failed is not None:
        counted = sum(
            int(value)
            for _kind, value in re.findall(r"(failures|errors)=(\d+)", failed.group(1))
        )
    elif ok is not None:
        counted = 0
    else:
        return Report(
            INCONSISTENT, tests_run, deaths, "no OK/FAILED summary line to cross-check against"
        )
    return _verdict(tests_run, deaths, counted, returncode)


_CARGO_RUNNING = re.compile(r"^running (\d+) tests?$", re.M)
_CARGO_RESULT = re.compile(
    r"^test result: (?:ok|FAILED)\. (\d+) passed; (\d+) failed;", re.M
)
_CARGO_DEATH = re.compile(r"^test (\S+) \.\.\. FAILED$", re.M)


def classify_cargo(returncode: int, output: str, baseline_tests: int | None) -> Report:
    """Read a `cargo test` run the same way.

    `cargo test` is where the trap was found: a mutant that does not compile
    prints no `test result:` line at all, and a suite behind an unset feature
    prints `running 0 tests ... ok` and exits 0.  Both are caught here rather
    than being read off the exit status.
    """
    if returncode == 75:
        return Report(INCONSISTENT, None, (), "cargo-serialized.sh could not take a slot (75)")
    blocks = _CARGO_RUNNING.findall(output)
    results = _CARGO_RESULT.findall(output)
    if len(blocks) != len(results):
        return Report(
            INCONSISTENT,
            None,
            (),
            f"{len(blocks)} test binaries started but {len(results)} reported a result",
        )
    tests_run = sum(int(n) for n in blocks) if blocks else None
    early = _collection_report(tests_run, baseline_tests)
    if early is not None:
        return early
    deaths = tuple(match.group(1) for match in _CARGO_DEATH.finditer(output))
    counted = sum(int(failed) for _passed, failed in results)
    return _verdict(int(tests_run or 0), deaths, counted, returncode)


# --------------------------------------------------------------------------
# Runners.  A runner knows two things: how to BUILD the subject without running
# it (so `DID NOT BUILD` is decided before any test count is believed), and how
# to run the suite and classify the output.
# --------------------------------------------------------------------------


def _capture(argv: list[str], cwd: Path, env: dict[str, str] | None = None) -> tuple[int, str]:
    done = subprocess.run(
        argv,
        cwd=cwd,
        capture_output=True,
        text=True,
        env={**os.environ, **(env or {})} if env else None,
    )
    return done.returncode, done.stdout + done.stderr


@dataclass(frozen=True)
class Unittest:
    """`python3 -m unittest <module>`."""

    module: str

    def describe(self) -> str:
        return f"python3 -m unittest {self.module}"

    def build(self, work: Path, targets: list[str]) -> tuple[bool, str]:
        for target in targets:
            code, out = _capture([sys.executable, "-m", "py_compile", str(work / target)], work)
            if code != 0:
                return (False, _tail(out))
        # Importing the test module loads the subject without running a test,
        # which is this route's `cargo test --no-run`: it catches an import-time
        # failure that `py_compile` cannot see.
        code, out = _capture([sys.executable, "-c", f"import {self.module}"], work)
        return (code == 0, _tail(out))

    def measure(self, work: Path, baseline_tests: int | None) -> Report:
        code, out = _capture([sys.executable, "-m", "unittest", self.module], work)
        return classify_unittest(code, out, baseline_tests)


@dataclass(frozen=True)
class Cargo:
    """`scripts/cargo-serialized.sh test <args>` -- heavy cargo is never bare.

    `target_dir` is a persistent cache OUTSIDE the scratch tree, so the second
    mutation does not pay the first one's cold build.  It defaults to
    `$AXEYUM_MUTATION_CARGO_TARGET` or a per-suite directory under /data0,
    never the shared checkout's `target/` (which other lanes are using).
    """

    args: tuple[str, ...]
    slug: str

    def describe(self) -> str:
        return "scripts/cargo-serialized.sh test " + " ".join(self.args)

    def _env(self) -> dict[str, str]:
        root = os.environ.get("AXEYUM_MUTATION_CARGO_TARGET", "/data0/axeyum-mutation-target")
        return {"CARGO_TARGET_DIR": f"{root}/{self.slug}"}

    def _cargo(self, work: Path, extra: list[str]) -> tuple[int, str]:
        return _capture(
            [str(ROOT / "scripts" / "cargo-serialized.sh"), "test", *self.args, *extra],
            work,
            self._env(),
        )

    def build(self, work: Path, targets: list[str]) -> tuple[bool, str]:
        code, out = self._cargo(work, ["--no-run"])
        return (code == 0, _tail(out))

    def measure(self, work: Path, baseline_tests: int | None) -> Report:
        code, out = self._cargo(work, [])
        return classify_cargo(code, out, baseline_tests)


def _tail(text: str, lines: int = 4) -> str:
    kept = [line for line in text.strip().splitlines() if line.strip()][-lines:]
    return " / ".join(kept)[:400]


# --------------------------------------------------------------------------
# Suite normalization.  The committed entries are 3-tuples of 3-tuples; a
# mutation may carry a fourth element naming the file it edits, which is how a
# control can mutate a CONTROL (see `self-demo`).
# --------------------------------------------------------------------------


@dataclass(frozen=True)
class Mutation:
    label: str
    find: str
    replace: str
    target: str | None = None


@dataclass(frozen=True)
class Suite:
    subject: str
    runner: Unittest | Cargo
    mutations: tuple[Mutation, ...]
    targets: tuple[str, ...] = field(default=())


def normalize(name: str) -> Suite:
    subject, runner, raw = SUITES[name]
    if isinstance(runner, str):
        runner = Unittest(runner)
    mutations = tuple(
        Mutation(entry[0], entry[1], entry[2], entry[3] if len(entry) > 3 else None)
        for entry in raw
    )
    targets = tuple(dict.fromkeys([subject] + [m.target for m in mutations if m.target]))
    return Suite(subject, runner, mutations, targets)


def _touch_tree(work: Path) -> None:
    """Cargo decides freshness by MTIME and `copytree` preserves it (CLAUDE.md).

    Without this a scratch tree whose files are older than a warm target cache
    is invisible to cargo, and the mutant that "passed" was never rebuilt.
    """
    for path in work.rglob("*"):
        try:
            os.utime(path, None)
        except OSError:
            pass


def _apply(text: str, mutation: Mutation) -> tuple[str | None, Report | None]:
    occurrences = text.count(mutation.find)
    if occurrences == 0:
        return (None, Report(NOT_APPLIED, None, (), "the anchor text is not in the subject"))
    if occurrences > 1:
        return (
            None,
            Report(
                AMBIGUOUS,
                None,
                (),
                f"the anchor matches {occurrences} places; nobody can say which was mutated",
            ),
        )
    mutated = text.replace(mutation.find, mutation.replace, 1)
    if mutated == text:
        return (None, Report(NOT_APPLIED, None, (), "the replacement leaves the file unchanged"))
    return (mutated, None)


def _scratch_root() -> str | None:
    """Where the scratch copy goes.  NOT /tmp, which on this fleet is RAM.

    CLAUDE.md measures /tmp here as a 62 G **tmpfs** at 81% full with 9.3 GB of
    abandoned snapshots in it, and a kernel OOM has already killed a live agent
    on this box.  Each suite copies ~430 MB, so a run of the harness's own
    control module is a couple of GB of transient tmpfs if nobody says
    otherwise.  `$AXEYUM_MUTATION_TMP` wins; /data0 is the fleet's disk; the
    system default is the last resort.
    """
    override = os.environ.get("AXEYUM_MUTATION_TMP")
    if override:
        Path(override).mkdir(parents=True, exist_ok=True)
        return override
    disk = Path("/data0/axeyum-mutation-scratch")
    if Path("/data0").is_dir():
        disk.mkdir(parents=True, exist_ok=True)
        return str(disk)
    return None


def _restore(path: Path, original: str) -> None:
    """Put the file back, and CHECK that it went back.

    The subject only ever lives in a scratch copy, so a mutated tree cannot
    escape this process -- but a restore that silently did not take would let
    mutation N+1 run against mutation N's damage and report a death for it.
    """
    path.write_text(original, encoding="utf-8")
    if path.read_text(encoding="utf-8") != original:
        raise RuntimeError(f"{path} was not restored")


def baseline_and_mutants(name: str, quiet: bool = False) -> tuple[int, list[tuple[str, Report]]]:
    suite = normalize(name)
    reports: list[tuple[str, Report]] = []

    with tempfile.TemporaryDirectory(prefix=f"mutation-{name}-", dir=_scratch_root()) as tmp:
        work = Path(tmp) / "repo"
        shutil.copytree(
            ROOT,
            work,
            ignore=shutil.ignore_patterns(
                ".git", "target", "references", "corpus", "bench-results", "__pycache__"
            ),
            symlinks=True,
        )
        _touch_tree(work)
        originals = {target: (work / target).read_text(encoding="utf-8") for target in suite.targets}

        built, why = suite.runner.build(work, list(suite.targets))
        if not built:
            print(f"{name}: BASELINE DID NOT BUILD; {why}")
            return (1, reports)
        base = suite.runner.measure(work, None)
        if base.outcome != SURVIVED:
            print(f"{name}: BASELINE IS NOT GREEN — {base.line()}")
            return (1, reports)
        baseline_tests = base.tests_run
        print(f"{name}: baseline green, {baseline_tests} tests ({suite.runner.describe()})")

        for mutation in suite.mutations:
            target = mutation.target or suite.subject
            original = originals[target]
            mutated, refusal = _apply(original, mutation)
            if refusal is not None:
                reports.append((mutation.label, refusal))
                if not quiet:
                    print(f"  {mutation.label:34s} {refusal.line()}")
                continue
            path = work / target
            try:
                path.write_text(mutated or "", encoding="utf-8")
                built, why = suite.runner.build(work, list(suite.targets))
                if not built:
                    report = Report(NO_BUILD, None, (), why)
                else:
                    report = suite.runner.measure(work, baseline_tests)
            finally:
                _restore(path, original)
            reports.append((mutation.label, report))
            if not quiet:
                print(f"  {mutation.label:34s} {report.line()}")

    survivors = [label for label, report in reports if report.outcome == SURVIVED]
    unmeasured = [(label, report) for label, report in reports if not report.measured]
    if unmeasured:
        print(f"{name}: {len(unmeasured)} mutation(s) NOT MEASURED — these are not results:")
        for label, report in unmeasured:
            print(f"    {label}: {report.line()}")
    if survivors:
        print(f"{name}: {len(survivors)} guard(s) not covered by any test")
    status = 0
    if unmeasured:
        status = 1
    if survivors:
        status = 1
    return (status, reports)


# --------------------------------------------------------------------------
# `self-demo` — the four outcomes, each from a real mutation.
#
# A harness that has only ever been shown its happy path is exactly what this
# file is about, so the four outcomes are not asserted in prose: this suite
# produces one of each, live, and fails unless the harness names each correctly.
# The fourth mutation targets the CONTROL rather than the subject, because
# "the suite executed zero tests" is a property of the suite -- that is the
# `#![cfg(feature = "full")]` shape, where the module compiles and collects
# nothing.
# --------------------------------------------------------------------------

# --------------------------------------------------------------------------
# `fp-width-guard` — the CARGO route, exercised end to end.
#
# The incident that prompted the four-outcome rewrite was a Rust mutation using
# a method that does not exist: `cargo test` printed a compile error, no
# `test result:` line, and the grep watching for a death found nothing --
# silence, in a slot where "the guard did not fire" and "the mutant never ran"
# look identical.  `classify_cargo` is unit-tested against captured output; this
# suite is what actually drives `cargo test` through it, on the cheapest real
# soundness guard in the workspace (`FloatFormat::check`, 2 tests, ~2 s warm).
#
# Heavy cargo goes through `scripts/cargo-serialized.sh`, and the build cache is
# a persistent directory OUTSIDE both the scratch tree and the shared checkout's
# `target/`, so the second mutation does not pay the first one's cold build and
# no other lane's build is disturbed.
# --------------------------------------------------------------------------

SUITES["fp-width-guard"] = (
    "crates/axeyum-fp/src/lib.rs",
    Cargo(("-p", "axeyum-fp", "--test", "width_guard"), "fp-width-guard"),
    [
        (
            "the >128-bit width guard exists at all",
            "        if self.width() > 128 {",
            "        if self.width() > 100_000 {",
        ),
        (
            "128 itself is representable (the boundary, not the guard)",
            "        if self.width() > 128 {",
            "        if self.width() >= 128 {",
        ),
    ],
)


# --------------------------------------------------------------------------
# `mutation-controls` — the harness applied to itself.  The table lives in the
# sibling module: an anchor stored in the file it mutates matches twice and the
# harness rightly refuses it (`AMBIGUOUS ANCHOR`).
# --------------------------------------------------------------------------

_SELF = importlib.util.spec_from_file_location(
    "mutation_controls_self", Path(__file__).with_name("mutation_controls_self.py")
)
assert _SELF is not None and _SELF.loader is not None
_SELF_TABLE = importlib.util.module_from_spec(_SELF)
_SELF.loader.exec_module(_SELF_TABLE)

SUITES["mutation-controls"] = (
    _SELF_TABLE.SUBJECT,
    _SELF_TABLE.CONTROLS,
    _SELF_TABLE.MUTATIONS,
)


DEMO_SUBJECT = "scripts/tests/fixtures/mutation_demo/subject.py"
DEMO_CONTROL = "scripts/tests/fixtures/mutation_demo/suite_tests.py"

SUITES["self-demo"] = (
    DEMO_SUBJECT,
    "scripts.tests.fixtures.mutation_demo.suite_tests",
    [
        ("a guard a control drives", "    if n < 0:", "    if False:"),
        ("a guard NO control drives", "    if n > 100:", "    if False:"),
        ("a mutation that breaks the parse", "def classify(n: int) -> str:", "def classify(n: int) -> str"),
        (
            # Renaming the CLASS does not work -- `unittest` collects by base
            # class, not by name -- and finding that out is why this demo exists.
            # Dropping the base is the `#![cfg(feature = "full")]` shape: the
            # module still imports, and collects nothing.
            "a mutation that empties collection",
            "class DemoControls(unittest.TestCase):",
            "class DemoControls:",
            DEMO_CONTROL,
        ),
    ],
)

DEMO_EXPECTED = {
    "a guard a control drives": KILLED,
    "a guard NO control drives": SURVIVED,
    "a mutation that breaks the parse": NO_BUILD,
    "a mutation that empties collection": NO_RUN,
}

#: Suites whose point is to produce non-results; excluded from a bare run.
DEMOS = {"self-demo"}


def run_demo() -> int:
    _status, reports = baseline_and_mutants("self-demo")
    observed = {label: report.outcome for label, report in reports}
    wrong = [
        f"{label}: expected {want}, harness said {observed.get(label, '<no report>')}"
        for label, want in DEMO_EXPECTED.items()
        if observed.get(label) != want
    ]
    if wrong:
        print("self-demo: the harness MISCLASSIFIED " + f"{len(wrong)} of {len(DEMO_EXPECTED)}:")
        for line in wrong:
            print(f"    {line}")
        return 1
    print(f"self-demo: all {len(DEMO_EXPECTED)} outcomes named correctly")
    return 0


def main(argv: list[str]) -> int:
    names = argv[1:] or sorted(set(SUITES) - DEMOS)
    failed = 0
    for name in names:
        if name not in SUITES:
            print(f"unknown suite {name!r}; known: {', '.join(sorted(SUITES))}")
            return 2
        if name in DEMOS:
            failed |= run_demo()
            continue
        status, _reports = baseline_and_mutants(name)
        failed |= status
    return failed


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
