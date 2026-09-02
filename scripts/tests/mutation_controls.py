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
    "artifact-gate-provenance": (
        "scripts/check-artifact-gate-provenance.py",
        "scripts.tests.test_artifact_gate_provenance",
        [
            (
                "absolute / out-of-repo citation guard",
                '        if raw.startswith("/") or not candidates:',
                "        if False:",
            ),
            (
                "cited script exists nowhere",
                "        if name not in live and name not in archived:",
                "        if False:",
            ),
            (
                "cited script is archived, so cannot run in place",
                "        if name in archived:",
                "        if False:",
            ),
            (
                "spelled directory disagrees with the file's location",
                '        if prefix.strip("/") and f"scripts/{name}" not in candidates:',
                "        if False:",
            ),
            (
                "live script invoking an archived sibling",
                "        if name in archived and name not in live:",
                "        if False:",
            ),
            (
                "artifact-citation vacuity floor",
                "    if floors and artifact_citations < MIN_ARTIFACT_CITATIONS:",
                "    if False:",
            ),
            (
                "sibling-reference vacuity floor",
                "    if floors and sibling_references < MIN_SIBLING_REFERENCES:",
                "    if False:",
            ),
        ],
    ),
    "settled-fact-statements": (
        "scripts/check-settled-fact-statements.py",
        "scripts.tests.test_settled_fact_statements",
        [
            (
                "unamended-drift guard",
                "        if amendment is None:",
                "        if False:",
            ),
            # Re-anchored for S1 (ADR-0763): the drift branch moved into
            # `evaluate()` and rustfmt-style rewrapping changed the line shape.
            # The guard is the same one and still kills exactly this test.
            (
                "amendment must describe THIS change",
                '                amendment["from_sha256"] != pin["statement_sha256"]',
                "                False",
            ),
            (
                "amendment must carry a reason",
                '        missing = [k for k in ("fact_id", "from_sha256", "to_sha256", "reason") if not row.get(k)]',
                '        missing = [k for k in ("fact_id", "from_sha256", "to_sha256") if not row.get(k)]',
            ),
            (
                "silent-retraction guard",
                "        if fact_id not in amendments:",
                "        if False:",
            ),
            (
                "empty-manifest fail-closed",
                "    if not isinstance(pins, list) or not pins:",
                "    if False:",
            ),
            (
                "no-settled-facts fail-closed",
                "    if not out:",
                "    if False:",
            ),
        ],
    ),
    # `development-without-train rule` kills FIVE tests and that is structural,
    # not a suite defect (ADR-1563). Three of the five are the grandfather
    # controls, and a grandfather has no meaning outside the rule it excuses:
    # delete the rule and there is nothing left for an exemption to be right or
    # wrong about. The three grandfather mutants below each kill exactly one,
    # which is the number that says whether the re-derivation works.
    "development-partition": (
        "scripts/check-development-partition.py",
        "scripts.tests.test_development_partition",
        [
            (
                "development-without-train rule",
                "        if dev_only:\n"
                "            # ADR-1563.",
                "        if False:\n"
                "            # ADR-1563.",
            ),
            (
                "generic string walk, not applicability.fact_ids only",
                "        referenced = {s for s in _strings(operation) if s in partitions}",
                '        referenced = {\n            s\n            for s in operation.get("applicability", {}).get("fact_ids", [])\n            if s in partitions\n        }',
            ),
            (
                "recorded-amendment exemption",
                '        touched_dev = {f for f in referenced if partitions[f] == "development"} - exempt',
                '        touched_dev = {f for f in referenced if partitions[f] == "development"}',
            ),
            (
                "nursery/policy agreement guard",
                "    if disagreements:",
                "    if False:",
            ),
            (
                "empty-development fail-closed",
                "    if not development:",
                "    if False:",
            ),
            (
                "generality ratchet",
                "    if covered < MULTI_TARGET_FLOOR:",
                "    if False:",
            ),
            (
                "empty-registry fail-closed",
                "    if not isinstance(registry, list) or not registry:",
                "    if False:",
            ),
            # ADR-1563. The grandfather excuses an operation that CANNOT be
            # retired, so each of its two re-derived properties has to be
            # removable and each removal has to be visible in exactly one test.
            (
                "a grandfather may not cover live development work",
                "    unsettled = sorted(f for f in touched_dev if statuses.get(f) not in SETTLED)",
                "    unsettled = []",
            ),
            (
                "a grandfather holds only while its targets PIN the operation",
                "    unpinned = sorted(f for f in touched_dev if op_id not in bindings.get(f, set()))",
                "    unpinned = []",
            ),
            (
                "a grandfather that excuses nothing is itself a violation",
                "    for stale in sorted((set(GRANDFATHERED_OPERATIONS) & registry_ids)\n"
                "                        - grandfathers_considered):",
                "    for stale in []:",
            ),
        ],
    ),
    "python-coverage": (
        "scripts/gen-python-coverage.py",
        "scripts.tests.test_gen_python_coverage",
        [
            (
                "pub(crate) is not public",
                '            if matched is not None and matched.group("restrict") is None:',
                "            if matched is not None:",
            ),
            (
                "cfg(test) modules are not public surface",
                '        skip_here = any("cfg(test)" in a.replace(" ", "") for a in pending)',
                "        skip_here = False",
            ),
            (
                "a method is referenced only when its OWNING type is",
                '        if owner in names and (bare in binding["calls"] or bare in names):  # type: ignore[operator]',
                '        if bare in binding["calls"] or bare in names:  # type: ignore[operator]',
            ),
            (
                "a backticked keyword is not an item",
                "                        if name not in NOT_AN_ITEM",
                "                        if True",
            ),
            (
                "empty-inventory fail-closed",
                '        raise CoverageError(f"{INVENTORY_DIR} produced zero rows -- the parser or the tables changed")',
                "        pass",
            ),
            (
                "no-crates fail-closed",
                '        raise CoverageError("no crates found under crates/ -- wrong ROOT?")',
                "        pass",
            ),
            (
                "a deferral must carry a reason",
                "        if not isinstance(reason, str) or not reason.strip():",
                "        if False:",
            ),
            (
                "claim guard",
                "    if unreferenced > 0 and claims:",
                "    if False:",
            ),
            (
                "claim-guard polarity: a denial is not a claim",
                "                if NOT_A_CLAIM.search(line):",
                "                if False:",
            ),
            (
                "--check staleness guard",
                "        if _normalise(current) == _normalise(content):",
                "        if True:",
            ),
            (
                "git_commit is normalised, not compared",
                '    return re.sub(r\'"git_commit": "[^"]*"\', \'"git_commit": "<normalised>"\', text)',
                "    return text",
            ),
        ],
    ),
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
            (
                "--accept-rename refuses an unmeasured target",
                "            if key not in admitted:\n                raise LedgerError(",
                "            if False:\n                raise LedgerError(",
            ),
            (
                "--accept-rename prefix does not capture a longer name",
                'elif name.startswith(f"{old}."):',
                "elif name.startswith(old):",
            ),
            (
                "--accept-rename OLD=NEW argument shape",
                "    if not separator or not old or not new:",
                "    if False:",
            ),
            # REMOVED 2026-08-18. This one was listed with the note "not
            # independently isolable: without the flag `measure()` fails
            # cross-check and the whole suite dies at setUpClass. Listed so the
            # control records that, rather than leaving it untested-looking."
            # It did not record that -- it recorded a KILL. Deleting the flag
            # sabotages the FIXTURE, so the run reported `Ran 0 tests` with an
            # error on `setUpClass`, and the old classifier read a non-zero exit
            # as a death: this suite's "11 guards, no survivors" was 10 measured
            # and one never run, in the control guarding the project's headline
            # trust number. The four-outcome harness now calls it
            # `DID NOT RUN` -- which is the truth, and a permanently unmeasurable
            # entry is worse than an absent one, so it is gone rather than red.
            #
            # It is not a guard deletion and no test module can make it one: every
            # test here depends on the fixture the flag builds. If the flag is to
            # be falsifiable it needs an assertion about the COMMAND, in a class
            # with no `setUpClass` -- and even then the surviving `Ran N` would
            # differ from the baseline. That is work for the lane that owns
            # `gen-lean-axiom-ledger.py`.
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
                # THE THIRD COPY. The mutation harness measured this one
                # SURVIVED on 2026-08-19 -- deleting it changed no test result --
                # while the two below had controls. `structural` is the largest
                # class in the census (102 of 135), so an unguarded smuggled
                # axiom there is most of the coverage this repository claims for
                # transcription binding, not a corner case. Anchored on the
                # SINGLE-LINE return, which is the only one of the three copies
                # written that way; the other two spread it over four lines. An
                # anchor that matches more than one copy is how the previous two
                # controls came to drive the same code path under different
                # labels.
                "structural: no axiom beyond the opaque sort",
                '                return (False, f"`{name} : {ty}` is not the opaque sort `\u03b1 : Sort (1)`", 0)',
                '                return (True, "", 0)  # MUTANT',
            ),
            (
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
    # --------------------------------------------------------------------
    # `producer-contracts` (ADR-0602) -- the falsifiability guards on the new
    # prospective producer-contract artifact. A contract is a CAPABILITY
    # claim, never a completion claim, and the only thing standing between
    # that and the checker-that-cannot-fail defect this project keeps
    # re-finding is: a non-example must be a real fact AND must actually fail
    # the predicate (checked by EXECUTION), and a predicate that swallows
    # every open fact in the ledger must be rejected outright.
    # --------------------------------------------------------------------
    "producer-contracts": (
        "scripts/validate-producer-contracts.py",
        "scripts.tests.test_validate_producer_contracts",
        [
            (
                "non-example must resolve to a real fact",
                "        if fact is None:",
                "        if False:",
            ),
            (
                "non-example must actually FAIL the shape predicate (checked by execution)",
                "        if shape_matches(shape, fact):",
                "        if False:",
            ),
            (
                "the vacuous-matcher guard: a shape cannot claim every open fact",
                "    if open_ids and matched_open_ids == open_ids:",
                "    if False:",
            ),
            (
                "a shape narrowed only by language/fragment is too coarse",
                "    if not any(key in shape for key in SHAPE_NARROWING_KEYS):",
                "    if False:",
            ),
            (
                "non_examples must be a non-empty list",
                "    if not isinstance(non_examples, list) or not non_examples:",
                "    if False:",
            ),
            # ADR-1510 rule 1: a contract is sized by the frontier and retires
            # when that population empties. A capability claim over an EMPTY
            # population cannot be falsified by any dispatch -- the same
            # unfalsifiable object ADR-0602 prevents one arrow upstream.
            (
                "a contract may not be SIZED against held-out population",
                "    if sized_held_out:",
                "    if False:",
            ),
            (
                "an exhausted contract must be retired",
                "    if not live and retirement is None:",
                "    if False:",
            ),
            (
                "retirement may not silence a contract with live work",
                "    if live and retirement is not None:",
                "    if False:",
            ),
        ],
    ),
    # --------------------------------------------------------------------
    # `producer-contract-declines` (doc 291) -- the falsifiability guards on
    # the new contract-driven decline artifact. The failure mode this suite
    # exists to catch, verbatim from the task that added it: a decline
    # artifact becomes a cheap way to make the selector shut up about a fact
    # forever. Each guard below is a real, independent way that could
    # happen, and each is expected to die under exactly one mutation.
    # --------------------------------------------------------------------
    "producer-contract-declines": (
        "scripts/validate-producer-contract-declines.py",
        "scripts.tests.test_validate_producer_contract_declines",
        [
            (
                "fact_id must resolve to a real fact",
                "    if fact_id not in facts:",
                "    if False:",
            ),
            (
                "contract path must resolve under producer-contracts/",
                "    if contracts_dir_resolved not in resolved.parents:",
                "    if False:",
            ),
            (
                "contract path must resolve to a real file",
                "    if not resolved.is_file():",
                "    if False:",
            ),
            (
                "decline_reason must be a typed identifier, never free text",
                "    if not isinstance(reason, str) or not TYPED_REASON_RE.match(reason):",
                "    if False:",
            ),
            (
                "producer.result must be exactly \"declined\"",
                '    if producer["result"] != "declined":',
                "    if False:",
            ),
            (
                "contract_sha256 must be a well-formed sha256 hex digest",
                "    if not isinstance(contract_sha256, str) or not SHA256_RE.match(contract_sha256):",
                "    if False:",
            ),
            (
                "producer.tool must be non-empty (producer identity)",
                "    if not isinstance(tool, str) or not tool:",
                "    if False:",
            ),
            (
                "every required top-level key must be present",
                "    if missing:",
                "    if False:",
            ),
            # ADR-1510 rule 2: a decline dies with its fact. Measured
            # 2026-09-01, 26 of 27 live suppressions named facts that were
            # already proved, and nothing could tell them apart from a decline
            # suppressing live work.
            (
                "a decline against a settled fact must carry a resolution",
                "    if settled and resolution is None:",
                "    if False:",
            ),
            (
                "a decline against an OPEN fact may not carry a resolution",
                "    if not settled and resolution is not None:",
                "    if False:",
            ),
            (
                "resolution.closed_by must name a real path in this repository",
                "    if not (ROOT / closed_by).exists():",
                "    if False:",
            ),
        ],
    ),
    "mirror-statement-fidelity": (
        "scripts/check-mirror-statement-fidelity.py",
        "scripts.tests.test_mirror_statement_fidelity",
        [
            (
                "G1 a kernel declaration keyword is not a proposition",
                "        if stmt.startswith(KERNEL_PREFIXES):",
                "        if False:",
            ),
            (
                "G2 a lean_pp carrier root cannot appear in Mathlib surface syntax",
                "        hit = KERNEL_CARRIER_RE.search(stmt)",
                "        hit = None",
            ),
            (
                "G3 an explicit universe annotation is render_lean's, not Mathlib's",
                "        hit = UNIVERSE_RE.search(stmt)",
                "        hit = None",
            ),
            (
                "G4 render_lean's generated binder names",
                "        hit = KERNEL_BINDER_RE.search(stmt)",
                "        hit = None",
            ),
            (
                "G5 a mirror declares surface syntax, never kernel core",
                '        if formal.get("language") != MIRROR_LANGUAGE:',
                "        if False:",
            ),
            (
                "G6 exact fidelity to the preregistered statement hash",
                "            if _sha(stmt) not in claimed:",
                "            if False:",
            ),
            (
                "G7 kernel_statement is meaningless without kernel_theorem",
                '        if "kernel_statement" in formal and not isinstance(formal.get("kernel_theorem"), str):',
                "        if False:  # mutated",
            ),
            (
                "G8 non-vacuity of the scope selector",
                '    if stats["mirrors"] == 0:',
                "    if False:",
            ),
            (
                "G9 non-vacuity of the hash check specifically",
                '    if stats["mirrors"] > 0 and stats["pinned"] == 0:',
                "    if False:",
            ),
        ],
    ),
    "semantic-control-fixtures": (
        "scripts/check-semantic-control-fixtures.py",
        "scripts.tests.test_semantic_control_fixtures",
        [
            (
                "zero executed cases, per fixture",
                '    bad = [f"{r[\'id\']}: executed 0 cases" for r in results if r["executed"] == 0]',
                "    bad = []",
            ),
            (
                "zero executed cases, whole pack",
                '    if results and sum(r["executed"] for r in results) == 0:',
                "    if False:",
            ),
            (
                "an empty pack is a failure",
                "    if not results:",
                "    if False:",
            ),
            (
                "a known-FALSE statement must be refuted",
                '        if r["expect"] == "false" and r["counterexamples"] == 0',
                "        if False",
            ),
            (
                "a known-VALID control must stay accepted",
                '        if r["expect"] == "valid" and r["counterexamples"] > 0',
                "        if False",
            ),
            (
                "a VALID control must discriminate something",
                '        if r["expect"] == "valid" and r["discriminating"] == 0',
                "        if False",
            ),
            (
                "a VALID control must kill a mutation (load-bearing)",
                '        if r["expect"] == "valid" and r["killed"] == 0',
                "        if False",
            ),
            (
                "a VACUOUS pin must really discriminate nothing",
                '        if r["discriminating"] != 0:',
                "        if False:",
            ),
            (
                "a VACUOUS pin must not actually be false",
                '        if r["counterexamples"] != 0:',
                "        if False:",
            ),
            (
                "a failing numerics script is refused",
                '        if n["exit"] != 0:',
                "        if False:",
            ),
            (
                "a numerics script with no negative control is refused",
                '        if n["negative_controls"] == 0:',
                "        if False:",
            ),
            (
                "the negative-control detector covers both spellings",
                'NEG_CONTROL = re.compile(r"negative control|genuinely fail", re.IGNORECASE)',
                'NEG_CONTROL = re.compile(r"negative control", re.IGNORECASE)',
            ),
            (
                "no fixture may name a held-out row",
                "            if fid in held:",
                "            if False:",
            ),
            (
                "a fixture must name a fact that exists",
                "            if not path.exists():",
                "            if False:",
            ),
            (
                "a fixture must name a PROVED fact",
                '            if status != "proved":',
                "            if False:",
            ),
            (
                "a moved executed/killed count is drift",
                "            if p.get(field) != r[field]:",
                "            if False:",
            ),
            (
                "a deleted fixture is refused",
                "    for missing in sorted(pinned - seen):",
                "    for missing in []:",
            ),
            (
                "an unpinned fixture is refused",
                "    for extra in sorted(seen - pinned):",
                "    for extra in []:",
            ),
            (
                "an unfalsified mutation declared also-true is classified, not failed",
                "        elif mut.also_true:",
                "        elif False:",
            ),
            (
                "census: a numerics script with no negative control is not load-bearing",
                '        n["script"] for n in numerics if n["exit"] == 0 and n["negative_controls"] > 0',
                '        n["script"] for n in numerics',
            ),
            (
                "census: a fixture with no killed mutation is not load-bearing",
                '        if r["expect"] != "valid" or r["killed"] == 0:',
                "        if False:",
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
            # A subject need not be Python: `check-kernel-suites.sh` is a shell
            # gate whose controls are a `unittest` module that shells out to it.
            # `py_compile` on a shell script reports `SyntaxError` and every
            # mutation scores DID NOT BUILD -- a whole suite unmeasurable for a
            # reason that has nothing to do with the mutation. `bash -n` is the
            # same check on the other side of the boundary: parse, do not run.
            if target.endswith(".sh"):
                code, out = _capture(["bash", "-n", str(work / target)], work)
            elif target.endswith(".py"):
                code, out = _capture([sys.executable, "-m", "py_compile", str(work / target)], work)
            else:
                continue
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
                # `corpus` is NOT excluded, and the omission cost a whole class
                # of suite. It is 23 MB / 1,154 files against `references` at
                # 219 MB and `bench-results` at 206 MB, and every solver test
                # that `include_str!`s a `.smt2` file — which is how the
                # certificate checkers pin their fixtures to real queries —
                # fails to COMPILE without it. Measured 2026-08-20: the first
                # certificate-checker suite registered here reported `BASELINE
                # DID NOT BUILD` with 99 errors, all of them missing corpus
                # paths, and no mutation was measurable at all.
                ".git", "target", "references", "bench-results", "__pycache__",
                # `.claude` holds every lane worktree (`.claude/worktrees/*`,
                # 279 of them on 2026-09-02, each with its own `target/`).
                # Run from the MAIN checkout this copy reached 47 GB and the
                # harness sat in uninterruptible disk wait for 27 minutes with
                # an empty log; from inside a worktree the directory does not
                # exist, which is why every lane's run had been fast.
                ".claude",
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
# `nra-monomial-bound-cert` — an independent re-validator for a route that
# ships `unsat`.
#
# This module had a REAL soundness hole on 2026-08-20: the producer
# distinguished `M < k` from `M <= k` (the second is refuted only by the
# strictly stronger `M > k`) and the certificate recorded only the constant, so
# `check_monomial_bound_refutation` returned `true` for a certificate refuting
# `a >= 1 and b >= 1 and a*b <= 1` — satisfiable at a = b = 1. No wrong `unsat`
# shipped, because the producer declines that query; but the independent
# re-validator, whose entire job is to catch a producer that is wrong, would
# have accepted a forged refutation of a SAT query.
#
# The guards below are the fix and its neighbours. They were mutation-checked by
# hand when they landed, in a commit message — which is not a gate, and a guard
# that rots back to survivable would be found by nobody. That is what this entry
# is for. Note what it still cannot do: mutation deletes guards that EXIST, and
# the hole above was a guard that was never written, in a certificate field that
# did not exist. See CLAUDE.md.
# --------------------------------------------------------------------------

SUITES["nra-monomial-bound-cert"] = (
    "crates/axeyum-solver/src/nra_monomial_bound_cert.rs",
    Cargo(
        ("-p", "axeyum-solver", "--features", "full", "--lib", "nra_monomial_bound_cert"),
        "nra-monomial-bound-cert",
    ),
    [
        (
            # THE 2026-08-20 HOLE. `M <= k` needs `M > k`; accepting `M >= k`
            # certifies a satisfiable query.
            "a non-strict atom may be refuted by a non-strict bound",
            "            claimed == derived && claimed > against",
            "            claimed == derived && claimed >= against",
        ),
        (
            "the carried bound must be the one the arithmetic re-derives",
            "            let derived = if any_unbounded { zero } else { product };\n            claimed == derived && claimed >= against",
            "            let derived = if any_unbounded { zero } else { product };\n            let _ = derived;\n            claimed >= against",
        ),
        (
            # `x^2 >= 0` for every real x, but an ODD power of an unbounded
            # variable is unbounded below and the refutation is false.
            "an unbounded factor needs an even exponent",
            "            if exp % 2 != 0 {\n                return false;\n            }",
            "            if false {\n                return false;\n            }",
        ),
        (
            # Multiplying bounds is monotone only on the nonnegative orthant:
            # (-2)*(-3) = 6 is not a lower bound for a*b.
            "a negative lower bound may not be multiplied",
            "        if value < zero {\n            return false;\n        }",
            "        if false {\n            return false;\n        }",
        ),
        (
            "the refuted atom's COMPARISON must match the query's",
            "        let kind_ok = refuted.kind() == certificate.refuted_kind;",
            "        let kind_ok = true;",
        ),
        (
            "the refuted atom's CONSTANT must match the query's",
            "        if kind_ok && constant_ok {",
            "        if kind_ok {",
        ),
        (
            "the query must actually state the atom being refuted",
            "    if !atom_matches {\n        return false;\n    }",
            "    if false {\n        return false;\n    }",
        ),
        (
            "a carried per-variable bound must be the query's own",
            "        Some(w) => rat(*w).is_some_and(|value| bounds.lower.get(name) == Some(&value)),",
            "        Some(w) => rat(*w).is_some(),",
        ),
    ],
)


# --------------------------------------------------------------------------
# `array-bv-abstraction-walk` — the SIXTH time a term-DAG walk here recursed as
# a tree.
#
# `contains_quantifier` (9.8e9 calls), `lower_derived_bv` (2.24e9),
# `collect_enumerable_symbols_rec` (1.28e10), `collect_nested_registrations`,
# `certify.rs`, and now `abstract_term`. A shared subterm is re-explored once
# per path, so cost is exponential in sharing while the node count stays small.
# On `QF_FP/solver__fp__fp_misc.smt2` — a query with no arrays in it at all —
# the walk made 4,194,309 visits over 5,762 reachable nodes and did not finish
# inside 125 s; memoized it makes 4,365.
#
# Registered because a memo is invisible when it works. Nothing about a correct
# result says whether it was reached once or a million times, so a regression
# here shows up only as "slow", which is exactly how this one survived: it was
# recorded as a proof-production TIMEOUT and read as a budget problem.
#
# The two guards are a pair, and the pairing is the point: the memo makes the
# walk linear, and the budget makes a DEFEATED memo fail fast instead of
# hanging. Each is deleted separately below and each kills its own test.
# --------------------------------------------------------------------------

SUITES["array-bv-abstraction-walk"] = (
    "crates/axeyum-solver/src/array_bv_abs.rs",
    Cargo(
        ("-p", "axeyum-solver", "--features", "full", "--lib", "array_bv_abs"),
        "array-bv-abstraction-walk",
    ),
    [
        (
            "the memo that makes the walk linear in the DAG",
            "        if let Some(&cached) = self.memo.get(&term) {\n            return cached;\n        }",
            "        if let Some(&cached) = self.memo.get(&term) {\n            let _ = cached;\n        }",
        ),
        (
            "the visit budget that turns a defeated memo into a decline",
            "        if self.visits > self.visit_budget {\n            return None;\n        }",
            "        if false {\n            return None;\n        }",
        ),
    ],
)


# --------------------------------------------------------------------------
# `solver-memory-budget` — a config field that was SET BUT NEVER READ.
#
# `SolverConfig::memory_limit_mb` had exactly one read in the workspace, under
# `#[cfg(feature = "z3")]`, so on the default pure-Rust build — the shipped
# product — setting it did nothing and nothing said so.  A live caller
# (`axeyum-verify`'s `tock_log2_external`) set a 2 GB cap on a non-z3 build.
#
# The guards below are the two mechanisms and the three probe sites.  Note what
# this entry can and cannot show, since the distinction has cost this repository
# real work: mutation deletes guards that EXIST.  It says nothing about the
# routes that still have no probe at all (simplex mid-solve, string search
# mid-solve), which `crate::memory_budget` documents rather than hides.
# --------------------------------------------------------------------------

SUITES["solver-memory-budget"] = (
    "crates/axeyum-solver/src/sat_bv_backend.rs",
    Cargo(
        ("-p", "axeyum-solver", "--lib", "memory_budget"),
        "solver-memory-budget",
    ),
    [
        (
            # Mechanism 1: megabytes -> clause ceiling, before lowering.
            "the pre-lowering clause ceiling derived from megabytes",
            "    if let Some(budget) = MemoryBudget::from_config(config)\n        && estimated_clauses > budget.clause_ceiling()\n    {",
            "    if false\n        && let Some(budget) = MemoryBudget::from_config(config)\n        && estimated_clauses > budget.clause_ceiling()\n    {",
        ),
        (
            # Mechanism 2, boundary 1 of 3.
            "the resident-set probe at backend entry",
            '            && let Some(reason) = budget.exceeded("backend entry")',
            '            && let Some(reason) = budget.exceeded("backend entry").filter(|_| false)',
        ),
        (
            # Mechanism 2, boundary 2 of 3.
            "the resident-set probe after bit-vector lowering",
            '            && let Some(reason) = budget.exceeded("after bit-vector lowering")',
            '            && let Some(reason) = budget.exceeded("after bit-vector lowering").filter(|_| false)',
        ),
        (
            # Mechanism 2, boundary 3 of 3.
            "the resident-set probe before the SAT search",
            '        && let Some(reason) = budget.exceeded("before SAT search")',
            '        && let Some(reason) = budget.exceeded("before SAT search").filter(|_| false)',
        ),
        (
            # The exact clause count, not the ~8x over-estimate, after encoding.
            "the post-encoding clause ceiling on the REAL clause count",
            "    if let Some(budget) = MemoryBudget::from_config(config)\n        && clauses > budget.clause_ceiling()\n    {",
            "    if false\n        && let Some(budget) = MemoryBudget::from_config(config)\n        && clauses > budget.clause_ceiling()\n    {",
        ),
    ],
)


# --------------------------------------------------------------------------
# `ir-bv-nego-width` — a width guard that was MISSING, not weak.
#
# `TermArena::bv_nego` built the signed minimum as `1u128 << (w - 1)` while legal
# widths run to `MAX_BV_WIDTH = 65536`.  Rust masks a shift amount mod 128, so
# `w = 129` produced `1` in **release** — a silently wrong term, `x == 1` where
# `x == 2^128` was meant — and a panic in debug.  The sibling `bv_umulo` had
# handled the wide case since it was written; `bv_nego` never did.
#
# It survived because the exhaustive overflow-predicate sweep loops
# `for w in 1..=4` and the one wide test in the suite covered `bv_umulo` only.
# Registered so the asymmetry cannot come back: the first mutation removes the
# wide branch, the second moves the boundary onto 128 itself.
# --------------------------------------------------------------------------

SUITES["ir-bv-nego-width"] = (
    "crates/axeyum-ir/src/arena.rs",
    Cargo(("-p", "axeyum-ir", "--test", "ir"), "ir-bv-nego-width"),
    [
        (
            "the >128-bit signed-minimum branch exists at all",
            "        let min = if w > 128 {",
            "        let min = if false {",
        ),
        (
            "128 itself stays on the narrow path (the boundary, not the guard)",
            "        let min = if w > 128 {",
            "        let min = if w >= 128 {",
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


# --------------------------------------------------------------------------
# `kernel-suite-partition` -- the push-time / real-Lean split of the kernel's
# integration suites.  Its guards are what make the split safe: a real-Lean
# suite that no gate owns must fail HERE, because the alternative is a suite the
# hook stopped running and nothing else picked up.
# --------------------------------------------------------------------------

SUITES["kernel-suite-partition"] = (
    "scripts/check-kernel-suites.sh",
    "scripts.tests.test_check_kernel_suites",
    [
        (
            "discovery found (nearly) nothing",
            'if [ "$all_count" -lt 2 ]; then',
            "if false; then",
        ),
        (
            "the real-Lean gate's table is unreadable",
            'if [ "$gate_count" -eq 0 ] && [ "$lean_count" -gt 0 ]; then',
            "if false; then",
        ),
        (
            "a real-Lean suite no gate owns",
            "  if ! printf '%s\\n' \"$gate_suites\" | grep -qxF \"$suite\"; then",
            "  if false; then",
        ),
        (
            "the gate names a suite that no longer exists",
            '  if [ ! -f "$TESTS_DIR/$suite.rs" ]; then',
            "  if false; then",
        ),
        (
            "the gate names a suite that needs no Lean (both halves)",
            "  if ! printf '%s\\n' \"$lean_suites\" | grep -qxF \"$suite\"; then",
            "  if false; then",
        ),
        (
            "a suite that resolves its own `lean` instead of the probe",
            '  grep -qF "$PROBE_MARKER" "$file" && continue',
            "  continue",
        ),
        (
            "a real-Lean suite that hand-writes its check count",
            "  grep -q 'report_checked' \"$file\" && continue",
            "  continue",
        ),
        (
            "a split with nothing left to run at push time",
            'if [ "$push_count" -eq 0 ]; then',
            "if false; then",
        ),
        (
            "a suite that ran ZERO tests",
            '  if [ "$ran" -lt 1 ]; then',
            "  if false; then",
        ),
        (
            "the run itself was red",
            'if [ "$status" -ne 0 ]; then\n  printf \'%s\\n\' "$out" | tail -60 >&2',
            'if false; then\n  printf \'%s\\n\' "$out" | tail -60 >&2',
        ),
    ],
)


# The agent-episode gate (docs/python-2026-08/03-agentic-layer.md, slice A1).
#
# An episode is the ONLY thing separating "a model ran" from "a model proved
# something", so a rule in it that cannot fail is worse than no rule: it
# manufactures unfalsifiable claims at the speed of the loop. Eighteen guards,
# every one with a nonempty killed-set and no two sharing a member -- so each
# guard is uniquely identified by which tests die and none can be deleted while
# the suite stays green. (Some killed-sets have more than one member: the schema
# guard is exercised by five documents, and three v1 rules are exercised on a v2
# document as well, which is the control that a NEW SCHEMA VERSION did not turn
# an old rule off.) Two are worth naming here because they are the ones
# a reader would assume are covered by something else:
#
#   `ledger-writes-must-be-zero` overlaps the schema's `maximum: 0`, so the test
#   asserts the RULE NAME rather than the exit status. Delete the rule and the
#   document still fails -- on `schema` -- and a status-only test would survive.
#
#   `no-episodes-is-not-a-pass` is the audited defect itself (40 of 162 checker
#   runs exiting 0 on completion alone, CLAUDE.md 2026-08-15). Removing it makes
#   `check-agent-episode.py <nothing>` exit 0.
SUITES["agent-episode"] = (
    "scripts/check-agent-episode.py",
    "scripts.tests.test_check_agent_episode",
    [
        (
            "schema violations are reported",
            "    for message in validate(document, schema, schema):",
            "    for message in []:",
        ),
        (
            "--require-ancestor actually fails",
            '                fail("git-commit-ancestor", f"{commit} {reason}")',
            "                pass",
        ),
        (
            "frontier digest must match the saved frontier",
            "            if actual is not None and actual != claimed:",
            "            if False:",
        ),
        (
            "the saved frontier must re-verify against the live ledger",
            "            if not ok:",
            "            if False:",
        ),
        (
            "a web snapshot's bytes must hash to what it claims",
            '        if digest != snapshot.get("sha256"):',
            "        if False:",
        ),
        (
            "ledger_writes must be zero",
            "    if writes != 0:",
            "    if False:",
        ),
        (
            "a held-out id anywhere in the document is a violation",
            "        if value in held:",
            "        if False:",
        ),
        (
            "proved requires a checker that exited zero",
            "        if status != 0:",
            "        if False:",
        ),
        (
            "proved requires a named checker command",
            "        if not (isinstance(command, str) and command.strip()):",
            "        if False:",
        ),
        (
            "a proposal's bytes must hash to what it claims",
            '        if digest != proposal.get("sha256"):',
            "        if False:",
        ),
        (
            "a run that called nothing is not a clean decline",
            "    if not calls:",
            "    if False:",
        ),
        (
            "the selected fact must exist in the ledger",
            "    if fact_id not in fact_ids:",
            "    if False:",
        ),
        (
            "checking zero episodes is not a pass",
            "    if checked == 0:",
            "    if False:",
        ),
        (
            "an empty fact ledger is an error, not a pass",
            "    if not fact_ids:",
            "    if False:",
        ),
        (
            "an unreadable nursery is an error, not an empty held-out set",
            '        print(f"EPISODE_ERROR|held-out-population|{error}", file=sys.stderr)\n        return 2',
            "        held = set()",
        ),
        # Slice A4. Rule 11 is TWO guards under one rule name and the split is
        # deliberate: "a producer nobody re-validated" and "a checker that ran
        # against nothing" are different defects, and one guard covering both
        # would be deletable in half while a status-only test stayed green.
        (
            "proved requires a tool call that actually dispatched",
            "        if not checked_calls:",
            "        if False:",
        ),
        (
            "proved requires a checker run that exited zero",
            "        if not passing_runs:",
            "        if False:",
        ),
        # The version dispatch itself. Falling back to v1 for an unknown version
        # is the failure mode a new schema version invites: the document is
        # still CHECKED, so nothing looks wrong, and it is checked against
        # constraints nobody wrote for it.
        (
            "an unknown schema version is refused, not checked against v1",
            "        schema = schemas.get(declared) if isinstance(declared, int) else None",
            "        schema = schemas.get(declared) or schemas[1]",
        ),
    ],
)


# The tactic catalog (docs/python-2026-08/04-tactic-catalog.md, slice A3).
#
# The catalog is what a plan resolves against, so a rule in it that cannot fail
# lets the agent name a strategy the code does not have. Thirteen guards,
# thirteen tests, one each. Three are worth naming:
#
#   `precondition-shapes` and `reach-empty` are the doc-228 finding as a gate:
#   a catalog whose entries each match one goal shape is a dispatch table, and a
#   tactic with no measured accepted or declined goal is a name. Neither can be
#   caught by validating fields; both are census properties of the whole file.
#
#   The two technique-RESOLUTION anchors are gone (ADR-0553). They covered a
#   pin against `../math-education` and a stat of its `graph/techniques/*.md`,
#   both removed with the coupling; their hermetic fixture existed because the
#   live sibling is not beside a scratch copy, which was the right fix for the
#   wrong problem -- the guard should not have reached outside the checkout at
#   all. What replaces them refuses the fields: `uses_technique` takes exactly
#   `id`, and the overlay may declare no external source.
SUITES["tactic-catalog"] = (
    "scripts/validate-tactic-catalog.py",
    "scripts.tests.test_validate_tactic_catalog",
    [
        (
            "duplicate tactic ids",
            "        if ident in seen:",
            "        if False:",
        ),
        (
            "implemented_by.path must exist",
            "        if source_path is None or not source_path.is_file():",
            "        if False:",
        ),
        (
            "the symbol must be declared in that file",
            "            if re.search(pattern, text) is None:",
            "            if False:",
        ),
        (
            "decline reasons must be that file's own variants",
            "                if reason not in variants:",
            "                if False:",
        ),
        (
            "budget constants must equal the Rust const",
            "                elif consts[name] != value:",
            "                elif False:",
        ),
        (
            "realizes must resolve in the knowledge overlay",
            "        if realizes not in capabilities:",
            "        if False:",
        ),
        (
            "uses_technique takes exactly id -- no source, no revision",
            '    if not isinstance(technique, dict) or set(technique) != {"id"}:',
            "    if False:",
        ),
        (
            "the overlay may declare no external source",
            '        if isinstance(source, dict) and source.get("kind", "").startswith("external"):',
            "        if False:",
        ),
        (
            "residual shape and measure are \"none\" together",
            "        if shape_none != measure_none:",
            "        if False:",
        ),
        (
            "a tactic with zero reach rows",
            "        if rows_accepted + rows_declined == 0:",
            "        if False:",
        ),
        (
            "one precondition shape is a dispatch table",
            "    if len(shapes) < 2:",
            "    if False:",
        ),
        (
            "the tactic kind enum",
            '    if tactic.get("kind") not in TACTIC_KINDS:',
            "    if False:",
        ),
        (
            "the precondition predicate vocabulary",
            '    if kind not in PREDICATES:\n        err(errors, "schema", f"{where}: unknown predicate kind {kind!r}")\n        return',
            "    if kind not in PREDICATES:\n        return",
        ),
    ],
)

# The external-coupling gate (ADR-0553).
#
# This gate exists because the owner's "math-education is reference only" rule
# had NO gate, and by the time anyone looked it had been violated in five places
# at once. A gate born from an ungated guarantee had better not be one itself.
#
# `R1`, `R2` and `R3` each have ONE control asserting every value that guard must
# catch, via `subTest`. Three separate tests per guard would all die together and
# report a shared rejection path as thorough coverage.
#
# The vacuity guards are driven through `vacuity()` rather than `main()` for the
# same reason: routed through `main()` all three fail together, so one mutation
# kills three tests. Extracting the function was what made them separable.
#
# Expected SURVIVORS under these mutations, by design -- they are acceptance
# cases, and deleting a guard makes them pass more easily:
#   test_a_registered_local_key_is_accepted
#   test_a_registered_foreign_import_is_accepted
#   test_a_local_path_containing_two_dots_is_not_rejected
#   test_a_healthy_scan_is_not_a_finding
# They exist to stop the opposite failure: a rule so broad it rejects Mathlib's
# deliberate pin, or every version string in the tree.
SUITES["external-coupling"] = (
    "scripts/check-external-coupling.py",
    "scripts.tests.test_check_external_coupling",
    [
        (
            "R1 the external-declaration vocabulary",
            "        if value in EXTERNAL_VOCABULARY:",
            "        if False:",
        ),
        (
            "R2 a path segment that escapes the checkout",
            "        if DOTDOT.search(value):",
            "        if False:",
        ),
        (
            "R3 a revision pin under an unregistered key",
            "        if HEX40.match(value) and key not in REVISION_KEYS:",
            "        if False:",
        ),
        (
            "R4 source that builds a path out of the checkout",
            "            if needle in code:",
            "            if False:",
        ),
        (
            "vacuity: zero artifacts scanned",
            "    if files == 0:",
            "    if False:",
        ),
        (
            "vacuity: zero strings examined",
            "    if strings == 0:",
            "    if False:",
        ),
        (
            "vacuity: zero scripts scanned",
            "    if script_files == 0:",
            "    if False:",
        ),
        (
            "the exit status depends on the finding",
            "    return 1 if findings else 0",
            "    return 0",
        ),
    ],
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


def check_anchors() -> int:
    """Every registered anchor still matches its subject exactly once.

    Builds nothing and runs no test, so this is cheap enough to be a gate — and
    it catches the rot that actually happens. No gate runs any real mutation
    suite: `scripts/check.sh` and the `justfile` run the harness's OWN controls
    and `self-demo`, so the harness is verified continuously and every SUBJECT
    is verified once, by hand, at commit time. When the source then drifts, the
    anchor stops matching, the mutation reports `NOT APPLIED` — and nobody is
    looking, so a suite can decay to measuring nothing while its commit message
    still claims "each guard killed exactly one test".

    `NOT APPLIED` and `AMBIGUOUS ANCHOR` are both failures here for the reason
    `_apply` gives: an anchor matching twice would be resolved by
    `str.replace(..., 1)` picking whichever came first, and the report could not
    say which guard was deleted.

    This does NOT say the guards still kill anything. That needs the builds.
    It says the suites are still POINTED at real code, which is the difference
    between a stale suite and a green one.
    """
    failed = 0
    for name in sorted(set(SUITES) - DEMOS):
        suite = normalize(name)
        for mutation in suite.mutations:
            target = mutation.target or suite.subject
            path = ROOT / target
            if not path.exists():
                print(f"MISSING SUBJECT {name}: {target}")
                failed = 1
                continue
            text = path.read_text(encoding="utf-8")
            occurrences = text.count(mutation.find)
            if occurrences != 1:
                verdict = "NOT APPLIED" if occurrences == 0 else "AMBIGUOUS ANCHOR"
                print(f"{verdict} {name}: {mutation.label!r} matches {occurrences} places in {target}")
                failed = 1
    total = sum(len(normalize(n).mutations) for n in sorted(set(SUITES) - DEMOS))
    print(f"MUTATION_ANCHORS|suites={len(set(SUITES) - DEMOS)}|anchors={total}|stale={failed}")
    return failed


# S1 of the trusted-library safety roadmap (ADR-0763). Until S1 this gate could
# not fail on the commonest way a statement goes unwatched: never being pinned.
# Every guard below is mutation-verified because the defect being fixed IS a
# checker that cannot fail, and reproducing it here would be the worst possible
# outcome.
SUITES["settled-fact-statement-identity"] = (
    "scripts/check-settled-fact-statements.py",
    "scripts.tests.test_settled_fact_statements",
    [
        # ABSENCE. The headline S1 fix. Before it, an unpinned settled fact was
        # read as "newly settled" and 1,976 of 2,120 statements were unwatched.
        (
            "an unpinned settled fact above the allowance is a violation",
            '    if len(unpinned) > floors["max_unpinned_settled"]:',
            "    if False:",
        ),
        # SLACK. A ratchet that can be hand-loosened is decoration; the gate
        # re-derives the floor and reports a too-generous allowance as a
        # violation, which is what makes a loosened floor self-reverting.
        (
            "a slack unpinned allowance is a violation",
            '    elif len(unpinned) < floors["max_unpinned_settled"]:',
            "    elif False:",
        ),
        # PROSE. The reader-facing `statement` is the only field most readers
        # see. Pinning only `formal.statement` left it rewritable.
        (
            "the reader-facing statement must not drift",
            '        if pinned_prose is not None and pinned_prose != now["prose_sha256"]:',
            "        if False:",
        ),
        # REPOINTING. Which declaration a fact is about is a larger claim than
        # how its statement is spelled, and nothing watched it.
        (
            "a fact must not be repointed at another declaration",
            '        if pinned_theorem is not None and pinned_theorem != now["kernel_theorem"]:',
            "        if False:",
        ),
        # HEADER BIND. A content hash says "changed"; this says "changed into a
        # rendering of a DIFFERENT theorem", which no hash can express.
        (
            "the rendered header must name the claimed declaration",
            '            elif now["header_name"] != now["kernel_theorem"]:',
            "            elif False:",
        ),
        # HEADERLESS ALLOWANCE. 30 statements carry no `theorem <name> :`
        # header and cannot be checked against their declaration. Counted, not
        # ignored, so a 31st cannot appear quietly.
        (
            "a new headerless statement is counted, not ignored",
            '    if len(header_exempt) > floors["max_header_exempt"]:',
            "    if False:",
        ),
        # IDENTITY FLOOR. Dropping `kernel_theorem` un-binds a fact from its
        # declaration while every hash stays intact, so no drift guard sees it.
        (
            "losing an identity binding is a violation",
            '    if identity_bound < floors["min_identity_bound"]:',
            "    if False:",
        ),
        (
            "a slack identity floor is a violation",
            '    elif identity_bound > floors["min_identity_bound"]:',
            "    elif False:",
        ),
        # The pre-S1 guards -- unamended drift, the wrong-digest amendment
        # check, the reason requirement, silent retraction, and both
        # fail-closed paths -- are NOT repeated here. They are already
        # mutation-verified by the `settled-fact-statements` suite above,
        # against the same subject file. Mutating one line from two suites
        # would double the cost and make a stale anchor look like coverage.
        # FAIL-CLOSED ON A MISSING RATCHET. A manifest with no `coverage_floor`
        # has no opinion about absence -- exactly the state S1 found this gate
        # in -- so it is an error, not a default.
        (
            "a manifest with no coverage_floor is an error",
            '    floor = manifest.get("coverage_floor")',
            '    floor = manifest.get("coverage_floor") or {k: 0 for k in FLOOR_KEYS}',
        ),
        (
            "a non-integer coverage_floor is an error",
            "        if not isinstance(value, int) or isinstance(value, bool) or value < 0:",
            "        if False:",
        ),
        # `--write` MUST NOT LAUNDER. It used to rebuild pins from current state
        # unconditionally, so running it after a drift re-pinned the damage and
        # the gate went green.
        (
            "--write refuses to re-pin an unamended change",
            "    if blocked:",
            "    if False:",
        ),
        # `--write` PRESERVES THE SUPERSEDED STATEMENT -- the roadmap's
        # "preserve previous statements when correcting a row".
        (
            "--write preserves the superseded statement",
            "                history.append(superseded)",
            "                pass",
        ),
        # `--write` ONLY TIGHTENS. A loosened floor must not survive a write.
        (
            "--write only tightens the ratchet",
            '            old_floor.get("max_unpinned_settled", len(unpinned)), len(unpinned)',
            '            old_floor.get("max_unpinned_settled", len(unpinned)), 10**9',
        ),
    ],
)

def main(argv: list[str]) -> int:
    if argv[1:2] == ["--check-anchors"]:
        return check_anchors()
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


SUITES["mobility-census"] = (
    "scripts/check-mobility-census.py",
    "scripts.tests.test_check_mobility_census",
    [
        (
            "schema_version",
            '    if census.get("schema_version") != SCHEMA_VERSION:',
            "    if False:",
        ),
        (
            "kind",
            '    if census.get("kind") != KIND:',
            "    if False:",
        ),
        (
            "required top-level keys",
            "        if key not in census:",
            "        if False:",
        ),
        (
            "pins must match their files",
            "        if census.get(key) != measured:",
            "        if False:",
        ),
        (
            "every catalog tactic must be evaluated",
            "    for missing in sorted(declared - present):",
            "    for missing in []:",
        ),
        (
            "no tactic the catalog does not declare",
            "    for extra in sorted(present - declared):",
            "    for extra in []:",
        ),
        (
            "no held-out id anywhere",
            "        if fact_id in text",
            "        if False",
        ),
        (
            "every fact id exists in the ledger",
            "        if fact_id not in statuses:",
            "        if False:",
        ),
        # The blanket "the census is over OPEN facts" guard is GONE. It rejected
        # graduation -- a fact open at census time and proved now -- and on
        # 2026-08-30 emitted 126 identical lines over one census, burying the
        # finding that mattered. Graduation is now audited against the census's
        # pinned commit by `check_population`, whose guards follow.
        (
            "a census pinning no commit cannot be audited",
            "    if not isinstance(commit, str) or not commit.strip():",
            "    if False:",
        ),
        (
            "an unreachable pinned commit is a violation, not a skip",
            '    if state == "unreachable":',
            "    if False:",
        ),
        (
            "a row with no fact file at the pinned commit",
            "        if was is None:",
            "        if False:",
        ),
        (
            "a row already settled at the pinned commit is padding",
            '        elif was != "open":',
            "        elif False:",
        ),
        (
            "held-out facts are never demanded as census rows",
            "    live_exportable = sorted((live_open & exportable) - held_out)",
            "    live_exportable = sorted(live_open & exportable)",
        ),
        (
            "no open fact carries an export: the census has no subject",
            "    if not live_exportable:",
            "    if False:",
        ),
        (
            "open exports the census never evaluated demand a regeneration",
            "    elif not live_evaluable:",
            "    elif False:",
        ),
        (
            "an open exportable fact with no census row went unmeasured",
            "        if fact_id not in rows:",
            "        if False:",
        ),
        (
            "a zero-match cluster of settled facts names no capability",
            '        if fact_ids and not any(statuses.get(fact_id) == "open" for fact_id in fact_ids):',
            "        if False:",
        ),
        (
            "an export index with no entries fails closed",
            "    if not isinstance(exports, list) or not exports:",
            "    if False:",
        ),
        (
            "an export index naming no fact ids fails closed",
            "    if not exportable:",
            "    if False:",
        ),
        (
            "no duplicated fact row",
            "        if fact_id in seen:",
            "        if False:",
        ),
        (
            "a cluster names a known fact",
            "            if fact_id not in seen:\n                problems.append(f\"cluster names {fact_id}, which has no fact row\")",
            '            if False:\n                problems.append(f"cluster names {fact_id}, which has no fact row")',
        ),
        (
            "a tactic names a known matched fact",
            "            if fact_id not in seen:\n                problems.append(f\"{row.get('id')} names matched fact {fact_id} with no fact row\")",
            "            if False:\n                problems.append(f\"{row.get('id')} names matched fact {fact_id} with no fact row\")",
        ),
        (
            "an empty ledger fails closed",
            "    if not out:",
            "    if False:",
        ),
        (
            "a nursery with no held-out rows fails closed",
            "    if not ids:",
            "    if False:",
        ),
        (
            "evaluable + unevaluable = open",
            '    if totals.get("evaluable", 0) + totals.get("unevaluable", 0) != open_facts:',
            "    if False:",
        ),
        (
            "pairs = facts * tactics",
            '    if totals.get("pairs") != open_facts * tactics:',
            "    if False:",
        ),
        (
            "the three verdict counts sum to pairs",
            '    if pair_sum != totals.get("pairs"):',
            "    if False:",
        ),
        (
            "written_fact_rows matches the list",
            '    if totals.get("written_fact_rows") != len(rows):',
            "    if False:",
        ),
        (
            "written + held-out accounts for every open fact",
            '    if totals.get("written_fact_rows", 0) + totals.get("held_out_excluded", 0) != open_facts:',
            "    if False:",
        ),
        (
            "mobility is the matched count",
            '        if row.get("mobility") != len(matched):',
            "        if False:",
        ),
        (
            "an unevaluable row may not match",
            "        elif matched:",
            "        elif False:",
        ),
        (
            "a tactic carries one verdict",
            "        if overlap:",
            "        if False:",
        ),
        (
            "one verdict per tactic per fact",
            '        if total_verdicts != census["totals"]["tactics"]:',
            "        if False:",
        ),
        (
            "tactic matched counts agree with the fact rows",
            "        if named != counted:",
            "        if False:",
        ),
        (
            "shapes cannot exceed matched facts",
            "        if shapes > counted:",
            "        if False:",
        ),
        (
            "a matching tactic reports a shape",
            "        if counted and not shapes:",
            "        if False:",
        ),
        (
            "a fact appears in one cluster",
            "    if len(clustered) != len(set(clustered)):",
            "    if False:",
        ),
        (
            "the clusters cover the zero-match set",
            "    if len(clustered) != zero_match_written:",
            "    if False:",
        ),
        (
            "totals.clusters agrees with the list",
            '    if totals.get("clusters") != len(census.get("zero_match_clusters") or []):',
            "    if False:",
        ),
        (
            "a cluster size matches its facts",
            '        if cluster.get("size") != len(cluster.get("fact_ids") or []):',
            "        if False:",
        ),
        (
            "a cluster names its reasons",
            '        if not cluster.get("reasons"):',
            "        if False:",
        ),
        (
            "the partition table sums to the totals",
            "        if summed != want:",
            "        if False:",
        ),
        (
            "a census that evaluated nothing is void",
            '    if totals.get("evaluable", 0) > 0:',
            "    if True:",
        ),
        (
            "the sampling block is required",
            "    if not isinstance(block, dict):",
            "    if False:",
        ),
        (
            "the sampling block carries every counter",
            "        if key not in block:",
            "        if False:",
        ),
        (
            "an empty must-decline population",
            '    if block["rows"] <= 0:',
            "    if False:",
        ),
        (
            "sampling counters sum to rows",
            '    if block["evaluated"] + block["unevaluable"] != block["rows"]:',
            "    if False:",
        ),
        (
            "a suspect needs a fact behind it",
            '    if block["suspects"] and not block["suspect_facts"]:',
            "    if False:",
        ),
        (
            "a suspect voids the census",
            '    if block["suspects"]:\n        problems.append(\n            f"a tactic precondition admits',
            '    if False:\n        problems.append(\n            f"a tactic precondition admits',
        ),
    ],
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


def check_anchors() -> int:
    """Every registered anchor still matches its subject exactly once.

    Builds nothing and runs no test, so this is cheap enough to be a gate — and
    it catches the rot that actually happens. No gate runs any real mutation
    suite: `scripts/check.sh` and the `justfile` run the harness's OWN controls
    and `self-demo`, so the harness is verified continuously and every SUBJECT
    is verified once, by hand, at commit time. When the source then drifts, the
    anchor stops matching, the mutation reports `NOT APPLIED` — and nobody is
    looking, so a suite can decay to measuring nothing while its commit message
    still claims "each guard killed exactly one test".

    `NOT APPLIED` and `AMBIGUOUS ANCHOR` are both failures here for the reason
    `_apply` gives: an anchor matching twice would be resolved by
    `str.replace(..., 1)` picking whichever came first, and the report could not
    say which guard was deleted.

    This does NOT say the guards still kill anything. That needs the builds.
    It says the suites are still POINTED at real code, which is the difference
    between a stale suite and a green one.
    """
    failed = 0
    for name in sorted(set(SUITES) - DEMOS):
        suite = normalize(name)
        for mutation in suite.mutations:
            target = mutation.target or suite.subject
            path = ROOT / target
            if not path.exists():
                print(f"MISSING SUBJECT {name}: {target}")
                failed = 1
                continue
            text = path.read_text(encoding="utf-8")
            occurrences = text.count(mutation.find)
            if occurrences != 1:
                verdict = "NOT APPLIED" if occurrences == 0 else "AMBIGUOUS ANCHOR"
                print(f"{verdict} {name}: {mutation.label!r} matches {occurrences} places in {target}")
                failed = 1
    total = sum(len(normalize(n).mutations) for n in sorted(set(SUITES) - DEMOS))
    print(f"MUTATION_ANCHORS|suites={len(set(SUITES) - DEMOS)}|anchors={total}|stale={failed}")
    return failed


def main(argv: list[str]) -> int:
    if argv[1:2] == ["--check-anchors"]:
        return check_anchors()
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


SUITES["obstruction-graph"] = (
    "scripts/validate-obstruction-graph.py",
    "scripts.tests.test_obstruction_graph",
    [
        (
            "an obstruction id must re-derive from its cluster key",
            "        if ident != expected:",
            "        if False:",
        ),
        (
            "entity assurance ceiling",
            '        if entity["assurance"] not in ASSURANCE:',
            "        if False:",
        ),
        (
            "link assurance ceiling",
            '        if link["assurance"] not in ASSURANCE:',
            "        if False:",
        ),
        (
            "provenance method must be mechanically-observed",
            '        if link["provenance"]["method"] != METHOD:',
            "        if False:",
        ),
        (
            "evidence digests are re-hashed from disk",
            '            if digest != row["sha256"]:',
            "            if False:",
        ),
        (
            "evidence must be on disk",
            "            if not path.is_file():\n"
            "                errors.append(f\"{where}: evidence {row['path']} is not on disk\")",
            "            if False:\n"
            "                errors.append(f\"{where}: evidence {row['path']} is not on disk\")",
        ),
        (
            "an obstruction with no evidence",
            '        if not entity["evidence"]:',
            "        if False:",
        ),
        (
            "facts_blocked must equal the population",
            '        if entity["facts_blocked"] != len(fact_ids):',
            "        if False:",
        ),
        (
            "candidate_capability.exists is re-measured against the overlay",
            '        if candidate["exists"] != exists:',
            "        if False:",
        ),
        (
            "an absent capability must be spelled K:proposed-",
            '        if not exists and not candidate["id"].startswith(PROPOSED_CAPABILITY):',
            "        if False:",
        ),
        (
            "the first blocker must be in the known set",
            '        elif not any(\n'
            '            row["kind"] == first["kind"] and row["detail"] == first["detail"] '
            "for row in known\n        ):",
            "        elif False:",
        ),
        (
            "decline classes come from the v2 episode enum",
            "            if value not in DECLINE_CLASSES:",
            "            if False:",
        ),
        (
            "tactic ids must resolve in the catalog",
            "            if tactic_id not in tactics:",
            "            if False:",
        ),
        (
            "population facts must resolve in the ledger",
            "            if not path.is_file():\n                errors.append("
            'f"{where}: population fact {fact_id} does not resolve in the ledger")',
            "            if False:\n                errors.append("
            'f"{where}: population fact {fact_id} does not resolve in the ledger")',
        ),
        (
            "a link must point at an obstruction this graph declares",
            '        if link["target"]["id"] not in seen_ids:',
            "        if False:",
        ),
        (
            "relation domain",
            '        if link["source"]["kind"] not in relation["source_kinds"]:',
            "        if False:",
        ),
        (
            "duplicate obstruction ids",
            "        if ident in seen_ids:",
            "        if False:",
        ),
        (
            "an after-funnel without a resolution commit",
            '        if resolution["commit"] is None and resolution["after"] is not None:',
            "        if False:",
        ),
        (
            "a graph with no entity fails closed",
            "    if not entities:",
            "    if False:",
        ),
        (
            "the validator refuses a held-out population",
            "            if fact_id in blind:\n"
            '                errors.append(f"{where}: population names a held-out fact")',
            "            if False:\n"
            '                errors.append(f"{where}: population names a held-out fact")',
        ),
        (
            "the validator refuses a held-out partition count",
            '        if "held-out" in population["partitions"]:',
            "        if False:",
        ),
        (
            "the validator walks every string for a held-out id",
            "    leaked = sorted(ident for ident in blind if any(ident in text for text in strings))",
            "    leaked = []",
        ),
        (
            "the generator refuses a tree with no dated episode directory",
            "    if not paths:\n        raise DeriveError(f\"{EPISODES}: no dated episode "
            'directories; nothing to derive from")',
            "    if False:\n        raise DeriveError(f\"{EPISODES}: no dated episode "
            'directories; nothing to derive from")',
            "scripts/gen-obstruction-graph.py",
        ),
        (
            "the generator refuses an unclassifiable decline record",
            "    if unclassified:",
            "    if False:",
            "scripts/gen-obstruction-graph.py",
        ),
        (
            "the generator refuses an episode selecting a held-out fact",
            "        if blind_selection:",
            "        if False:",
            "scripts/gen-obstruction-graph.py",
        ),
        (
            "the generator walks the rendered bytes for a held-out id",
            "    breaches.extend(\n"
            '        f"rendered document names held-out fact {ident}"',
            "    breaches.extend(\n"
            '        f"IGNORED {ident}"',
            "scripts/gen-obstruction-graph.py",
        ),
    ],
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


def check_anchors() -> int:
    """Every registered anchor still matches its subject exactly once.

    Builds nothing and runs no test, so this is cheap enough to be a gate — and
    it catches the rot that actually happens. No gate runs any real mutation
    suite: `scripts/check.sh` and the `justfile` run the harness's OWN controls
    and `self-demo`, so the harness is verified continuously and every SUBJECT
    is verified once, by hand, at commit time. When the source then drifts, the
    anchor stops matching, the mutation reports `NOT APPLIED` — and nobody is
    looking, so a suite can decay to measuring nothing while its commit message
    still claims "each guard killed exactly one test".

    `NOT APPLIED` and `AMBIGUOUS ANCHOR` are both failures here for the reason
    `_apply` gives: an anchor matching twice would be resolved by
    `str.replace(..., 1)` picking whichever came first, and the report could not
    say which guard was deleted.

    This does NOT say the guards still kill anything. That needs the builds.
    It says the suites are still POINTED at real code, which is the difference
    between a stale suite and a green one.
    """
    failed = 0
    for name in sorted(set(SUITES) - DEMOS):
        suite = normalize(name)
        for mutation in suite.mutations:
            target = mutation.target or suite.subject
            path = ROOT / target
            if not path.exists():
                print(f"MISSING SUBJECT {name}: {target}")
                failed = 1
                continue
            text = path.read_text(encoding="utf-8")
            occurrences = text.count(mutation.find)
            if occurrences != 1:
                verdict = "NOT APPLIED" if occurrences == 0 else "AMBIGUOUS ANCHOR"
                print(f"{verdict} {name}: {mutation.label!r} matches {occurrences} places in {target}")
                failed = 1
    total = sum(len(normalize(n).mutations) for n in sorted(set(SUITES) - DEMOS))
    print(f"MUTATION_ANCHORS|suites={len(set(SUITES) - DEMOS)}|anchors={total}|stale={failed}")
    return failed


SUITES["correspondences"] = (
    "scripts/validate-correspondences.py",
    "scripts.tests.test_validate_correspondences",
    [
        # -- vacuity: an empty population must fail, not pass -----------------
        (
            "an empty correspondence directory fails closed",
            "    if not paths:",
            "    if False:",
        ),
        (
            "an empty fact ledger fails closed",
            "    if not facts:",
            "    if False:",
        ),
        # -- the rule the artifact exists for ---------------------------------
        (
            "a pair the ledger already links by depends_on is refused",
            "    if right_id in closure.get(left_id, ()) or left_id in closure.get(right_id, ()):",
            "    if False:",
        ),
        # -- endpoints --------------------------------------------------------
        ("a self-loop is refused", "    if left_id == right_id:", "    if False:"),
        (
            "an endpoint that is not a fact is refused",
            "    missing = [e for e in (left_id, right_id) if e not in facts]\n    if missing:",
            "    missing = [e for e in (left_id, right_id) if e not in facts]\n    if False:",
        ),
        (
            "an unsettled endpoint is refused",
            '        if fact.get("epistemic_status") not in SETTLED:',
            "        if False:",
        ),
        (
            "two identical formal statements are a duplicate, not a correspondence",
            '    if left.get("formal", {}).get("statement") == right.get("formal", {}).get("statement"):',
            "    if False:",
        ),
        # -- the two defects found by lanes USING the gate, not by the gate ---
        (
            "a specialization whose every via ref is null is refused",
            """        elif not any(
            isinstance(step, dict) and isinstance(step.get("ref"), str) and step["ref"].strip()
            for step in document["via"]
        ):""",
            "        elif False:",
        ),
        (
            "AxNat is the Nat carrier, so a kernel-spelled transport erases",
            '    "Nat": ("AxNat", "Nat", "\u2115"),',
            '    "Nat": ("Nat", "\u2115"),',
        ),
        # -- carrier-transport is checked structurally ------------------------
        (
            "two facts in one fragment are not a transport",
            "        if left_fragment == right_fragment:",
            "        if False:",
        ),
        (
            "a fragment with no carrier spelling fails closed",
            "        unknown = [f for f in (left_fragment, right_fragment) if f not in CARRIERS]\n        if unknown:",
            "        unknown = [f for f in (left_fragment, right_fragment) if f not in CARRIERS]\n        if False:",
        ),
        (
            "carrier erasure must leave the same statement",
            "        if left_erased != right_erased:",
            "        if False:",
        ),
        (
            "independent-formalization needs two different proof routes",
            '        if left.get("proof_route") == right.get("proof_route"):',
            "        if False:",
        ),
        (
            "a specialization must record its instantiation route",
            '        if document["derivation_status"] == "asserted":',
            "        if False:",
        ),
        # -- the two status axes must be backed, not toned --------------------
        (
            "asserted holds exactly when via is empty",
            '    if (derivation == "asserted") != (not via):',
            "    if False:",
        ),
        (
            "a via ref must name a fact that exists",
            "        if ref in facts:",
            "        if True:",
        ),
        (
            "a via ref must name a declaration the projection observed",
            "        if name in declarations:",
            "        if True:",
        ),
        (
            "a via ref of neither shape is refused",
            '    return f"via ref {ref!r} is neither an F: fact id nor a kernel:<Name> reference"',
            "    return None",
        ),
        (
            "mechanized-here forbids a missing step",
            '        if any(isinstance(s, dict) and s.get("ref") is None for s in via):',
            "        if False:",
        ),
        (
            "mechanized-here requires evidence",
            "        if not evidence:",
            "        if False:",
        ),
        (
            "evidence must carry a checker command",
            '            if not isinstance(row, dict) or not str(row.get("checker_command", "")).strip():',
            "            if False:",
        ),
        (
            "evidence under a weaker status is refused",
            "    elif evidence:",
            "    elif False:",
        ),
        (
            "novel-here requires a mechanized derivation",
            '    if document["external_status"] == "novel-here" and derivation != "mechanized-here":',
            "    if False:",
        ),
        # -- prose floors -----------------------------------------------------
        (
            "a short claim is refused",
            '    if len(document["claim"].strip()) < MIN_CLAIM:',
            "    if False:",
        ),
        (
            "a short transport is refused",
            '    if len(document["transport"].strip()) < MIN_TRANSPORT:',
            "    if False:",
        ),
        (
            "a transport copied from the claim is refused",
            '    if document["claim"].strip() == document["transport"].strip():',
            "    if False:",
        ),
        # -- identity ---------------------------------------------------------
        (
            "a filename that disagrees with the id is refused",
            "        if name != expected:",
            "        if False:",
        ),
        ("a duplicate id is refused", "        if identifier in seen_ids:", "        if False:"),
        (
            "one adjudication per endpoint pair",
            "        if len(pair) == 2 and pair in seen_pairs:",
            "        if False:",
        ),
        # -- shape and enum membership ----------------------------------------
        (
            "an unknown key is refused",
            "    unknown = set(document) - set(REQUIRED_KEYS) - set(OPTIONAL_KEYS)\n    if unknown:",
            "    unknown = set(document) - set(REQUIRED_KEYS) - set(OPTIONAL_KEYS)\n    if False:",
        ),
        (
            "a missing required key is refused",
            "    missing = [key for key in REQUIRED_KEYS if key not in document]\n    if missing:",
            "    missing = [key for key in REQUIRED_KEYS if key not in document]\n    if False:",
        ),
        (
            "schema_version is pinned",
            '    if document["schema_version"] != 1:',
            "    if False:",
        ),
        (
            "kind is pinned",
            '    if document["kind"] != "axeyum-theorem-correspondence":',
            "    if False:",
        ),
        (
            "the id pattern is enforced",
            '    if not isinstance(document["id"], str) or not ID_RE.fullmatch(document["id"]):',
            "    if False:",
        ),
        (
            "correspondence_kind membership",
            '    if document["correspondence_kind"] not in KINDS:',
            "    if False:",
        ),
        (
            "derivation_status membership",
            '    if document["derivation_status"] not in DERIVATION_STATUSES:',
            "    if False:",
        ),
        (
            "external_status membership",
            '    if document["external_status"] not in EXTERNAL_STATUSES:',
            "    if False:",
        ),
        (
            "exactly two endpoints",
            "    if not isinstance(endpoints, list) or len(endpoints) != 2:",
            "    if False:",
        ),
        (
            "every endpoint is an F: fact id",
            "    if not all(isinstance(e, str) and FACT_ID_RE.fullmatch(e) for e in endpoints):",
            "    if False:",
        ),
        (
            "via and evidence are arrays",
            '    if not isinstance(document["via"], list) or not isinstance(document["evidence"], list):',
            "    if False:",
        ),
        (
            "provenance.date is a date",
            '    if not isinstance(provenance, dict) or not DATE_RE.fullmatch(str(provenance.get("date", ""))):',
            "    if False:",
        ),
        (
            "provenance names a source",
            '    if not provenance.get("sources"):',
            "    if False:",
        ),
    ],
)

SUITES["fact-checker-grep-dash-q"] = (
    "scripts/validate-facts.py",
    "scripts.tests.test_validate_facts",
    [
        # `grep -q` as a pipeline consumer SIGPIPEs the producer under
        # `set -o pipefail`, turning the exit status nondeterministic
        # (CLAUDE.md, banned-shell-idioms #2; measured 7-vs-3 orphans on an
        # UNCHANGED tree). Deleting this guard must kill exactly the one test
        # that asserts a `grep -q` checker_command is rejected -- the
        # acceptance tests (committed form, `grep -c` forms) do not touch this
        # branch and must keep passing.
        (
            "grep -q checker_command is refused",
            "        if checker_command_uses_grep_dash_q(cmd):",
            "        if False:",
        ),
    ],
)

SUITES["fact-checker-grep-backslash-t"] = (
    "scripts/validate-facts.py",
    "scripts.tests.test_validate_facts",
    [
        # `\t` inside a grep -E pattern is NOT a tab in POSIX ERE (or BRE) --
        # GNU grep drops the backslash and matches a literal 't'. 54 facts /
        # 68 checker_commands carried this before 2026-08-25's rewrite to
        # `[[:space:]]`, each silently reporting a PRESENT theorem as ABSENT
        # under any script or CI run. Deleting this guard must kill exactly
        # the one test that asserts a `\t` checker_command is rejected -- the
        # acceptance tests (committed `[[:space:]]` forms, the `$(printf
        # '\t')` exception) do not touch this branch and must keep passing.
        (
            "grep \\t checker_command is refused",
            "        if checker_command_uses_grep_backslash_t(cmd):",
            "        if False:",
        ),
    ],
)

SUITES["fact-checker-deep-stack-release"] = (
    "scripts/validate-facts.py",
    "scripts.tests.test_validate_facts",
    [
        # `nat_axiom_inventory --include-constructed`, `prelude_theorem_inventory
        # --include-constructed` and any `theorem_dependency_inventory` build the
        # constructed carriers (CReal/Complex/CPoint) deep enough through
        # `Kernel::add_declaration` to overflow a debug build's default thread
        # stack -- measured exit 134 ("has overflowed its stack") without
        # `--release`, exit 0 with it. 19 committed `F-creal-*`/`F-complex-*`
        # checker commands carried this before 2026-08-25's fix. Deleting this
        # guard must kill exactly the one test that asserts such a
        # checker_command is rejected -- the acceptance tests (committed
        # `--release` forms, the --include-constructed-absent exception, the
        # unrelated-tool exception) do not touch this branch and must keep
        # passing.
        (
            "deep-stack inventory without --release is refused",
            "        if checker_command_needs_release_for_deep_stack(cmd):",
            "        if False:",
        ),
    ],
)

SUITES["fact-checker-kernel-theorem-shape"] = (
    "scripts/validate-facts.py",
    "scripts.tests.test_validate_facts",
    [
        # `formal.kernel_theorem` is what `theorem_of`
        # (scripts/check-fact-depends-derived.py, shared by the chain catalog
        # and the autogenesis snapshot builder) reads as a fact's subject
        # theorem when the key is present -- nothing else in the ledger reads
        # or validates this field, so a malformed value would be silently
        # treated as a real theorem name by every one of those consumers.
        # Deleting this guard must kill exactly the one test that asserts an
        # invalid value is rejected THROUGH `validate_one` -- the broader
        # good/bad-shape coverage (`kernel_theorem_is_valid` exercised
        # directly) does not touch this call site and must keep passing.
        (
            "invalid formal.kernel_theorem is refused",
            '    if "kernel_theorem" in formal and not kernel_theorem_is_valid(formal["kernel_theorem"]):',
            "    if False:",
        ),
    ],
)

SUITES["fact-cas-certificate-classification"] = (
    "scripts/validate-facts.py",
    "scripts.tests.test_validate_facts",
    [
        # ADR-0601 SS2: a `cas-certificate` fact's evidence must classify as
        # `kernel-reconstructed` or `cas-internal`, never an unclassifiable
        # third case -- otherwise a bogus checker_command could hide inside
        # the route the same way the 40-of-162 vacuous checkers did before
        # this project made "a checker that cannot fail is worse than no
        # checker" a standing rule. Deleting this guard must kill exactly the
        # one test that asserts a bogus checker_command is rejected THROUGH
        # `validate_one` -- the broader classifier coverage
        # (`classify_cas_certificate_checker` / `classify_cas_certificate_fact`
        # exercised directly) does not touch this call site and must keep
        # passing.
        (
            "unrecognized cas-certificate checker_command is refused",
            "            if classification == \"unrecognized\":",
            "            if False:",
        ),
    ],
)

SUITES["fact-theorem-of-explicit-field"] = (
    "scripts/check-fact-depends-derived.py",
    "scripts.tests.test_check_fact_depends_derived",
    [
        # `F:cassini-identity-over-constructed-integers` extracted `Int.sub`
        # (matched out of its own embedded formal-statement fragment) instead
        # of its real subject `Int.fib_cassini`, until `formal.kernel_theorem`
        # existed to let a fact pin the right answer over extraction. Deleting
        # the override kills exactly `test_an_explicit_string_wins...`; the
        # null-handling mutation below is separate and independent.
        (
            "an explicit string kernel_theorem wins over extraction",
            "        return value if isinstance(value, str) else None",
            "        return None",
        ),
        # `F:complex-ring-constructed-axiom-free` and `F:complex-mul-assoc`
        # both extracted `Complex.mul_assoc` and collided in
        # `create-autogenesis-chain-catalog.py --check`, until an explicit
        # `null` marked the package-level fact as having no single subject.
        # A presence check that degrades to a truthiness check would silently
        # treat that `null` as "key absent" and fall back to extraction again
        # -- kills exactly `test_an_explicit_null_means_no_single_subject...`.
        (
            "an explicit null kernel_theorem is honoured, not falsy-skipped",
            '    if "kernel_theorem" in formal:',
            '    if formal.get("kernel_theorem"):',
        ),
    ],
)

SUITES["import-backlog-classification"] = (
    "scripts/gen-import-backlog.py",
    "scripts.tests.test_gen_import_backlog",
    [
        # ADR-0601 SS3: a fact maps to a curriculum node only via an EXACT
        # match on `concept_refs[].graph == "math-education"` -- a crude
        # classifier that also accepted an unrelated graph carrying the same
        # ref id would manufacture curriculum edges nobody asserted (CLAUDE.md:
        # "a crude classifier that flags a whole shape is not a measurement").
        # Deleting this guard must kill exactly
        # `test_wrong_graph_does_not_map_even_with_matching_id`.
        (
            "curriculum mapping requires graph == math-education",
            '        if ref.get("graph") != "math-education":',
            "        if False:",
        ),
        # `dependency_ready` requires every dep's `epistemic_status` to be in
        # `OURS_SETTLED`, not merely present. Weakening this to "present-only"
        # must kill exactly `test_any_dep_open_is_not_ready` -- the sibling
        # `test_missing_dep_is_not_ready` (a dep id absent from the ledger)
        # exercises the OTHER half of this same condition and must survive.
        (
            "dependency readiness requires a SETTLED status, not just presence",
            '        if dep is None or dep.get("epistemic_status") not in VALIDATE_FACTS.OURS_SETTLED:',
            "        if dep is None:",
        ),
    ],
)

SUITES["ledger-coverage"] = (
    "scripts/gen-ledger-coverage.py",
    "scripts.tests.test_gen_ledger_coverage",
    [
        # F:real-lattice-is-constructed-axiom-free's literal "TODO: the
        # formal statement..." placeholder otherwise parses as a declared
        # name "TODO" -- a checker-that-cannot-fail shape one layer removed
        # (a placeholder read as real data). Kills exactly
        # `test_placeholder_todo_statement_is_not_treated_as_a_declared_name`.
        (
            "placeholder ALL-CAPS statement heads are not declared names",
            "        if match and not match.group(1).isupper():",
            "        if match:",
        ),
        # An explicit `kernel_theorem: null` means "no single subject" and
        # must stop resolution rather than fall through to the
        # statement/checker_command tiers -- the exact collision
        # (`F:complex-mul-assoc` / `F:complex-ring-constructed-axiom-free`
        # both extracting `Complex.mul_assoc`) this field exists to prevent.
        # Kills exactly
        # `test_explicit_field_null_means_no_single_subject_and_does_not_fall_through`.
        (
            "an explicit null kernel_theorem stops resolution, not falsy-skipped",
            '    if "kernel_theorem" in formal:',
            '    if formal.get("kernel_theorem"):',
        ),
        # `axeyum.string.2.*` names carry no capitalised namespace segment,
        # so without this case-first check `"axeyum".split(...)` would match
        # nothing in NAMESPACE_TO_PRELUDE and silently misfile every string-
        # prelude theorem under `logic`. Kills exactly
        # `test_string_prelude_has_no_capitalised_namespace`.
        (
            "string-prelude names are recognised before the namespace split",
            '    if name.startswith("axeyum.string."):',
            "    if False:",
        ),
        # A theorem name printed with two different footprint sizes across
        # nested prelude groups means the inventory tool's own output is
        # internally inconsistent -- silently picking the last one would
        # hide that rather than fail the gate. Kills exactly
        # `test_disagreeing_footprint_sizes_for_the_same_name_is_an_error`.
        (
            "disagreeing footprint sizes for one theorem name is an error",
            "        if previous is not None and previous != size:",
            "        if False:",
        ),
        # Zero inventory rows must be a hard error, not an empty (and
        # therefore vacuously "fully covered") denominator -- the debug-
        # build SIGABRT / missing --include-constructed trap CLAUDE.md
        # documents. Kills exactly
        # `test_zero_rows_is_an_error_not_a_silent_empty_denominator`.
        (
            "an empty theorem inventory is an error, not a silent zero",
            "    if not footprints:",
            "    if False:",
        ),
        # Only `proof_route == kernel-lean` facts are joined -- an
        # `smt-term-level` or `open` fact makes no claim this kernel's own
        # environment could corroborate. Kills exactly
        # `test_non_kernel_route_facts_are_not_joined`.
        (
            "only kernel-lean facts are joined against the kernel inventory",
            '        if fact.get("proof_route") not in KERNEL_ROUTES:',
            "        if False:",
        ),
        # Only `proved`/`computed` facts are joined -- an `open` fact
        # establishes nothing yet. Kills exactly
        # `test_open_facts_are_not_joined`.
        (
            "only established (proved/computed) facts are joined",
            '        if fact.get("epistemic_status") not in OURS_ESTABLISHED:',
            "        if False:",
        ),
    ],
)

# --------------------------------------------------------------------------
# `kernel-facts` -- the BULK-GENERATION suite, where the stakes are inverted.
#
# Every other suite here asks "does this guard stop a wrong answer".  This one
# asks "does this guard stop a PLAUSIBLE answer being manufactured at scale".
# `gen-kernel-facts.py` writes ledger facts mechanically, and the repository's
# central audit finding is that 40 of 162 checker runs exited 0 on completion
# alone.  A generator with a weak refusal set reproduces that finding 923 times
# in one commit, so the guards below are all either REFUSALS (things the script
# must decline to derive) or PROVENANCE (things that keep a generated fact
# distinguishable from a curated one).
#
# The `checker_command` shape guard is the one that matters most: without it a
# generated fact could carry `cargo run ... theorem_dependency_inventory` with
# the pipe removed, which lists theorems and says nothing about whether THIS one
# is among them.
# --------------------------------------------------------------------------

SUITES["kernel-facts"] = (
    "scripts/gen-kernel-facts.py",
    "scripts.tests.test_gen_kernel_facts",
    [
        # The projection prints the footprint SIZE, never the axiom NAMES, so a
        # non-zero footprint cannot be transcribed into `axiom_footprint` -- only
        # guessed at, and the whole value of that field is that it is measured.
        # Kills exactly `test_nonzero_axiom_footprint_is_declined`.
        (
            "a non-zero axiom footprint is declined, not guessed at",
            "    if row.footprint != 0:",
            "    if False:",
        ),
        # `lean_pp` renders `axeyum.string.2.X`'s namespace as
        # `axeyum.string._2.`. That is a RULE this script applies, so it is
        # checked against the type body rather than trusted. Kills exactly
        # `test_unconfirmable_numeric_namespace_spelling_is_declined`.
        (
            "the derived _-form namespace is verified against the type body",
            "        if namespace not in row.rendered_type:",
            "        if False:",
        ),
        # A zero-row projection is what a debug build's SIGABRT looks like, and
        # "measured, nothing to report" is the most dangerous available reading.
        # Kills exactly `test_zero_rows_is_an_error_not_an_empty_answer`.
        (
            "an empty projection is an error, not an empty answer",
            "    if total == 0:",
            "    if False:",
        ),
        # A generated fact must never overwrite a hand-written one. Kills exactly
        # `test_a_slug_taken_by_an_existing_curated_fact_is_declined`.
        (
            "a slug already taken by a curated fact is declined",
            "            if fact_id in existing_ids:",
            "            if False:",
        ),
        # Two theorems slugging to one id would silently give one fact two
        # subjects, the second write overwriting the first. Kills exactly
        # `test_two_theorems_slugging_to_one_id_is_declined_not_merged`.
        (
            "two theorems slugging to one id is declined, not merged",
            "            if fact_id in claimed:",
            "            if False:",
        ),
        # A direct proof dependency that no fact registers is DISCLOSED in
        # `notes` rather than silently dropped -- otherwise a generated fact's
        # `depends_on` reads as complete when it is a filtered subset. Kills
        # exactly `test_omitted_dependency_edges_are_disclosed_in_notes`.
        (
            "unregistered dependency edges are disclosed, not silently dropped",
            "    if omitted:",
            "    if False:",
        ),
        # THE PROVENANCE MARKER'S LOAD-BEARING GUARD. Without it, hand-written
        # prose sits under a `generated-unreviewed` marker and "generated" and
        # "curated" become indistinguishable again -- the exact thing the marker
        # exists to prevent. Kills exactly
        # `test_hand_edited_prose_under_a_generated_marker_is_a_problem`.
        (
            "enriched prose must flip curation, not sit under the generated marker",
            '        if fact.get("title") != expected_title:',
            "        if False:",
        ),
        # `external_status` is a judgement about the LITERATURE and this project
        # has already cited Zenodo self-deposits as refereed results. A generator
        # must never supply one. Kills exactly
        # `test_an_added_external_status_is_a_problem`.
        (
            "a generated fact may not carry external_status",
            '        if "external_status" in fact:',
            "        if False:",
        ),
        # THE CHECKER-THAT-CANNOT-FAIL GUARD. Kills exactly
        # `test_a_checker_that_cannot_fail_is_a_problem`.
        (
            "every generated checker_command must be able to fail",
            "            if not any(shape.match(cmd) for shape in ALLOWED_CHECKER_SHAPES):",
            "            if False:",
        ),
        # `curation` is defined only for generated facts; on a hand-written fact
        # it would read as "a lane reviewed this generated skeleton", a different
        # and stronger statement. Kills exactly
        # `test_a_curation_marker_without_a_generator_marker_is_a_problem`.
        (
            "a curation marker without a generator marker is rejected",
            '            if provenance.get("curation") in CURATION_VALUES:',
            "            if False:",
        ),
        # A fact flipped to `curated` is exempt from the byte-identity check --
        # that exemption is the whole point of the two-key marker, so it has to
        # be tested rather than assumed. Kills exactly
        # `test_flipping_curation_to_curated_permits_enriched_prose`.
        (
            "flipping curation to curated exempts a fact from byte-identity",
            "        if curation == CURATION_CURATED:",
            "        if False:",
        ),
        # `\t` in a scripted (GNU) grep is a literal `t`. 54 facts / 68 checkers
        # in this ledger were once wrong exactly this way, passing only in an
        # interactive ugrep-backed shell.
        #
        # MEASURED: this one kills FOUR tests, not one, and the overlap is
        # structural rather than sloppy -- ALLOWED_CHECKER_SHAPES is the AUDIT
        # half of the same contract the emitter implements, so changing the
        # emitted anchor also makes every generated fixture fail the audit. The
        # test that NAMES this guard is
        # `test_anchor_is_a_posix_class_that_gnu_grep_matches_against_a_real_tab`,
        # the only one of the four that RUNS the pattern; the other three die
        # through the audit regex. Splitting the halves apart to get a clean 1:1
        # would mean letting the emitter and the audit disagree about what a
        # valid checker looks like -- a worse property than an impure control.
        (
            "the checker anchor is [[:space:]], never a backslash-t",
            "f\"grep -cE '^{anchored}[[:space:]]'\"",
            "f\"grep -cE '^{anchored}\\\\t'\"",
        ),
        # `grep -q` exits at the first match and SIGPIPEs the producer, which
        # under `set -o pipefail` reads as "not found". Same four-way kill and the
        # same structural reason as the entry above; the test that NAMES this
        # guard is `test_uses_grep_c_not_grep_q`.
        (
            "the checker consumes the pipe with grep -c, never grep -q",
            "f\"grep -cE '^{anchored}",
            "f\"grep -qE '^{anchored}",
        ),
    ],
)

SUITES["autogenesis-authored-declaration-driver"] = (
    "scripts/validate-autogenesis-operations.py",
    "scripts.tests.test_validate_autogenesis_operations",
    [
        # docs/autogenesis/296: the registry could only describe PIPELINED
        # work (8 of 10 EXECUTION_DRIVERS were axeyum-lean-import/*); this
        # driver is the general shape for "an agent hand-authored a kernel
        # declaration directly", and every guard below exists so a receipt
        # naming work that never happened must fail, not silently pass.
        (
            "a declaration must appear in its claimed source file",
            "            if declaration not in declaration_source_text:",
            "            if False:",
        ),
        (
            "one Lean declaration may not be bound to two facts",
            "            if declaration in seen_declarations:",
            "            if False:",
        ),
        (
            "a verifying test must exist as a fn in the named test file",
            'if not re.search(rf"fn\\s+{re.escape(test_name)}\\s*\\(", test_source):',
            "if False:",
        ),
        (
            "declaration_source/test_path must stay inside the kernel crate",
            '''        if not declaration_source.is_relative_to(
            crate_root
        ) or not test_path.is_relative_to(crate_root):''',
            "        if False:",
        ),
        (
            "a target declaration must be a qualified Lean name",
            """            if not isinstance(declaration, str) or not LEAN_DECLARATION_RE.fullmatch(
                declaration
            ):""",
            "            if False:",
        ),
        (
            "no fact id may repeat across input_fact_id/additional_fact_ids",
            '''        if len(all_fact_ids) != len(set(all_fact_ids)):
            raise RegistryError(
                f"{label} names a fact id more than once across "
                "input_fact_id/additional_fact_ids"
            )
        declaration_source = repository_file(''',
            '''        if False:
            raise RegistryError(
                f"{label} names a fact id more than once across "
                "input_fact_id/additional_fact_ids"
            )
        declaration_source = repository_file(''',
        ),
        (
            "targets must bind fact ids in input+additional order",
            '''        if target_fact_ids != all_fact_ids:
            raise RegistryError(
                f"{label}.targets fact_id order must match input_fact_id "
                "followed by additional_fact_ids"
            )
    elif driver == "axeyum-lean-import/statement-reflexivity-v1":''',
            '''        if False:
            raise RegistryError(
                f"{label}.targets fact_id order must match input_fact_id "
                "followed by additional_fact_ids"
            )
    elif driver == "axeyum-lean-import/statement-reflexivity-v1":''',
        ),
        (
            "this driver's applicability/admission must stay in its closed set",
            '''            elif executor["driver"] == "axeyum-lean-kernel/authored-declaration-v1":
                # Fragment-agnostic like modeq-family-multi-target-v1 (this
                # driver is not tied to Int specifically -- a future
                # hand-authored Nat closure is the same shape), but the proof
                # itself runs entirely inside this repository's own kernel
                # crate, never through the importer.
                if (''',
            '''            elif executor["driver"] == "axeyum-lean-kernel/authored-declaration-v1":
                # Fragment-agnostic like modeq-family-multi-target-v1 (this
                # driver is not tied to Int specifically -- a future
                # hand-authored Nat closure is the same shape), but the proof
                # itself runs entirely inside this repository's own kernel
                # crate, never through the importer.
                if False and (''',
        ),
    ],
)


# --------------------------------------------------------------------------
# `ledger-coverage` — independent validation that curated and registered
# counters measure distinct properties and cannot silently swap meaning.
#
# The incident that prompted this was a demonstration that a VACUOUS fixture —
# a fact not in the registered population — was used as "proof" the counter
# moved. Deleting this control would let a future author swap in a similarly-
# vacuous fixture and the guard would fire at exactly the wrong time: when the
# counter did NOT move and the author could not see why.
#
# This suite has two fixtures: one in-population fact that is generated-unreviewed,
# and one in-population fact that is curated. The guards assert both memberships
# explicitly, so a future author cannot repeat the vacuity trap.
# --------------------------------------------------------------------------

SUITES["ledger-coverage"] = (
    "scripts/gen-ledger-coverage.py",
    Unittest("scripts.tests.test_gen_ledger_coverage"),
    [
        (
            "is_curated returns false for generated-unreviewed provenance",
            '    curation = provenance.get("curation")\n    # If curation field is missing or not "generated-unreviewed", it\'s curated\n    return curation != "generated-unreviewed"',
            '    curation = provenance.get("curation")\n    # If curation field is missing or not "generated-unreviewed", it\'s curated\n    return curation == "generated-unreviewed"',
        ),
        (
            "is_curated recognizes the \"generated-unreviewed\" marker",
            '    return curation != "generated-unreviewed"',
            '    return True',
        ),
        (
            "curated counter tracks is_curated in join()",
            '        if is_curated(fact):\n            result.curated.setdefault(name, []).append(fid)\n            result.curated_facts += 1',
            '        if not is_curated(fact):\n            result.curated.setdefault(name, []).append(fid)\n            result.curated_facts += 1',
        ),
        (
            "curated counter is reported in build_document",
            '"curated": len(curated_names),',
            '"curated": 0,',
        ),
    ],
)



SUITES["absence-claims"] = (
    "scripts/check-absence-claims.py",
    Unittest("scripts.tests.test_check_absence_claims"),
    [
        (
            "G1 an `absent:` claim whose declaration is present",
            '            if marker.kind == "absent" and present:',
            "            if False:",
        ),
        (
            "G2 the spelling-normalized fallback (snake_case vs camelCase)",
            "        hit = self.normalized.get(normalize_spelling(name))",
            "        hit = None",
        ),
        (
            "G3 a `was-absent:` record pointing at a declaration that is gone",
            '            elif marker.kind == "was-absent" and not present:',
            "            elif False:",
        ),
        (
            # Reordering the regex alternation is an EQUIVALENT mutant --
            # leftmost-first still cannot match `absent` at the `w` of
            # `was-absent` -- so it survives without meaning anything. The real
            # hazard is the one CLAUDE.md's `AxNat`/`Nat` entry describes:
            # comparing the kind by substring instead of by equality, which
            # silently reads every historical record as a live claim.
            "G4 the marker kind is compared by equality, not substring",
            '            if marker.kind == "absent" and present:',
            '            if "absent" in marker.kind and present:',
        ),
        (
            "G5 a marker naming a root the authority does not carry",
            "            if root not in authority.roots:",
            "            if False:",
        ),
        (
            "G6 the stale-projection floor",
            "    if len(exact) < floor:",
            "    if False:",
        ),
        (
            "G7 the projection-row shape",
            "        if len(fields) < 4:",
            "        if False:",
        ),
        (
            "the authority tool's own exit status",
            "    if proc.returncode != 0:",
            "    if False:",
        ),
        (
            "G8 a marker that names nothing",
            "    if not names:",
            "    if False:",
        ),
        (
            "G9 a marker naming something that is not a declaration name",
            "        if not DECL_RE.fullmatch(name):",
            "        if False:",
        ),
        (
            "G10 vacuity: zero files scanned",
            "    if not files:",
            "    if False:",
        ),
        (
            "G11 vacuity: zero claim sites detected",
            "    if not sites:",
            "    if False:",
        ),
        (
            "G12 vacuity: zero markers",
            "    if not markers:",
            "    if False:",
        ),
        (
            "G13 the unexpirable-claim budget",
            "    if len(bare_named) > budget:",
            "    if False:",
        ),
        (
            "G14 claim names derive from the authority, not a literal root list",
            '        return tuple(n for n in self.candidates if n.split(".", 1)[0] in authority.roots)',
            "        return tuple(self.candidates)",
        ),
        (
            "G15 a stale exclusion (a carve-out for a path that is gone)",
            '        if not (root / entry["path"]).exists()',
            "        if False",
        ),
        (
            "G16 an exclusion without a written reason",
            "        if not isinstance(reason, str) or not reason.strip():",
            "        if False:",
        ),
        (
            "the exclusion actually skips the file",
            "            if path.relative_to(root).as_posix() in excluded:",
            "            if False:",
        ),
        (
            "G17 Rust claims are read from comments only",
            "        return bool(RUST_COMMENT_RE.match(line))",
            "        return True",
        ),
        (
            "G19 a marker quoted in a code span is documentation, not a claim",
            '    masked = CODE_SPAN_RE.sub(" ", line)',
            "    masked = line",
        ),
        (
            "G20 a marker inside a code fence is documentation, not a claim",
            "            if FENCE_RE.match(line):\n                in_fence = not in_fence",
            "            if FENCE_RE.match(line):\n                in_fence = in_fence",
        ),
        (
            "quoted markers are counted rather than silently dropped",
            '            quoted += len(MARKER_RE.findall("".join(CODE_SPAN_RE.findall(line))))',
            "            quoted += 0",
        ),
        (
            # A marker attaches to its own BLOCK. Gathering names file-wide
            # would silence a claim a paragraph away that the marker never
            # answered -- the exact defect the 133-ledger-uc.md stale claim
            # had in reverse (a correct marker one blank line too far).
            "a marker attaches to its own block",
            '            marker_scan = "\\n".join(marker_scan_line(rel, line) for line in block)',
            '            marker_scan = "\\n".join(marker_scan_line(rel, line) for line in lines)',
        ),
        (
            # ADR-1250. A marker is an HTML COMMENT, so it is legitimately
            # multi-line, and one carrying a note wraps at the same column as
            # the prose around it. Without DOTALL the body's `.*?` stops at the
            # newline and such a marker matches NOTHING -- not merely
            # unattached, INVISIBLE, in all three readers at once. That is a
            # marker that cannot attach: the mirror of a checker that cannot
            # fail, leaving `--update-budget` as the only way to retire a
            # resolved claim.
            "G25 a marker may be written across lines",
            "    re.IGNORECASE | re.DOTALL,",
            "    re.IGNORECASE,",
        ),
        (
            # A marker wrapped inside a `//!` doc comment carries `//!` at the
            # head of every continuation line. Left in place it lands in the
            # names field and the marker is rejected as malformed -- so the
            # Rust surface would support only single-line markers while the
            # Markdown surface supported both.
            "G26 a wrapped Rust comment prefix is not part of a marker's names",
            '        masked = RUST_COMMENT_PREFIX_RE.sub("", masked)',
            "        masked = masked",
        ),
        (
            # The census locates a claim by index into the marker-stripped
            # body, so collapsing an N-line marker to one space shifts every
            # later line in that block by N-1 and the gate names the wrong
            # source line -- pointing a reader at prose that carries no claim.
            "G27 stripping a marker keeps its newlines",
            '    return " " + "\\n" * match.group(0).count("\\n")',
            '    return " "',
        ),
        (
            "G21 a claim's subjects are the names in its OWN unit",
            "    for piece in SENTENCE_SPLIT_RE.split(text):",
            "    for piece in [text]:",
        ),
        (
            "G22 a colon does not end a claim unit",
            'SENTENCE_SPLIT_RE = re.compile(r"(?<=[.!?])\\s")',
            'SENTENCE_SPLIT_RE = re.compile(r"(?<=[.!?:;])\\s")',
        ),
        (
            "G23 a table row / list item is its own claim unit",
            'RECORD_MD_RE = re.compile(r"^\\s*(?:\\||[-*+]\\s|\\d+[.)]\\s)")',
            'RECORD_MD_RE = re.compile(r"(?!x)x")',
        ),
        (
            "G23 a wrapped item's continuation lines stay with it",
            "        if chunk and record_re.match(line):",
            "        if chunk:",
        ),
        (
            "G24 a marker only silences a claim it NAMES",
            "                annotated = exact_hit or normalized_hit",
            "                annotated = bool(marker_names)",
        ),
        (
            "G24 the marker match falls back to the normalized spelling",
            "                annotated = exact_hit or normalized_hit",
            "                annotated = exact_hit",
        ),
        (
            "--update-budget reports that the number moved",
            "        if recorded != counted:",
            "        if False:",
        ),
        (
            "G18 the exit status depends on the finding",
            "        return 0\n    return 1",
            "        return 0\n    return 0",
        ),
    ],
)


# --------------------------------------------------------------------------
# `nursery-refill-ceiling` — ADR-0616. R3 used to compare a FLAT COUNT of the
# extension manifest against 214, so re-attesting a row bought nothing and the
# ADR's own stated exit ("when it binds, re-attest") could not be taken. The
# comparison now counts by attestation.
#
# Two mutants are load-bearing in opposite directions, and neither is "does a
# bound exist":
#   * dropping the extension's attested rows from `attested_cohort` reverts the
#     promotion, and is killed ONLY by the case where an attested row buys the
#     headroom an unattested one does not;
#   * dropping `not_elaborable` from `unattested_cohort` promotes a string Lean
#     REFUSED, and is killed ONLY by the case that supplies its weight from that
#     bucket.
#
# The plain comparison `unattested > attested` is deliberately not mutated to a
# no-op: two cases assert it fires and both would die, which measures nothing
# the two mutants above do not already measure more precisely.
# --------------------------------------------------------------------------

SUITES["nursery-refill-ceiling"] = (
    "scripts/gen-autogenesis-nursery-refill.py",
    Unittest("scripts.tests.test_gen_autogenesis_nursery_refill"),
    [
        (
            "an ATTESTED extension row counts toward the attested cohort",
            '    return len(v1_evaluation) + len(validation.get("attested", []))',
            "    return len(v1_evaluation)",
        ),
        (
            "a Lean-REFUSED row counts as unattested, never as headroom",
            '    return (len(validation.get("unattested", []))\n'
            '            + len(validation.get("not_elaborable", [])))',
            '    return len(validation.get("unattested", []))',
        ),
        (
            "an ingested run must name the PINNED Mathlib commit",
            '        if record.get("mathlib_commit") != SOURCE_COMMIT:',
            "        if False:",
        ),
        (
            "an ingested run whose negative control was ACCEPTED is refused",
            '        if record.get("negative_control_rejected") is not True:',
            "        if False:",
        ),
        (
            "a partly-attested cohort reports both populations, not just one",
            '            f"{attested} of {total} statements carry the same real-Lean "',
            '            f"{attested} of {attested} statements carry the same real-Lean "',
        ),
        (
            "an UNRUN cohort is still described as quotation grade",
            '            f"These {total} statements carry the quotation grade, not v1\'s "\n'
            '            f"real-Lean round-trip attestation; the two must not be reported "\n'
            '            f"together as one attested population.")',
            '            f"These {total} statements carry the same real-Lean "\n'
            '            f"round-trip attestation as nursery-v1\'s 214.")',
        ),
        (
            "the dependency-component gap survives full attestation",
            '        "Attestation does not make this an evaluation population equivalent to "\n'
            '        "nursery-v1\'s. v1 freezes partitions against declared dependency weak "\n'
            '        "components (policy.split_component_authority); here source_group is "\n'
            '        "the Mathlib defining module and no dependency-component analysis was "\n'
            '        "run, so a held-out row can share a component with a dispatchable one "\n'
            '        "and nothing in this manifest sees it. Attestation grades the "\n'
            '        "STATEMENT; this is a property of the ROW.",',
            '        "Attestation makes this equivalent to nursery-v1.",',
        ),
    ],
)


# --------------------------------------------------------------------------
# `nursery-refill-amendment` — ADR-0542 / ADR-0617. R10 ties a moved partition
# in `nursery-v2-extension.json` to a recorded breach in the amendment ledger.
#
# Before it, `frozen_partitions` froze `family_partitions`, so the manifest was
# its own authority: a hand edit that moved a family AND recomputed
# `extension_sha256` regenerated perfectly clean with no amendment anywhere.
# The digest catches a careless edit, never a deliberate one. Found 2026-08-30
# while making the `natural-divisibility` amendment the holdout-isolation gate
# demands — there was nothing to record it against.
#
# Every mutant below reverts a check that had NO predecessor, so each kills
# exactly one case and none is shadowed by R6 or R8. Two earlier drafts of R10
# are NOT registered here because they could not be killed at all: comparing
# `assign_partitions()` against `preregistered_assignment()` makes the
# no-amendment and destination branches unreachable (the ledger is applied
# last, so the two agree by construction), and re-aiming R8 at
# `preregistered_assignment()` compares a function against the dict it derives
# from. Both are recorded in the source comments as measured dead ends.
# --------------------------------------------------------------------------

SUITES["nursery-refill-amendment"] = (
    "scripts/gen-autogenesis-nursery-refill.py",
    Unittest("scripts.tests.test_gen_autogenesis_nursery_refill"),
    [
        (
            "a moved partition with NO amendment is refused",
            "        if amendment is None:\n"
            "            if now != was:",
            "        if amendment is None:\n"
            "            if False:",
        ),
        (
            "an amendment whose `from` is not the preregistered partition",
            '        if amendment.get("from") != was:',
            "        if False:",
        ),
        (
            "an amendment whose `to` is not the manifest's partition",
            '        if amendment.get("to") != now:',
            "        if False:",
        ),
        (
            "an amended family may not be recycled into held-out",
            '        if now == "held-out":',
            "        if False:",
        ),
        (
            "a manifest with no preregistered freeze has nothing to check",
            '    partitions = manifest.get("preregistered_family_partitions")\n'
            "    if not isinstance(partitions, dict) or not partitions:",
            '    partitions = manifest.get("preregistered_family_partitions")\n'
            "    if False:",
        ),
        (
            "a missing amendment ledger is an error, not a quiet pass",
            "    if not SPLIT_POLICY.is_file():",
            "    if False:",
        ),
        (
            "a family amended twice has no defined origin",
            "        if family in by_family:",
            "        if False:",
        ),
    ],
)


# --------------------------------------------------------------------------
# `nursery-refill-historical-draw` — ADR-1445.
#
# `select()` re-screened EVERY family on every invocation, so a divergence
# registered after a draw retroactively removed rows from it. Measured
# 2026-09-01: the ADR-1415 sweep took 31 drawn rows out of four families, 30 of
# them held-out, and `--check` went red with no legal remedy — un-registering a
# true divergence or deleting held-out rows are both forbidden.
#
# The mutants below are aimed at the failure this fix could EASILY have
# introduced, which is the opposite one: a freeze that simply copies recorded
# rows through is a checker that cannot fail, and the manifest becomes its own
# authority about its own rows (the R10 hole, one level down). So each F-guard
# has a case, and the first mutant deletes the freeze itself — killed by the
# twin that proves the regression control is not vacuous.
#
# NOT registered, because it cannot be killed: freezing `partition` alongside
# the pinned fields. That mutant makes `test_an_amendment_still_moves_a_frozen_family`
# fail, which is a KILL — but it is the guard being wrong rather than the guard
# being removed, so it belongs in the source comment (it is there) and not here.
# --------------------------------------------------------------------------

SUITES["nursery-refill-historical-draw"] = (
    "scripts/gen-autogenesis-nursery-refill.py",
    Unittest("scripts.tests.test_gen_autogenesis_nursery_refill"),
    [
        (
            "the membership freeze itself — without it a later divergence "
            "re-screens an already-drawn family",
            "        recorded = drawn.get(family)\n"
            "        if recorded is not None:",
            "        recorded = drawn.get(family)\n"
            "        if False:",
        ),
        (
            "F1 a drawn row absent from the pinned inventory",
            "        if record is None:\n"
            "            raise RefillError(\n"
            "                f\"F1 drawn row",
            "        if False:\n"
            "            raise RefillError(\n"
            "                f\"F1 drawn row",
        ),
        (
            "F2 a drawn row whose module now maps to another family",
            '        if module_family.get(record["module"]) != family:',
            "        if False:",
        ),
        (
            "F3 a drawn row that no longer re-derives from the pinned source",
            "        differing = sorted(field for field in PINNED_ENTRY_FIELDS\n"
            "                           if rebuilt[field] != row.get(field))",
            "        differing = []",
        ),
        (
            "F4 a drawn family recording the wrong number of rows",
            "    if len(recorded) != PER_FAMILY:",
            "    if False:",
        ),
        (
            "the drawn freeze's own digest check — a hand-edited manifest "
            "must not become the freeze",
            "    if digest(body) != recorded:\n"
            "        raise RefillError(\n"
            "            f\"{EXTENSION.name} does not match its own "
            "extension_sha256, so its \"\n"
            "            f\"recorded entries cannot be trusted as the drawn "
            "freeze\")",
            "    if False:\n"
            "        raise RefillError(\n"
            "            f\"{EXTENSION.name} does not match its own "
            "extension_sha256, so its \"\n"
            "            f\"recorded entries cannot be trusted as the drawn "
            "freeze\")",
        ),
        (
            "the drift report — the freeze must not make the thinning invisible",
            "        if reason is None:\n"
            "            continue",
            "        if True:\n"
            "            continue",
        ),
    ],
)


# --------------------------------------------------------------------------
# cas-substance (ADR-0622).
#
# The defect being guarded against is one level up from a weak checker: the
# `kernel-reconstructed` counter moved for a reconstruction whose kernel
# obligation was `poly_expr(X) = 1 * poly_expr(X)`, because the classifier read
# a PACKAGE NAME out of a checker_command and never looked at what the kernel
# was asked to check. So the controls here are aimed less at "does the guard
# reject" and more at "does the gate still DISTINGUISH the two kinds" -- three
# positive controls assert that an honest `combination`, a DISCLOSED `refl`,
# and an ordinary cas-internal fact are all accepted, because a gate that
# refused everything would satisfy every refusal test below and be useless.
# --------------------------------------------------------------------------

SUITES["cas-substance"] = (
    "scripts/check-cas-substance.py",
    Unittest("scripts.tests.test_check_cas_substance"),
    [
        (
            "G1 a kernel-reconstructed fact with no cas_substance block",
            "    if not isinstance(substance, dict):",
            "    if False:",
        ),
        (
            "G2 a shape outside the enumeration",
            "    if declared_shape not in SHAPES:",
            "    if False:",
        ),
        (
            "G3 no `certificate` key at all",
            '    if "certificate" not in substance:',
            "    if False:",
        ),
        (
            "G4 a certificate path that does not resolve",
            "            if not resolved.is_file():",
            "            if False:",
        ),
        (
            "G5 a declared shape disagreeing with the certificate's derived one",
            '                if derived["shape"] != declared_shape:',
            "                if False:",
        ),
        (
            "G6 a null certificate with no derivation_declined_reason",
            "            if not reason:",
            "            if False:",
        ),
        (
            "G7 a non-discriminating shape with no disclosure",
            '        if not (substance.get("disclosure") or "").strip():',
            "        if False:",
        ),
        (
            "G8 a non-discriminating shape with no disclosure_axiom_key",
            "        if not key:",
            "        if False:",
        ),
        (
            "G9 a disclosure key naming no axiom_footprint entry",
            "        elif key not in axiom_footprint_keys(fact):",
            "        elif False:",
        ),
        (
            "G10 shape `empty` registered at all",
            '    if declared_shape == "empty":',
            "    if False:",
        ),
        (
            "G11 a text-refl formal.statement declared as something else",
            '    if text_refl is True and declared_shape != "refl":',
            "    if False:",
        ),
        (
            "G12 a cas_substance block on a fact that is not kernel-reconstructed",
            '            if isinstance(fact.get("cas_substance"), dict):',
            "            if False:",
        ),
        # -- THE RATCHET (ADR-0699). The 2026-08-30 audit's third survivor:
        # every guard above passes a CONSISTENT downgrade, so a fact could lose
        # its kernel reconstruction, or vanish, and the gate stayed green with a
        # quietly smaller headline.
        (
            "R0 a missing ratchet file is refused",
            "    if recorded is None:",
            "    if False:",
        ),
        (
            "R0b a trimmed ratchet is refused by the absolute floor",
            "    if len(recorded) < args.min_reconstructed:",
            "    if False:",
        ),
        (
            "R0c a ledger below the absolute floor is refused",
            "    if kernel_reconstructed < args.min_reconstructed:",
            "    if False:",
        ),
        (
            "R1 a ratcheted fact that is no longer kernel-reconstructed",
            "        if fid not in current:",
            "        if False:",
        ),
        (
            "R2 a derived shape that became self-reported",
            '        if was_provenance == "derived" and now_provenance != "derived":',
            "        if False:",
        ),
        (
            "R3 a discriminating shape that became non-discriminating",
            "        if was_discriminating and not now_discriminating:",
            "        if False:",
        ),
        (
            "R4 the ratchet is CONSULTED at all",
            "    errors.extend(ratchet_errors(recorded, current))",
            "    pass",
        ),
    ],
)


# The derivation core is registered separately because it is a different
# subject FILE, and because its guards fail in the opposite direction from the
# gate's: a broken derivation does not refuse a good fact, it silently reports a
# refl-shaped obligation as a combination and the gate then agrees with it.
# Note D1 in particular -- no committed certificate has a zero cofactor today
# (measured 2026-08-30: 0 of 45 across all ten), so the real ledger cannot
# exercise that rule and only this control does.

SUITES["cas-substance-derivation"] = (
    "scripts/cas_substance.py",
    Unittest("scripts.tests.test_check_cas_substance"),
    [
        (
            "D1 a zero cofactor must not count as an active generator",
            "        i for i, cofactor in enumerate(cofactors) if not is_zero_poly(cofactor)",
            "        i for i, cofactor in enumerate(cofactors) if not False",
        ),
        (
            "D2 the cofactor must be the constant ONE, not merely a constant",
            "    return den != 0 and num == den",
            "    return den != 0",
        ),
        (
            "D3 the generator must be identical to the conclusion for `refl`",
            "        if is_constant_one_poly(cofactors[i]) and generator == concl_poly:",
            "        if is_constant_one_poly(cofactors[i]):",
        ),
        (
            "D4 a certificate is only as strong as its WEAKEST conclusion",
            "        weakest = min(",
            "        weakest = max(",
        ),
        (
            "D5 an unparseable statement yields no signal, never `clean`",
            "    return top if len(stack) == 1 else None",
            "    return top if len(stack) >= 1 else None",
        ),
    ],
)

# --------------------------------------------------------------------------
# `artifact-ownership` -- ADR-0652. One producer per generated artifact.
#
# Two of these mutants deliberately kill more than one case, and that is the
# structure of the gate rather than a weak suite: CTRL is DEFINED as "the RUNS
# machinery must reject a planted second writer", so blinding the RUNS
# comparison necessarily blinds CTRL as well. A suite in which those two died
# separately would be testing two comparisons, and there is only one.
#
# Kill sets are reported as measured, survivors included.
# --------------------------------------------------------------------------

SUITES["artifact-ownership"] = (
    "scripts/check-generated-artifact-ownership.py",
    Unittest("scripts.tests.test_check_generated_artifact_ownership"),
    [
        (
            "KEYS names a dropped top-level key",
            "missing = [k for k in artifact.required_keys if k not in doc]",
            "missing = []",
        ),
        (
            "KEYS names a dropped nested tier count",
            "gone = [k for k in keys if k not in block]",
            "gone = []",
        ),
        (
            "KEYS refuses a top level that is not an object",
            "    if not isinstance(doc, dict):",
            "    if False:",
        ),
        (
            "KNOWN names a script that is not classified",
            "for path in sorted(found - classified):",
            "for path in sorted(set()):",
        ),
        (
            "KNOWN names a classification that has gone stale",
            "for path in sorted(classified - found):",
            "for path in sorted(frozenset()):",
        ),
        (
            "READS rejects a declared reader that can write",
            "        if calls:",
            "        if False:",
        ),
        (
            "RUNS compares the artifact before and after each producer",
            "    if after != before:",
            "    if False:",
        ),
        (
            "RUNS catches a producer that DELETES the artifact",
            "    if not target.is_file():",
            "    if False:",
        ),
        (
            "CTRL reports an inert RUNS arm",
            "    if verdict is None:",
            "    if False:",
        ),
        (
            "OWNER requires byte-for-byte restoration from a perturbed copy",
            "    if restored != good:",
            "    if False:",
        ),
        # -- COVER, the DENOMINATOR. The audit's fourth finding: every arm
        # above is correct and derives what it needs from the tree, while
        # `GUARDED` itself was a hand-written literal of length one reported as
        # `artifacts=1`, so an artifact with a second producer and no entry was
        # structurally invisible.
        (
            "COVER a NEW multi-writer artifact must be guarded or recorded",
            "    for base in sorted(set(current) - recorded - guarded):",
            "    for base in sorted(set()):",
        ),
        # -- COVER's ARTIFACT IDENTIFICATION, distinct from its writer
        # over-approximation. Matching a basename as a bare substring made
        # `schema.json` a three-producer artifact out of two mentions of
        # `fact.schema.json` and `obstruction-graph.schema.json`, and COVER
        # demanded the fiction be recorded. Restoring the substring semantics
        # must kill the tests that name it.
        (
            "COVER takes the WHOLE dotted component, so a name that is a "
            "suffix of another is not attributed to it",
            r"(?<![A-Za-z0-9_.\-])([A-Za-z0-9_.\-]+\.json)(?![A-Za-z0-9_\-])",
            r"(?<![A-Za-z0-9_.\-])([A-Za-z0-9_\-]+\.json)(?![A-Za-z0-9_\-])",
        ),
        (
            "COVER refuses a name that CONTINUES past `.json`",
            r"([A-Za-z0-9_.\-]+\.json)(?![A-Za-z0-9_\-])",
            r"([A-Za-z0-9_.\-]+\.json)",
        ),
        (
            "COVER a stale candidate row is named",
            "    for base in sorted(recorded - set(current) - guarded):",
            "    for base in sorted(frozenset()):",
        ),
        (
            "COVER a missing candidate list is refused",
            "    if recorded is None:",
            "    if False:",
        ),
        (
            "COVER guarding satisfies the arm without a candidate row",
            "    for base in sorted(set(current) - recorded - guarded):",
            "    for base in sorted(set(current) - recorded):",
        ),
        (
            "COVER the candidate set needs TWO producers, not one",
            "        if len(naming) >= 2:",
            "        if len(naming) >= 1:",
        ),
        (
            "COVER a comment line is not a candidate",
            "        if line.strip() and not line.lstrip().startswith(\"#\")",
            "        if line.strip()",
        ),
        # -- INVOKES, the third classification (2026-09-02). The KNOWN arm
        # went red on `scripts/lane-merge-land.sh`, which names a guarded
        # artifact to clear a merge conflict on it and stage it, and then
        # regenerates it by calling the OWNER. `runs` would execute a merge
        # driver inside the ownership sandbox and `reads` is false for a
        # script that redirects and stages, so the arm is BY INSPECTION.
        #
        # The LAST mutant kills FOUR cases, and that is the structure of the
        # arm rather than a weak suite. Following bindings is not one of the
        # arm's guards; it is its REACHABILITY -- what lets a path bound into
        # an array and staged through a loop variable be judged at all. Every
        # case whose fixture binds a name therefore depends on it: the array
        # case, the binding-that-writes case, the vacuity case, and the
        # real-tree false-positive control, whose script is the array shape.
        # Removing it does not blind the arm, it makes the arm judge the
        # BINDING line and refuse the real script -- so the four deaths are
        # over-firing, not a shared blind spot. The six guards above each kill
        # exactly one. Kill sets are reported as measured.
        (
            "INVOKES a line reaching the artifact must be a staging line",
            "            if not STAGING.search(line):",
            "            if False:",
        ),
        (
            "INVOKES a redirection INTO the artifact is not staging, whatever "
            "else is on the line",
            "            if redirects_into(line, pat):",
            "            if False:",
        ),
        (
            "INVOKES an invoker must name the OWNER it regenerates with",
            "        if artifact.owner.path not in text:",
            "        if False:",
        ),
        (
            "INVOKES a classification that stages nothing is vacuous",
            "        if not staged:",
            "        if False:",
        ),
        (
            "INVOKES a binding that also writes is judged, not exempted",
            "                if binding and not WRITE_SHAPE.search(line):",
            "                if binding:",
        ),
        (
            "INVOKES a comment reaching the artifact executes nothing",
            '                if line.lstrip().startswith("#") or not pat.search(line):',
            "                if not pat.search(line):",
        ),
        (
            "INVOKES bindings are FOLLOWED, so a name reaching the artifact "
            "is judged wherever it is used",
            "                binding = FOR_BINDING.match(line) or NAME_BINDING.match(line)",
            "                binding = None",
        ),
    ],
)



# --------------------------------------------------------------------------
# `merge-hygiene` -- `scripts/check-merge-hygiene.sh`, which landed on
# 2026-08-30 with ZERO registered controls. The 2026-08-30 session audit named
# it first among five survivors: `ls scripts/tests/ | grep -c merge-hygiene`
# returned 0 against a positive control of 1 for `aggregate-scope`, so every
# guard in it was a survivor by definition however well it behaved by hand.
#
# The controls drive the SHIPPED script against a throwaway git repository via
# `AXEYUM_MERGE_HYGIENE_ROOT`, with stub generators whose exit status the
# scenario chooses. Nothing is re-implemented.
#
# Two of these mutants kill more than one test, and it is the structure of the
# gate rather than a weak suite: the marker branch is ONE `if`, and three
# scenarios (a `.rs` file, a bare `=======` in a fact file, a control suite)
# reach failure through it. Kill sets are reported as measured.
#
# M8/M9 are the two halves of the ADR-1512 guard and are deliberately split:
# M8 removes the failure branch (a stale `prelude_fields.rs` stops being
# reported) and M9 removes the exit-2 branch (a host without `rustfmt` starts
# being reported as drift). Each must kill exactly one test -- a single mutant
# over the whole block could not tell the two apart.
#
# M10/M11/M12 are the ADR-1511 amendment (2026-09-02), and they are split three
# ways for the same reason M8/M9 are two. The shape-duplicates guard has an
# exit code that means two different things: `check-shape-duplicates.py` exits
# 2 both for a malformed allowlist (a committed defect, must block) and for an
# absent-or-stale prebuilt binary (a fact about this host, must not). M11
# removes the marker condition, so an unanswerable run starts blocking; M12
# removes the marker requirement's discrimination, so a malformed allowlist
# starts being swallowed as `skipped`. A single mutant over the whole block
# would report a kill without saying which direction is guarded, and the
# direction that matters most is the one that fails SILENTLY.
# --------------------------------------------------------------------------

SUITES["merge-hygiene"] = (
    "scripts/check-merge-hygiene.sh",
    Unittest("scripts.tests.test_check_merge_hygiene"),
    [
        (
            "M1 conflict markers in tracked files fail the gate",
            'if [ "$markers" -ne 0 ]; then',
            "if false; then",
        ),
        (
            "M2 a bare `=======` counts as a marker",
            "marker_re='^(<<<<<<< |>>>>>>> |={7}$)'",
            "marker_re='^(<<<<<<< |>>>>>>> )'",
        ),
        (
            "M3 the exemption is fixtures/, not the whole controls directory",
            "':!scripts/tests/fixtures/*'",
            "':!scripts/tests/*'",
        ),
        (
            "M4 a duplicate ADR number fails the gate",
            "if ! adr_out=$(python3 scripts/gen-adr-index.py --check 2>&1); then",
            "if false; then",
        ),
        (
            "M5 the ADR checker's own output is reported",
            """printf '%s\\n' "$adr_out" | /usr/bin/grep -E 'ADR_INDEX' | sed 's/^/    /'""",
            "true",
        ),
        (
            "M6 a stale generated file fails the gate",
            "if ! plan_out=$(python3 scripts/gen-plan.py --check 2>&1); then",
            "if false; then",
        ),
        (
            "M7 a stale creal STEPS table fails the gate",
            "if ! creal_out=$(python3 scripts/creal-declare-deps.py "
            "--check --strict --self-check 2>&1); then",
            "if false; then",
        ),
        (
            "M8 a stale Python prelude field table fails the gate",
            'elif [ "$py_fields_rc" -ne 0 ]; then',
            "elif false; then",
        ),
        (
            "M9 exit 2 (no rustfmt) is SKIPPED, not a failure",
            'if [ "$py_fields_rc" -eq 2 ]; then',
            "if false; then",
        ),
        (
            # Lane `shape-census`: widening the exit-2 arm to swallow every
            # nonzero status must split the two census scenarios -- the stale
            # run must die, the unanswerable run must survive. (Was M7 on that
            # lane's branch; renumbered at merge, three lanes appended here.)
            "M10 a stale shape census fails the gate, and exit 2 does not",
            'elif [ "$census_rc" -eq 2 ]; then',
            'elif [ "$census_rc" -ne 0 ]; then',
        ),
        (
            "M11 a reported duplicate declaration group fails the gate",
            'elif [ "$shape_dupes_rc" -ne 0 ]; then',
            "elif false; then",
        ),
        (
            "M12 an absent/stale prebuilt index is SKIPPED, not a failure",
            'if [ "$shape_dupes_rc" -eq 2 ] && [ -n "$shape_dupes_marker" ]; then',
            'if [ "$shape_dupes_rc" -eq 99 ]; then',
        ),
        (
            "M13 exit 2 WITHOUT the UNAVAILABLE marker still blocks",
            '[ "$shape_dupes_rc" -eq 2 ] && [ -n "$shape_dupes_marker" ]',
            '[ "$shape_dupes_rc" -eq 2 ]',
        ),
        (
            "M14 the opt-out is honoured and reported",
            'if [ "${AXEYUM_SKIP_SHAPE_DUPLICATES:-0}" = "1" ]; then',
            "if false; then",
        ),
        (
            # ADR-1550 (lane `partition-edge-gate`). Split the same two ways
            # M10 is: the blocking arm and the not-answerable arm are separate
            # decisions, and the one that fails SILENTLY is the second.
            "M15 a new partition-crossing edge fails the gate",
            'elif [ "$part_edges_rc" -eq 2 ]; then',
            'elif [ "$part_edges_rc" -ne 0 ]; then',
        ),
        (
            "M16 an unanswerable partition-edge check does NOT fail the gate",
            'if [ "$part_edges_rc" -eq 0 ]; then',
            'if [ "$part_edges_rc" -ne 1 ]; then',
        ),
    ],
)


# --------------------------------------------------------------------------
# `partition-edges` -- `scripts/check-partition-edges.py`, the per-EDGE
# replacement for the component-level partition gate (ADR-1546 option 2,
# ADR-1550).
#
# This suite matters more than most, because the gate it supersedes for
# producer purposes is the one CLAUDE.md's rule was written about: it was kept
# green for four days by an exemption re-scoped 228 -> 230 -> 258 -> 274 to
# fit whatever it had just failed on. A replacement whose own guards were
# never driven to failure would be the same artifact with a newer date.
#
# EVERY MUTANT BELOW KILLS EXACTLY ONE TEST, and getting there changed the
# FIXTURES rather than the guards. M1 widens the "same partition" test to
# `False`, so every edge in the drawn population becomes a crossing; the first
# draft of the suite put a clean same-partition edge in nine fixtures and M1
# killed six of them. A mutant that kills six says less about the guard than
# one that kills the test whose subject it is, so only
# `one_crossing_and_one_clean` -- the fixture for the comparison itself --
# carries a clean edge now, and `one_crossing_only` serves the rest. Same for
# M4: the `new crossing blocks` scenario stopped asserting the baselined COUNT,
# because ignoring the baseline leaves that scenario's subject true and only
# the accept case is about the subtraction.
#
# M2 is the mutant this gate exists to make possible. `component_covered`
# holds every ordered pair a manifest's component exemption would suppress;
# the shipped line honours the per-edge amendments and nothing else, and M2
# unions the component pairs in. On the live tree that is not hypothetical:
# `component_exemptions_would_wave=154` of the 198 recorded crossings.
# --------------------------------------------------------------------------

SUITES["partition-edges"] = (
    "scripts/check-partition-edges.py",
    Unittest("scripts.tests.test_check_partition_edges"),
    [
        (
            "M1 an edge within one partition is not a crossing",
            "        if source == target:\n            return False",
            "        if source == target:\n            return True",
        ),
        (
            "M2 a component exemption is NOT honoured as an amendment",
            "    honoured = amendments\n",
            "    honoured = amendments | component_covered\n",
        ),
        (
            "M3 an amendment must name from/to/reason/date",
            'missing = [k for k in ("from", "to", "reason", "date")',
            "missing = [k for k in ()",
        ),
        (
            "M4 an edge already in the baseline is not a new violation",
            "    violations = [e for e in edges if edge_key(e) not in honoured\n"
            "                  and redacted_key(e, baseline_salt) not in baseline]",
            "    violations = [e for e in edges if edge_key(e) not in honoured\n"
            "                  and True]",
        ),
        (
            "M5 --record-baseline refuses to grow the baseline",
            "        if grew:",
            "        if False:",
        ),
        (
            "M6 no nursery manifest is UNANSWERABLE, not clean",
            "    if not manifests:",
            "    if False:",
        ),
        (
            "M7 --baseline without a baseline file says WHY it cannot answer",
            "    if not path.is_file():\n"
            "        raise Unanswerable(",
            "    if False:\n"
            "        raise Unanswerable(",
        ),
        (
            "M8 a fact drawn into two partitions is UNANSWERABLE",
            "            if fact_id in partition_of and partition_of[fact_id] != partition:",
            "            if False:",
        ),
        (
            "M9 the declined component exemptions are REPORTED, not merely unused",
            "    if violations or args.verbose:",
            "    if False:",
        ),
        (
            "M10 a repaired baseline edge is reported so the gain is locked in",
            "        repaired = sorted(baseline - {redacted_key(e, baseline_salt)\n"
            "                                      for e in edges})",
            "        repaired = []",
        ),
        (
            "M12 an amendment CLASS is re-derived from the live manifests",
            '        if target_partition != "longitudinal":',
            "        if False:",
        ),
        (
            "M13 an unrecognised class kills the amendment",
            "    if declared not in AMENDMENT_CLASSES:",
            "    if False:",
        ),
        (
            "M14 --record-baseline excludes the honoured amendments",
            "        return record(root, [e for e in edges if edge_key(e) not in amendments],\n"
            "                      manifests, partition_of, dependencies, previous)",
            "        return record(root, edges,\n"
            "                      manifests, partition_of, dependencies, previous)",
        ),
        # ADR-1564. The partition ROLES are read from the policy, and the
        # crossing rule is no longer "the endpoints differ". M17 restores the
        # old rule and must kill exactly one test -- which it can only do
        # because every OTHER scenario in the suite runs under the
        # PREREGISTERED policy (train evaluated) on purpose. A suite whose
        # fixtures all used the shipped roles could not tell "read from the
        # policy" from "the literal happens to have been updated".
        #
        # M19/M20's tests assert the MESSAGE, not just exit 2: four inputs
        # here are exit 2, and with M19 applied the empty-evaluation policy
        # still exits 2 through the blind check, so an exit-code-only test
        # would have survived it.
        (
            "M17 a training/evaluation pair is not a crossing",
            "        return peer not in self.evaluation\n",
            "        return True\n",
        ),
        (
            "M18 a BLIND partition is sealed in both directions",
            "        if peer in self.blind:\n",
            "        if False:\n",
        ),
        (
            "M19 a policy naming no evaluation partition is unanswerable",
            "    if not evaluation:\n        raise Unanswerable(",
            "    if False:\n        raise Unanswerable(",
        ),
        (
            "M20 blind_partitions may not be empty",
            "    if not blind or blind - evaluation:",
            "    if False:",
        ),
        (
            "M21 training and evaluation are disjoint roles",
            "    if training & evaluation:",
            "    if False:",
        ),
        (
            "M22 a manifest carrying no policy at all is unanswerable",
            "    if not found:\n        raise Unanswerable(",
            "    if False:\n        raise Unanswerable(",
        ),
        (
            "M23 two manifests disagreeing about the roles is unanswerable",
            "    if len(set(roles)) != 1:",
            "    if False:",
        ),
        (
            "M11 a held-out endpoint is redacted before it is written to the "
            "baseline",
            '    frm = (digest_fact_id(edge["from"], salt)\n'
            '           if salt and edge["from_partition"] == "held-out" else edge["from"])\n'
            '    to = (digest_fact_id(edge["to"], salt)\n'
            '          if salt and edge["to_partition"] == "held-out" else edge["to"])',
            '    frm = edge["from"]\n'
            '    to = edge["to"]',
        ),
    ],
)


# --------------------------------------------------------------------------
# `creal-migrate-consumers` -- the workspace-wide consumer scan in
# `scripts/creal-migrate-registry.py`.
#
# The scan answers "would this move break something the rewriter cannot see?",
# and it exists because the answer was YES and nobody asked:
# `crates/axeyum-py/src/kernel/prelude_fields.rs` is generated, lives outside
# the kernel crate, names every `CRealPrelude` field, and the first migration
# batch left it addressing fields that had moved. Main stopped compiling.
#
# C1 is the refusal itself and kills four scenarios, because four scenarios
# reach the exit through one `sys.exit`. The rest are one apiece, and the two
# that matter most are the NEGATIVE controls (C2, C7): a scan that refused
# unconditionally would satisfy the refusal test and teach every lane to pass
# `--allow-external`. Kill sets are reported as measured.
# --------------------------------------------------------------------------

SUITES["creal-migrate-consumers"] = (
    "scripts/creal-migrate-registry.py",
    Unittest("scripts.tests.test_creal_migrate_registry"),
    [
        (
            "C1 an external consumer refuses the migration",
            "    sys.exit(1)",
            "    return",
        ),
        (
            "C2 files the rewriter WILL fix are not findings",
            "        if path in skip or not path.is_file():",
            "        if not path.is_file():",
        ),
        (
            "C3 an accessor in a COMMENT is not a finding",
            "        for m in accessor.finditer(cdd.strip_noise(raw)):",
            "        for m in accessor.finditer(raw):",
        ),
        (
            "C4 a rustdoc `CRealPrelude::<field>` link IS a finding",
            "        for m in doclink.finditer(raw):",
            "        for m in doclink.finditer(\"\"):",
        ),
        (
            "C5 --allow-external proceeds instead of refusing",
            "    if allow:",
            "    if False:",
        ),
        (
            "C6 a generated consumer is labelled GENERATED",
            '        kind = "GENERATED" if is_generated(path) else "hand-written"',
            '        kind = "hand-written"',
        ),
        (
            "C7 a clean tree is NOT refused (the vacuity control)",
            "    if not findings:",
            "    if False:",
            # NOT `fail=1 -> fail=0`: that would also weaken the aggregate
            # scenario, so the mutant would kill two tests and prove nothing
            # about this guard specifically. Widening the exit-2 arm to swallow
            # EVERY nonzero status is the mutation that separates the two
            # census scenarios -- the stale run must die, the unanswerable run
            # must survive.
            "M7 a stale shape census fails the gate, and exit 2 does not",
            'elif [ "$census_rc" -eq 2 ]; then',
            'elif [ "$census_rc" -ne 0 ]; then',
        ),
    ],
)


# --------------------------------------------------------------------------
# `shell-antipatterns-scope` -- the SCAN SET of `check-shell-antipatterns.sh`.
#
# The 2026-08-30 session audit's fifth survivor. The gate's DETECTOR was
# verified in both directions by `scripts/tests/test-check-shell-antipatterns.sh`
# and is not re-tested here; what had no control at all was the gate's SCOPE.
# `git ls-files '*.sh'` never reached `hooks/pre-push` or `hooks/commit-msg`,
# and both violated -- including the nonzero-test-count guard this repository
# leans on hardest.
#
# Scope is the thing that reverts silently: narrowing the enumeration back to
# `*.sh` leaves every number in the summary line unchanged and every detector
# control green. So the first mutation is exactly that revert.
#
# Kill sets are reported as measured, survivors included.
# --------------------------------------------------------------------------

SUITES["shell-antipatterns-scope"] = (
    "scripts/check-shell-antipatterns.sh",
    Unittest("scripts.tests.test_check_shell_antipatterns_scope"),
    [
        (
            "S1 the scan set is derived, not the `*.sh` glob",
            'git ls-files -s | python3 -c',
            "git ls-files -s -- '*.sh' | python3 -c",
        ),
        (
            "S2 an executable file with a shell shebang is scanned",
            'if not head.startswith(b"100755 "):',
            "if True:",
        ),
        (
            "S2b a NON-executable file is not probed at all",
            'if not head.startswith(b"100755 "):',
            "if False:",
        ),
        (
            "S2c the first line must be a shell shebang",
            '    if SHEBANG.match(first.rstrip(b"\\r\\n") + b"\\n") or SHEBANG.match(first):',
            "    if True:",
        ),
        (
            "S3 `*.sh` files are scanned whatever their mode",
            'if path.endswith(".sh"):',
            "if False:",
        ),
        (
            "S4 a collapsed scan set is refused",
            'if [ "$scan_count" -lt "$MIN_SCAN" ]; then',
            "if false; then",
        ),
        (
            "S5 a required file absent from the scan set is refused",
            'if [ "$(grep -cxF "$required" "$scanned")" -eq 0 ]; then',
            "if false; then",
        ),
    ],
)


# --------------------------------------------------------------------------
# `aggregate-scope-failure` -- the FAILURE PATH of `check-aggregate-scope.sh`.
#
# The 2026-08-30 session audit's second survivor. Replacing
# `if [ -s "$new" ]; then` with `if false; then` left the whole registered
# suite green: all five registered controls test the NORMALIZER and none
# tested the gate's own decision to fail.
#
# `scripts/tests/test-check-aggregate-scope.sh` keeps the normalizer job.
# These scenarios drive the gate end to end on a synthetic tree via
# `AXEYUM_AGGREGATE_SCOPE_ROOT` -- hermetic, because the real tree costs
# 412 + 468 steps to enumerate and because the zero-side refusal cannot be
# reached on it at all.
#
# A1 is the survivor itself. A5 is the live normalizer bug fixed in the same
# change: `strip_wrappers` tested for a leading assignment with a quote-aware
# regex and stripped it with `line.split(" ", 1)`, which cuts inside the quotes.
#
# Kill sets are reported as measured, survivors included.
# --------------------------------------------------------------------------

SUITES["aggregate-scope-failure"] = (
    "scripts/check-aggregate-scope.sh",
    Unittest("scripts.tests.test_check_aggregate_scope"),
    [
        (
            "A1 an unrecorded divergence fails the gate",
            'if [ -s "$new" ]; then',
            "if false; then",
        ),
        (
            "A2 a side enumerating ZERO steps is refused with exit 2",
            'if [ "$sh_count" -eq 0 ] || [ "$just_count" -eq 0 ]; then',
            "if false; then",
        ),
        (
            "A3 a missing expectation file is refused",
            'if [ ! -f "$expected_file" ]; then',
            "if false; then",
        ),
        (
            "A4 the just-only arm of the comparison is compared at all",
            '  comm -13 "$sh_steps" "$just_steps" | sed \'s/^/just-only:     /\'',
            "  true",
        ),
        (
            "A5 a QUOTED environment assignment is stripped whole",
            '        assignment = re.match(r"^[A-Za-z_][A-Za-z0-9_]*=(\\"[^\\"]*\\"|\\S+)\\s+", line)',
            '        assignment = re.match(r"^[A-Za-z_][A-Za-z0-9_]*=\\S+\\s+", line)',
        ),
        (
            "A6 the strip consumes exactly what the regex matched",
            "        line = line[assignment.end():].strip()",
            '        line = line.split(" ", 1)[1].strip()',
        ),
    ],
)

def main(argv: list[str]) -> int:
    if argv[1:2] == ["--check-anchors"]:
        return check_anchors()
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


# --------------------------------------------------------------------------
# holdout-adjacency (ADR-0763): ADR-0653's adjacency rule, as R11.
#
# The defect is the one this whole harness exists for, one arrow upstream.
# `guard()` carried ten rules and R9, the blindness screen, compares a
# candidate's Mathlib NAME against the kernel environment. ADR-0762 measured
# that a draw putting `Init.Data.Nat.Bitwise.Lemmas` and
# `Mathlib.Data.Nat.GCD.Basic` into HELD-OUT -- beside `natural-bitwise` and
# `natural-gcd`, both development -- is R9-clean 0/10 on each and returns
# `GUARD PASSED`. So a lane could author the ADR-0542 breach on purpose and
# see green.
#
# Two of the mutations below are aimed at the OPPOSITE failure, because it is
# the live risk: three consecutive draws have been declined, and a screen that
# refuses everything is indistinguishable from a broken flywheel. Dropping the
# library-root rule, the syntax filter or the plumbing rule each makes the
# screen refuse more, and each kills a false-positive control rather than a
# refusal test.
# --------------------------------------------------------------------------

SUITES["holdout-adjacency"] = (
    "scripts/check-holdout-adjacency.py",
    Unittest("scripts.tests.test_check_holdout_adjacency"),
    [
        (
            "the topic signal -- a shared module topic segment",
            "    if topic_hits:\n",
            "    if False:\n",
        ),
        (
            "the vocabulary signal -- rows about a published subject",
            "    if hit_rows > allowance:\n",
            "    if False:\n",
        ),
        (
            "the vocabulary allowance is a STRICT threshold",
            "    if hit_rows > allowance:\n",
            "    if hit_rows >= allowance:\n",
        ),
        (
            "a family may not be scored against itself",
            "    if family in published_rows:\n",
            "    if False:\n",
        ),
        (
            "a recorded review must still describe the environment",
            "        if recorded != env_hits:\n",
            "        if False:\n",
        ),
        (
            "a new held-out family with a non-empty sweep needs a review",
            "    elif require_disclosure and env_hits:\n",
            "    elif False:\n",
        ),
        (
            "the review DEMAND is scoped to draw time",
            "    elif require_disclosure and env_hits:\n",
            "    elif env_hits:\n",
        ),
        (
            "an acceptance that no longer matches the measurement",
            "    if accepted is not None and accepted.get(\"vocabulary_rows\") "
            "not in (None, hit_rows):\n",
            "    if False:\n",
        ),
        (
            "syntax is not mathematics",
            "    return any(p.search(constant) for p in SYNTAX_PATTERNS)\n",
            "    return False\n",
        ),
        (
            "a constant characteristic of many families is plumbing",
            "    return {c for c, k in seen.items() if k > ambient_families}\n",
            "    return set()\n",
        ),
        (
            "the leading module component is the library, not a topic",
            '    segments = module.split(".")[1:]\n',
            '    segments = module.split(".")\n',
        ),
        (
            "the environment sweep is deterministic over an unordered set",
            "    lowered = sorted((name, name.lower()) for name in env)\n",
            "    lowered = sorted(((name, name.lower()) for name in env), "
            "reverse=True)\n",
        ),
        (
            "a manifest contributing zero rows is an error, not a clean screen",
            '    if not counts["v1"] or not counts["extension"]:\n',
            "    if False:\n",
        ),
        (
            "an unreadable review file is not 'nothing to disclose'",
            "    if not isinstance(reviews, dict):\n",
            "    if False:\n",
        ),
        (
            "a same-draw development family counts as published",
            '        if new_partition.get(fam) in ("development", "train"):\n',
            "        if False:\n",
        ),
        (
            "only held-out families are screened",
            '        if new_partition.get(fam) != "held-out":\n',
            "        if False:\n",
        ),
        # ADR-1450. A `do-not-draw-held-out` row in the review file BINDS, and
        # until this landed nothing read `refused` at all: `screen_family`
        # looks up `reviews[family]`, so a refusal recorded under a MODULE name
        # was unreachable by every lookup the guard performed. Measured --
        # ADR-1100/ADR-1115 recorded `Mathlib.Data.Nat.Count` as
        # do-not-draw-held-out because our `Nat.countRange` already proves
        # several of its rows under other names; ADR-1430 then declared
        # `Nat.count` to open exactly that module for a held-out draw, and
        # every screen stayed green. Two of the four below aim at the OPPOSITE
        # failure, which is the live risk once a bar exists: a bar that applies
        # to development/train families would delete a 22-row dispatchable pool
        # for an argument that is only about blindness.
        (
            "a recorded do-not-draw-held-out verdict bars the draw",
            "    if blocked:\n        raise RefusalError(\n",
            "    if False:\n        raise RefusalError(\n",
        ),
        (
            "the recorded-refusal bar is scoped to held-out families",
            '                         if new_partition.get(f) == "held-out"]\n',
            "                         if True]\n",
        ),
        (
            "only a do-not-draw-held-out verdict bars, not any recorded note",
            '        if entry.get("verdict") != "do-not-draw-held-out":\n',
            "        if False:\n",
        ),
        (
            "an unreadable `refused` list is not 'nothing has been refused'",
            "    if not isinstance(refused, list):\n",
            "    if False:\n",
        ),
    ],
)


# --------------------------------------------------------------------------
# nursery-refill-adjacency (ADR-0763): R11's CALL SITE, not the screen.
#
# Deleting the call leaves every test in the suite above green: the screen
# stays correct and never runs. That is exactly the state ADR-0762 found the
# repository in, with the rule written down and nothing invoking it, so the
# call site needs its own control.
# --------------------------------------------------------------------------

SUITES["nursery-refill-adjacency"] = (
    "scripts/gen-autogenesis-nursery-refill.py",
    Unittest("scripts.tests.test_check_holdout_adjacency"),
    [
        (
            "R11 runs at all",
            "        _adjacency_screen(new_entries, env)\n",
            "        pass\n",
        ),
        (
            "a failure to LOAD the screen is a refusal, not a skip",
            '        raise RefillError(\n'
            '            "R11 the adjacency screen '
            '(scripts/check-holdout-adjacency.py) "\n',
            "        return  # noqa\n"
            '        raise RefillError(\n'
            '            "R11 the adjacency screen '
            '(scripts/check-holdout-adjacency.py) "\n',
        ),
    ],
)


# --------------------------------------------------------------------------
# declaration-spec (L3 phase D1, ADR-0965): the four pre-construction guards
# gen-declaration-spec.py runs over a declaration-spec file BEFORE any kernel
# construction is attempted, plus the dependency-consistency and
# empty-corpus checks added alongside them. Each mutation disables exactly
# one guard's reporting (not its surrounding control flow, which several
# guards share), so a mutation that "succeeds" here means one specific
# adversarial fixture (artifacts/declaration-spec/negative-fixtures/*.json)
# would silently validate.
# --------------------------------------------------------------------------

SUITES["declaration-spec"] = (
    "scripts/gen-declaration-spec.py",
    "scripts.tests.test_declaration_spec",
    [
        (
            "in-corpus duplicate name guard",
            "        violations.extend(check_in_corpus_duplicates(specs))\n",
            "        pass\n",
        ),
        (
            "cross-prelude duplicate name guard",
            "            violations.extend(check_cross_prelude_duplicates(specs, args.snapshot))\n",
            "            pass\n",
        ),
        (
            "dependency cycle guard",
            "        violations.extend(check_dependency_cycles(specs))\n",
            "        pass\n",
        ),
        (
            "phase order guard",
            "        violations.extend(check_phase_order(specs))\n",
            "        pass\n",
        ),
        (
            "dependency/const_ref consistency guard",
            "        violations.extend(check_dependency_consistency(specs))\n",
            "        pass\n",
        ),
        (
            "missing-phase guard (the reporting line, not the `if`, which a "
            "downstream KeyError would otherwise turn into a build failure "
            "rather than a silent pass)",
            '            violations.append(Violation("MISSING_PHASE", f"{where}: no \'phase\' field"))\n',
            "            pass\n",
        ),
        (
            "empty-corpus guard (zero spec files found)",
            '        print("GUARD:EMPTY_CORPUS no spec files found -- nothing was checked", file=sys.stderr)\n',
            '        print("GUARD:MUTATED this text deliberately omits the phrase this test checks for", file=sys.stderr)\n',
        ),
    ],
)

SUITES["l0-gate-enforcement"] = (
    "scripts/check-l0-gate-enforcement.py",
    "scripts.tests.test_l0_gate_enforcement",
    [
        # Measured 2026-08-31: all seven L0 safety gates ran in NO automated
        # context -- 0 references in ci.yml, hooks/pre-push and local-ci.sh
        # against positive controls of 44, 28 and 10 `scripts/` references in
        # those same files. Each guard below must be killed by exactly the one
        # test that names it; the acceptance test
        # (`test_committed_tree_passes`) is what kills a guard rewritten so it
        # can never fire, and must keep passing for every mutation here.
        (
            "a gate absent from CI is refused",
            "        if not hits:                                              # GUARD:G1",
            "        if False:",
        ),
        (
            "an L0 step with continue-on-error is refused",
            "            if coe:                                               # GUARD:G2",
            "            if False:",
        ),
        (
            "an L0 command spelled `|| true` is refused",
            "            if SWALLOW.search(block):                             # GUARD:G3",
            "            if False:",
        ),
        (
            "a cheap gate absent from pre-push is refused",
            "        if gate not in code:                                      # GUARD:G4",
            "        if False:",
        ),
        # G5 is the finding this lane exists for: below the Rust/TOML early
        # exit, a push touching only artifacts/ or docs/ -- exactly what these
        # gates protect -- is gated by nothing.
        (
            "an L0 block below the pre-push early exit is refused",
            "        if last > exit_at:                                        # GUARD:G5",
            "        if False:",
        ),
        (
            "a pre-push block with no failure branch is refused",
            "    if SWALLOW.search(prepush_text) or \"L0 gate rejected this push\" not in prepush_text:",
            "    if False:",
        ),
        # G7/G8 close the third context this lane's own task named:
        # scripts/local-ci.sh -- ci.yml calls it "the authoritative gate for
        # main" and it ran none of the seven either, until this lane wired
        # them in with the file's own `run <cmd> || rc=$?` idiom.
        (
            "a gate absent from local-ci.sh is refused",
            "        if not gate_lines:                                        # GUARD:G7",
            "        if False:",
        ),
        (
            "a local-ci.sh gate call missing `|| rc=$?` is refused",
            "        if not any(RC_CAPTURE.search(ln) for ln in gate_lines):    # GUARD:G8",
            "        if False:",
        ),
    ],
)

SUITES["curriculum-bucket-cohesion"] = (
    "scripts/measure-curriculum-kernel-coverage.py",
    "scripts.tests.test_curriculum_bucket_cohesion",
    [
        # ADR-1215. The curriculum classifier attributes by NAME against an
        # ordered pattern table whose tail entries are catch-alls, so a
        # declaration attributed to the WRONG bucket is attributed, counted,
        # and invisible -- twice in two days (ADR-1140 `det2|det3`, ADR-1205
        # `gauss_fold_injective`). Each mutation below removes one of the
        # three guards or one of the two input refusals; the suite's two
        # RED cases replay the historical pattern tables against a slice of
        # the real projection, and its control asserts the SHIPPED table is
        # green on the same slice -- so a guard that fired on everything
        # would not pass.
        (
            "G1: an unpinned split bucket set is refused",
            "            if splits.get(key) != nodes:",
            "            if False:",
        ),
        (
            "G2: an unpinned pure-catch-all family is refused",
            "                if families.get(key) != node:",
            "                if False:",
        ),
        (
            "G3: a stale split pin is refused",
            "    for key in sorted(set(splits) - seen_split):",
            "    for key in sorted(set() - seen_split):",
        ),
        (
            "G3: a stale family pin is refused",
            "    for key in sorted(set(families) - seen_family):",
            "    for key in sorted(set() - seen_family):",
        ),
        # The floor is what keeps G2 from reddening on ordinary new work. A
        # floor of 1 turns every single-declaration family in a carrier
        # bucket into a finding, which is the design the brief for this lane
        # ruled out ("disabled within a week").
        (
            "the family floor bounds G2's false positives",
            "FAMILY_FLOOR = 8",
            "FAMILY_FLOOR = 1",
        ),
        # `det2`, `det3` and `det` must be ONE family or ADR-1140's exact
        # shape -- a pattern naming the numbered instances while the general
        # construction grows past them -- never produces a split at all.
        (
            "trailing digits are stripped from a name stem",
            '    return carrier, (stem.rstrip("0123456789") or stem)',
            "    return carrier, stem",
        ),
        # `Nat.gaussFold` and `Nat.gauss_neg_count_succ` must be ONE family:
        # this kernel spells a single mathematical family both ways, and a
        # guard keyed on the raw spelling sees two families and compares
        # neither.
        (
            "camelCase folds into the same stem as snake_case",
            "    words = _STEM_WORDS.findall(first)",
            "    words = [first]",
        ),
        # A short projection makes a newly-landed family look like it was
        # always in the catch-all -- the failure these guards exist to catch,
        # arriving through the INPUT rather than the table.
        (
            "a stale or truncated projection is refused",
            "PROJECTION_FLOOR = 2500",
            "PROJECTION_FLOOR = 0",
        ),
        # A missing pin file reads as an EMPTY pin, which is right for a
        # hand run and catastrophic for the gate: every guard would examine
        # nothing and exit 0.
        (
            "--require-pin refuses a missing pin file",
            "    if args.require_pin and not os.path.isfile(args.cohesion_pin):",
            "    if False:",
        ),
    ],
)


# --------------------------------------------------------------------------
# `prelude-inventory-ownership` -- the gate that reads a prelude's inventory
# from the AUTHORITY rather than from a namespace prefix.
#
# Every "every X is checked and axiom-free" test in the kernel was fixed once
# already (the `creal` array that found twelve unchecked declarations), and each
# fix filters `kernel.environment()` by a NAMESPACE PREFIX that is itself a
# hand-written literal. Measured 2026-08-31, 27 introduced declarations sit
# outside their introducing prelude's filter and seven are reached by no
# completeness guard at all.
#
# The mutations below each remove one guard of the replacement gate. The suite
# they run is the cheap control module (`logic` + `nat` only, ~5 s); the gate
# itself builds ten preludes and takes ~180 s, which no mutation loop can pay.
# --------------------------------------------------------------------------

SUITES["prelude-inventory-ownership"] = (
    "crates/axeyum-lean-kernel/src/cross_prelude_collision_tests.rs",
    Cargo(
        (
            "-p",
            "axeyum-lean-kernel",
            "--lib",
            "cross_prelude_collision_tests::inventory_control",
        ),
        "prelude-inventory-ownership",
    ),
    [
        # A declaration admitted with NO checked proof body, introduced by a
        # prelude `ASSUMED_BY` does not license. Every prelude but `axreal`
        # measures zero and that is the headline claim.
        (
            "an unlicensed prelude introducing an axiom is reported",
            "                    if allowed == 0 {",
            "                    if false {",
        ),
        # Exact in both directions: an axiom LEAVING `axreal` changes the
        # trusted base as much as one arriving, and `>=` would not see it.
        (
            "the licensed trusted count is exact, not a ceiling",
            "        if trusted != allowed {",
            "        if false {",
        ),
        # A proof reaching something assumed.
        (
            "a declaration resting on an axiom is reported",
            "                        && !footprint.is_empty()",
            "                        && false",
        ),
        # The footprints are computed only when the environment carries
        # something trusted -- emptiness follows by construction otherwise.
        # Switching that off makes the guard above unreachable, which is a
        # DIFFERENT way for the same finding to disappear.
        (
            "footprints are measured once anything is assumed",
            "        let footprints = if any_trusted {",
            "        let footprints = if false {",
        ),
        # The record that licenses skipping those footprints. If a prelude
        # holding an axiom were still recorded as carrying nothing trusted,
        # the by-construction argument would be applied where it is false.
        (
            "an environment carrying nothing trusted is recorded as such",
            "        if !group.any_trusted() {",
            "        if false {",
        ),
        # Exhaustiveness of the ownership partition. A declaration in some
        # prelude's environment that no prelude on its dependency chain
        # introduces was inspected under no owner, while the gate's `checked`
        # count stayed large and reassuring.
        (
            "a declaration owned by no prelude is reported",
            "                        report.unattributed.push(format!(\"{label}: {name}\"));",
            "                        let _ = format!(\"{label}: {name}\");",
        ),
        (
            "a declaration owned by two preludes on one chain is reported",
            "                _ => report\n                    .doubly_attributed\n"
            "                    .push(format!(\"{label}: {name} introduced by {owners:?}\")),",
            "                _ => {\n                    let _ = &owners;\n                }",
        ),
    ],
)

# --------------------------------------------------------------------------
# spivak-cas-column (ADR-1300): the Spivak spine table must state a CAS
# (ADR-0603 row 3) verdict on every row.
#
# The defect this gate exists to prevent already happened. `spivak.md`'s legend
# read "Three routes, not two: S / K / X", the string `axeyum-cas` appeared once
# in the whole file, and chapter 20 read `| 20 | Taylor polynomials | - | open |`
# while `crates/axeyum-cas/src/taylor.rs` shipped Taylor's theorem with the
# Lagrange remainder, naming ADR-0603 row 3 and Spivak ch. 20 in its own module
# doc. Chapter 19 had no row at all. The wrong answer was then reported to the
# user from that column.
#
# The guards are split so that each fails on something the others cannot see --
# a blank cell (R3), an unexplained "none" (R4), an assertion with no citation
# (R5), a missing chapter (R6), a dangling fact id (R7), a dropped pipe (R2), a
# stale legend (R8), and an absent table that would make every per-row guard
# iterate over nothing (R1). CLAUDE.md records a suite where six of seven guards
# were removable with everything green because all seven rejected through one
# shared check; that is the shape being avoided here.
# --------------------------------------------------------------------------

SUITES["spivak-cas-column"] = (
    "scripts/check-spivak-cas-column.py",
    Unittest("scripts.tests.test_check_spivak_cas_column"),
    [
        (
            "R1 an absent table is not a vacuous pass",
            '        fail(errors, f"{doc}: no spine table found '
            '(no line starting {HEADER_START!r})")',
            "        return errors",
        ),
        (
            "R2 a row whose cell count does not match the header",
            "        if len(cells) != len(header):",
            "        if False:",
        ),
        (
            "R3 an empty or dashed C cell (the original defect)",
            '        if not bare or bare in {"-", "—", "–", "?", "TBD", "UNAUDITED"}:',
            "        if False:",
        ),
        (
            "R4 audited-none carrying no reason",
            "            if len(reason) < MIN_REASON_CHARS:",
            "            if False:",
        ),
        (
            "R5 a C cell asserting a route and citing nothing",
            "        elif not names_artifact:",
            "        elif False:",
        ),
        (
            "R7 a C cell citing a non-cas-certificate fact id",
            "            if fid not in cas_ids:",
            "            if False:",
        ),
        (
            "R6 a Spivak chapter with no row",
            "    missing = sorted(set(range(1, 31)) - seen_chapters)",
            "    missing = []",
        ),
        (
            "R8 the legend still advertising three routes",
            '    if re.search(r"Three routes, not two", text):',
            "    if False:",
        ),
    ],
)

# `header-settled-fact-statements` rewrites the `formal.statement` of SETTLED
# facts -- the field `check-settled-fact-statements.py` exists to keep from
# moving quietly. What makes that safe is not the rewrite; it is the four
# refusals, each declining a case the tool cannot prove is a pure prefix. So the
# mutations below delete refusals, not the happy path: a suite exercising only
# the fix would let every refusal be removed while staying green, and the tool
# would then head a statement it had no authority to head.
#
# Note why each refusal test asserts the REASON. Deleting the ABSENT guard alone
# leaves the same fact refused as DIVERGENT (an empty candidate set contains no
# statement), so a test checking only "the statement did not change" cannot tell
# the two guards apart and one deletion would kill zero tests.
# --------------------------------------------------------------------------

SUITES["header-settled-fact-statements"] = (
    "scripts/header-settled-fact-statements.py",
    Unittest("scripts.tests.test_header_settled_fact_statements"),
    [
        # A name absent from the projection is a proof-isolated import with no
        # persistent declaration. Heading it fabricates a rendering.
        (
            "a declaration absent from the projection is refused",
            '        if not found:\n            refused.append((data["id"], name, "ABSENT"))\n'
            "            continue",
            '        if not found:\n            found = {("theorem", statement)}',
        ),
        # The byte-identity against `canonical_type` is the ENTIRE argument that
        # the prefix preserves the proposition. Without it the tool heads a
        # hand-written paraphrase as though it were the kernel's own rendering.
        (
            "a statement that is not the declaration's rendering is refused",
            '        if statement not in canonicals:\n'
            '            refused.append((data["id"], name, "DIVERGENT"))\n            continue',
            "        if False:\n            pass",
        ),
        # Two renderings of one name means the tool cannot know which
        # proposition the fact is about.
        (
            "one name rendering to two types is refused",
            "        if len(canonicals) > 1:\n"
            '            refused.append((data["id"], name, "AMBIGUOUS"))\n            continue',
            "        if False:\n            pass",
        ),
        # `theorem` is not a safe default: a definition headed `theorem` claims
        # a proof exists where there is only a body.
        (
            "a kind with no header keyword is refused",
            "        if len(keywords) != 1:\n"
            '            refused.append((data["id"], name, "UNKNOWN-KIND"))\n            continue',
            '        if len(keywords) != 1:\n            keywords = {"theorem"}',
        ),
        # The keyword must track the kind, or every `def` lands headed
        # `theorem` and the ledger reads as carrying proofs it does not.
        (
            "the header keyword follows the declaration kind",
            "        keyword = keywords.pop()",
            '        keyword = "theorem"',
        ),
        # `--check`'s exit status must depend on the finding. This repository
        # has shipped checkers that exit 0 on completion alone.
        (
            "--check exits nonzero on a finding",
            "    if fixable:\n        print(",
            "    if False:\n        print(",
        ),
        # An amendment is what `check-settled-fact-statements.py` requires
        # before a changed pin may be rewritten. Without one the next `--write`
        # refuses -- or, if the refusal were ever relaxed, launders the change.
        (
            "an applied fix records an amendment",
            "        amendments.append(",
            "        [].append(",
        ),
        # Re-running must not record one act twice. The ledger's amendment list
        # is a history, and a duplicated row misreports how often a claim moved.
        (
            "a re-run does not duplicate an amendment",
            '        if row["fact_id"] in already:\n            continue',
            "        if False:\n            continue",
        ),
        # A tool whose authority is empty must error, not report PASS. An empty
        # projection would otherwise make every fact read as ABSENT and the run
        # as clean.
        (
            "an empty projection is an error, not a quiet pass",
            "    if not decls:\n        raise HeaderError(",
            "    if False:\n        raise HeaderError(",
        ),
    ],
)

# `constant-canonicity` -- one canonical definition per mathematical object.
#
# The registry this gate reads is a DECLARATIVE adjudication, because
# `CReal.Equiv` is undecidable and no tool can answer "is this constructed
# real the same real as that one". A declarative registry is exactly the
# shape this repository has been burned by: a list maintained by hand
# measures the maintainer's memory. What keeps it honest is that the
# POPULATION is derived from the kernel and every guard below is removable
# in one edit -- so each one has to be shown to kill a test.
#
# Note why the failure tests assert `evaluate()` rather than `main()`'s exit
# status. If they all went through `main()`, the single mutation
# `return 1` -> `return 0` would kill eleven tests at once, and a control
# that kills eleven tests measures nothing about the eleven guards it was
# supposed to distinguish. `MainExitStatusTests` is the one place the status
# is asserted, so that mutation kills exactly one test -- and that mutation
# is the most important one here, because a checker that exits 0 on
# completion alone is the defect this file exists to prevent.
# --------------------------------------------------------------------------

SUITES["constant-canonicity"] = (
    "scripts/check-constant-canonicity.py",
    Unittest("scripts.tests.test_check_constant_canonicity"),
    [
        # G1 is the guard with no evasion: a constant the kernel declares and
        # the registry does not mention. Every other guard here constrains how
        # an adjudication may be written; this one forces there to BE one.
        (
            "G1 a kernel constant with no registry row",
            '            findings.append(\n                f"G1 UNADJUDICATED',
            '            [].append(\n                f"G1 UNADJUDICATED',
        ),
        # Without the stale half the registry silently accumulates rows for
        # constants that were renamed or removed, and "this is adjudicated"
        # reads as still-considered when it is not.
        (
            "G2 a row naming a constant the kernel no longer declares",
            '            findings.append(\n                f"G2 STALE',
            '            [].append(\n                f"G2 STALE',
        ),
        (
            "G3 a row whose carrier is not the kernel's type",
            '            findings.append(\n                f"G3 CARRIER-MISMATCH',
            '            [].append(\n                f"G3 CARRIER-MISMATCH',
        ),
        # Two canonical constants for one object IS the twenty-pi outcome,
        # written down. Without this guard the registry records it and passes.
        (
            "G4 two canonical constants for one mathematical object",
            '            findings.append(\n                f"G4 AMBIGUOUS',
            '            [].append(\n                f"G4 AMBIGUOUS',
        ),
        (
            "G5 an alternate whose object has no canonical constant",
            '            findings.append(\n                f"G5 ORPHAN-ALTERNATE',
            '            [].append(\n                f"G5 ORPHAN-ALTERNATE',
        ),
        # An alternate with no bridge is a second definition wearing a label.
        (
            "G6 an alternate naming no bridge theorem",
            '            findings.append(\n                f"G6 MISSING-BRIDGE',
            '            [].append(\n                f"G6 MISSING-BRIDGE',
        ),
        (
            "G7 a bridge that is not a theorem in the environment",
            '            findings.append(\n                f"G7 ABSENT-BRIDGE',
            '            [].append(\n                f"G7 ABSENT-BRIDGE',
        ),
        # G8 is what stops the registry being self-certifying: without it any
        # real theorem name satisfies an alternate row, and the "bridge" column
        # becomes a field nobody reads.
        (
            "G8 a bridge whose stated type relates neither constant",
            '            findings.append(\n                f"G8 VACUOUS-BRIDGE',
            '            [].append(\n                f"G8 VACUOUS-BRIDGE',
        ),
        (
            "G9 a row carrying no reason",
            '            findings.append(\n                f"G9 NO-REASON',
            '            [].append(\n                f"G9 NO-REASON',
        ),
        # G10 is the heuristic that fires on `CReal.pi` + `CReal.piMachin`
        # without anyone having anticipated the pair.
        (
            "G10 prefix-matching names registered as different objects",
            '                findings.append(\n                    f"G10 NAME-COLLISION',
            '                [].append(\n                    f"G10 NAME-COLLISION',
        ),
        # The escape hatch must stay an escape hatch. Removing it makes G10
        # unappealable, which is how a gate gets deleted rather than obeyed.
        (
            "G10's explicit distinct-from claim is honoured",
            "                if token in other.reason or "
            'f"distinct-from:{other.object}" in shorter.reason:',
            "                if False:",
        ),
        (
            "G11 two rows for one constant",
            '            findings.append(\n                f"G11 DUPLICATE-ROW',
            '            [].append(\n                f"G11 DUPLICATE-ROW',
        ),
        # The `Prop` exclusion is DERIVED (the head symbol's own declaration is
        # looked up and its result sort read), not a hand-written exemption
        # list. Deleting it demands a registry row for every proof-valued
        # nullary definition -- the shape of gate lanes turn off.
        (
            "a nullary Prop-valued definition is excluded as a proof",
            "        and not is_proof_valued(d.canonical_type, decls)",
            "        and True",
        ),
        # A bridge must be stated, not merely used. Reading the all-kinds
        # dependency column instead of the type column accepts any theorem
        # whose PROOF happens to touch both constants.
        (
            "a bridge is read from the theorem's type, not its proof term",
            "        _label, kind, name, _footprint, type_deps_field, _all_deps, _thm_deps, ctype = fields",
            "        _label, kind, name, _footprint, _type_deps, type_deps_field, _thm_deps, ctype = fields",
        ),
        # An empty population is a broken projection, not a clean tree. This
        # repository has shipped gates that exit 0 on completion alone.
        (
            "an empty authority is an error, not a quiet pass",
            "    if not pop:",
            "    if False:",
        ),
        # The exit status must depend on the finding.
        (
            "a finding exits nonzero",
            "        return 1\n\n    print(",
            "        return 0\n\n    print(",
        ),
        (
            "a projection row with the wrong field count is rejected",
            "        if len(fields) != 8:",
            "        if False:",
        ),
        (
            "a registry with no header line is rejected",
            "            if tuple(f.strip() for f in fields) != COLUMNS:",
            "            if False:",
        ),
        (
            "an unknown role is rejected",
            "        if role not in ROLES:",
            "        if False:",
        ),
    ],
)


# --------------------------------------------------------------------------
# nursery-refill-headroom-screen (ADR-1405, 2026-09-01).
#
# Two blind spots found screening Mathlib.Data.Nat.Log for a nursery draw,
# both in the OVERSTATING direction: propose-nursery-refill.py's
# used_source_names() never read the fact ledger (a directly-flipped mirror
# stayed "unused" forever -- 20 of 37 reported Nat.Log survivors), and it
# never applied the generator's HELD_OUT_CONSTRUCTIONS screen at all (a
# module whose candidates all mention a held-out-guarding constant could
# read as ready here while select() would refuse it). The second mutation
# below is the more important one: it is the guard on Nat.sqrt, the last
# construction still protecting a v1 held-out family
# (natural-square-root), and until this suite existed nothing but a
# comment enforced it.
# --------------------------------------------------------------------------

SUITES["nursery-refill-headroom-screen"] = (
    "scripts/propose-nursery-refill.py",
    Unittest("scripts.tests.test_propose_nursery_refill"),
    [
        (
            "a fact-catalog name (drawn or flipped directly) is not headroom",
            "    names |= catalogued_source_names()",
            "    pass  # removed for mutation testing",
        ),
        (
            "Nat.sqrt and Nat.log2 must stay in HELD_OUT_CONSTRUCTIONS -- "
            "Nat.sqrt guards the only surviving v1 held-out family, and "
            "Nat.log2 guards an unrelated already-drawn held-out family "
            "(natural-elementary-bounds) from a measured alphabetical-slice "
            "displacement, not from its own topic",
            'HELD_OUT_CONSTRUCTIONS = {"Nat.log2", "Nat.sqrt"}',
            'HELD_OUT_CONSTRUCTIONS = {"Nat.evil"}',
            "scripts/gen-autogenesis-nursery-refill.py",
        ),
    ],
)

# --------------------------------------------------------------------------
# check-autogenesis-nursery.py's split-exemption guards (ADR-1455).
#
# The suite is `test_nursery_exemption_guards`, NOT the fuller
# `test_check_autogenesis_nursery`, and the reason is mechanical rather than
# stylistic: this harness refuses a suite whose baseline is not green, and that
# module's `LiveManifestTests` reads the committed `nursery-v2-extension.json`,
# whose cross-population exemption is stale for a reason belonging to another
# lane. Pointing the mutation at it would print `BASELINE IS NOT GREEN` and
# measure nothing at all -- the outcome this harness exists to stop being
# mistaken for coverage.
#
# Each mutation kills tests on BOTH report paths where the guard sits on both,
# which is the point: `validate_exemptions` is shared by the v1 and the
# cross-population reports, and a guard that only bit on one of them would be
# half a guard.
# --------------------------------------------------------------------------

SUITES["nursery-split-exemption-guards"] = (
    "scripts/check-autogenesis-nursery.py",
    Unittest("scripts.tests.test_nursery_exemption_guards"),
    [
        (
            "an exemption naming a held-out row is refused, on both report paths",
            "        if held_out_members:",
            "        if False:",
        ),
        (
            "a v1 exemption matching no live crossing component fails the gate",
            "    if unused_exemptions:\n"
            "        violation_blocks.append(describe_stale_exemptions(unused_exemptions))",
            "    if False:\n"
            "        violation_blocks.append(describe_stale_exemptions(unused_exemptions))",
        ),
        (
            "a cross-population exemption matching no live crossing component "
            "fails the gate",
            "    if unused_exemptions:\n"
            "        violation_blocks.append(\n"
            '            describe_stale_exemptions(unused_exemptions, label="cross-population ")\n'
            "        )",
            "    if False:\n"
            "        violation_blocks.append(\n"
            '            describe_stale_exemptions(unused_exemptions, label="cross-population ")\n'
            "        )",
        ),
        # ADR-1563. The per-edge amendment contraction. N2 is the one worth
        # reading twice: it does not DELETE the contraction, it makes it
        # undirected, which is the mutation that would clear the leaking
        # `longitudinal -> evaluation` direction along with the benign one and
        # leave both reports green. A guard whose only mutant is `if False:`
        # never gets asked whether it is doing the RIGHT contraction.
        (
            "N1 an amended edge is contracted out of the component graph",
            "            if (fact_id, dependency) in amended:\n"
            "                continue",
            "            if False:\n"
            "                continue",
        ),
        (
            "N2 the contraction is DIRECTED, so the leaking direction stays",
            "            if (fact_id, dependency) in amended:\n"
            "                continue",
            "            if ((fact_id, dependency) in amended\n"
            "                    or (dependency, fact_id) in amended):\n"
            "                continue",
        ),
        (
            "N3 an unhonoured amendment stops the report, never restores edges",
            "    if complaints:\n"
            "        raise NurseryError(",
            "    if False:\n"
            "        raise NurseryError(",
        ),
        # ADR-1564. `EVALUATION_PARTITIONS` was a module literal three lines
        # from a `validate_policy` that asserted the manifest said the same
        # triple -- two copies of one decision, with the gate answering from
        # the copy that was never the authority. N4 restores the literal.
        # `AmendedPartitionRoleTests` is a BEFORE/AFTER pair over ONE fixture
        # (same facts, same entries, same edge; only the policy differs), so
        # N4 kills the AFTER half alone and leaves the BEFORE half green --
        # which is what distinguishes a derived set from a lucky literal.
        (
            "N4 the evaluated partitions are read from the policy",
            '    return set(policy["required_evaluation_partitions"])',
            '    return {"train", "development", "held-out"}',
        ),
        (
            "N5 a policy naming no evaluation partition is refused",
            "        or not required\n",
            "        or False\n",
        ),
        (
            "N6 blind_partitions may not be empty or foreign",
            "    if not isinstance(blind, list) or not blind or set(blind) - set(required):",
            "    if False:",
        ),
    ],
)


# --------------------------------------------------------------------------
# `mathlib-nursery-split` -- the AMENDMENT REQUIREMENT on the partition roles
# (ADR-1564).
#
# `required_evaluation_partitions` is part of what `split_freeze:
# before-target-outcomes` froze. Editing it in place would be
# indistinguishable from having always meant it -- ADR-1546's exemption
# re-scoped 228 -> 230 -> 258 -> 274 at a coarser unit. So the generator
# carries a `PREREGISTERED_PARTITION_ROLES` constant (the shape frozen on
# 2026-08-18, NOT the shape that ships) and refuses a departure with no dated
# `policy_amendments` entry.
#
# S2 is the direction that is easy to leave out, and the reason it is here:
# without it a lane could record an amendment, change nothing, and the file
# would carry a dated claim about a change that never happened.
# --------------------------------------------------------------------------

SUITES["mathlib-nursery-split"] = (
    "scripts/create-autogenesis-mathlib-nursery-split.py",
    Unittest("scripts.tests.test_create_autogenesis_mathlib_nursery_split"),
    [
        (
            "S1 a role change with no policy_amendments entry is refused",
            "    if departed and not amendments:",
            "    if False:",
        ),
        (
            "S2 an amendment recorded against unchanged roles is refused",
            "    if amendments and not departed:",
            "    if False:",
        ),
        (
            "S3 blind_partitions may not be empty",
            '    if not lists["blind_partitions"]:',
            "    if False:",
        ),
    ],
)

# --------------------------------------------------------------------------
# rescope-nursery-exemption.py's gate-output parser (ADR-1455).
#
# The tool had NO tests. Its parser scraped every `F:… -> partition` line out
# of the gate's combined output with one regex, which -- because the gate
# validates nursery-v1 first and raises before the cross-population report runs
# -- returned V1 fact ids and would have written them over the 258-member
# cross-population exemption. Both guards below are what stop that, and they
# cover DISJOINT cases: counting components does not catch a v1 error that
# reports exactly one component, and the header check does not catch two
# genuine cross-population components. Each mutation must therefore kill its
# own test and leave the other's alive.
# --------------------------------------------------------------------------

SUITES["nursery-rescope-parser"] = (
    "scripts/rescope-nursery-exemption.py",
    Unittest("scripts.tests.test_rescope_nursery_exemption"),
    [
        (
            "members are attributed only to a CROSS-POPULATION component, "
            "never to nursery-v1's own crossing",
            "            current = component.group(1) if in_cross_population else None",
            "            current = component.group(1)",
        ),
        (
            "two reported components are refused rather than unioned into a "
            "component that exists nowhere",
            "    if len(blocks) > 1:",
            "    if False:",
        ),
    ],
)

# --------------------------------------------------------------------------
# check-autogenesis-holdout-isolation.py's pinned population size.
#
# The pin (`held_out=186` in `test_the_committed_repository_passes`) exists to
# make a change in the blind population's size impossible to land silently.
# What it is worth depends entirely on the assertion reading the gate's LIVE
# output rather than a constant that happens to agree with it, and nothing
# proved that: the pin has been stale five times (116, 136, 156, 146, 186) and
# each repair transcribed a new number.
#
# So mutate the SUBJECT -- perturb the count the gate reports -- and require
# the pin to die. A pin that survives a wrong count is a rubber stamp, which
# is exactly what the repair procedure risks turning it into.
# --------------------------------------------------------------------------

SUITES["holdout-isolation-population-pin"] = (
    "scripts/check-autogenesis-holdout-isolation.py",
    Unittest("scripts.tests.test_check_autogenesis_holdout_isolation"),
    [
        (
            "the pinned population size is read from the gate's live output, "
            "not asserted against a constant that merely agrees with it",
            '        f"AUTOGENESIS_HOLDOUT_ISOLATION|held_out={len(held)}|"',
            '        f"AUTOGENESIS_HOLDOUT_ISOLATION|held_out={len(held) + 1}|"',
        ),
    ],
)

# --------------------------------------------------------------------------
# inductive-universe-guard (ADR-1495, pinned by ADR-1500): Lean's
# `check_constructor` universe constraint in `Kernel::add_inductive`.
#
# Without it, `U : Sort 1` with `mk : Sort 1 -> U` is admitted; large
# elimination then gives `el : U -> Sort 1` with `el (mk X)` def-eq `X`,
# making `Sort u` a retract of an inhabitant of `Sort u` -- the `Type : Type`
# precondition for Girard's paradox, from which `False` is derivable. This is
# the one trust anchor the whole project's axiom-freedom claim rests on.
#
# The guard shipped with its rejection assertion and its two admission
# controls in ONE `#[test]`, which measured less than it looked: the test dies
# on its FIRST assertion, so the admission controls were unreachable in the
# only configuration where their answer matters. They are separate `#[test]`s
# now, and the three integration suites the fix touched
# (`kernel_seam_fuzz`, `mutual_inductive_group_grammar`,
# `nested_inductive_grammar`) SURVIVE the guard's removal -- confirmed
# independently, 1 passed / exit 0 each -- because the grammar generator was
# moved to emitting only Lean-legal shapes. So `--lib inductive` is the only
# thing in the workspace that dies, which is exactly why it is registered here.
#
# The two mutations below fail in OPPOSITE directions and are killed by
# different tests: dropping the guard admits the paradox shape, and dropping
# the `Prop` exemption refuses `Exists` and `Acc`.
# --------------------------------------------------------------------------

SUITES["inductive-universe-guard"] = (
    "crates/axeyum-lean-kernel/src/inductive.rs",
    Cargo(
        ("-p", "axeyum-lean-kernel", "--lib", "inductive"),
        "inductive-universe-guard",
    ),
    [
        # THE GUARD ITSELF. `false &&` makes the whole `if` dead, which is
        # semantically removal. Killed by
        # `reject_ctor_field_universe_above_result_universe`,
        # `..._polymorphic`, and `universe_check_precedes_positivity_check`.
        (
            "a constructor field above the family's result universe is refused",
            "            if !self.level_is_zero(group.result_level)",
            "            if false && !self.level_is_zero(group.result_level)",
        ),
        # THE OTHER DIRECTION: a guard that refuses too much is also a defect,
        # and this one sits in the path of every inductive the project
        # declares. Dropping the `Prop` exemption makes the constraint apply
        # to impredicative families, refusing `Exists` and `Acc`. Killed by
        # `admit_prop_family_with_sort1_field` and
        # `prop_exemption_is_sound_because_large_elimination_is_denied`.
        (
            "Prop is exempt because it is impredicative",
            "            if !self.level_is_zero(group.result_level)",
            "            if true",
        ),
    ],
)


# ADR-1545. The `nat-testbit-bool-codomain` row said `new-construction` and
# gave as its reason that a Bool-valued testBit view and its bridge theorem
# were not built. Both WERE built, axiom-free, and had moved no mirror for a
# week. A stale claim about the tree, sitting in the field a selector reads,
# next to the generator docstring's own record of the same mistake made about
# `fastFib`. Prose did not stop the second one, so the corrected row is pinned
# by tests instead.
SUITES["obstruction-testbit-classification"] = (
    "scripts/gen-obstruction-producers.py",
    "scripts.tests.test_gen_obstruction_producers",
    [
        (
            "the Bool-codomain row is not-removable",
            '"id": "nat-testbit-bool-codomain",\n'
            '            "capability_gap": "definitional-non-equivalence",\n'
            '            "removability": "not-removable",',
            '"id": "nat-testbit-bool-codomain",\n'
            '            "capability_gap": "definitional-non-equivalence",\n'
            '            "removability": "new-construction",',
        ),
        (
            "the row cites the ADR its removability rests on",
            '                "docs/research/09-decisions/adr-1545-the-testbit-codomain-is-the-"\n'
            '                "outermost-link-of-a-chain-and-the-bool-view-is-already-built.md",\n',
            "",
        ),
        (
            "every path-shaped evidence entry names a real file",
            '"crates/axeyum-lean-kernel/examples/nat_testbit_bool_bridge.rs",',
            '"crates/axeyum-lean-kernel/examples/nat_testbit_bool_bridge_absent.rs",',
        ),
        (
            "the List-Bool group is split out by what the statements say",
            '        if "bits" in stmt or "getI" in stmt or "List" in stmt:',
            "        if False:",
        ),
        # --- the ADR-1510 settlement policy (2026-09-02) ------------------
        #
        # Both mutations reinstate a shape this generator actually shipped.
        # The first restores the P2 behaviour that was red on `main`: a
        # contract whose whole population closed died with exit 2 before any
        # artifact was written, so success and defect were indistinguishable
        # at the exit status. The second is the half that no version of this
        # generator ever had: on a PARTIAL close it kept every settled target
        # in `applicability`, where G7 would (correctly) fire on a contract
        # that is actually healthy.
        (
            # `raise SystemExit`, not the `die()` this generator really used:
            # `die` prints `ERROR: ...` to stderr, and `classify_unittest`'s
            # death regex reads that line as a SECOND dead test, so the run
            # comes back INCONSISTENT (1 counted, 2 named) and measures
            # nothing. The exit path being reinstated is identical.
            "an exhausted population retires instead of erroring",
            '    if spent:\n        return "fulfilled"\n',
            "    if spent:\n        raise SystemExit(2)\n",
        ),
        (
            "a partial settlement keeps its live targets live",
            '        if status_of(facts[fid]) == "open":\n            live.append(fid)\n',
            "        if False:\n            live.append(fid)\n",
        ),
    ],
)


# --------------------------------------------------------------------------
# `nursery-components` -- `scripts/nursery-components.py`, the measurement
# ADR-1546 option 1 needed and the refusal ADR-1551 records.
#
# This suite's subject is unusual: the tool's entire output is a REFUSAL, so
# the guards that must be driven to failure are the ones that would tell the
# next lane the refusal has expired. A `--check` that cannot go red asserts
# "option 1 is still impossible" forever with nobody able to falsify it --
# which is the exemption shape ADR-1550 replaced, wearing a newer date.
#
# N6 and N7 are the two that carry the artifact's ownership rather than a
# finding: the ledger block is carried forward on `--record` because
# `check-generated-artifact-ownership.py`'s OWNER arm perturbs the committed
# file and demands a byte-identical restore, and `--remeasure` is the mode
# that keeps that carry-forward from being a permanent snapshot. Each mutant
# kills exactly one test.
# --------------------------------------------------------------------------

SUITES["nursery-components"] = (
    "scripts/nursery-components.py",
    Unittest("scripts.tests.test_nursery_components"),
    [
        (
            "N1 a family holding two partitions is a finding",
            '    if manifest["families_holding_two_partitions"]:',
            "    if False:",
        ),
        (
            "N2 the blob no longer spanning two evaluation partitions is a finding",
            "        if len(evaluation) < 2:",
            "        if False:",
        ),
        (
            "N3 a blob containing neither pinned family is a finding",
            '    if blob is not None and not blob["pinned_families"]:',
            "    if False:",
        ),
        (
            "N4 the pinned crossings disappearing is a finding",
            '    if ledger["pinned_incident_edge_count"] == 0:',
            "    if False:",
        ),
        (
            "N5 an internally inconsistent census FAILS rather than drifting",
            '        if fams.get("count") != len(fams["components"]):',
            "        if False:",
        ),
        (
            "N6 --record carries the ledger block forward",
            "    if previous is not None and not remeasure:",
            "    if False:",
        ),
        (
            "N7 --remeasure actually re-measures",
            "    if args.record:\n"
            "        path.write_text(render(root, measured, previous, args.remeasure))",
            "    if args.record:\n"
            "        path.write_text(render(root, measured, previous, False))",
        ),
        (
            "N8 a pinned family is never proposed for a move",
            "    free = sorted(f for f in rows_of\n"
            "                  if f not in PINNED_FAMILIES",
            "    free = sorted(f for f in rows_of\n"
            "                  if True",
        ),
        (
            "N9 numeric drift from the snapshot is advisory, not a failure",
            "    return 1 if (complaints or inconsistent) else 0",
            "    return 1 if (complaints or inconsistent or drift) else 0",
        ),
        (
            # The defect this caught for real. A dict keyed by component SIZE
            # is written in numeric order and read back in lexicographic
            # order, so the carried-forward block changes shape on the second
            # write and the artifact stops being a fixed point of its own
            # writer -- which is precisely what
            # `check-generated-artifact-ownership.py`'s OWNER arm measures.
            "N11 --record is a fixed point on its own output",
            '            "size_distribution": [\n'
            '                {"size": size, "components": count}\n'
            "                for size, count in sorted(collections.Counter(\n"
            "                    len(m) for m in facts).items())],",
            '            "size_distribution": dict(sorted(collections.Counter(\n'
            "                len(m) for m in facts).items())),",
        ),
        (
            "N10 a component's families really do take ONE partition",
            "        if best is None or best[0] >= cut(assignment):",
            "        if True:",
        ),
    ],
)


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))

