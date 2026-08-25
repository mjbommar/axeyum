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
    "settled-fact-statements": (
        "scripts/check-settled-fact-statements.py",
        "scripts.tests.test_settled_fact_statements",
        [
            (
                "unamended-drift guard",
                "        if amendment is None:",
                "        if False:",
            ),
            (
                "amendment must describe THIS change",
                '        elif amendment["from_sha256"] != pin["statement_sha256"] or amendment[\n            "to_sha256"\n        ] != now["statement_sha256"]:',
                "        elif False:",
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
    "development-partition": (
        "scripts/check-development-partition.py",
        "scripts.tests.test_development_partition",
        [
            (
                "development-without-train rule",
                "        if touched_dev and not touched_train:",
                "        if False:",
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
                ".git", "target", "references", "bench-results", "__pycache__"
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
        (
            "the census is over OPEN facts",
            '        elif statuses[fact_id] != "open":',
            "        elif False:",
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

if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
