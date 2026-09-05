#!/usr/bin/env python3
"""Mutation controls for `certificate-spec` fact statements."""

from __future__ import annotations

import copy
import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "validate-facts.py"
FACT = ROOT / "artifacts" / "facts" / "F-gf2-general-monomial-composition-criterion.json"

SPEC = importlib.util.spec_from_file_location("validate_facts", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

class CertificateSpecValidationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.fact = json.loads(FACT.read_text(encoding="utf-8"))

    def errors_for(self, statement: str) -> list[str]:
        fact = copy.deepcopy(self.fact)
        fact["formal"]["statement"] = statement
        return MODULE.validate_one(FACT, fact, {fact["id"]})

    def test_committed_statement_is_valid(self) -> None:
        self.assertEqual(self.errors_for(self.fact["formal"]["statement"]), [])

    def test_malformed_and_non_object_statements_are_rejected(self) -> None:
        for statement, expected in (
            ("{", "not valid JSON"),
            ("[]", "must be a JSON object"),
        ):
            with self.subTest(statement=statement):
                self.assertTrue(any(expected in error for error in self.errors_for(statement)))

    def test_noncanonical_statement_is_rejected(self) -> None:
        parsed = json.loads(self.fact["formal"]["statement"])
        statement = json.dumps(parsed, sort_keys=False, indent=2)
        self.assertTrue(
            any("must use canonical JSON" in error for error in self.errors_for(statement))
        )

    def test_format_and_version_contract_is_rejected_when_mutated(self) -> None:
        parsed = json.loads(self.fact["formal"]["statement"])
        mutations = (
            ({**parsed, "format": ""}, "non-empty string format"),
            ({key: value for key, value in parsed.items() if key != "format"}, "format"),
            ({**parsed, "version": 0}, "positive integer version"),
            ({**parsed, "version": True}, "positive integer version"),
        )
        for mutation, expected in mutations:
            with self.subTest(mutation=mutation):
                statement = json.dumps(mutation, sort_keys=True, separators=(",", ":"))
                self.assertTrue(any(expected in error for error in self.errors_for(statement)))


# The two range-binding controls (semantic and canonicalization mutation of
# `check-gf2-lemire-range.py`) moved out with that checker and the
# `F:gf2-lemire-half-degree-through-400` fact; see
# ../lemire-half-degree-irreducibles. What remains here is the guard that
# lives in this repo: `certificate-spec` statement validation.


GREP_Q_FACT = ROOT / "artifacts" / "facts" / "F-nat-add-assoc.json"


class GrepDashQCheckerCommandTests(unittest.TestCase):
    """`grep -q` as a pipeline consumer under `set -o pipefail` is banned
    (CLAUDE.md, banned-shell-idioms #2): `-q` exits at the first match and
    SIGPIPEs the producer, turning the pipeline's exit status nondeterministic.
    99 committed facts carried this idiom before 2026-08-25's rewrite to
    `grep -c` + a count `test`; this guard is what keeps it from coming back.
    """

    def setUp(self) -> None:
        self.fact = json.loads(GREP_Q_FACT.read_text(encoding="utf-8"))

    def errors_for_checker_command(self, cmd: str) -> list[str]:
        fact = copy.deepcopy(self.fact)
        fact["evidence"][0]["checker_command"] = cmd
        return MODULE.validate_one(GREP_Q_FACT, fact, {fact["id"]})

    def test_committed_checker_commands_use_grep_dash_c_and_are_accepted(self) -> None:
        # The real, already-rewritten command in the committed fact must not
        # trip the guard -- otherwise the guard would be rejecting the exact
        # form it is supposed to require.
        self.assertEqual(self.errors_for_checker_command(
            self.fact["evidence"][0]["checker_command"]
        ), [])

    def test_grep_dash_q_pipeline_consumer_is_rejected(self) -> None:
        # Deliberately ONE assertion, not a subTest loop: the mutation harness
        # counts each subTest failure as a separate death, and this suite's
        # contract is that deleting the guard kills exactly one test. The
        # broader spelling coverage lives in
        # `test_grep_dash_q_helper_detects_every_spelling` below, which calls
        # the detector function directly and so is unaffected by a mutation
        # at the `validate_one` call site.
        errors = self.errors_for_checker_command("cmd 2>/dev/null | grep -q 'pattern'")
        self.assertTrue(
            any("grep -q" in e and "SIGPIPE" in e for e in errors),
            f"expected a grep -q rejection, got {errors!r}",
        )

    def test_grep_dash_q_helper_detects_every_spelling(self) -> None:
        # Exercises `checker_command_uses_grep_dash_q` directly (not through
        # `validate_one`), so this test's outcome is independent of the
        # `fact-checker-grep-dash-q` mutation control above.
        for bad_cmd in (
            "cmd 2>/dev/null | grep -q 'pattern'",
            "cmd 2>/dev/null | grep -qE 'pattern'",
            "cmd 2>/dev/null | grep -Eq 'pattern'",
            "cmd 2>/dev/null | grep -qxF 'pattern'",
            "cmd 2>/dev/null | grep --quiet 'pattern'",
            "cmd 2>/dev/null | grep -q -E 'pattern'",
        ):
            with self.subTest(bad_cmd=bad_cmd):
                self.assertTrue(
                    MODULE.checker_command_uses_grep_dash_q(bad_cmd),
                    f"expected {bad_cmd!r} to be detected as grep -q",
                )
        for ok_cmd in (
            "cmd 2>/dev/null | grep -c 'pattern'",
            "cmd -A1 'x' 2>/dev/null | grep -Ec 'pattern'",
        ):
            with self.subTest(ok_cmd=ok_cmd):
                self.assertFalse(MODULE.checker_command_uses_grep_dash_q(ok_cmd))

    def test_grep_dash_c_forms_are_not_flagged(self) -> None:
        # A guard broad enough to also catch the REMEDY is worse than no
        # guard: every fact using the correct form would fail the ledger.
        for ok_cmd in (
            "cmd 2>/dev/null | grep -c 'pattern'",
            "cmd 2>/dev/null | grep -cE 'pattern'",
            "cmd 2>/dev/null | grep -Ec 'pattern'",
            "cmd 2>/dev/null | grep -xFc 'pattern'",
            "cmd -A1 'x' 2>/dev/null | grep -Ec 'pattern'",
        ):
            with self.subTest(ok_cmd=ok_cmd):
                self.assertEqual(self.errors_for_checker_command(ok_cmd), [])


# In POSIX ERE (and BRE), `\t` is NOT a tab -- GNU grep drops the backslash
# and matches a literal 't'. Measured with `/usr/bin/grep` (GNU grep 3.12):
# `printf 'a\tb\n' | grep -cE 'a\tb'` -> 0 (a real tab does not match this
# pattern) and `printf 'atb\n' | grep -cE 'a\tb'` -> 1 (it matches the
# literal 't' instead). 54 facts / 68 checker_commands carried this before
# 2026-08-25's rewrite to `[[:space:]]`, all silently reporting a PRESENT
# theorem as ABSENT under a script or CI run.
GREP_T_FACT = ROOT / "artifacts" / "facts" / "F-cpoint-cauchy-schwarz.json"


class GrepBackslashTCheckerCommandTests(unittest.TestCase):
    """`\\t` inside a grep -E pattern is not a tab; the fix is `[[:space:]]`
    (or, for a bracket expression `[^\\t]`, `[^[:space:]]`)."""

    def setUp(self) -> None:
        self.fact = json.loads(GREP_T_FACT.read_text(encoding="utf-8"))

    def errors_for_checker_command(self, cmd: str, index: int = 0) -> list[str]:
        fact = copy.deepcopy(self.fact)
        fact["evidence"][index]["checker_command"] = cmd
        # `F-cpoint-cauchy-schwarz.json` (chosen because it carries BOTH the
        # standalone-`\t` and bracket-`[^\t]` shapes) has non-empty
        # `depends_on`; include those ids so a dependency-DAG error doesn't
        # drown out the guard this test targets.
        known_ids = {fact["id"], *fact.get("depends_on", [])}
        return MODULE.validate_one(GREP_T_FACT, fact, known_ids)

    def test_committed_checker_commands_use_bracket_space_and_are_accepted(self) -> None:
        # Both evidence rows on this fact were rewritten 2026-08-25: one uses
        # the standalone `\t` -> `[[:space:]]` form, the other the bracket
        # form `[^\t]` -> `[^[:space:]]`. Neither may trip the guard.
        for index in range(len(self.fact["evidence"])):
            with self.subTest(index=index):
                cmd = self.fact["evidence"][index]["checker_command"]
                self.assertEqual(self.errors_for_checker_command(cmd, index=index), [])

    def test_grep_backslash_t_is_rejected(self) -> None:
        # Deliberately ONE assertion (see the analogous note on
        # test_grep_dash_q_pipeline_consumer_is_rejected): the mutation
        # harness counts each subTest failure as a separate death, and this
        # suite's contract is that deleting the guard kills exactly one test.
        errors = self.errors_for_checker_command("cmd 2>/dev/null | grep -cE '^Name\\t'")
        self.assertTrue(
            any("\\t" in e and "ERE" in e and "tab" in e for e in errors),
            f"expected a grep \\t rejection, got {errors!r}",
        )

    def test_grep_backslash_t_helper_detects_both_shapes(self) -> None:
        # Exercises `checker_command_uses_grep_backslash_t` directly, so this
        # test's outcome is independent of the `validate_one` call site and
        # of the `fact-checker-grep-backslash-t` mutation control above.
        for bad_cmd in (
            "cmd 2>/dev/null | grep -cE '^Name\\t'",
            "cmd 2>/dev/null | grep -cE '^a\\tb\\t[^\\t]*\\t0\\t$'",
        ):
            with self.subTest(bad_cmd=bad_cmd):
                self.assertTrue(
                    MODULE.checker_command_uses_grep_backslash_t(bad_cmd),
                    f"expected {bad_cmd!r} to be detected as grep \\t",
                )
        for ok_cmd in (
            "cmd 2>/dev/null | grep -cE '^Name[[:space:]]'",
            "cmd 2>/dev/null | grep -cE '^a[[:space:]]b[[:space:]][^[:space:]]*[[:space:]]0[[:space:]]$'",
            "cmd 2>/dev/null | grep -c 'plain text'",
            "cmd 2>/dev/null | grep -cE '^Name'\"$(printf '\\t')\"'$'",
        ):
            with self.subTest(ok_cmd=ok_cmd):
                self.assertFalse(MODULE.checker_command_uses_grep_backslash_t(ok_cmd))


DEEP_STACK_FACT = ROOT / "artifacts" / "facts" / "F-creal-add-comm.json"


class DeepStackInventoryCheckerCommandTests(unittest.TestCase):
    """`nat_axiom_inventory --include-constructed`, `prelude_theorem_inventory
    --include-constructed` and any `theorem_dependency_inventory` invocation
    build the constructed carriers (CReal/Complex/CPoint) deep enough through
    `Kernel::add_declaration` to overflow a debug build's default thread
    stack. 19 committed `F-creal-*`/`F-complex-*` checker commands carried
    this before 2026-08-25's fix -- exit 134 ('has overflowed its stack')
    without `--release`, exit 0 with it, measured against the exact command
    `F:creal-add-comm`'s footprint evidence now runs."""

    def setUp(self) -> None:
        self.fact = json.loads(DEEP_STACK_FACT.read_text(encoding="utf-8"))

    def errors_for_checker_command(self, cmd: str, index: int = 0) -> list[str]:
        fact = copy.deepcopy(self.fact)
        fact["evidence"][index]["checker_command"] = cmd
        known_ids = {fact["id"], *fact.get("depends_on", [])}
        return MODULE.validate_one(DEEP_STACK_FACT, fact, known_ids)

    def test_committed_checker_commands_carry_release_and_are_accepted(self) -> None:
        # `F:creal-add-comm` carries both affected tools (theorem_dependency_
        # inventory in evidence 0, nat_axiom_inventory --include-constructed in
        # evidence 1); after 2026-08-25's fix, neither may trip the guard.
        for index in range(len(self.fact["evidence"])):
            with self.subTest(index=index):
                cmd = self.fact["evidence"][index]["checker_command"]
                self.assertEqual(self.errors_for_checker_command(cmd, index=index), [])

    def test_nat_axiom_inventory_include_constructed_without_release_is_rejected(self) -> None:
        # Deliberately ONE assertion (see the analogous note on the grep -q and
        # grep \t guards above): the mutation harness counts each subTest
        # failure as a separate death, and this suite's contract is that
        # deleting the guard kills exactly one test.
        errors = self.errors_for_checker_command(
            "cargo run -q -p axeyum-lean-kernel --example nat_axiom_inventory -- "
            "--include-constructed --require-axiom-free creal",
            index=1,
        )
        self.assertTrue(
            any("--release" in e and "overflow" in e for e in errors),
            f"expected a deep-stack --release rejection, got {errors!r}",
        )

    def test_the_two_tools_and_the_include_constructed_scoping_are_all_exercised(self) -> None:
        # Exercises `checker_command_needs_release_for_deep_stack` directly, so
        # this test's outcome is independent of the `validate_one` call site
        # and of the mutation control's own deletion.
        for bad_cmd in (
            "cargo run -q -p axeyum-lean-kernel --example nat_axiom_inventory -- "
            "--include-constructed --require-axiom-free creal",
            "cargo run -q -p axeyum-lean-kernel --example prelude_theorem_inventory -- "
            "--include-constructed",
            "cargo run -q -p axeyum-lean-kernel --example theorem_dependency_inventory -- "
            "CReal.add_comm",
            # theorem_dependency_inventory builds every constructed prelude
            # unconditionally, so it is flagged even WITHOUT --include-constructed.
            "cargo run -q -p axeyum-lean-kernel --example theorem_dependency_inventory",
        ):
            with self.subTest(bad_cmd=bad_cmd):
                self.assertTrue(
                    MODULE.checker_command_needs_release_for_deep_stack(bad_cmd),
                    f"expected {bad_cmd!r} to be flagged",
                )
        for ok_cmd in (
            "cargo run -q --release -p axeyum-lean-kernel --example nat_axiom_inventory "
            "-- --include-constructed --require-axiom-free creal",
            "cargo run -q --release -p axeyum-lean-kernel --example theorem_dependency_inventory",
            # --include-constructed absent: nat_axiom_inventory's Nat/Int/Rat/
            # logic-only forms run fine in a debug build (measured 2026-08-25).
            "cargo run -q -p axeyum-lean-kernel --example nat_axiom_inventory -- "
            "--require-axiom-free nat",
            # A tool this guard does not cover at all.
            "cargo run -q -p axeyum-lean-kernel --example nat_theorem_inventory -- x",
        ):
            with self.subTest(ok_cmd=ok_cmd):
                self.assertFalse(MODULE.checker_command_needs_release_for_deep_stack(ok_cmd))


KERNEL_THEOREM_FACT = ROOT / "artifacts" / "facts" / "F-nat-add-assoc.json"


class KernelTheoremFieldTests(unittest.TestCase):
    """`formal.kernel_theorem` is what `theorem_of`
    (scripts/check-fact-depends-derived.py, shared by the chain catalog and
    the autogenesis snapshot builder) reads, WHEN PRESENT, as a fact's
    subject theorem -- `null` included, meaning "explicitly no single kernel
    theorem" (a package-level fact). A malformed value here is never caught
    by anything else, since no other tool reads this key, so it must be
    validated the same way an extracted theorem name is."""

    def setUp(self) -> None:
        self.fact = json.loads(KERNEL_THEOREM_FACT.read_text(encoding="utf-8"))

    def errors_for_kernel_theorem(self, value, *, key_present: bool = True) -> list[str]:
        fact = copy.deepcopy(self.fact)
        if key_present:
            fact["formal"]["kernel_theorem"] = value
        else:
            fact["formal"].pop("kernel_theorem", None)
        return MODULE.validate_one(KERNEL_THEOREM_FACT, fact, {fact["id"]})

    def test_absent_key_is_accepted(self) -> None:
        self.assertEqual(self.errors_for_kernel_theorem(None, key_present=False), [])

    def test_explicit_null_is_accepted(self) -> None:
        # `null` means "package-level, no single subject" -- a real, valid
        # value, not an error.
        self.assertEqual(self.errors_for_kernel_theorem(None), [])

    def test_a_real_dotted_theorem_name_is_accepted(self) -> None:
        self.assertEqual(self.errors_for_kernel_theorem("Nat.add_assoc"), [])

    def test_a_multi_segment_characterization_name_is_accepted(self) -> None:
        self.assertEqual(
            self.errors_for_kernel_theorem("Int.Characterization.categorical"), []
        )

    def test_an_invalid_value_is_rejected(self) -> None:
        # Deliberately ONE assertion through `validate_one`, not a subTest
        # loop over every bad shape: this suite's contract is that deleting
        # the guard kills exactly one test. Coverage of WHICH shapes are
        # invalid lives in the two tests below, which call
        # `kernel_theorem_is_valid` directly and so are unaffected by a
        # mutation at the `validate_one` call site.
        errors = self.errors_for_kernel_theorem("not a theorem name")
        self.assertTrue(
            any("formal.kernel_theorem" in e for e in errors), errors
        )

    def test_kernel_theorem_is_valid_rejects_every_bad_shape(self) -> None:
        for value in (
            "not a theorem name",
            "Nat",  # bare namespace, no dot-segment
            42,
            "",
            "nat.add_assoc",  # lowercase namespace
        ):
            with self.subTest(value=value):
                self.assertFalse(MODULE.kernel_theorem_is_valid(value))

    def test_kernel_theorem_is_valid_accepts_every_good_shape(self) -> None:
        for value in (
            None,
            "Nat.add_assoc",
            "Int.Characterization.categorical",
            "AxReal.add_comm",
            "AxNat.fib",
            "CReal.add_comm",
            "Complex.mul_assoc",
            "CPoint.dot_comm",
        ):
            with self.subTest(value=value):
                self.assertTrue(MODULE.kernel_theorem_is_valid(value))


CAS_CERTIFICATE_FACT = ROOT / "artifacts" / "facts" / "F-alternating-binomial-row-sum-zero.json"


class CasCertificateClassificationTests(unittest.TestCase):
    """ADR-0601 SS2: `cas-certificate` evidence must classify as either
    `kernel-reconstructed` (an independent re-derivation through the kernel
    exists) or `cas-internal` (the checker never leaves the CAS's own normal
    form) -- never a third, unclassifiable case that would let a bogus
    checker_command hide inside the route silently.
    """

    def setUp(self) -> None:
        self.fact = json.loads(CAS_CERTIFICATE_FACT.read_text(encoding="utf-8"))
        self.assertEqual(self.fact.get("proof_route"), "cas-certificate")

    def errors_for_checker_command(self, cmd: str, index: int = 0) -> list[str]:
        fact = copy.deepcopy(self.fact)
        fact["evidence"][index]["checker_command"] = cmd
        known_ids = {fact["id"], *fact.get("depends_on", [])}
        return MODULE.validate_one(CAS_CERTIFICATE_FACT, fact, known_ids)

    def test_committed_cas_internal_checker_commands_are_accepted(self) -> None:
        # The real, already-committed form must not trip the guard -- every
        # evidence row here is a `cargo test -p axeyum-cas ...` invocation.
        for index in range(len(self.fact["evidence"])):
            with self.subTest(index=index):
                cmd = self.fact["evidence"][index]["checker_command"]
                self.assertEqual(self.errors_for_checker_command(cmd, index=index), [])

    def test_rewriting_the_checker_to_a_kernel_consulting_form_is_accepted(self) -> None:
        # ADR-0601's own example of the OTHER honest class: a checker that
        # reconstructs through the kernel. This must NOT be rejected --
        # validate_one only refuses the unclassifiable third case.
        self.assertEqual(
            self.errors_for_checker_command(
                "cargo test -p axeyum-lean-kernel --test bridge_polynomial_identity"
            ),
            [],
        )

    def test_bogus_checker_command_is_rejected(self) -> None:
        # Deliberately ONE assertion (see the analogous note on the grep -q,
        # grep \t, and deep-stack guards above): the mutation harness counts
        # each subTest failure as a separate death, and this suite's
        # contract is that deleting the guard kills exactly one test.
        errors = self.errors_for_checker_command("echo this consults nothing")
        self.assertTrue(
            any("does not consult a recognized checker" in e for e in errors),
            f"expected a cas-certificate classification rejection, got {errors!r}",
        )

    def test_classifier_distinguishes_kernel_cas_and_bogus(self) -> None:
        # Exercises `classify_cas_certificate_checker` directly, so this
        # test's outcome is independent of the `validate_one` call site and
        # of the mutation control's own deletion.
        for cmd in (
            "cargo test -p axeyum-lean-kernel --test bridge_polynomial_identity",
            "cargo run -p axeyum-lean-kernel --example prelude_theorem_inventory",
            # Both packages named: kernel wins, since that is the stronger,
            # accurate claim (an independent re-derivation exists).
            "cargo test -p axeyum-cas --test telescoping_identities && "
            "cargo test -p axeyum-lean-kernel --test bridge_polynomial_identity",
        ):
            with self.subTest(cmd=cmd):
                self.assertEqual(
                    MODULE.classify_cas_certificate_checker(cmd), "kernel-reconstructed"
                )
        for cmd in (
            "cargo test -p axeyum-cas --test telescoping_identities",
            "cargo test -p axeyum-cas --all-features composition_shape_classification",
            "cargo test -p axeyum-cas --test geometry_certificate_artifacts && "
            "python3 scripts/check-geometry-fact-transcription.py F:x",
        ):
            with self.subTest(cmd=cmd):
                self.assertEqual(MODULE.classify_cas_certificate_checker(cmd), "cas-internal")
        for cmd in (
            "",
            "echo this consults nothing",
            # cargo check/build/doc never EXECUTE anything -- naming a
            # package after one of those subcommands does not count as
            # "consulted".
            "cargo check -p axeyum-cas",
            "cargo doc -p axeyum-lean-kernel",
        ):
            with self.subTest(cmd=cmd):
                self.assertEqual(MODULE.classify_cas_certificate_checker(cmd), "unrecognized")

    def test_fact_level_classification_prefers_kernel_then_flags_unrecognized(self) -> None:
        # `classify_cas_certificate_fact` aggregates across evidence rows:
        # kernel-reconstructed wins if present; otherwise unrecognized is
        # surfaced rather than silently read as cas-internal.
        cas_only = json.loads(CAS_CERTIFICATE_FACT.read_text(encoding="utf-8"))
        self.assertEqual(MODULE.classify_cas_certificate_fact(cas_only), "cas-internal")

        mixed = copy.deepcopy(cas_only)
        mixed["evidence"][0]["checker_command"] = (
            "cargo test -p axeyum-lean-kernel --test bridge_polynomial_identity"
        )
        self.assertEqual(MODULE.classify_cas_certificate_fact(mixed), "kernel-reconstructed")

        bogus = copy.deepcopy(cas_only)
        bogus["evidence"][0]["checker_command"] = "echo nothing"
        self.assertEqual(MODULE.classify_cas_certificate_fact(bogus), "unrecognized")


class DependsDerivedGateIsWiredIntoTheValidator(unittest.TestCase):
    """`validate-facts.py` is the command a lane is told to run when it
    touches a fact (CLAUDE.md's Commands section lists it standalone), so
    that is where `check-fact-depends-derived.py`'s finding is enforced --
    this pins the wiring itself, not the derivation logic (which has its own
    controls in `test_check_fact_depends_derived.py`)."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        tmp = Path(self._tmp.name)
        self.ok_script = tmp / "ok.py"
        self.ok_script.write_text(
            "print('DEPENDS_DERIVED|kernel_facts=0|named=0|graph=0|missing_edges=0')\n",
            encoding="utf-8",
        )
        self.fail_script = tmp / "fail.py"
        self.fail_script.write_text(
            "import sys\n"
            "print('DEPENDS_DERIVED_ERROR|fixture failure', file=sys.stderr)\n"
            "sys.exit(1)\n",
            encoding="utf-8",
        )
        self._original_script = MODULE.DEPENDS_DERIVED_SCRIPT

    def tearDown(self) -> None:
        MODULE.DEPENDS_DERIVED_SCRIPT = self._original_script
        self._tmp.cleanup()

    def test_skip_flag_short_circuits_without_running_anything(self) -> None:
        MODULE.DEPENDS_DERIVED_SCRIPT = self.fail_script  # would fail if run
        self.assertEqual(MODULE.run_depends_derived_gate(skip=True), 0)

    def test_a_passing_checker_propagates_zero(self) -> None:
        MODULE.DEPENDS_DERIVED_SCRIPT = self.ok_script
        self.assertEqual(MODULE.run_depends_derived_gate(skip=False), 0)

    def test_a_failing_checker_propagates_nonzero(self) -> None:
        MODULE.DEPENDS_DERIVED_SCRIPT = self.fail_script
        self.assertEqual(MODULE.run_depends_derived_gate(skip=False), 1)

    def test_a_missing_checker_script_fails_rather_than_silently_passing(self) -> None:
        """If the sibling script has been moved or deleted, this must not
        read as depends_on being fine -- it fails closed."""
        MODULE.DEPENDS_DERIVED_SCRIPT = Path(self._tmp.name) / "does-not-exist.py"
        self.assertEqual(MODULE.run_depends_derived_gate(skip=False), 1)


class MainFailsWhenDependsOnDrifts(unittest.TestCase):
    """End-to-end through `main`: a structurally valid ledger (copied real
    fact files, so `validate_one` has nothing to object to) must still fail
    the whole validator when the depends-derived gate fails, and must not
    write anything either way -- `main` only reads."""

    def setUp(self) -> None:
        self._tmp = tempfile.TemporaryDirectory()
        tmp = Path(self._tmp.name)
        # Two small, already-valid committed facts -- structural content is
        # irrelevant here since the depends-derived subprocess is stubbed.
        for name in (
            "F-affirming-the-consequent.json",
            "F-cas-evt-endpoint-exclusion-cubic-kernel-checked.json",
        ):
            (tmp / name).write_text(
                (ROOT / "artifacts" / "facts" / name).read_text(encoding="utf-8"),
                encoding="utf-8",
            )
        self.ok_script = tmp / "ok.py"
        self.ok_script.write_text(
            "print('DEPENDS_DERIVED|kernel_facts=0|named=0|graph=0|missing_edges=0')\n",
            encoding="utf-8",
        )
        self.fail_script = tmp / "fail.py"
        self.fail_script.write_text(
            "import sys\n"
            "print('DEPENDS_DERIVED_ERROR|fixture failure', file=sys.stderr)\n"
            "sys.exit(1)\n",
            encoding="utf-8",
        )
        self._originals = (MODULE.FACTS, MODULE.DEPENDS_DERIVED_SCRIPT, list(sys.argv))
        MODULE.FACTS = tmp

    def tearDown(self) -> None:
        MODULE.FACTS, MODULE.DEPENDS_DERIVED_SCRIPT, sys.argv[:] = self._originals
        self._tmp.cleanup()

    def test_main_fails_when_the_depends_derived_gate_fails(self) -> None:
        MODULE.DEPENDS_DERIVED_SCRIPT = self.fail_script
        sys.argv = ["validate-facts.py"]
        self.assertEqual(MODULE.main(), 1)

    def test_main_passes_when_the_depends_derived_gate_passes(self) -> None:
        MODULE.DEPENDS_DERIVED_SCRIPT = self.ok_script
        sys.argv = ["validate-facts.py"]
        self.assertEqual(MODULE.main(), 0)

    def test_skip_flag_lets_main_pass_despite_a_failing_gate(self) -> None:
        """The escape hatch actually reaches `main`, not only the helper
        function -- this is the case that would break if the flag were
        threaded through incorrectly (e.g. checked against the wrong argv)."""
        MODULE.DEPENDS_DERIVED_SCRIPT = self.fail_script
        sys.argv = ["validate-facts.py", "--skip-depends-derived"]
        self.assertEqual(MODULE.main(), 0)


# ---------------------------------------------------------------------------
# ADR-1664: the composed route, `kernel-lean-over-import`
# ---------------------------------------------------------------------------

IMPORTED_FACT = ROOT / "artifacts" / "facts" / "F-bool-and-comm.json"
# The path the fixture would live at. It does NOT exist and must not: the
# validator checks that a fact's id and its filename agree, so handing it
# `IMPORTED_FACT` would produce a filename-mismatch error that drowns out the
# rules these tests target. `validate_one` reads the dict, never the file.
COMPOSED_PATH = ROOT / "artifacts" / "facts" / "F-composed-fixture.json"


def composed_fixture() -> dict:
    """A minimal, VALID `kernel-lean-over-import` fact.

    Built from the committed `F:bool-and-comm` import so its `depends_on` edge
    points at a real imported fact rather than an invented id -- a fixture whose
    dependency does not exist would be rejected by the dangling-edge rule and
    would then pass or fail these tests for the wrong reason.

    No such fact is committed yet: ADR-1664 decides how one is RECORDED, and the
    first one is not built (see its Consequences, `K = 0`). So the fixture is
    synthetic by necessity, and each test below mutates exactly one field of it,
    with the unmutated fixture asserted valid first -- otherwise a guard broad
    enough to reject the CONFORMING shape would be invisible.
    """
    imported = json.loads(IMPORTED_FACT.read_text(encoding="utf-8"))
    return {
        "schema_version": 1,
        "id": "F:composed-fixture",
        "title": "A composed theorem, for the validator's controls",
        "statement": "A statement proved here on top of a labeled import.",
        "formal": {
            "language": "lean4",
            "statement": "((x : Bool) -> Eq.{1} Bool (Bool.and x Bool.true) "
                         "(Bool.and Bool.true x))",
            "fragment": "Bool",
        },
        "epistemic_status": "proved",
        "proof_route": "kernel-lean-over-import",
        "depends_on": ["F:bool-and-comm"],
        "axiom_footprint": list(MODULE.IMPORT_ROUTE_ASSUMPTIONS),
        "evidence": [
            {
                "id": "composed-term",
                "kind": "kernel-term",
                "supports": "the composed proof term type-checks in our kernel",
                "check_status": "checked",
                "checkers": ["Kernel::add_declaration"],
                "checker_command": (
                    "test \"$(cargo test -p axeyum-lean-import "
                    "--test imported_composition_footprint -- --nocapture "
                    "2>/dev/null | grep -c 'AXEYUM-COMPOSE|')\" -ge 1"
                ),
            }
        ],
        "provenance": {
            "date": "2026-09-05",
            "established_by": "the validator's ADR-1664 controls",
            "source": "artifacts/lean-imports/bool-and-comm.ndjson",
            "prior_art": imported["provenance"]["prior_art"],
        },
    }


COMPOSED_KNOWN_IDS = {"F:composed-fixture", "F:bool-and-comm"}


class ComposedRouteTests(unittest.TestCase):
    """ADR-1664 rules 2 and 3, enforced in `validate_one`.

    Rule 2 (the import-route assumptions must be transcribed) is the rule that
    makes ADR-1664's rejected option (3) impossible. Measured 2026-09-05
    (`crates/axeyum-lean-import/tests/imported_composition_footprint.rs`): an
    originated theorem composed over the Init-only `bool-and-comm.ndjson` import
    has a `Kernel::axiom_footprint` of EXACTLY EMPTY, because that walk keeps
    trusted DECLARATIONS and the three import assumptions are not declarations --
    they are claims about how the declarations reached the environment at all.
    Without this rule such a fact could be filed with `[]` and counted in the
    axiom-free headline.
    """

    def setUp(self) -> None:
        self.fact = composed_fixture()

    def errors_for(self, fact: dict) -> list[str]:
        return MODULE.validate_one(COMPOSED_PATH, fact, set(COMPOSED_KNOWN_IDS))

    def test_the_conforming_composed_fixture_is_accepted(self) -> None:
        # The acceptance half. A guard broad enough to reject the shape ADR-1664
        # REQUIRES would fail every composed fact ever filed, and no rejection
        # test would notice.
        self.assertEqual(self.errors_for(self.fact), [])

    def test_the_route_is_recognised_and_is_not_axiom_free_capable(self) -> None:
        # Derived from the validator's own sets, not from a second copy of the
        # literal: a test that spells the route name twice measures the author's
        # memory rather than the validator.
        self.assertIn("kernel-lean-over-import", MODULE.ROUTES)
        self.assertNotIn("kernel-lean-over-import", MODULE.AXIOM_FREE_CAPABLE)
        self.assertNotIn("kernel-lean-over-import", MODULE.IMPORTED_ROUTES)
        self.assertIn("kernel-lean-over-import", MODULE.COMPOSED_ROUTES)
        self.assertIn("kernel-lean-over-import", MODULE.IMPORT_DEPENDENT_ROUTES)

    def test_an_empty_footprint_is_refused_on_the_composed_route(self) -> None:
        # Delegated to the pre-existing AXIOM_FREE_CAPABLE guard, which this
        # route joins by NOT being in that set. Asserted anyway because it is
        # half of what the route means, and because a future edit adding the
        # route to AXIOM_FREE_CAPABLE would otherwise be silent.
        fact = copy.deepcopy(self.fact)
        fact["axiom_footprint"] = []
        errors = self.errors_for(fact)
        self.assertTrue(
            any("axiom_footprint []" in e for e in errors),
            f"expected an empty-footprint rejection, got {errors!r}",
        )

    def test_a_missing_import_route_assumption_is_refused(self) -> None:
        # Deliberately ONE assertion and ONE dropped assumption: the mutation
        # harness counts each subTest failure as a separate death, and this
        # suite's contract is that deleting the guard kills exactly one test.
        fact = copy.deepcopy(self.fact)
        fact["axiom_footprint"] = [
            a for a in MODULE.IMPORT_ROUTE_ASSUMPTIONS
            if a != "axeyum-lean-import-wire-translation"
        ]
        errors = self.errors_for(fact)
        self.assertTrue(
            any("import-route assumption" in e for e in errors),
            f"expected a missing-assumption rejection, got {errors!r}",
        )

    def test_a_kernel_measured_axiom_beside_the_assumptions_is_accepted(self) -> None:
        # The Mathlib-shaped case: `Kernel::axiom_footprint` names are ADDED to
        # the three assumptions, never substituted for them. Measured for
        # `intermediate_value_Icc`, eight kernel names; the six-name
        # `Classical.em` closure is used here because it is the one this lane
        # actually composed over.
        fact = copy.deepcopy(self.fact)
        fact["axiom_footprint"] = list(MODULE.IMPORT_ROUTE_ASSUMPTIONS) + [
            "Classical.choice", "Quot", "Quot.lift", "Quot.mk", "Quot.sound", "propext",
        ]
        self.assertEqual(self.errors_for(fact), [])

    def test_missing_prior_art_is_refused_on_the_composed_route(self) -> None:
        # Rule 3. The proof term is partly ours and partly not; a composed
        # theorem that reads as wholly local is the failure the import route
        # exists to prevent.
        fact = copy.deepcopy(self.fact)
        del fact["provenance"]["prior_art"]
        errors = self.errors_for(fact)
        self.assertTrue(
            any("prior_art" in e for e in errors),
            f"expected a prior_art rejection, got {errors!r}",
        )

    def test_prior_art_is_still_required_on_the_plain_imported_route(self) -> None:
        # The composed rule is enforced by its OWN branch beside the imported
        # one, rather than by widening that branch's route set. This asserts the
        # original case survived the change -- a refactor that folded the two
        # together and then narrowed would leave seven committed imports
        # unguarded, and a shared branch could not tell a control which rule it
        # had deleted.
        fact = json.loads(IMPORTED_FACT.read_text(encoding="utf-8"))
        del fact["provenance"]["prior_art"]
        errors = MODULE.validate_one(IMPORTED_FACT, fact, {fact["id"]})
        self.assertTrue(
            any("prior_art" in e for e in errors),
            f"expected a prior_art rejection on the imported route, got {errors!r}",
        )


class ComposedRouteTraceabilityTests(unittest.TestCase):
    """ADR-1664 rule 4: a composed fact must name WHICH import it rests on.

    Cross-fact, so it cannot live in `validate_one` -- deciding whether an edge
    points at an import needs the other fact's `proof_route`, and `validate_one`
    is handed only the set of known ids.
    """

    def setUp(self) -> None:
        self.imported = json.loads(IMPORTED_FACT.read_text(encoding="utf-8"))
        self.composed = composed_fixture()

    def by_id(self, composed: dict) -> dict:
        return {self.imported["id"]: self.imported, composed["id"]: composed}

    def test_a_composed_fact_citing_an_import_is_accepted(self) -> None:
        self.assertEqual(
            MODULE.validate_composed_route_traceability(self.by_id(self.composed)), []
        )

    def test_a_composed_fact_citing_no_import_is_refused(self) -> None:
        # Deliberately ONE assertion (see the note on the assumption guard):
        # deleting the guard must kill exactly one test.
        composed = copy.deepcopy(self.composed)
        composed["depends_on"] = []
        errors = MODULE.validate_composed_route_traceability(self.by_id(composed))
        self.assertTrue(
            any("depends_on is a fact on" in e for e in errors),
            f"expected a traceability rejection, got {errors!r}",
        )

    def test_the_predicate_distinguishes_an_import_edge_from_any_other_edge(self) -> None:
        # Exercises `depends_on_an_import` DIRECTLY, not through
        # `validate_composed_route_traceability`, so this test's outcome is
        # independent of the call site the mutation control deletes -- the same
        # arrangement the `grep -q` and `grep \t` guards above use.
        #
        # The rule is "cites an IMPORT", not "cites anything": a composed fact
        # whose only edge is to another originated theorem is exactly the case a
        # naive non-empty-depends_on check would wave through.
        by_id = {
            "F:an-import": {"proof_route": "imported-kernel-lean"},
            "F:originated": {"proof_route": "kernel-lean"},
            "F:smt": {"proof_route": "smt-term-level"},
        }
        self.assertTrue(
            MODULE.depends_on_an_import({"depends_on": ["F:an-import"]}, by_id)
        )
        self.assertTrue(
            MODULE.depends_on_an_import(
                {"depends_on": ["F:originated", "F:an-import"]}, by_id
            )
        )
        for edges in ([], ["F:originated"], ["F:smt"], ["F:originated", "F:smt"],
                      ["F:not-a-known-id"]):
            with self.subTest(edges=edges):
                self.assertFalse(
                    MODULE.depends_on_an_import({"depends_on": edges}, by_id)
                )

    def test_a_non_composed_fact_is_never_subject_to_the_rule(self) -> None:
        # The imported fact itself has an empty `depends_on`; the rule must not
        # reach it, or every import in the ledger would fail this gate.
        self.assertEqual(
            MODULE.validate_composed_route_traceability(
                {self.imported["id"]: self.imported}
            ),
            [],
        )


if __name__ == "__main__":
    unittest.main()
