"""Controls for `scripts/check-cas-substance.py` and `scripts/cas_substance.py`.

One test per guard, each written so that every OTHER field of its fixture is
valid -- otherwise a mutation would kill several tests at once and the kill set
would not tell you which guard the test actually measures.

Registered in `scripts/tests/mutation_controls.py` under `cas-substance` (the
gate) and `cas-substance-derivation` (the derivation core), so each guard is
deleted and the harness checks that exactly one test dies.  The harness
`copytree`s to a scratch root and `py_compile`s each subject, which is what
keeps a hand-rolled loop's stale-`__pycache__` trap out of this: mutants here
are equal-size by construction and would otherwise re-run the previous mutant's
bytecode.
"""

from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
GATE = REPO_ROOT / "scripts" / "check-cas-substance.py"


def _load_gate():
    spec = importlib.util.spec_from_file_location("check_cas_substance", GATE)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def poly(*monomials) -> dict:
    """A polynomial whose terms are the given monomials, each with coefficient 1."""
    return {
        "terms": [
            {"monomial": list(m), "coefficient": [1, 1]} for m in monomials
        ]
    }


ONE = {"terms": [{"monomial": [], "coefficient": [1, 1]}]}
ZERO: dict = {"terms": []}

# A conclusion equal to its single generator, under the constant cofactor 1:
# the Thales shape, and the whole reason this gate exists.
REFL_CERT = {
    "id": "fixture-refl",
    "coordinates": ["ax", "bx"],
    "generators": [poly([["ax", 1]], [["bx", 1]])],
    "conclusions": [
        {
            "id": "c",
            "poly": poly([["ax", 1]], [["bx", 1]]),
            "cofactors": [ONE],
        }
    ],
}

# Two generators both carrying nonzero cofactors: monomials from distinct
# generators must cancel, which is what makes an identity specific.
COMBINATION_CERT = {
    "id": "fixture-combination",
    "coordinates": ["ax", "bx"],
    "generators": [poly([["ax", 1]]), poly([["bx", 1]])],
    "conclusions": [
        {
            "id": "c",
            "poly": poly([["ax", 1]], [["bx", 1]]),
            "cofactors": [ONE, ONE],
        }
    ],
}

EMPTY_CERT = {
    "id": "fixture-empty",
    "coordinates": [],
    "generators": [],
    "conclusions": [{"id": "c", "poly": ZERO, "cofactors": []}],
}

KERNEL_CHECKER = "cargo test -p axeyum-lean-kernel --lib fixture -- --exact"
CAS_CHECKER = "cargo test -p axeyum-cas --lib fixture -- --exact"


def fact(
    fid: str = "F:fixture",
    *,
    substance: dict | None,
    statement: str = "(assert (= (+ a b) (* 2 (+ a b))))",
    footprint: list[str] | None = None,
    checker: str = KERNEL_CHECKER,
) -> dict:
    body = {
        "schema_version": 1,
        "id": fid,
        "proof_route": "cas-certificate",
        "formal": {"language": "cas-term", "statement": statement},
        "axiom_footprint": footprint if footprint is not None else ["k.assumption: prose"],
        "evidence": [{"id": "e", "checker_command": checker}],
    }
    if substance is not None:
        body["cas_substance"] = substance
    return body


# `ratchet=ABSENT` writes no ratchet file at all, which is a different state
# from an empty one and is refused by a different guard.
ABSENT = "<no ratchet file>"


class GateHarness(unittest.TestCase):
    """Writes a fixture ledger to a temp root and runs the gate over it."""

    def run_gate(
        self,
        facts: list[dict],
        certificates: dict[str, dict] | None = None,
        ratchet: list[str] | None = None,
        min_reconstructed: int = 0,
    ):
        """`ratchet=None` means "derive the floor from this fixture", which is
        what every substance guard wants: it isolates the guard under test from
        the ratchet entirely. A guard that needs the RATCHET to fire passes the
        rows explicitly."""
        module = _load_gate()
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            facts_dir = root / "artifacts" / "facts"
            facts_dir.mkdir(parents=True)
            for index, f in enumerate(facts):
                (facts_dir / f"F-{index}.json").write_text(json.dumps(f, indent=2))
            certs_dir = root / "artifacts" / "geometry-certificates"
            certs_dir.mkdir(parents=True)
            for name, cert in (certificates or {}).items():
                (certs_dir / name).write_text(json.dumps(cert, indent=2))
            import io
            import contextlib

            ratchet_path = root / "ratchet.tsv"
            buffer = io.StringIO()
            # `--min-reconstructed 0`: the absolute floor is a property of the
            # REAL ledger, not of a three-fact fixture. The two controls that
            # exercise it pass their own value.
            argv = ["--facts-root", str(root), "--ratchet", str(ratchet_path),
                    "--min-reconstructed", str(min_reconstructed)]
            # stderr too: the ratchet refusals print there, and a control that
            # asserted only on stdout would pass on an EMPTY message.
            with contextlib.redirect_stdout(buffer), contextlib.redirect_stderr(buffer):
                if ratchet is None:
                    module.main([*argv, "--update"])
                elif ratchet == ABSENT:
                    pass  # leave no file at all
                else:
                    ratchet_path.write_text(
                        "# fixture floor\n" + "".join(r + "\n" for r in ratchet)
                    )
                buffer.truncate(0)
                buffer.seek(0)
                status = module.main(argv)
            return status, buffer.getvalue()

    def assertRefused(self, facts, certificates=None, because: str = "", ratchet=None,
                      min_reconstructed: int = 0):
        status, output = self.run_gate(facts, certificates, ratchet, min_reconstructed)
        self.assertEqual(status, 1, f"expected refusal; got exit 0 with:\n{output}")
        if because:
            self.assertIn(because, output)
        return output

    def assertAccepted(self, facts, certificates=None, ratchet=None,
                       min_reconstructed: int = 0):
        status, output = self.run_gate(facts, certificates, ratchet, min_reconstructed)
        self.assertEqual(status, 0, f"expected acceptance; got:\n{output}")
        return output


CERTS = {
    "refl.json": REFL_CERT,
    "combination.json": COMBINATION_CERT,
    "empty.json": EMPTY_CERT,
}
REFL_PATH = "artifacts/geometry-certificates/refl.json"
COMBINATION_PATH = "artifacts/geometry-certificates/combination.json"
EMPTY_PATH = "artifacts/geometry-certificates/empty.json"

GOOD_COMBINATION = {"shape": "combination", "certificate": COMBINATION_PATH}
GOOD_REFL = {
    "shape": "refl",
    "certificate": REFL_PATH,
    "disclosure": "the obligation is X = 1*X and holds of every polynomial",
    "disclosure_axiom_key": "cas.refl-shaped",
}
REFL_FOOTPRINT = ["cas.refl-shaped: spelled out here too"]


class PositiveControls(GateHarness):
    """The gate must ACCEPT the two honest shapes, or every refusal below is
    consistent with a gate that simply always fails."""

    def test_a_derived_combination_is_accepted(self):
        self.assertAccepted([fact(substance=GOOD_COMBINATION)], CERTS)

    def test_a_disclosed_refl_is_accepted_not_excluded(self):
        # Thales' outcome: weaker than it looks, registered, disclosed.
        self.assertAccepted(
            [fact(substance=GOOD_REFL, footprint=REFL_FOOTPRINT)], CERTS
        )

    def test_a_cas_internal_fact_without_a_block_is_not_required_to_have_one(self):
        self.assertAccepted([fact(substance=None, checker=CAS_CHECKER)], CERTS)


class GateGuards(GateHarness):
    def test_g1_kernel_reconstructed_without_a_substance_block(self):
        self.assertRefused(
            [fact(substance=None)], CERTS, because="carries no `cas_substance` block"
        )

    def test_g2_shape_outside_the_enumeration(self):
        self.assertRefused(
            [fact(substance={"shape": "profound", "certificate": None,
                             "derivation_declined_reason": "r"})],
            CERTS,
            because="is not one of",
        )

    def test_g3_no_certificate_key_at_all(self):
        self.assertRefused(
            [fact(substance={"shape": "combination"})],
            CERTS,
            because="has no `certificate` key",
        )

    def test_g4_certificate_path_that_does_not_resolve(self):
        self.assertRefused(
            [fact(substance={"shape": "combination",
                             "certificate": "artifacts/geometry-certificates/nope.json"})],
            CERTS,
            because="is not a file",
        )

    def test_g5_declared_shape_disagrees_with_the_certificate(self):
        # The half a lane cannot talk around: the certificate is a combination,
        # the fact says refl, and the number comes from the CAS's own output.
        self.assertRefused(
            [fact(substance={**GOOD_REFL, "certificate": COMBINATION_PATH},
                  footprint=REFL_FOOTPRINT)],
            CERTS,
            because="derives 'combination'",
        )

    def test_g6_null_certificate_without_a_declined_reason(self):
        self.assertRefused(
            [fact(substance={"shape": "evaluation", "certificate": None})],
            CERTS,
            because="`derivation_declined_reason` must say why",
        )

    def test_g7_refl_without_a_disclosure(self):
        self.assertRefused(
            [fact(substance={"shape": "refl", "certificate": REFL_PATH,
                             "disclosure_axiom_key": "cas.refl-shaped"},
                  footprint=REFL_FOOTPRINT)],
            CERTS,
            because="`cas_substance.disclosure` must say",
        )

    def test_g8_refl_without_a_disclosure_axiom_key(self):
        self.assertRefused(
            [fact(substance={"shape": "refl", "certificate": REFL_PATH,
                             "disclosure": "the obligation is X = 1*X"},
                  footprint=REFL_FOOTPRINT)],
            CERTS,
            because="requires `cas_substance.disclosure_axiom_key`",
        )

    def test_g9_disclosure_key_naming_no_axiom_footprint_entry(self):
        self.assertRefused(
            [fact(substance=GOOD_REFL, footprint=["some.other.key: prose"])],
            CERTS,
            because="names no entry",
        )

    def test_g10_an_empty_certificate_is_refused_outright(self):
        # Varignon: no coordinates, no generators, an already-empty conclusion.
        # The registering lane declined it by judgement; this is the mechanism.
        self.assertRefused(
            [fact(substance={"shape": "empty", "certificate": EMPTY_PATH,
                             "disclosure": "nothing to reconstruct",
                             "disclosure_axiom_key": "cas.refl-shaped"},
                  footprint=REFL_FOOTPRINT)],
            CERTS,
            because="nothing to reconstruct",
        )

    def test_g11_a_text_refl_statement_declared_as_a_combination(self):
        # Independent of any certificate: the fact's own statement is X = 1*X.
        self.assertRefused(
            [fact(substance={"shape": "identity", "certificate": None,
                             "derivation_declined_reason": "no artifact"},
                  statement="(assert (= (+ a b) (* 1 (+ a b))))")],
            CERTS,
            because="once multiplication by 1 is erased",
        )

    def test_g12_a_substance_block_on_a_cas_internal_fact(self):
        self.assertRefused(
            [fact(substance=GOOD_COMBINATION, checker=CAS_CHECKER)],
            CERTS,
            because="not kernel-reconstructed",
        )


class DerivationGuards(unittest.TestCase):
    """Controls for `scripts/cas_substance.py` itself."""

    def setUp(self):
        sys.path.insert(0, str(REPO_ROOT / "scripts"))
        import cas_substance

        self.core = cas_substance

    def test_d1_a_zero_cofactor_does_not_make_a_generator_active(self):
        # Padding a refl certificate with a zero cofactor must NOT promote it to
        # `combination` -- the kernel obligation is unchanged.
        padded = {
            "id": "padded",
            "coordinates": ["ax", "bx"],
            "generators": [poly([["ax", 1]], [["bx", 1]]), poly([["ax", 1]])],
            "conclusions": [
                {
                    "id": "c",
                    "poly": poly([["ax", 1]], [["bx", 1]]),
                    "cofactors": [ONE, ZERO],
                }
            ],
        }
        self.assertEqual(self.core.analyse_certificate(padded)["shape"], "refl")

    def test_d2_a_non_unit_constant_cofactor_is_scale_not_refl(self):
        two = {"terms": [{"monomial": [], "coefficient": [2, 1]}]}
        scaled = {
            "id": "scaled",
            "coordinates": ["ax"],
            "generators": [poly([["ax", 1]])],
            "conclusions": [
                {"id": "c", "poly": poly([["ax", 1]]), "cofactors": [two]}
            ],
        }
        self.assertEqual(self.core.analyse_certificate(scaled)["shape"], "scale")

    def test_d3_a_conclusion_differing_from_its_generator_is_scale_not_refl(self):
        differing = {
            "id": "differing",
            "coordinates": ["ax", "bx"],
            "generators": [poly([["ax", 1]])],
            "conclusions": [
                {
                    "id": "c",
                    "poly": poly([["ax", 1]], [["bx", 1]]),
                    "cofactors": [ONE],
                }
            ],
        }
        self.assertEqual(self.core.analyse_certificate(differing)["shape"], "scale")

    def test_d4_a_certificate_is_only_as_strong_as_its_weakest_conclusion(self):
        mixed = {
            "id": "mixed",
            "coordinates": ["ax", "bx"],
            "generators": [poly([["ax", 1]], [["bx", 1]]), poly([["bx", 1]])],
            "conclusions": [
                {
                    "id": "strong",
                    "poly": poly([["ax", 1]], [["bx", 1]]),
                    "cofactors": [ONE, ONE],
                },
                {
                    # One generator, constant cofactor 1, conclusion identical
                    # to it -- refl. Deliberately NOT expressed with a zero
                    # cofactor, so this test measures weakest-wins and not the
                    # zero-cofactor rule that test_d1 owns.
                    "id": "weak",
                    "poly": poly([["ax", 1]], [["bx", 1]]),
                    "cofactors": [ONE],
                },
            ],
        }
        self.assertEqual(self.core.analyse_certificate(mixed)["shape"], "refl")

    def test_d5_an_unparseable_statement_yields_no_signal_never_clean(self):
        # None means "no signal". A gate reading it as False would silently stop
        # checking the three committed facts whose statements carry placeholders.
        self.assertIsNone(self.core.statement_is_refl_shaped("(assert (= a a)"))
        self.assertIsNone(self.core.statement_is_refl_shaped("(assert (= a a)))"))
        self.assertTrue(self.core.statement_is_refl_shaped("(assert (= a (* 1 a)))"))
        self.assertFalse(self.core.statement_is_refl_shaped("(assert (= a (* 2 a)))"))


class RatchetGuards(GateHarness):
    """The 2026-08-30 session audit's third survivor: the headline count was
    DERIVED but not DEFENDED.

    Measured that day, all three on the real ledger:

        strip a fact's kernel reconstruction AND its cas_substance block
            -> exit 0, "OK: 13 ..."
        strip the reconstruction but KEEP the block
            -> exit 1, G12 fires
        delete the fact file outright
            -> exit 0, "OK: 13 ..."

    So the gate caught an INCONSISTENT downgrade and passed a CONSISTENT one.
    A gate that reports a smaller number as success cannot notice deletion.
    """

    # The fixture's own id, so a ratchet row can name it.
    FID = "F:fixture"

    def rows(self, provenance="derived", discriminating="discriminating"):
        return [f"{self.FID}\t{provenance}\t{discriminating}"]

    def test_the_floor_holds_when_nothing_moved(self):
        """The positive control. Without it every refusal below is consistent
        with a ratchet that refuses everything."""
        out = self.assertAccepted(
            [fact(substance=GOOD_COMBINATION)], CERTS, ratchet=self.rows()
        )
        self.assertIn("ratchet floor 1, all held", out)

    def test_r1_a_ratcheted_fact_that_VANISHES_is_refused(self):
        """Deletion. The exact case that exited 0 with a smaller number."""
        self.assertRefused(
            [], CERTS,
            because="is not one now",
            ratchet=self.rows(),
        )

    def test_r1_a_ratcheted_fact_DOWNGRADED_to_cas_internal_is_refused(self):
        """A consistent downgrade: the checker stops naming the kernel package
        AND the block goes with it, so G12 has nothing to fire on."""
        self.assertRefused(
            [fact(substance=None, checker=CAS_CHECKER)], CERTS,
            because="is not one now",
            ratchet=self.rows(),
        )

    def test_r2_losing_a_CERTIFICATE_is_refused(self):
        """`derived` -> `declared`: the fact keeps a plausible shape and the
        gate quietly stops checking the half a lane cannot talk its way
        around."""
        self.assertRefused(
            [fact(substance={"shape": "combination", "certificate": None,
                             "derivation_declined_reason": "no artifact"})],
            CERTS,
            because="is now self-reported",
            ratchet=self.rows(provenance="derived"),
        )

    def test_r3_a_shape_going_NON_DISCRIMINATING_is_refused(self):
        """`combination` -> `refl`, fully disclosed so every substance rule
        still passes. Registration stays honest for a weak reconstruction;
        silently BECOMING weak does not."""
        self.assertRefused(
            [fact(substance=GOOD_REFL, footprint=REFL_FOOTPRINT)], CERTS,
            because="is now non-discriminating",
            ratchet=self.rows(discriminating="discriminating"),
        )

    def test_a_fact_going_the_OTHER_way_is_accepted(self):
        """Growth is free, and so is strengthening: a row recorded as
        non-discriminating that becomes discriminating must not fail. A ratchet
        that refuses improvement is a freeze."""
        self.assertAccepted(
            [fact(substance=GOOD_COMBINATION)], CERTS,
            ratchet=self.rows(discriminating="non-discriminating"),
        )

    def test_a_NEW_fact_absent_from_the_ratchet_is_accepted(self):
        """The floor constrains what was established, never what is new.
        Growth needs no edit here, which is what keeps the ratchet from
        becoming a tax on landing facts."""
        self.assertAccepted(
            [fact(substance=GOOD_COMBINATION)], CERTS, ratchet=["# nothing yet"]
        )

    def test_a_MISSING_ratchet_file_is_refused(self):
        """No file at all is the state the gate shipped in for its whole life,
        and it is the state in which a smaller headline reads as success."""
        self.assertRefused(
            [fact(substance=GOOD_COMBINATION)], CERTS,
            because="Without it this gate reports a SMALLER number as success",
            ratchet=ABSENT,
        )

    def test_a_TRIMMED_ratchet_is_refused_by_the_absolute_floor(self):
        """The per-fact rules alone have one hole, and it is the one that
        matters most: deleting a fact AND its ratchet row in one commit
        satisfies every one of them. The absolute floor is what makes that
        loud -- the shape `--expect-axioms 26` has elsewhere in this ledger."""
        self.assertRefused(
            [fact(substance=GOOD_COMBINATION)], CERTS,
            because="Trimming the ratchet and the ledger together",
            ratchet=["# emptied"],
            min_reconstructed=1,
        )

    def test_a_LEDGER_below_the_absolute_floor_is_refused(self):
        """The other half: the ratchet is intact and the LEDGER fell.

        The arrangement is deliberate. A ratchet of two rows against one live
        fact keeps the trimmed-ratchet rule satisfied (2 >= 2) so only this
        guard can fire, and the assertion is on the floor's OWN message rather
        than on a nonzero exit -- because R1 fires here too, and a
        status-only assertion would pass with this guard deleted."""
        self.assertRefused(
            [fact(substance=GOOD_COMBINATION)], CERTS,
            because="A smaller headline is a retreat to publish",
            ratchet=[*self.rows(), "F:other\tderived\tdiscriminating"],
            min_reconstructed=2,
        )

    def test_the_absolute_floor_is_satisfied_when_the_ledger_holds(self):
        """The negative control for both floor scenarios: at a floor the ledger
        meets, neither fires."""
        self.assertAccepted(
            [fact(substance=GOOD_COMBINATION)], CERTS,
            ratchet=self.rows(), min_reconstructed=1,
        )


class LiveLedger(unittest.TestCase):
    """The gate must be green on the committed ledger, and must SAY the two
    numbers this lane exists to publish."""

    def test_the_committed_ledger_passes_and_reports_the_split(self):
        result = subprocess.run(
            [sys.executable, str(GATE), "--report"],
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
        )
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("refl", result.stdout)
        self.assertIn("establishes nothing specific", result.stdout)
        self.assertIn("shape derived from a certificate:", result.stdout)


if __name__ == "__main__":
    unittest.main()
