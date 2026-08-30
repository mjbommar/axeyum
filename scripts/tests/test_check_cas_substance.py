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


class GateHarness(unittest.TestCase):
    """Writes a fixture ledger to a temp root and runs the gate over it."""

    def run_gate(self, facts: list[dict], certificates: dict[str, dict] | None = None):
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

            buffer = io.StringIO()
            with contextlib.redirect_stdout(buffer):
                status = module.main(["--facts-root", str(root)])
            return status, buffer.getvalue()

    def assertRefused(self, facts, certificates=None, because: str = ""):
        status, output = self.run_gate(facts, certificates)
        self.assertEqual(status, 1, f"expected refusal; got exit 0 with:\n{output}")
        if because:
            self.assertIn(because, output)
        return output

    def assertAccepted(self, facts, certificates=None):
        status, output = self.run_gate(facts, certificates)
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
