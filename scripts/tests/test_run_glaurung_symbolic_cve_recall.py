import importlib.util
import pathlib
import unittest


SCRIPT = (
    pathlib.Path(__file__).resolve().parents[1]
    / "run-glaurung-symbolic-cve-recall.py"
)
SPEC = importlib.util.spec_from_file_location("run_symbolic_cve_recall", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def report(*, kind: str, taint: list[str], witness: dict[str, str]) -> dict:
    return {
        "schema": MODULE.SIDE_SCHEMA,
        "object": "/tmp/object.o",
        "handler": "handler",
        "solver": "axeyum-qfbv",
        "max_states": 4096,
        "command": None,
        "environment": "generic",
        "admitted": True,
        "execution_acceptable": True,
        "error": None,
        "external_calls": 1,
        "modeled_external_calls": 1,
        "local_calls": 0,
        "modeled_local_calls": 0,
        "sinks": [
            {
                "va": 0x1000,
                "kind": kind,
                "severity": "constrained",
                "tainted_by": taint,
                "witness": witness,
            }
        ],
        "exploration": {"runs": 1, "completed": 1},
        "path_stops": {"returned": 1, "unmodeled_calls": {}},
        "concretization": {"policy": "glaurung-any-address-v1"},
    }


class SymbolicCveRecallTests(unittest.TestCase):
    def test_accepts_pci_signed_out_of_range_witness(self) -> None:
        sink = report(
            kind="OutOfBoundsIndex", taint=["IoctlArg"], witness={"1": "0xffffffff"}
        )["sinks"][0]
        MODULE.validate_target_sink(
            "CVE-2025-40117",
            sink,
            {"kind": "OutOfBoundsIndex", "tainted_by": ["IoctlArg"]},
        )

    def test_rejects_pci_in_range_witness(self) -> None:
        sink = report(
            kind="OutOfBoundsIndex", taint=["IoctlArg"], witness={"1": "0x5"}
        )["sinks"][0]
        with self.assertRaisesRegex(ValueError, "does not violate"):
            MODULE.validate_target_sink(
                "CVE-2025-40117",
                sink,
                {"kind": "OutOfBoundsIndex", "tainted_by": ["IoctlArg"]},
            )

    def test_applicom_requires_command_six(self) -> None:
        sink = report(kind="NullDeref", taint=["IoctlCmd"], witness={"0": "0x5"})[
            "sinks"
        ][0]
        with self.assertRaisesRegex(ValueError, "command 6"):
            MODULE.validate_target_sink(
                "CVE-2025-68797",
                sink,
                {"kind": "NullDeref", "tainted_by": ["IoctlCmd"]},
            )

    def test_pair_requires_ordinary_embedded_identity(self) -> None:
        vulnerable = report(
            kind="NullDeref", taint=["IoctlCmd"], witness={"0": "0x6"}
        )
        fixed = {**vulnerable, "sinks": []}
        cells = {
            "vulnerable/ordinary": vulnerable,
            "vulnerable/embedded": {**vulnerable, "max_states": 2048},
            "fixed/ordinary": fixed,
            "fixed/embedded": fixed,
        }
        with self.assertRaisesRegex(ValueError, "ordinary and embedded"):
            MODULE.evaluate_pair(
                "CVE-2025-68797",
                {
                    "handler": "handler",
                    "environment": "generic",
                    "expected_sink": {
                        "kind": "NullDeref",
                        "tainted_by": ["IoctlCmd"],
                    },
                },
                cells,
            )

    def test_pair_requires_fixed_side_clean(self) -> None:
        vulnerable = report(
            kind="NullDeref", taint=["IoctlCmd"], witness={"0": "0x6"}
        )
        cells = {
            "vulnerable/ordinary": vulnerable,
            "vulnerable/embedded": vulnerable,
            "fixed/ordinary": vulnerable,
            "fixed/embedded": vulnerable,
        }
        with self.assertRaisesRegex(ValueError, "fixed side emitted"):
            MODULE.evaluate_pair(
                "CVE-2025-68797",
                {
                    "handler": "handler",
                    "environment": "generic",
                    "expected_sink": {
                        "kind": "NullDeref",
                        "tainted_by": ["IoctlCmd"],
                    },
                },
                cells,
            )

    def test_normalization_excludes_only_object_path(self) -> None:
        first = report(kind="NullDeref", taint=["IoctlCmd"], witness={"0": "0x6"})
        second = {**first, "object": "/different/path.o"}
        self.assertEqual(MODULE.normalized_side(first), MODULE.normalized_side(second))


if __name__ == "__main__":
    unittest.main()
