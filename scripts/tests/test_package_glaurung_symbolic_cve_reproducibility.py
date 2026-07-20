import copy
import importlib.util
import pathlib
import tempfile
import unittest


SCRIPT = (
    pathlib.Path(__file__).resolve().parents[1]
    / "package-glaurung-symbolic-cve-reproducibility.py"
)
SPEC = importlib.util.spec_from_file_location("symbolic_cve_bundle", SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


def fixture() -> tuple[dict, dict[str, bytes]]:
    payloads = {
        f"CVE-{cve}/{side}/artifacts/{kind}.o": f"{cve}-{side}-{kind}".encode()
        for cve in ("ONE", "TWO")
        for side in MODULE.SIDES
        for kind in MODULE.OBJECT_KINDS
    }
    entries = [
        {"path": name, "sha256": MODULE.sha256(raw), "size": len(raw)}
        for name, raw in sorted(payloads.items())
    ]
    return (
        {
            "schema": MODULE.BUNDLE_SCHEMA,
            "registration_sha256": "a" * 64,
            "source_registration_sha256": "b" * 64,
            "materialization_sha256": "c" * 64,
            "objects": entries,
        },
        payloads,
    )


def binding(manifest: dict) -> dict:
    return {
        "registration_sha256": manifest["registration_sha256"],
        "source_registration_sha256": manifest["source_registration_sha256"],
        "materialization_sha256": manifest["materialization_sha256"],
        "object_hashes": {
            entry["path"]: entry["sha256"] for entry in manifest["objects"]
        },
    }


class SymbolicCveBundleTests(unittest.TestCase):
    def test_bundle_is_deterministic_and_valid(self) -> None:
        manifest, payloads = fixture()
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            first = root / "first.tar"
            second = root / "second.tar"
            first_hash = MODULE.write_bundle(first, manifest, payloads)
            second_hash = MODULE.write_bundle(second, manifest, payloads)
            self.assertEqual(first_hash, second_hash)
            self.assertEqual(first.read_bytes(), second.read_bytes())
            self.assertEqual(MODULE.read_bundle(first), (manifest, payloads))

    def test_manifest_tamper_is_rejected(self) -> None:
        manifest, payloads = fixture()
        changed = copy.deepcopy(manifest)
        changed["objects"][0]["sha256"] = "0" * 64
        with tempfile.TemporaryDirectory() as directory:
            bundle = pathlib.Path(directory) / "changed.tar"
            MODULE.write_bundle(bundle, changed, payloads)
            with self.assertRaisesRegex(ValueError, "object bytes differ"):
                MODULE.read_bundle(bundle)

    def test_unregistered_payload_is_rejected(self) -> None:
        manifest, payloads = fixture()
        payloads["extra.o"] = b"extra"
        with tempfile.TemporaryDirectory() as directory:
            bundle = pathlib.Path(directory) / "extra.tar"
            MODULE.write_bundle(bundle, manifest, payloads)
            with self.assertRaisesRegex(ValueError, "unregistered objects"):
                MODULE.read_bundle(bundle)

    def test_extract_requires_absent_output_and_registration_match(self) -> None:
        manifest, payloads = fixture()
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            bundle = root / "bundle.tar"
            output = root / "objects"
            MODULE.write_bundle(bundle, manifest, payloads)
            extracted = MODULE.extract_bundle(
                bundle,
                output,
                expected_binding=binding(manifest),
            )
            self.assertEqual(extracted, manifest)
            for name, raw in payloads.items():
                self.assertEqual((output / name).read_bytes(), raw)
            with self.assertRaisesRegex(ValueError, "output already exists"):
                MODULE.extract_bundle(
                    bundle,
                    output,
                    expected_binding=binding(manifest),
                )

    def test_extract_rejects_other_registration(self) -> None:
        manifest, payloads = fixture()
        with tempfile.TemporaryDirectory() as directory:
            root = pathlib.Path(directory)
            bundle = root / "bundle.tar"
            MODULE.write_bundle(bundle, manifest, payloads)
            with self.assertRaisesRegex(ValueError, "registration SHA-256 differs"):
                expected = binding(manifest)
                expected["registration_sha256"] = "f" * 64
                MODULE.extract_bundle(
                    bundle,
                    root / "objects",
                    expected_binding=expected,
                )

    def test_binding_rejects_other_registered_object_set(self) -> None:
        manifest, _ = fixture()
        expected = binding(manifest)
        expected["object_hashes"] = dict(expected["object_hashes"])
        first = next(iter(expected["object_hashes"]))
        expected["object_hashes"][first] = "f" * 64
        with self.assertRaisesRegex(ValueError, "object set differs"):
            MODULE.validate_binding(manifest, expected)


if __name__ == "__main__":
    unittest.main()
