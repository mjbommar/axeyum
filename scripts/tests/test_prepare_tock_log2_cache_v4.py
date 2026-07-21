import importlib.util
import os
import sys
import tempfile
import unittest
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/prepare-tock-log2-cache-v4.py"
SPEC = importlib.util.spec_from_file_location("prepare_tock_log2_cache_v4", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
PREPARE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = PREPARE
SPEC.loader.exec_module(PREPARE)


def capture_error(callable_):
    with unittest.TestCase().assertRaises(PREPARE.CaptureError) as raised:
        callable_()
    return raised.exception.stage, raised.exception.kind


class PrepareTockCacheV4Tests(unittest.TestCase):
    def test_hardlink_owner_is_lexicographic_and_creation_order_independent(self):
        results = []
        for creation_order in (("z", "a", "m"), ("m", "z", "a")):
            with tempfile.TemporaryDirectory() as raw:
                root = Path(raw)
                first = root / creation_order[0]
                first.write_bytes(b"shared payload\n")
                for name in creation_order[1:]:
                    os.link(first, root / name)
                inventory = PREPARE.inventory_cache(root)
                results.append(inventory)
                self.assertEqual(inventory["files"], 1)
                self.assertEqual(inventory["hardlinks"], 2)
                self.assertEqual(inventory["hardlink_groups"], 1)
                self.assertEqual(inventory["bytes"], len(b"shared payload\n"))
                self.assertEqual(
                    inventory["path_bytes"], 3 * len(b"shared payload\n")
                )
        self.assertEqual(results[0], results[1])

    def test_hardlink_topology_changes_inventory_identity(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            (root / "a").write_bytes(b"same\n")
            (root / "b").write_bytes(b"same\n")
            separate = PREPARE.inventory_cache(root)
            (root / "b").unlink()
            os.link(root / "a", root / "b")
            linked = PREPARE.inventory_cache(root)
            self.assertNotEqual(separate["sha256"], linked["sha256"])
            self.assertEqual(separate["hardlinks"], 0)
            self.assertEqual(linked["hardlinks"], 1)

    def test_link_outside_cache_is_rejected(self):
        with tempfile.TemporaryDirectory() as raw:
            parent = Path(raw)
            root = parent / "cache"
            root.mkdir()
            (root / "inside").write_bytes(b"payload\n")
            os.link(root / "inside", parent / "outside")
            self.assertEqual(
                capture_error(lambda: PREPARE.inventory_cache(root)),
                ("inventory", "hardlink_metadata"),
            )

    def test_single_file_and_inherited_special_cases_remain_stable(self):
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            (root / "file").write_bytes(b"payload\n")
            result = PREPARE.inventory_cache(root)
            self.assertEqual(result["schema"], PREPARE.INVENTORY_SCHEMA)
            self.assertEqual(result["files"], 1)
            self.assertEqual(result["hardlinks"], 0)
            self.assertEqual(result, PREPARE.inventory_cache(root))
            (root / "download.part").write_bytes(b"partial")
            self.assertEqual(
                capture_error(lambda: PREPARE.inventory_cache(root)),
                ("inventory", "temporary_path"),
            )


if __name__ == "__main__":
    unittest.main()
