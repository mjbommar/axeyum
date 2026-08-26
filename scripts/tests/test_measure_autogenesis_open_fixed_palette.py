from __future__ import annotations

import importlib.util
from pathlib import Path
import unittest


ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location(
    "open_fixed_palette",
    ROOT / "scripts/measure-autogenesis-open-fixed-palette.py",
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class OpenFixedPaletteTests(unittest.TestCase):
    def test_palette_is_sorted_unique_and_target_independent(self) -> None:
        self.assertEqual(tuple(sorted(set(MODULE.CANDIDATES))), MODULE.CANDIDATES)
        self.assertNotIn("Nat.fib_mono", MODULE.CANDIDATES)

    def test_capsule_name_is_stable(self) -> None:
        self.assertEqual(
            MODULE.capsule_path(Path("/packs"), "F:ml430-nat-foo-deadbeef"),
            Path("/packs/F-ml430-nat-foo-deadbeef.ndjson"),
        )


if __name__ == "__main__":
    unittest.main()
