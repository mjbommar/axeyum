#!/usr/bin/env python3
"""Controls for `scripts/check-lcg-raw-state.py`.

One test per guard, each built to die when its own guard is removed and no
other. Every test points the subject at a synthetic crate tree in a temp
directory, so the controls do not drift as generators land in the live tree.
"""

from __future__ import annotations

import importlib.util
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SUBJECT = ROOT / "scripts/check-lcg-raw-state.py"

RAW_STRUCT = """
struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }
}
"""

RAW_CLOSURE = """
fn run() {
    let mut state: u64 = 7;
    let mut next = || {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        state
    };
    let _ = next();
}
"""

RAW_FREE_FN = """
fn lcg(state: &mut u64) -> u64 {
    *state = state
        .wrapping_mul(6_364_136_223_846_793_005)
        .wrapping_add(1_442_695_040_888_963_407);
    *state
}
"""

MIXED = """
struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        let z = (self.0 ^ (self.0 >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        let z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }
}
"""

TOP_BITS = """
struct Lcg(u64);
impl Lcg {
    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0 >> 33
    }
}
"""


def load_subject():
    spec = importlib.util.spec_from_file_location("check_lcg_raw_state", SUBJECT)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


class Fixture:
    def __init__(self, tmp: pathlib.Path):
        self.root = tmp
        self.crates = tmp / "crates"
        self.crates.mkdir()
        self.baseline = tmp / "baseline.txt"
        self.baseline.write_text("", encoding="utf-8")

    def source(self, rel: str, text: str) -> None:
        path = self.crates / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def pin(self, entries: dict[str, int]) -> None:
        self.baseline.write_text(
            "".join(f"crates/{rel}:{n}\n" for rel, n in entries.items()), encoding="utf-8"
        )

    def run(self, subject) -> int:
        return subject.main(
            ["check", "--crates", str(self.crates), "--baseline", str(self.baseline)]
        )


class RawStateGate(unittest.TestCase):
    def setUp(self):
        self.subject = load_subject()
        self.tmp = tempfile.TemporaryDirectory()
        self.fx = Fixture(pathlib.Path(self.tmp.name))

    def tearDown(self):
        self.tmp.cleanup()

    def test_a_new_raw_state_site_fails(self):
        self.fx.source("a/src/lib.rs", RAW_STRUCT)
        self.assertEqual(self.fx.run(self.subject), 1)

    def test_a_pinned_site_at_its_pinned_count_passes(self):
        self.fx.source("a/src/lib.rs", RAW_STRUCT)
        self.fx.pin({"a/src/lib.rs": 1})
        self.assertEqual(self.fx.run(self.subject), 0)

    def test_a_grown_count_in_a_pinned_file_fails(self):
        self.fx.source("a/src/lib.rs", RAW_STRUCT + RAW_CLOSURE)
        self.fx.pin({"a/src/lib.rs": 1})
        self.assertEqual(self.fx.run(self.subject), 1)

    def test_a_stale_baseline_entry_fails(self):
        self.fx.source("a/src/lib.rs", MIXED)
        self.fx.pin({"a/src/lib.rs": 1})
        self.assertEqual(self.fx.run(self.subject), 1)

    def test_a_mixed_output_is_not_a_site(self):
        self.assertEqual(self.subject.raw_state_sites(MIXED), [])
        self.assertEqual(self.subject.raw_state_sites(TOP_BITS), [])

    def test_the_closure_and_free_function_shapes_are_sites(self):
        self.assertEqual(len(self.subject.raw_state_sites(RAW_CLOSURE)), 1)
        self.assertEqual(len(self.subject.raw_state_sites(RAW_FREE_FN)), 1)

    def test_scanning_zero_rust_files_fails(self):
        # An empty crates directory is a wrong path, not a clean tree.
        self.assertEqual(self.fx.run(self.subject), 1)


if __name__ == "__main__":
    unittest.main()
