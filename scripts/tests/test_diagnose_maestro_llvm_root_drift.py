from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/diagnose-maestro-llvm-root-drift.py"
SPEC = importlib.util.spec_from_file_location("diagnose_maestro_llvm_root_drift", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def test_committed_diagnostic_registration_and_inputs_validate() -> None:
    registration = json.loads(MODULE.DEFAULT_REGISTRATION.read_text(encoding="utf-8"))
    MODULE.validate_registration(registration)
    capture = MODULE.validate_registered_inputs(registration)
    assert capture["upstream"]["commit"] == "650a3f62c386d113b4cbbc11645d945d57620cbb"


def test_changed_line_buckets_are_total_and_stable() -> None:
    cases = {
        b"; ModuleID = '/tmp/a'\n": "module_source_identity",
        b"source_filename = \"x\"\n": "module_source_identity",
        b"module asm \"x\"\n": "target_module_assembly",
        b"define i8 @f() {\n": "global_function_comdat_identity",
        b"attributes #1 = { nounwind }\n": "attribute",
        b"!1 = !{i32 1}\n": "metadata",
        b"  %x = add i8 1, 2\n": "function_body_or_terminator",
        b"; comment\n": "comment_or_whitespace",
        b"unexpected top-level text\n": "other",
    }
    assert {line: MODULE.classify_changed_line(line) for line in cases} == cases


def test_complete_diff_analysis_counts_every_changed_line(tmp_path: Path) -> None:
    diff = tmp_path / "complete.diff"
    diff.write_bytes(
        b"--- a\n+++ b\n@@ -1,2 +1,2 @@\n"
        b"-; ModuleID = '/root-a/x'\n+; ModuleID = '/root-b/x'\n"
        b"-  %x = add i8 1, 2\n+  %x = add i8 1, 3\n"
    )
    report = MODULE.analyze_diff(diff, [Path("/root-a"), Path("/root-b")])
    assert report["hunks"] == 1
    assert report["added_lines"] == 2
    assert report["removed_lines"] == 2
    assert report["classified_lines"] == 4
    assert report["bucket_counts"] == {
        "function_body_or_terminator": 2,
        "module_source_identity": 2,
    }
    assert report["root_path_occurrences"] == [1, 1]


def test_selected_symbol_discovery_requires_comments_and_one_definition() -> None:
    module = b""
    for name, symbol in (
        ("major", b"_ZN6kernel6device2id5major17h0123456789abcdefE"),
        ("minor", b"_ZN6kernel6device2id5minor17h0123456789abcdefE"),
        ("makedev", b"_ZN6kernel6device2id7makedev17h0123456789abcdefE"),
    ):
        module += b"; kernel::device::id::" + name.encode() + b"\n"
        module += b"define i8 @" + symbol + b"() { ret i8 0 }\n"
    found = MODULE.discover_symbols(module)
    assert set(found) == {"major", "minor", "makedev"}
    assert found["major"].endswith("h0123456789abcdefE")
