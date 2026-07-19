import importlib.util
import unittest
from pathlib import Path


SCRIPT = (
    Path(__file__).resolve().parents[1]
    / "analyze-glaurung-symbolic-cve-frontend-surface.py"
)
SPEC = importlib.util.spec_from_file_location(
    "analyze_glaurung_symbolic_cve_frontend_surface", SCRIPT
)
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)


MODULE_IR = r'''
target triple = "aarch64-unknown-linux-gnu"
@board = internal global [4 x ptr] zeroinitializer
@counter = external global i32

declare i32 @external_helper(ptr)
declare void @llvm.lifetime.start.p0(i64, ptr nocapture)

define hidden i64 @entry(ptr %p, i32 %cmd, i64 %arg) {
entry:
  %slot = getelementptr inbounds [4 x ptr], ptr @board, i64 0, i64 %arg
  %value = load ptr, ptr %slot, align 8
  %ok = icmp ne ptr %value, null
  br i1 %ok, label %take, label %done

take:
  call void @llvm.lifetime.start.p0(i64 8, ptr %p)
  %r = call i32 @helper(
    ptr %value,
    i32 %cmd)
  store i32 %r, ptr @counter, align 4
  br label %done

done:
  %out = phi i64 [ -1, %entry ], [ 0, %take ]
  ret i64 %out
}

define internal i32 @helper(ptr %p, i32 %x) {
entry:
  %a = call i32 @external_helper(ptr %p)
  %b = add i32 %a, %x
  ret i32 %b
}
'''


class FrontendSurfaceAnalysisTests(unittest.TestCase):
    def test_normalizes_only_ephemeral_module_id(self) -> None:
        first = b"; ModuleID = '/tmp/one/recursive.ll'\nsource_filename = \"fixed.c\"\n"
        second = b"; ModuleID = '/tmp/two/recursive.ll'\nsource_filename = \"fixed.c\"\n"
        self.assertEqual(
            MODULE.normalize_stripped_ir(first), MODULE.normalize_stripped_ir(second)
        )
        self.assertIn(
            b"source_filename = \"fixed.c\"", MODULE.normalize_stripped_ir(first)
        )

    def test_parses_defined_reachable_functions_and_instruction_counts(self) -> None:
        surface = MODULE.parse_ir_surface(MODULE_IR)
        self.assertEqual(surface["target_triple"], "aarch64-unknown-linux-gnu")
        self.assertEqual(surface["defined_functions"], ["entry", "helper"])
        self.assertEqual(surface["function_count"], 2)
        self.assertEqual(surface["instruction_counts"]["call"], 3)
        self.assertEqual(surface["instruction_counts"]["br"], 2)
        self.assertEqual(surface["instruction_counts"]["getelementptr"], 1)
        self.assertEqual(surface["instruction_counts"]["load"], 1)
        self.assertEqual(surface["instruction_counts"]["store"], 1)
        self.assertEqual(surface["instruction_counts"]["ret"], 2)
        self.assertNotIn("ptr", surface["instruction_counts"])

    def test_classifies_defined_external_intrinsic_and_indirect_calls(self) -> None:
        value = MODULE_IR.replace(
            "%b = add i32 %a, %x", "%b = call i32 %fn(i32 %a)"
        )
        surface = MODULE.parse_ir_surface(value)
        self.assertEqual(surface["defined_direct_calls"], {"helper": 1})
        self.assertEqual(
            surface["external_direct_calls"], {"external_helper": 1}
        )
        self.assertEqual(
            surface["intrinsic_calls"], {"llvm.lifetime.start.p0": 1}
        )
        self.assertEqual(surface["indirect_calls"], 1)

    def test_records_only_data_global_references(self) -> None:
        surface = MODULE.parse_ir_surface(MODULE_IR)
        self.assertEqual(surface["defined_globals"], ["board", "counter"])
        self.assertEqual(surface["referenced_globals"], {"board": 1, "counter": 1})
        self.assertNotIn("helper", surface["referenced_globals"])

    def test_records_memory_control_and_pointer_surface(self) -> None:
        surface = MODULE.parse_ir_surface(MODULE_IR)
        self.assertEqual(
            surface["memory_instruction_counts"],
            {"getelementptr": 1, "load": 1, "store": 1},
        )
        self.assertEqual(
            surface["terminator_counts"], {"br": 2, "ret": 2}
        )
        self.assertEqual(surface["pointer_parameter_functions"], ["entry", "helper"])
        self.assertEqual(surface["basic_blocks"], 4)

    def test_axeyum_reflector_blockers_are_explicit(self) -> None:
        surface = MODULE.parse_ir_surface(MODULE_IR)
        blockers = surface["axeyum_reflector_blockers"]
        self.assertEqual(blockers["pointer_parameter_functions"], ["entry", "helper"])
        self.assertEqual(
            blockers["unsupported_instruction_counts"],
            {"call": 3, "getelementptr": 1, "load": 1, "store": 1},
        )
        self.assertEqual(blockers["unsupported_external_calls"], ["external_helper"])
        self.assertEqual(
            blockers["unsupported_intrinsics"], ["llvm.lifetime.start.p0"]
        )

    def test_rejects_malformed_or_empty_function_ir(self) -> None:
        for text, message in [
            ("target triple = \"aarch64\"\n", "no defined functions"),
            ("define i32 @f() {\n  %x = mystery i32 0\n", "unterminated"),
        ]:
            with self.subTest(message=message), self.assertRaisesRegex(
                ValueError, message
            ):
                MODULE.parse_ir_surface(text)

        with self.assertRaisesRegex(ValueError, "ModuleID"):
            MODULE.normalize_stripped_ir(b"source_filename = \"missing.c\"\n")

    def test_rejects_duplicate_function_definition(self) -> None:
        duplicate = MODULE_IR + "\ndefine i32 @entry() { ret i32 0 }\n"
        with self.assertRaisesRegex(ValueError, "duplicate function"):
            MODULE.parse_ir_surface(duplicate)

    def test_normalizes_quoted_llvm_names(self) -> None:
        text = r'''
target triple = "aarch64-unknown-linux-gnu"
@"global name" = global i8 0
declare void @"external name"()
define void @"entry name"() {
entry:
  call void @"external name"()
  store i8 1, ptr @"global name"
  ret void
}
'''
        surface = MODULE.parse_ir_surface(text)
        self.assertEqual(surface["defined_functions"], ["entry name"])
        self.assertEqual(surface["external_direct_calls"], {"external name": 1})
        self.assertEqual(surface["referenced_globals"], {"global name": 1})


if __name__ == "__main__":
    unittest.main()
