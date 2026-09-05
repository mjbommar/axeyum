"""Controls for `scripts/gen-py-prelude-fields.py`'s path-qualified field fix.

The defect (ADR-1613's "unrelated live gap"): the field regex excluded `:`,
so a PATH-QUALIFIED registry field (`pub poly: poly::PolyNames`) never even
matched the field pattern -- the line was invisible before classification
ever ran, and the generator printed a plausible count and exited 0 while the
field's names were silently absent from the Python surface. Fixing it is not
"match `:` and then search for the bare type name globally": `PolyNames` is
defined in BOTH `complex/poly.rs` and `nat_prelude/polynomial_setoid.rs`, so a
global search is ambiguous exactly when a field is qualified in the first
place. The fix walks the real `mod`/`use` declarations, like rustc's own path
resolution, starting from the file that declares the field.

Each test here is a control for exactly one guard: `RealComplexPolyTests`
uses the actual repository source (the real two-files case), and
`SyntheticResolverTests` builds minimal fixtures for guards the current
source doesn't happen to exercise (an absolute `crate::` path, a `super`
path, an unresolvable module, an unresolvable type, a `use` cycle).
`MirrorCompletenessTests` is independent of `collect()`'s own field regex --
it uses a deliberately looser, differently-written scanner -- so it does not
share the blind spot that let the original bug through a byte-for-byte
`--check`.
"""

from __future__ import annotations

import importlib.util
import re
import sys
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

ROOT = Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts" / "gen-py-prelude-fields.py"
SPEC = importlib.util.spec_from_file_location("gen_py_prelude_fields", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules["gen_py_prelude_fields"] = MODULE
SPEC.loader.exec_module(MODULE)


def write(directory: Path, relative: str, text: str) -> Path:
    path = directory / relative
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    return path


class RealComplexPolyTests(unittest.TestCase):
    """The actual `ComplexPrelude.poly: poly::PolyNames` field on main."""

    def test_qualified_field_matches_the_field_regex(self) -> None:
        fields = dict(
            MODULE.struct_fields("ComplexPrelude", MODULE.KERNEL_SRC / "complex.rs")
        )
        self.assertEqual(fields.get("poly"), "poly::PolyNames")

    def test_poly_resolves_to_the_complex_module_not_nat_prelude(self) -> None:
        resolved = MODULE.resolve_qualified_type(
            "poly::PolyNames", MODULE.KERNEL_SRC / "complex.rs"
        )
        self.assertEqual(resolved, MODULE.KERNEL_SRC / "complex" / "poly.rs")
        self.assertNotEqual(
            resolved, MODULE.KERNEL_SRC / "nat_prelude" / "polynomial_setoid.rs"
        )

    def test_complex_prelude_collect_includes_all_21_poly_fields(self) -> None:
        scalars, _lists, _nested = MODULE.collect(
            "ComplexPrelude", MODULE.KERNEL_SRC / "complex.rs", "", "p"
        )
        names = {name for name, _access in scalars}
        self.assertIn("poly.poly_eval", names)
        self.assertIn("poly.factor_quotient_succ_eq", names)
        poly_names = {n for n in names if n.startswith("poly.")}
        self.assertEqual(len(poly_names), 21, poly_names)

    def test_generated_file_mirrors_the_poly_fields(self) -> None:
        text = MODULE.TARGET.read_text(encoding="utf-8")
        self.assertIn('"poly.poly_eval"', text)
        self.assertIn('"poly.factor_quotient_succ_eq"', text)


class SyntheticResolverTests(unittest.TestCase):
    """Guards the real source doesn't currently exercise, in a scratch tree."""

    def setUp(self) -> None:
        self._tmp = TemporaryDirectory()
        self.dir = Path(self._tmp.name)
        self.addCleanup(self._tmp.cleanup)
        self._orig_kernel_src = MODULE.KERNEL_SRC
        self._orig_cache = dict(MODULE._STRUCT_FILE)
        MODULE.KERNEL_SRC = self.dir
        MODULE._STRUCT_FILE.clear()
        self.addCleanup(self._restore)

    def _restore(self) -> None:
        MODULE.KERNEL_SRC = self._orig_kernel_src
        MODULE._STRUCT_FILE.clear()
        MODULE._STRUCT_FILE.update(self._orig_cache)

    def test_qualified_field_via_a_child_module_is_mirrored(self) -> None:
        write(
            self.dir,
            "outer.rs",
            "mod inner;\n\npub struct OuterPrelude {\n    pub reg: inner::InnerNames,\n}\n",
        )
        write(self.dir, "outer/inner.rs", "pub struct InnerNames {\n    pub x: NameId,\n}\n")
        scalars, _lists, _nested = MODULE.collect(
            "OuterPrelude", self.dir / "outer.rs", "", "p"
        )
        self.assertEqual(scalars, [("reg.x", "p.reg.x")])

    def test_two_files_same_struct_name_disambiguated_by_qualifier(self) -> None:
        # The exact shape of the real defect: `SharedNames` is defined TWICE,
        # and each qualified field must resolve to the copy its own module
        # path names -- never the other one, and never "whichever sorts
        # first" the way a bare global scan would.
        write(
            self.dir,
            "host.rs",
            "mod a;\nmod b;\n\n"
            "pub struct HostPrelude {\n"
            "    pub via_a: a::SharedNames,\n"
            "    pub via_b: b::SharedNames,\n"
            "}\n",
        )
        write(self.dir, "host/a.rs", "pub struct SharedNames {\n    pub from_a: NameId,\n}\n")
        write(self.dir, "host/b.rs", "pub struct SharedNames {\n    pub from_b: NameId,\n}\n")
        scalars, _lists, _nested = MODULE.collect("HostPrelude", self.dir / "host.rs", "", "p")
        self.assertEqual(
            scalars,
            [("via_a.from_a", "p.via_a.from_a"), ("via_b.from_b", "p.via_b.from_b")],
        )

    def test_bare_ambiguous_registry_name_still_errors(self) -> None:
        # Regression control: the qualifier-based resolution must not have
        # disabled the existing ambiguity guard for a field that is NOT
        # qualified and whose type name genuinely exists in two files.
        write(self.dir, "host/a.rs", "pub struct SharedNames {\n    pub from_a: NameId,\n}\n")
        write(self.dir, "host/b.rs", "pub struct SharedNames {\n    pub from_b: NameId,\n}\n")
        write(
            self.dir,
            "host2.rs",
            "pub struct Host2Prelude {\n    pub via_bare: SharedNames,\n}\n",
        )
        with self.assertRaises(SystemExit) as caught:
            MODULE.collect("Host2Prelude", self.dir / "host2.rs", "", "p")
        self.assertIn("defined in 2 files", str(caught.exception.code))

    def test_crate_absolute_path_resolves_via_reexport(self) -> None:
        # Mirrors the OTHER real example in ADR-1613: `pub sigma:
        # crate::SigmaNames`, resolved via `pub use sigma_prelude::SigmaNames;`
        # at the crate root.
        write(self.dir, "lib.rs", "mod deep;\n\npub use deep::LeafNames;\n")
        write(self.dir, "deep.rs", "pub struct LeafNames {\n    pub z: NameId,\n}\n")
        write(
            self.dir,
            "consumer.rs",
            "pub struct ConsumerPrelude {\n    pub leaf: crate::LeafNames,\n}\n",
        )
        scalars, _lists, _nested = MODULE.collect(
            "ConsumerPrelude", self.dir / "consumer.rs", "", "p"
        )
        self.assertEqual(scalars, [("leaf.z", "p.leaf.z")])

    def test_use_reexport_two_levels_deep_is_followed(self) -> None:
        write(
            self.dir,
            "hostc.rs",
            "mod hub;\n\npub struct HostCPrelude {\n    pub thing: hub::ThingNames,\n}\n",
        )
        write(self.dir, "hostc/hub.rs", "mod real;\n\npub use real::ThingNames;\n")
        write(self.dir, "hostc/hub/real.rs", "pub struct ThingNames {\n    pub w: NameId,\n}\n")
        scalars, _lists, _nested = MODULE.collect(
            "HostCPrelude", self.dir / "hostc.rs", "", "p"
        )
        self.assertEqual(scalars, [("thing.w", "p.thing.w")])

    def test_super_path_component_is_resolved(self) -> None:
        write(
            self.dir,
            "root.rs",
            "mod child;\n\npub struct RootNames {\n    pub v: NameId,\n}\n",
        )
        write(
            self.dir,
            "root/child.rs",
            "pub struct ChildPrelude {\n    pub back: super::RootNames,\n}\n",
        )
        scalars, _lists, _nested = MODULE.collect(
            "ChildPrelude", self.dir / "root" / "child.rs", "", "p"
        )
        self.assertEqual(scalars, [("back.v", "p.back.v")])

    def test_unresolvable_module_fails_loudly_naming_the_field(self) -> None:
        write(
            self.dir,
            "outer2.rs",
            "pub struct Outer2Prelude {\n    pub reg: missing::MissingNames,\n}\n",
        )
        with self.assertRaises(SystemExit) as caught:
            MODULE.collect("Outer2Prelude", self.dir / "outer2.rs", "", "p")
        message = str(caught.exception.code)
        self.assertIn("Outer2Prelude.reg", message)
        self.assertIn("missing", message)

    def test_unresolvable_type_in_a_resolved_module_fails_loudly(self) -> None:
        write(
            self.dir,
            "outer3.rs",
            "mod mod3;\n\npub struct Outer3Prelude {\n    pub reg: mod3::NoSuchNames,\n}\n",
        )
        write(
            self.dir,
            "outer3/mod3.rs",
            "pub struct SomethingElseNames {\n    pub y: NameId,\n}\n",
        )
        with self.assertRaises(SystemExit) as caught:
            MODULE.collect("Outer3Prelude", self.dir / "outer3.rs", "", "p")
        message = str(caught.exception.code)
        self.assertIn("Outer3Prelude.reg", message)
        self.assertIn("NoSuchNames", message)

    def test_use_cycle_is_refused_not_infinitely_recursed(self) -> None:
        write(
            self.dir,
            "x.rs",
            "mod y;\n\npub use y::FooNames;\n\n"
            "pub struct XPrelude {\n    pub f: y::FooNames,\n}\n",
        )
        write(self.dir, "x/y.rs", "pub use super::FooNames;\n")
        with self.assertRaises(SystemExit) as caught:
            MODULE.collect("XPrelude", self.dir / "x.rs", "", "p")
        self.assertIn("cycle", str(caught.exception.code))

    def test_plain_nameid_field_still_parses(self) -> None:
        write(self.dir, "plain.rs", "pub struct PlainPrelude {\n    pub x: NameId,\n}\n")
        self.assertEqual(
            MODULE.struct_fields("PlainPrelude", self.dir / "plain.rs"), [("x", "NameId")]
        )


class MirrorCompletenessTests(unittest.TestCase):
    """Every registry-typed field of every walked struct has a mirror entry.

    Deliberately independent of `collect()`: this regex doesn't classify a
    type at all, doesn't exclude `:`, and doesn't walk `mod`/`use`
    declarations. It just asks "does a `pub name:` line at the top of a
    walked struct have ANY trace in the generated file" -- as a bare scalar
    (`"name"`), a nested sub-package (`"name"` again, next to `Sub::`), or a
    flattened registry (`"name.<something>"`). That is loose enough that it
    would have caught the original bug (the field simply wasn't classified),
    without re-deriving the same classification the fix might itself get
    wrong.
    """

    LOOSE_FIELD = re.compile(r"^\s{4}pub ([a-z_][a-z0-9_]*):", re.MULTILINE)

    def test_every_top_level_field_of_every_walked_struct_is_mirrored(self) -> None:
        target_text = MODULE.TARGET.read_text(encoding="utf-8")
        checked = 0
        for struct, filename, _kind in MODULE.PRELUDES:
            path = MODULE.KERNEL_SRC / filename
            text = path.read_text(encoding="utf-8")
            start = text.index(f"pub struct {struct} {{")
            end = text.index("\n}\n", start)
            for name in self.LOOSE_FIELD.findall(text[start:end]):
                checked += 1
                mirrored = f'"{name}"' in target_text or f'"{name}.' in target_text
                self.assertTrue(mirrored, f"{struct}.{name} has no trace in {MODULE.TARGET}")
        # A loop that silently iterated zero fields would pass vacuously --
        # the exact "checker that cannot fail" CLAUDE.md warns about.
        self.assertGreater(checked, 1000, "scanned suspiciously few top-level fields")


if __name__ == "__main__":
    unittest.main()
