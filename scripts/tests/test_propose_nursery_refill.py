"""Controls for scripts/propose-nursery-refill.py's headroom screens.

Two gaps found 2026-09-01 screening `Mathlib.Data.Nat.Log` for a draw, both
in the OVERSTATING direction -- a draw authored from either gap's number can
fail to clear the frontier floor after the fact:

  * `used_source_names()` read only the two nursery draw manifests. A
    Mathlib mirror already `proved` by DIRECT FLIP -- found already proved
    in the kernel, matched to `formal.statement`, status flipped with no new
    proof work -- never goes through a nursery draw, so it stayed an "unused
    candidate" here forever. Measured on `Mathlib.Data.Nat.Log`: 20 of 37
    reported survivors already had a `proved` fact this way.
  * Nothing here applied the generator's `HELD_OUT_CONSTRUCTIONS` screen at
    all, so a module whose every candidate mentions a construction that
    still guards a blind v1 held-out family (e.g. `Nat.sqrt`, guarding
    `natural-square-root`) could read as a "ready family" here while
    `select()` would refuse every one of its candidates once actually drawn.

`HeldOutConstructionsTests` also pins the *decision* recorded in ADR-1405:
`Nat.sqrt` must stay in the generator's `HELD_OUT_CONSTRUCTIONS` set. It is
the only construction left in that set and the only guard on the only
family in `nursery-v1.json` with any `held-out` row.
"""

from __future__ import annotations

import importlib.util
import json
import pathlib
import tempfile
import unittest

ROOT = pathlib.Path(__file__).resolve().parents[2]
SCRIPT = ROOT / "scripts/propose-nursery-refill.py"
GENERATOR = ROOT / "scripts/gen-autogenesis-nursery-refill.py"

_spec = importlib.util.spec_from_file_location("propose_nursery_refill", SCRIPT)
MODULE = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(MODULE)


class CataloguedSourceNamesTests(unittest.TestCase):
    """`catalogued_source_names()` / `used_source_names()` (the catalog fix)."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self._tmp.cleanup)
        work = pathlib.Path(self._tmp.name)

        catalog_path = work / "catalog.json"
        catalog_path.write_text(json.dumps({
            "facts": [
                {"source_name": "Nat.alreadyProved", "kind": "external-source"},
                {"source_name": "Nat.aMutation", "kind": "generated-mutation"},
            ],
        }))
        nursery_path = work / "nursery-v1.json"
        nursery_path.write_text(json.dumps({"entries": [
            {"source_name": "Nat.drawnDirectly"},
        ]}))
        extension_path = work / "nursery-v2-extension.json"
        extension_path.write_text(json.dumps({"entries": []}))

        self._orig = (MODULE.CATALOG, MODULE.NURSERY, MODULE.EXTENSION)
        MODULE.CATALOG = catalog_path
        MODULE.NURSERY = nursery_path
        MODULE.EXTENSION = extension_path
        self.addCleanup(self._restore)

    def _restore(self):
        MODULE.CATALOG, MODULE.NURSERY, MODULE.EXTENSION = self._orig

    def test_a_proved_fact_never_drawn_through_the_nursery_is_excluded(self):
        # This is exactly the Nat.log/Nat.clog shape found 2026-09-01: a name
        # with a fact-catalog entry (kind external-source) that never went
        # through a nursery draw at all. Without the fix this name is
        # invisible to used_source_names() and would be reported as fresh
        # headroom forever.
        names = MODULE.used_source_names()
        self.assertIn(
            "Nat.alreadyProved", names,
            "a catalogued external-source name must be excluded as headroom",
        )

    def test_a_generated_mutation_row_is_not_catalogued_as_a_mirror(self):
        # generated-mutation rows are negative controls, not mirrors of a
        # Mathlib source proposition; the real generator's select() does not
        # exclude candidates on them either (its catalogued set is filtered
        # to kind == "external-source"), so this proposer must match that,
        # not invent a wider rule of its own.
        names = MODULE.catalogued_source_names()
        self.assertNotIn("Nat.aMutation", names)

    def test_nursery_manifest_names_are_still_excluded(self):
        # The pre-existing behaviour the catalog fix must not regress.
        names = MODULE.used_source_names()
        self.assertIn("Nat.drawnDirectly", names)


class HeldOutConstructionsTests(unittest.TestCase):
    """`held_out_constructions()` and the decision it must keep enforcing.

    `Nat.sqrt` must never be dropped from the GENERATOR's
    `HELD_OUT_CONSTRUCTIONS`: `natural-square-root` is the only family in
    `nursery-v1.json` with any `held-out` row (verified in ADR-1405 against
    `entries[].partition` directly, not against this comment), so it is the
    last guard on the repository's only remaining v1 blind family.

    `Nat.log2` must ALSO never be dropped, for a DIFFERENT reason: dropping
    it alone (measured directly with `select()`, not reasoned about)
    displaces `Nat.not_exists_sq` from the already-drawn HELD-OUT family
    `natural-elementary-bounds`'s alphabetical top-10 slice in favour of
    `Nat.log2_two` -- an unrelated blind family, retroactively altered by a
    constant edit, exactly what ADR-0542's amendment discipline exists to
    prevent. `Nat.log`/`Nat.clog` were confirmed zero-diff and are the ones
    actually dropped.
    """

    def test_mirrors_the_generators_set(self):
        names = MODULE.held_out_constructions()
        self.assertEqual(names, {"Nat.log2", "Nat.sqrt"})

    def test_nat_sqrt_is_present(self):
        self.assertIn("Nat.sqrt", MODULE.held_out_constructions())

    def test_nat_log2_is_present(self):
        self.assertIn("Nat.log2", MODULE.held_out_constructions())

    def test_nat_log_and_clog_no_longer_need_to_be_held_out(self):
        # The corollary of the ADR-1405 decision: Nat.log/Nat.clog were
        # dropped because natural-logarithm no longer has any held-out row,
        # and because (unlike Nat.log2) dropping them is zero-diff against
        # every already-drawn family. Pinned here so a future re-add of
        # either is a deliberate, reviewed decision rather than an
        # accidental revert.
        names = MODULE.held_out_constructions()
        self.assertNotIn("Nat.log", names)
        self.assertNotIn("Nat.clog", names)


if __name__ == "__main__":
    unittest.main()
