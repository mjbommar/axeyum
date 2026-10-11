"""Public export workflow and independent checker rejection controls."""
from __future__ import annotations

import importlib.util
import os
from pathlib import Path

import pytest

EXAMPLE = Path(__file__).resolve().parents[1] / "examples" / "sat_certificate_export.py"
spec = importlib.util.spec_from_file_location("sat_certificate_export", EXAMPLE)
assert spec is not None and spec.loader is not None
example = importlib.util.module_from_spec(spec)
spec.loader.exec_module(example)


def test_exports_preserve_optional_lrat_and_source_boundary(tmp_path: Path) -> None:
    report = example.export(tmp_path / "export", None)
    assert report["source_translation"] == "not-independently-checked"
    assert report["checker_sha256"] is None
    assert set(report["routes"]) == {"boolean", "bit-vector", "raw-cnf"}
    assert report["routes"]["raw-cnf"]["lrat"] == "absent"
    for route in ("boolean", "bit-vector"):
        assert report["routes"][route]["lrat"] == "present"
        assert report["routes"][route]["external_cnf_check"] == "not-run"
        assert report["routes"][route]["source_binding"] == "replayed-with-trusted-bv-encoding"
        assert (tmp_path / "export" / route / "proof.lrat").stat().st_size > 0


@pytest.mark.skipif(not os.environ.get("AXEYUM_LRAT_CHECK"), reason="external LRAT checker not configured")
def test_external_empty_clause_controls(tmp_path: Path) -> None:
    checker = Path(os.environ["AXEYUM_LRAT_CHECK"]).resolve()
    report = example.export(tmp_path / "export", checker)
    for route in ("boolean", "bit-vector"):
        assert report["routes"][route]["external_cnf_check"] == "verified-with-two-rejection-controls"


def test_census_covers_public_exporters_and_replays_sat_models() -> None:
    from axeyum.solver import proofs

    rows = example.route_census()["term_exporters"]
    authority = {name for name in dir(proofs)
                 if name.startswith("export_") and name.endswith("_unsat_proof")}
    assert set(rows) == authority
    assert len(rows) == 6
    for row in rows.values():
        assert row["source_writer_round_trip"] == "parsed"
        assert row["verdict"] == "proved"
        assert row["lrat_recheck"] is True
        assert row["sat_control"] == "satisfiable"
        assert row["sat_model_verdict"] == "sat"
        assert row["sat_model_check"] == "verified"
        assert row["external_cnf_check"] == "not-run"
    assert rows["export_qf_lia_unsat_proof"]["int_width"] == 8
