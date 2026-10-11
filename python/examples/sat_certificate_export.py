"""Export Boolean/BV refutations and check their CNF with an external LRAT checker.

Use a fresh extension. --output must name a new directory. --lrat-check accepts
DRAT-trim's lrat-check executable; the report retains its binary hash. This
checks the exported CNF, not an independent source-to-CNF translation proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
from pathlib import Path

from axeyum import ir, smt, solver
from axeyum.solver import cnf, proofs


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def check_external(checker: Path, formula: Path, proof: Path) -> bool:
    result = subprocess.run(
        [str(checker), str(formula), str(proof)],
        capture_output=True, text=True, timeout=30, check=False,
    )
    # Some checker input-error exits are zero. Require its exact success line.
    lines = result.stdout.splitlines()
    if result.returncode == 0 and "c VERIFIED" in lines:
        return True
    if result.returncode == 1 and "c NOT VERIFIED" in lines:
        return False
    raise RuntimeError(f"external checker did not reach a verdict: {result.returncode}")


def export(output: Path, checker: Path | None) -> dict:
    output.mkdir(parents=True, exist_ok=False)
    report = {"schema_version": 1, "source_translation": "not-independently-checked",
              "checker_sha256": sha256(checker.read_bytes()) if checker else None,
              "routes": {}}
    for route in ("boolean", "bit-vector"):
        arena = ir.Arena()
        if route == "boolean":
            p = arena.bool_var("p")
            assertions = [p, arena.not_(p)]
        else:
            x = arena.bv_var("x", 8)
            assertions = [arena.bvult(x, arena.bv_const(8, 1)),
                          arena.bvugt(x, arena.bv_const(8, 0))]
        outcome = proofs.export_qf_bv_unsat_proof(arena, assertions, timeout_ms=20_000)
        if outcome.status != "proved" or outcome.proof is None:
            raise RuntimeError(f"{route}: proof production {outcome.status}")
        proof = outcome.proof
        if proof.recheck() is not True:
            raise RuntimeError(f"{route}: exported text rejected in tree")
        restored = proofs.UnsatProof(proof.dimacs, proof.drat, proof.lrat)
        if restored.recheck_for_bool_terms(arena, assertions) is not True:
            raise RuntimeError(f"{route}: restored text does not bind to original terms")
        changed_assertions = [assertions[0]]
        if restored.recheck_for_bool_terms(arena, changed_assertions) is not False:
            raise RuntimeError(f"{route}: changed satisfiable source accepted")
        directory = output / route
        directory.mkdir()
        blobs = {"source.smt2": arena.write_script(assertions).encode(),
                 "formula.cnf": proof.dimacs_bytes(), "proof.drat": proof.drat_bytes()}
        lrat = proof.lrat_bytes()
        if lrat is not None:
            blobs["proof.lrat"] = lrat
        for name, data in blobs.items():
            (directory / name).write_bytes(data)
        item = {"files": {name: sha256(data) for name, data in blobs.items()},
                "lrat": "present" if lrat is not None else "absent",
                "external_cnf_check": "not-run",
                "source_binding": "replayed-with-trusted-bv-encoding"}
        if checker:
            if lrat is None:
                raise RuntimeError(f"{route}: mandatory example LRAT is absent")
            if not check_external(checker, directory / "formula.cnf", directory / "proof.lrat"):
                raise RuntimeError(f"{route}: external checker rejected honest LRAT")
            # A well-formed satisfiable replacement CNF cannot admit this refutation.
            lines = proof.dimacs.splitlines()
            changed = [lines[0]] + [line.replace("-", "") for line in lines[1:]]
            (directory / "changed.cnf").write_text("\n".join(changed) + "\n")
            # Delete the empty clause's premises, retaining valid LRAT syntax.
            clause_id = lrat.decode().split()[0]
            (directory / "missing-hints.lrat").write_text(f"{clause_id} 0 0\n")
            if check_external(checker, directory / "changed.cnf", directory / "proof.lrat"):
                raise RuntimeError(f"{route}: satisfiable CNF accepted")
            if check_external(checker, directory / "formula.cnf", directory / "missing-hints.lrat"):
                raise RuntimeError(f"{route}: missing premises accepted")
            item["external_cnf_check"] = "verified-with-two-rejection-controls"
        report["routes"][route] = item
    # The raw native CNF route emits DRAT only; missing LRAT stays explicit.
    raw = cnf.parse_dimacs("p cnf 1 2\n1 0\n-1 0\n")
    raw_outcome = cnf.solve_with_drat_proof(raw)
    if raw_outcome.status != "unsat" or raw_outcome.drat is None:
        raise RuntimeError("raw CNF: missing DRAT refutation")
    checked = cnf.check_drat(raw, raw_outcome.drat)
    if checked.status != "verified" or checked.verified is not True:
        raise RuntimeError("raw CNF: rejected DRAT")
    (output / "raw.cnf").write_text("p cnf 1 2\n1 0\n-1 0\n")
    (output / "raw.drat").write_text(raw_outcome.drat)
    report["routes"]["raw-cnf"] = {"lrat": "absent", "drat": "checked-in-tree"}
    (output / "report.json").write_text(json.dumps(report, sort_keys=True, indent=2) + "\n")
    return report


def route_census(output: Path | None = None, checker: Path | None = None) -> dict:
    """Diagnostic census of all native Python term-to-clause proof exporters.

    Representative cases do not establish universal logic coverage. Preserve
    actual declines and missing translation artifacts rather than filling them.
    """
    names = sorted(name for name in dir(proofs)
                   if name.startswith("export_") and name.endswith("_unsat_proof"))
    expected = {"export_qf_bv_unsat_proof", "export_qf_abv_unsat_proof",
                "export_qf_aufbv_unsat_proof", "export_qf_uf_unsat_proof",
                "export_datatype_unsat_proof", "export_qf_lia_unsat_proof"}
    if set(names) != expected:
        raise RuntimeError("public exporter population changed; extend the census fixtures")
    rows = {}
    for name in names:
        arena = ir.Arena()
        if name == "export_datatype_unsat_proof":
            color = arena.declare_datatype("Color")
            red = arena.add_constructor(color, "red", [])
            blue = arena.add_constructor(color, "blue", [])
            assertions = [arena.eq(arena.construct(red, []), arena.construct(blue, []))]
        elif name == "export_qf_lia_unsat_proof":
            x = arena.int_var("x")
            assertions = [arena.eq(x, arena.int_const(1)), arena.eq(x, arena.int_const(2))]
        elif name == "export_qf_uf_unsat_proof":
            sort = ir.Sort.bv(4)
            f = arena.declare_fun("f", [sort], sort)
            x, y = arena.bv_var("x", 4), arena.bv_var("y", 4)
            assertions = [arena.eq(x, y), arena.not_(arena.eq(arena.apply(f, [x]), arena.apply(f, [y])))]
        elif name in ("export_qf_abv_unsat_proof", "export_qf_aufbv_unsat_proof"):
            array = arena.array_var("a", 4, 4)
            index, value = arena.bv_var("i", 4), arena.bv_var("v", 4)
            if name == "export_qf_aufbv_unsat_proof":
                f = arena.declare_fun("f", [ir.Sort.bv(4)], ir.Sort.bv(4))
                other = arena.bv_var("w", 4)
                assertions = [arena.eq(value, other)]
                stored, compared = arena.apply(f, [value]), arena.apply(f, [other])
            else:
                assertions, stored, compared = [], value, value
            read = arena.select(arena.store(array, index, stored), index)
            assertions.append(arena.not_(arena.eq(read, compared)))
        else:
            x = arena.bv_var("x", 8)
            assertions = [arena.bvult(x, arena.bv_const(8, 1)), arena.bvugt(x, arena.bv_const(8, 0))]
        exporter = getattr(proofs, name)
        arguments = (8,) if name == "export_qf_lia_unsat_proof" else ()
        outcome = exporter(arena, assertions, *arguments)
        if outcome.status != "proved" or outcome.proof is None:
            raise RuntimeError(f"{name}: representative refutation {outcome.status}")
        proof = outcome.proof
        if proof.recheck() is not True:
            raise RuntimeError(f"{name}: clausal text failed to replay")
        sat_assertions = assertions[:-1] + [arena.not_(assertions[-1])]
        sat = exporter(arena, sat_assertions, *arguments)
        if sat.status != "satisfiable" or sat.proof is not None:
            raise RuntimeError(f"{name}: SAT control produced {sat.status}")
        # Each exported source must remain a complete, reparsable query.
        # This checks serialization; it does not prove source-to-CNF lowering.
        source = arena.write_script(assertions)
        smt.parse(source)
        source_round_trip = "parsed"
        external = "not-run"
        if output is not None:
            directory = output / name
            directory.mkdir(parents=True, exist_ok=False)
            (directory / "formula.cnf").write_bytes(proof.dimacs_bytes())
            (directory / "proof.drat").write_bytes(proof.drat_bytes())
            (directory / "source.smt2").write_text(source)
            if proof.lrat_bytes() is not None:
                (directory / "proof.lrat").write_bytes(proof.lrat_bytes())
            if checker:
                if proof.lrat is None:
                    raise RuntimeError(f"{name}: external census cannot check absent LRAT")
                if not check_external(checker, directory / "formula.cnf", directory / "proof.lrat"):
                    raise RuntimeError(f"{name}: external clausal check rejected")
                external = "verified"
        witness = solver.produce_evidence(arena, sat_assertions, solver.Config(timeout_ms=20_000))
        checked = witness.check_outcome(arena, sat_assertions)
        rows[name] = {"verdict": outcome.status, "drat": "checked-in-tree",
                      "lrat": "present" if proof.lrat is not None else "absent",
                      "lrat_recheck": proof.recheck_lrat(),
                      "source_writer_round_trip": source_round_trip,
                      "int_width": 8 if arguments else None,
                      "source_to_cnf_map_export": "absent",
                      "sat_control": sat.status, "sat_model_check": checked.status,
                      "sat_model_verdict": witness.verdict, "external_cnf_check": external,
                      "source_sha256": sha256(source.encode())}
    return {"scope": "representative-queries", "term_exporters": rows,
            "raw_cnf": {"api": "cnf.solve_with_drat_proof", "lrat": "absent"},
            "smt_text": {"api": "smt.get_proof", "format": "Alethe-or-None",
                         "clausal_export": "not-exposed"},
            "general_solver": {"api": "solver.produce_evidence",
                               "format": "EvidenceReport", "clausal_export": "not-universal"}}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lrat-check", type=Path)
    parser.add_argument("--census", action="store_true")
    args = parser.parse_args()
    report = export(args.output, args.lrat_check.resolve() if args.lrat_check else None)
    if args.census:
        census = route_census(args.output / "census", args.lrat_check.resolve() if args.lrat_check else None)
        (args.output / "route-census.json").write_text(json.dumps(census, sort_keys=True, indent=2) + "\n")
        report["route_census"] = census
    print(json.dumps(report, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
