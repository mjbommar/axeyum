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

from axeyum import ir
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
                "external_cnf_check": "not-run"}
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


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lrat-check", type=Path)
    args = parser.parse_args()
    print(json.dumps(export(args.output, args.lrat_check.resolve() if args.lrat_check else None),
                     sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
