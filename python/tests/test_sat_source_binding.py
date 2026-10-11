"""Restored clausal certificates bind to independently supplied Boolean/BV terms."""
from __future__ import annotations

import json
import subprocess
import sys

import pytest
from axeyum import AxeyumError, EpochError, ir
from axeyum.solver import proofs


def fixture(kind: str):
    arena = ir.Arena()
    if kind == "boolean":
        x = arena.bool_var("p")
        assertions = [x, arena.not_(x)]
    else:
        x = arena.bv_var("x", 8)
        assertions = [arena.eq(x, arena.bv_const(8, 0)),
                      arena.eq(x, arena.bv_const(8, 1))]
    outcome = proofs.export_qf_bv_unsat_proof(arena, assertions)
    assert outcome.status == "proved" and outcome.proof is not None
    return arena, assertions, outcome.proof


@pytest.mark.parametrize("kind", ["boolean", "bit-vector"])
def test_restored_proof_rechecks_against_original_terms(kind):
    arena, assertions, proof = fixture(kind)
    restored = proofs.UnsatProof(proof.dimacs, proof.drat, proof.lrat)
    assert restored.recheck() is True
    assert restored.recheck_for_bool_terms(arena, assertions) is True
    assert restored.dimacs_bytes() == proof.dimacs_bytes()
    assert restored.drat_bytes() == proof.drat_bytes()
    assert restored.lrat_bytes() == proof.lrat_bytes()


def test_source_binding_rejects_a_satisfiable_substitute():
    arena, assertions, proof = fixture("boolean")
    restored = proofs.UnsatProof(proof.dimacs, proof.drat, proof.lrat)
    assert restored.recheck_for_bool_terms(arena, assertions) is True
    # The clausal proof remains valid; only the caller's proposition changes.
    assert restored.recheck() is True
    assert restored.recheck_for_bool_terms(arena, [assertions[0]]) is False


def test_optional_lrat_is_preserved_and_drat_still_replays():
    arena, assertions, proof = fixture("boolean")
    restored = proofs.UnsatProof(proof.dimacs, proof.drat)
    assert restored.lrat is None and restored.lrat_bytes() is None
    assert restored.recheck_lrat() is None
    assert restored.recheck_for_bool_terms(arena, assertions) is True


def test_tampered_refutations_cannot_replay():
    arena, assertions, proof = fixture("boolean")
    missing_empty = "\n".join(line for line in proof.drat.splitlines() if line.strip() != "0")
    for changed in [proofs.UnsatProof(proof.dimacs, missing_empty, proof.lrat),
                    proofs.UnsatProof(proof.dimacs, proof.drat, "")]:
        try:
            accepted = changed.recheck_for_bool_terms(arena, assertions)
        except AxeyumError:
            accepted = False
        assert accepted is False


def test_unsupported_source_and_foreign_handles_are_explicit():
    arena, assertions, proof = fixture("boolean")
    other = ir.Arena()
    with pytest.raises(EpochError):
        proof.recheck_for_bool_terms(other, assertions)
    x = arena.int_var("x")
    with pytest.raises(AxeyumError, match="unsupported|cannot bit-blast"):
        proof.recheck_for_bool_terms(arena, [arena.eq(x, arena.int_const(1))])
    with pytest.raises(AxeyumError, match="unparseable"):
        proofs.UnsatProof("malformed", "0\n").recheck()


def test_restored_certificate_transport_caps_are_explicit():
    cap = 8 * 1024 * 1024
    with pytest.raises(ValueError, match="resource limit"):
        proofs.UnsatProof(" " * (cap + 1), "")
    with pytest.raises(ValueError, match="resource limit"):
        proofs.UnsatProof(" " * cap, " " * cap, " ")
    # At the boundary transport stores data; it does not accept a proof claim.
    proof = proofs.UnsatProof(" " * cap, " " * cap)
    assert proof.lrat is None
    with pytest.raises(AxeyumError):
        proof.recheck()


@pytest.mark.parametrize("kind", ["boolean", "bit-vector"])
def test_saved_text_replays_in_a_child_without_a_producer(kind, tmp_path):
    _, _, proof = fixture(kind)
    payload = tmp_path / "proof.json"
    payload.write_text(json.dumps({"kind": kind, "dimacs": proof.dimacs,
                                   "drat": proof.drat, "lrat": proof.lrat}))
    # The child independently reconstructs the caller's known proposition. It
    # cannot ask a producer to manufacture a replacement certificate.
    code = r'''
import json, sys
from axeyum import ir
from axeyum.solver import proofs

def forbidden(*args, **kwargs):
    raise AssertionError("replay called proof production")
for name in dir(proofs):
    if name.startswith("export_") and name.endswith("_unsat_proof"):
        setattr(proofs, name, forbidden)
data = json.loads(open(sys.argv[1]).read())
arena = ir.Arena()
if data["kind"] == "boolean":
    p = arena.bool_var("p")
    assertions = [p, arena.not_(p)]
else:
    x = arena.bv_var("x", 8)
    assertions = [arena.eq(x, arena.bv_const(8, 0)), arena.eq(x, arena.bv_const(8, 1))]
proof = proofs.UnsatProof(data["dimacs"], data["drat"], data["lrat"])
assert proof.recheck_for_bool_terms(arena, assertions) is True
print("SOURCE_BOUND_REPLAY_OK")
'''
    result = subprocess.run([sys.executable, "-c", code, str(payload)],
                            capture_output=True, text=True, timeout=30, check=False)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == "SOURCE_BOUND_REPLAY_OK"
