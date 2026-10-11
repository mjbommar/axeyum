"""Reference-miter certificates bind restored proof components to typed queries."""
from __future__ import annotations

import json
import subprocess
import sys

import pytest
from axeyum import AxeyumError, EpochError, ir
from axeyum.solver import proofs


def make_query(kind):
    arena = ir.Arena()
    if kind == "boolean":
        p = arena.bool_var("p")
        assertions = [p, arena.not_(p)]
    else:
        x = arena.bv_var("x", 4)
        assertions = [arena.eq(x, arena.bv_const(4, 0)),
                      arena.eq(x, arena.bv_const(4, 1))]
    return arena, assertions


def certified(kind="bit-vector"):
    arena, assertions = make_query(kind)
    outcome = proofs.certify_qf_bv_unsat_end_to_end(arena, assertions, timeout_ms=20_000)
    assert outcome.status == "certified" and outcome.proof is not None
    return arena, assertions, outcome.proof


@pytest.mark.parametrize("kind", ["boolean", "bit-vector"])
def test_reference_certificates_bind_the_original_terms(kind):
    arena, assertions, proof = certified(kind)
    assert proof.recheck_refutations() is True
    assert proof.recheck_for_bool_terms(arena, assertions) is True
    assert proof.faithfulness.lrat is None
    assert proof.faithfulness.recheck() is True
    assert proof.unsat.recheck() is True


@pytest.mark.parametrize("kind", ["boolean", "bit-vector"])
def test_restore_against_independently_rebuilt_source(kind):
    _, _, proof = certified(kind)
    restored = proofs.EndToEndUnsatProof(proof.faithfulness.dimacs, proof.faithfulness.drat,
                                        proofs.UnsatProof(proof.unsat.dimacs, proof.unsat.drat, proof.unsat.lrat))
    arena, assertions = make_query(kind)
    assert restored.recheck_for_bool_terms(arena, assertions) is True


def test_source_substitution_cannot_borrow_a_valid_refutation():
    arena, assertions, proof = certified()
    assert proof.recheck_refutations() is True
    assert proof.recheck_for_bool_terms(arena, assertions[:1]) is False


def test_two_valid_refutations_do_not_certify_an_unrelated_miter():
    arena, assertions, proof = certified()
    unsat = proof.unsat
    assert proof.faithfulness.dimacs != unsat.dimacs
    swapped = proofs.EndToEndUnsatProof(unsat.dimacs, unsat.drat, unsat)
    assert swapped.recheck_refutations() is True
    assert swapped.recheck_for_bool_terms(arena, assertions) is False


def test_missing_miter_steps_and_invalid_final_hints_reject():
    arena, assertions, proof = certified()
    broken_final = proofs.UnsatProof(proof.unsat.dimacs, proof.unsat.drat, "")
    for broken in [proofs.EndToEndUnsatProof(proof.faithfulness.dimacs, "", proof.unsat),
                   proofs.EndToEndUnsatProof(proof.faithfulness.dimacs, proof.faithfulness.drat, broken_final)]:
        try:
            accepted = broken.recheck_for_bool_terms(arena, assertions)
        except AxeyumError:
            accepted = False
        assert accepted is False


def test_sat_unsupported_and_zero_budget_outcomes_have_no_certificate():
    arena, assertions = make_query("bit-vector")
    sat = proofs.certify_qf_bv_unsat_end_to_end(arena, assertions[:1])
    assert sat.status == "satisfiable" and sat.proof is None
    limited = proofs.certify_qf_bv_unsat_end_to_end(arena, assertions, timeout_ms=0)
    assert limited.status == "not-certified" and limited.proof is None
    x = arena.int_var("z")
    unsupported = proofs.certify_qf_bv_unsat_end_to_end(arena, [arena.eq(x, arena.int_const(1))])
    assert unsupported.status == "not-certified" and unsupported.proof is None


def test_foreign_handles_and_unsupported_replay_are_explicit():
    arena, assertions, proof = certified()
    with pytest.raises(EpochError):
        proof.recheck_for_bool_terms(ir.Arena(), assertions)
    with pytest.raises(EpochError):
        proofs.certify_qf_bv_unsat_end_to_end(ir.Arena(), assertions)
    x = arena.int_var("z")
    with pytest.raises(AxeyumError, match="unsupported|cannot bit-blast"):
        proof.recheck_for_bool_terms(arena, [arena.eq(x, arena.int_const(1))])


def test_saved_miter_transport_caps_do_not_accept_oversized_text():
    _, _, proof = certified()
    with pytest.raises(ValueError, match="resource limit"):
        proofs.EndToEndUnsatProof(" " * (8 * 1024 * 1024 + 1), "", proof.unsat)


@pytest.mark.parametrize("kind", ["boolean", "bit-vector"])
def test_child_restores_source_certificate_without_production(kind, tmp_path):
    _, _, proof = certified(kind)
    path = tmp_path / "certificate.json"
    path.write_text(json.dumps({"kind": kind, "miter_dimacs": proof.faithfulness.dimacs,
                                "miter_drat": proof.faithfulness.drat,
                                "dimacs": proof.unsat.dimacs, "drat": proof.unsat.drat,
                                "lrat": proof.unsat.lrat}))
    code = r'''
import json,sys
from axeyum import ir
from axeyum.solver import proofs

def forbidden(*a, **kw):
    raise AssertionError("certificate replay invoked production")
for name in dir(proofs):
    if name.startswith("export_") or name.startswith("certify_"):
        setattr(proofs,name,forbidden)
data=json.loads(open(sys.argv[1]).read())
arena=ir.Arena()
if data["kind"]=="boolean":
    p=arena.bool_var("p")
    assertions=[p,arena.not_(p)]
else:
    x=arena.bv_var("x",4)
    assertions=[arena.eq(x,arena.bv_const(4,0)),arena.eq(x,arena.bv_const(4,1))]
unsat=proofs.UnsatProof(data["dimacs"],data["drat"],data["lrat"])
proof=proofs.EndToEndUnsatProof(data["miter_dimacs"],data["miter_drat"],unsat)
assert proof.recheck_for_bool_terms(arena,assertions) is True
assert proof.recheck_for_bool_terms(arena,assertions[:1]) is False
print("REFERENCE_MITER_REPLAY_OK")
'''
    result = subprocess.run([sys.executable, "-c", code, str(path)],capture_output=True,
                            text=True,timeout=30,check=False)
    assert result.returncode == 0, result.stdout + result.stderr
    assert result.stdout.strip() == "REFERENCE_MITER_REPLAY_OK"
