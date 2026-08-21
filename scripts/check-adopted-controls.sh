#!/usr/bin/env bash
# Control modules that existed but which NO gate ran, now adopted.
#
# `scripts/check-control-tests-reachable.py` measured 63 of 137 control modules
# executed by nothing on 2026-08-17. These 44 are the ones that pass as-is: they
# were already written, already committed, and already correct — they were simply
# never wired to a runner, so nothing they guard was actually guarded.
#
# The list is explicit rather than a `unittest discover` sweep for two reasons.
# Discovery would silently adopt a module the moment someone adds it, which is
# how an unreviewed and possibly failing control ends up gating everyone else;
# and it would hide the seven modules deliberately left out below, turning a
# recorded exclusion into an invisible one.
#
# NOT adopted, measured individually on 2026-08-17:
#   test_capture_maestro_device_id       ) pytest-style; `pytest` is not
#   test_capture_maestro_device_id_v2    ) installed on this host, so these
#   test_qf_linear_a5_census             ) fail to IMPORT under plain unittest.
#   test_qf_nia_a3_census                ) Adopting them would make the gate
#   test_qf_uflia_a4_census              ) depend on a package the repo does
#                                        ) not otherwise require.
#   test_validate_glaurung_llvm_loop_semantic_census
#       genuinely stale: `ResultValidationError: producer drift: Cargo.lock`.
#       This is the one real case of a control rotting because nothing ran it.
#   test_diagnose_maestro_llvm_root_drift
#       fails only when run in isolation; passes inside the batch, so it has an
#       order dependency that must be fixed before it can gate anything.
#
# Fixing those seven, and lowering ORPHAN_BASELINE as each is adopted, is the
# remaining work.
set -euo pipefail
cd "$(dirname "$0")/.."

python3 -m unittest scripts.tests.test_analyze_cnf_construction_profile \
  scripts.tests.test_analyze_direct_root_parity_memo \
  scripts.tests.test_analyze_direct_root_parity_memo_timing \
  scripts.tests.test_analyze_glaurung_authority_coverage_union \
  scripts.tests.test_analyze_glaurung_authority_site_schedule_union \
  scripts.tests.test_analyze_glaurung_authority_timeout_policy \
  scripts.tests.test_analyze_glaurung_concretization_sweep \
  scripts.tests.test_analyze_glaurung_constraint_cache_opportunity \
  scripts.tests.test_analyze_glaurung_engine_cache_factorial \
  scripts.tests.test_analyze_glaurung_six_cell_calibration \
  scripts.tests.test_analyze_glaurung_symbolic_cve_frontend_surface \
  scripts.tests.test_analyze_qfbv_timeout_sweep \
  scripts.tests.test_analyze_solver_group_collapse \
  scripts.tests.test_census_glaurung_llvm_loop_semantics \
  scripts.tests.test_census_glaurung_llvm_loops \
  scripts.tests.test_check_reflection_semantics_gate \
  scripts.tests.test_check_verify_mir_fixture \
  scripts.tests.test_fixed_authority_shadow_calibration \
  scripts.tests.test_freeze_glaurung_policy_difference_population \
  scripts.tests.test_gen_measurement_provenance \
  scripts.tests.test_glaurung_usbprint_frontier \
  scripts.tests.test_joint_triplet_census \
  scripts.tests.test_materialize_glaurung_proof_holdout \
  scripts.tests.test_materialize_glaurung_symbolic_cve_artifacts \
  scripts.tests.test_package_glaurung_symbolic_cve_reproducibility \
  scripts.tests.test_prototype_lean4export_census \
  scripts.tests.test_qualify_glaurung_symbolic_cve_recall \
  scripts.tests.test_run_glaurung_concretization_sweep \
  scripts.tests.test_run_glaurung_engine_cache_factorial \
  scripts.tests.test_run_glaurung_six_cell_calibration \
  scripts.tests.test_run_glaurung_symbolic_cve_recall \
  scripts.tests.test_run_glaurung_symbolic_cve_reproducibility \
  scripts.tests.test_select_glaurung_proof_holdout \
  scripts.tests.test_select_nontrivial_external_drat \
  scripts.tests.test_smtcomp_full_admission \
  scripts.tests.test_smtcomp_full_compare \
  scripts.tests.test_smtcomp_full_execution \
  scripts.tests.test_smtcomp_full_result \
  scripts.tests.test_smtcomp_p0_compare \
  scripts.tests.test_smtcomp_resource_enforcement \
  scripts.tests.test_validate_glaurung_finding_population \
  scripts.tests.test_validate_glaurung_llvm_direct_call_fixture \
  scripts.tests.test_validate_glaurung_policy_difference_adjudication \
  scripts.tests.test_validate_glaurung_symbolic_cve_execution

# Autogenesis evidence controls added after the original adoption pass. Keep
# this list explicit: adding a checker does not make its mutation controls part
# of a gate until this runner names them.
python3 -m unittest \
  scripts.tests.test_check_autogenesis_coprime_factor_cancellation_generic_plan \
  scripts.tests.test_check_autogenesis_nat_fib_child_qualification \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_clean_dvd_antisymm_plan_v3 \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_clean_dvd_antisymm_plan_v4 \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_clean_dvd_antisymm_plan_v5 \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_clean_dvd_antisymm_result_v2 \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_clean_dvd_antisymm_result_v3 \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_clean_dvd_antisymm_result_v4 \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_clean_dvd_antisymm_result_v5 \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_exact_plan \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_portable_support_capsules_plan \
  scripts.tests.test_check_autogenesis_nat_gcd_fib_add_self_portable_support_capsules_result \
  scripts.tests.test_check_autogenesis_official_gcd_balanced_bezout_exact_reuse_plan \
  scripts.tests.test_check_autogenesis_official_gcd_balanced_bezout_exact_reuse_result \
  scripts.tests.test_check_autogenesis_official_cancellation_acc_path_and_package \
  scripts.tests.test_check_autogenesis_official_r091_clean_dvd_antisymm_plan_v5
