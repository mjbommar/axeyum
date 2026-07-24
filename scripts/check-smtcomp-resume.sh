#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

export PYTHONWARNINGS=error
python3 -m unittest \
  scripts.tests.test_smtcomp_resume_fs \
  scripts.tests.test_smtcomp_resume_runner \
  scripts.tests.test_smtcomp_resource_enforcement \
  scripts.tests.test_smtcomp_cgroup_host \
  scripts.tests.test_smtcomp_multi_host \
  scripts.tests.test_smtcomp_multi_host_live \
  scripts.tests.test_smtcomp_full_admission \
  scripts.tests.test_smtcomp_full_compare \
  scripts.tests.test_smtcomp_full_execution \
  scripts.tests.test_smtcomp_full_population \
  scripts.tests.test_smtcomp_full_result \
  scripts.tests.test_smtcomp_p0_compare \
  scripts.tests.test_smtcomp_p0_prepare \
  scripts.smtcomp_repro.tests.test_corpus_acquisition \
  scripts.smtcomp_repro.tests.test_final_selection_audit \
  scripts.smtcomp_repro.tests.test_official_producer \
  scripts.smtcomp_repro.tests.test_official_selection
python3 scripts/smtcomp_repro/tests/test_runner.py
for test in test_scoring test_pipeline test_selection test_provenance; do
  python3 "scripts/smtcomp_repro/tests/$test.py"
done
python3 scripts/gen-smtcomp-resume-contract.py --check
python3 scripts/gen-smtcomp-selection-authority.py --check
python3 scripts/generate-smtcomp-repaired-p0-comparison.py --check
