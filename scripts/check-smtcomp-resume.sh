#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

export PYTHONWARNINGS=error
python3 -m unittest \
  scripts.tests.test_smtcomp_resume_fs \
  scripts.tests.test_smtcomp_resume_runner
python3 scripts/smtcomp_repro/tests/test_runner.py
for test in test_scoring test_pipeline test_selection test_provenance; do
  python3 "scripts/smtcomp_repro/tests/$test.py"
done
python3 scripts/gen-smtcomp-resume-contract.py --check
