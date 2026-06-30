#!/usr/bin/env bash
# Validate foundational resource data and ensure generated dashboards are current.
set -euo pipefail

cd "$(dirname "$0")/.."

python3 scripts/gen-foundational-concepts.py
python3 scripts/validate-foundational-concepts.py
python3 scripts/validate-foundational-example-pack.py
python3 scripts/check-foundational-negative-fixtures.py
python3 scripts/consume-foundational-resources.py
python3 scripts/query-foundational-resources.py summary >/dev/null
python3 scripts/query-foundational-resources.py packs --solver-reuse promoted --require-any >/dev/null
python3 scripts/query-foundational-resources.py packs --field probability_theory --route Farkas --require-any >/dev/null
python3 scripts/query-foundational-resources.py checks --field graph_theory --expected-result unsat --require-any >/dev/null
python3 scripts/query-foundational-resources.py concepts --kind example-family --format json --require-any >/dev/null
python3 scripts/gen-foundational-dashboards.py

git diff --exit-code -- \
  artifacts/ontology/foundational-concepts.json \
  docs/foundational-resources/generated/math-coverage.md \
  docs/foundational-resources/generated/curriculum-status-audit.md \
  docs/foundational-resources/generated/math-field-dashboard.md \
  docs/foundational-resources/generated/proof-gap-dashboard.md \
  docs/foundational-resources/generated/learner-proof-upgrade-dashboard.md \
  docs/foundational-resources/generated/curriculum-pressure-by-fragment.md
