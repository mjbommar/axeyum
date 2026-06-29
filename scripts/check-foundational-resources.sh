#!/usr/bin/env bash
# Validate foundational resource data and ensure generated dashboards are current.
set -euo pipefail

cd "$(dirname "$0")/.."

python3 scripts/gen-foundational-concepts.py
python3 scripts/validate-foundational-concepts.py
python3 scripts/validate-foundational-example-pack.py
python3 scripts/consume-foundational-resources.py
python3 scripts/gen-foundational-dashboards.py

git diff --exit-code -- \
  artifacts/ontology/foundational-concepts.json \
  docs/foundational-resources/generated/math-coverage.md \
  docs/foundational-resources/generated/math-field-dashboard.md \
  docs/foundational-resources/generated/proof-gap-dashboard.md
