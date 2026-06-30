# Foundational Example-Pack Negative Fixtures

These directories are intentionally invalid example packs. They are not scanned
by the normal valid-pack validator because they live outside
`artifacts/examples/math/`.

Run:

```sh
python3 scripts/check-foundational-negative-fixtures.py
```

The check runner validates that each fixture fails
`scripts/validate-foundational-example-pack.py` with the expected diagnostic.
The normal foundational-resource gate runs the same negative-fixture check.
