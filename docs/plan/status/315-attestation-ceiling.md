# Lane: attestation-ceiling -- does re-attestation actually unbind ADR-0615's ceiling?

<!-- plan-section: lane-status -->

**Lane block (`IN PROGRESS -- step 0 measurement recorded`,
attestation-ceiling, 2026-08-30).**

## Step 0 -- re-measurement (main merged)

```
python3 scripts/gen-autogenesis-nursery-refill.py --check
AUTOGENESIS_NURSERY_REFILL_OK|entries=200|settled_mirrors_admitted=162|bridge=70
  |env=2207|development=60|held-out=90|train=50|combined=414
exit 0

python3 scripts/check-dispatchable-frontier.py
open ml430 mirrors: 146
  held-out: 115   mutation controls: 12   structurally blocked: 11
  DISPATCHABLE: 8
exit 0
```

`nursery-v2-extension.json`: 200 entries, `surface_validation.grade =
real-lean-axiom-elaboration-per-row`, `attested` 197, `not_elaborable` 3,
`unattested` 0. `EXTENSION_CEILING = V1_EVALUATION_ENTRIES = 214`, so headroom
is **14** against a smallest compliant draw of 40.

`nursery-v1.json` has **no `surface_validation` key at all**.
