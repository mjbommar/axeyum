# Template Math Example Pack

This is the structural template for future foundational math example packs.
It validates the required file layout and metadata contract without making a
mathematical claim.

Real packs should copy this shape and then replace the template status with:

- concrete concept and curriculum links;
- a finite model or computable claim;
- SAT/UNSAT/UNKNOWN checks;
- replayed witnesses or explicit proof gaps;
- a validator command that replays the pack's expected results.

Validation:

```sh
python3 scripts/validate-foundational-example-pack.py artifacts/examples/math/template-v0
```
