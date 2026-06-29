# Model

The finite model uses explicit sets of string-labeled elements and total
function graphs.

Finite function data:

- `domain`: finite input labels.
- `codomain`: finite output labels.
- `pairs`: graph entries `[input, output]`.

The validator checks:

- a function is total when every domain element has an output;
- a function is single-valued when no domain element has two outputs;
- an injection has no repeated output values;
- a surjection covers every codomain value;
- a bijection is both injective and surjective;
- finite UNSAT rows have no function in the enumerated function space.

Infinite cardinality is deliberately outside this finite model. The Cantor row
records the future theorem target without treating a finite shadow as evidence
for the infinite theorem.
