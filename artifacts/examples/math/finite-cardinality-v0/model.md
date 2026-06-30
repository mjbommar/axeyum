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

The promoted `no-injection-four-to-three` row has an additional CNF model:
Boolean variable `x_{i,j}` means domain element `p_i` maps to codomain element
`h_j`. The clauses require every `p_i` to map somewhere, every `p_i` to map to
at most one `h_j`, and no two domain elements to share one codomain value.

Infinite cardinality is deliberately outside this finite model. The Cantor row
records the future theorem target without treating a finite shadow as evidence
for the infinite theorem.
