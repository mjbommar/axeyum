# ADR-8400: Nested conditional CAS steps bind congruence and domain

Status: proposed; implementation in progress
Date: 2026-10-11

ADR6400/6600 certify a quotient cancellation at the root. LIB-5 also needs
conditional rewrites inside a surrounding expression and an ordered trace
combining them. Keep the existing polynomial and guarded-quotient contracts;
introduce a separate versioned conditional-composition envelope.

Each step binds its full before/after expressions, consecutive ID, predecessor,
child-index location, ordered nonzero assumption context and a checked guarded
quotient witness. The selected input must be exactly the witness's quotient;
the replacement must be exactly its polynomial result. Replay recomputes the
contextual replacement and requires the rest of the expression to be unchanged.
It checks each local witness against the caller's context, not a context inferred
from the producer, and binds the original source, continuity and final endpoint.
Replay never calls cancellation search. Deterministic postorder production
selects supported quotient cancellations and logs only actual changes.

Semantics are partial rational expressions. Under the explicit nonzero context,
local cancellation preserves both value and definedness. Congruence through
addition, multiplication, negation, nonnegative integer powers and surrounding
division preserves that relation; surrounding division still requires its own
denominator to be defined and nonzero. No equality claim asserts that an
arbitrary outer expression is total. A zero local denominator rejects even with
an inconsistent nonzero assumption. Nested quotient operands that cannot be
checked by the existing polynomial witness are explicit unsupported cases,
not unchecked identities. This slice composes checked cancellations; it does
not claim complete rational-function normalization or kernel admission.

Syntax validation permits symbolic division in the composition tree without
using the polynomial normalizer on that tree. Validate coefficient encodings,
variable names, nodes, depth and exponent bounds independently. Each local
witness retains its arithmetic work caps. Bound aggregate witness/step work,
assumption count and serialized bytes; caller policy cannot be enlarged by an
untrusted envelope. Distinguish rejected, unsupported and resource-limited.
Python must preserve those outcomes, source expressions and context in replay.

Required controls: two nested cancellations with deterministic serialized replay;
independent exact evaluations at nonzero assignments; unchanged surrounding
subtrees; modified path/source/context/premise/result/witness; deleted/reordered
steps; zero denominator and unsupported nested operands; aggregate resource
exhaustion. In a private snapshot, remove the surrounding-expression guard and
require exactly its targeted corruption test to fail. Kernel reconstruction is
a separate route and retains its explicit admitted-statement/axiom accounting.
