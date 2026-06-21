# Glossary

Plain definitions for the abbreviations used across the docs. Beginner pages
define terms inline; this is the quick reference.

| Term | Meaning |
|---|---|
| **SAT** | Boolean satisfiability: is there a true/false assignment making a Boolean formula true? The core engine under everything. |
| **SMT** | SAT *Modulo Theories*: SAT's Boolean structure plus theories (bit-vectors, integers, arrays, …) that give variables meaning. |
| **model** | A satisfying assignment — concrete values for the variables. Returned on `sat`, and replay-verified in Axeyum. |
| **sat / unsat / unknown** | A solution exists / provably none exists / not settled within resources. All three are valid results; `unknown` is first-class. See [05](05-models-unsat-and-unknown.md). |
| **theory** | A domain with its own semantics and decision procedure: `BV`, `LIA`/`LRA`, `UF`, arrays, `FP`, … |
| **QF_** | "Quantifier-Free" prefix on a logic name (e.g. **QF_BV** = quantifier-free bit-vectors). |
| **BV** | Bit-vector: a fixed-width machine word; arithmetic wraps (mod 2ⁿ). |
| **LIA / LRA** | Linear Integer / Real Arithmetic. |
| **NRA / NIA** | Nonlinear Real / Integer Arithmetic (products of variables). Sound-but-incomplete in Axeyum. |
| **UF / EUF** | Uninterpreted Functions / with Equality: unknown functions where only `a=b ⇒ f(a)=f(b)` is assumed. |
| **FP** | IEEE-754 floating point. |
| **bit-blasting** | Lowering bit-vector (and other) operations to a Boolean circuit, then to SAT. See [the SVG](07-how-axeyum-solves-a-query.md). |
| **AIG** | And-Inverter Graph: a compact Boolean circuit representation. |
| **CNF** | Conjunctive Normal Form: an AND of OR-clauses — the input format SAT solvers consume. |
| **Tseitin** | The standard encoding turning a circuit into equisatisfiable CNF. |
| **CDCL** | Conflict-Driven Clause Learning: the modern SAT algorithm. |
| **DRAT** | A clausal UNSAT *proof* format; re-checkable independently (`check_drat`). |
| **LRAT** | A *hinted* clausal proof format — linear-time checkable (`check_lrat`). |
| **Alethe** | An SMT proof format (veriT/cvc5); Axeyum emits + checks a growing subset, and reconstructs it to Lean. |
| **Farkas certificate** | A small linear-algebra witness that a set of linear constraints is infeasible — the LRA `unsat` evidence. |
| **MBQI** | Model-Based Quantifier Instantiation: a quantifier-reasoning technique. |
| **replay** | Re-evaluating a returned `sat` model against the *original* query in the trusted ground evaluator. |
| **trust boundary** | The line between *untrusted* fast search and *trusted* small checking — the project's core idea. See [07](07-how-axeyum-solves-a-query.md). |
| **PAR-2** | A benchmark scoring rule: solve time, or 2× the timeout if unsolved. |

See also: the [capability matrix](../research/08-planning/capability-matrix.md)
(what's supported), the [trust ledger](../research/08-planning/trust-ledger.md)
(what's checked vs trusted).
