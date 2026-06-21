# Architecture

Axeyum is a workspace of small crates with a deliberately minimal split (crates
are added only when a boundary is proven by use — see
[ADR-0001](../research/09-decisions/README.md)). The shape mirrors the
[solve pipeline](../learn/07-how-axeyum-solves-a-query.md): a typed IR at the
base, a circuit/SAT lowering stack, theory and proof modules, and one solver hub
that ties them together.

## Crate dependency graph

```mermaid
flowchart TD
    subgraph foundation["Foundation"]
        ir["axeyum-ir<br/>typed terms · arena · evaluator"]
    end
    subgraph circuit["Circuit → SAT lowering"]
        aig["axeyum-aig<br/>AIG circuit"]
        bv["axeyum-bv<br/>term → AIG bit-blast"]
        cnf["axeyum-cnf<br/>Tseitin · SAT · DRAT/LRAT/Alethe"]
    end
    subgraph theories["Theories & transforms"]
        fp["axeyum-fp<br/>IEEE-754"]
        rewrite["axeyum-rewrite<br/>canonicalize · reduce"]
        egraph["axeyum-egraph<br/>congruence bus"]
        query["axeyum-query<br/>assertions · scopes"]
        smtlib["axeyum-smtlib<br/>SMT-LIB front door"]
    end
    subgraph proof["Proof / trust"]
        lean["axeyum-lean-kernel<br/>Rust Lean-grade kernel"]
    end
    subgraph hub["Hub & consumers"]
        solver["axeyum-solver<br/>backends · dispatch · evidence"]
        scenarios["axeyum-scenarios<br/>self-checking workloads"]
        bench["axeyum-bench<br/>corpus harness"]
    end

    ir --> bv & fp & rewrite & query & smtlib & scenarios
    aig --> bv --> cnf
    aig --> cnf
    fp --> smtlib
    query --> scenarios
    ir --> solver
    aig --> solver
    bv --> solver
    cnf --> solver
    fp --> solver
    rewrite --> solver
    egraph --> solver
    query --> solver
    smtlib --> solver
    scenarios --> solver
    lean --> solver
    solver --> bench
    smtlib --> bench

    classDef base fill:#eef3ff,stroke:#3355aa;
    classDef low fill:#eef,stroke:#557;
    classDef th fill:#f3f0ff,stroke:#6a5acd;
    classDef pf fill:#e7f6e7,stroke:#2e7d32;
    classDef hb fill:#fff7e0,stroke:#b8860b;
    class ir base;
    class aig,bv,cnf low;
    class fp,rewrite,egraph,query,smtlib th;
    class lean pf;
    class solver,scenarios,bench hb;
```

Notable independents: `axeyum-aig`, `axeyum-egraph`, and `axeyum-lean-kernel`
depend on **nothing** in the workspace — they're self-contained, separately
testable engines. `axeyum-solver` is the only hub.

## Pipeline → crates

| Stage | Crate(s) | Trust |
|---|---|---|
| Parse / build query | `axeyum-smtlib`, `axeyum-ir`, `axeyum-query` | input |
| Word-level preprocess | `axeyum-rewrite` | untrusted |
| Bit-blast → AIG | `axeyum-bv`, `axeyum-aig` | untrusted |
| Tseitin → CNF, SAT | `axeyum-cnf` | untrusted |
| Theory engines (EUF, LRA, NRA, FP…) | `axeyum-solver`, `axeyum-egraph`, `axeyum-fp` | mixed |
| **Model replay** | `axeyum-ir` (ground evaluator) | **trusted** |
| **Proof check** (DRAT/LRAT/Alethe) | `axeyum-cnf` | **trusted** |
| **Lean reconstruction** | `axeyum-lean-kernel` | **trusted** |
| Dispatch + evidence | `axeyum-solver` | orchestration |

## Hard rules that shape the design

- **No C/C++ in the default build.** Native solver backends (Z3) are
  feature-gated leaf dependencies only — the pure-Rust stack is the product.
- **`unsafe_code` is denied** workspace-wide (exceptions need an ADR).
- **Lifetime-free `Copy` term IDs.** Backend FFI types and lifetimes never leak
  into public APIs — which (among other things) is what makes the arena `Sync`
  and a parallel strategy portfolio feasible.
- **Determinism** is a public promise: stable iteration order, explicit seeds,
  explicit budgets.

## Read next

- [Term IR](term-ir.md) *(planned)* — the arena and evaluator.
- [Bit-blasting](bit-blasting.md) *(planned)* — term → AIG → CNF.
- [Proof stack](proof-stack.md) and [Lean kernel](lean-kernel.md) *(planned)*.
- [How this documentation is built](documentation.md) — the diagram/site/WASM
  approach.
