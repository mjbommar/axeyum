# How Axeyum Solves a Query

This page traces one query from text to answer, and shows the single most
important idea in the system: the **trust boundary** between *fast search* (which
may be buggy) and *small checking* (which guards correctness).

> Prerequisite vocabulary: [`sat` / `unsat` / `unknown`](05-models-unsat-and-unknown.md)
> and [bit-vectors & bit-blasting](04-bit-vectors-and-bit-blasting.md). New to
> all this? Start at [What is automated reasoning?](01-what-is-automated-reasoning.md)

## The pipeline

A quantifier-free bit-vector (`QF_BV`) query flows left to right. The **blue**
band performs untrusted search. The **green** boxes are possible checking
endpoints; a result follows only the boxes supported by its selected route.

```mermaid
flowchart LR
    subgraph parse[" "]
        direction TB
        smt["SMT-LIB text<br/>or Rust IR builder"] --> ir["Typed term IR<br/>(arena, hash-consed DAG)"]
    end

    subgraph search["UNTRUSTED — fast search (may be buggy)"]
        direction TB
        ir --> pre["Word-level preprocess<br/>canonicalize · solve_eqs ·<br/>propagate · elim_unconstrained"]
        pre --> blast["Bit-blast → AIG circuit"]
        blast --> cnf["Tseitin → CNF"]
        cnf --> sat["SAT core<br/>batsat / native CDCL"]
    end

    subgraph check["TRUSTED — small independent checking"]
        direction TB
        model["Lift model to IR values"] --> replay["Replay vs ORIGINAL query<br/>(ground evaluator)"]
        prop["DRAT / optional LRAT"] --> pcheck["Clausal proof checker"]
        theory["Theory certificate"] --> tcheck["Fragment checker"]
        alethe["Selected Alethe proof"] --> acheck["Alethe checker"]
        alethe --> lean["Selected Lean reconstruction<br/>→ kernel check"]
    end

    sat -->|"SAT: assignment"| model
    sat -->|"selected proof route"| prop
    sat -->|"selected theory route"| theory
    sat -->|"selected SMT proof route"| alethe
    sat -->|"proofless UNSAT route"| lower["unsat + lower assurance<br/>(for example Unchecked)"]
    sat -->|"budget / incomplete route"| unknown["unknown<br/>(not settled)"]

    replay -->|"every assertion true"| satOut(["✅ sat + verified model"])
    replay -->|"mismatch"| alarm(["soundness alarm → error"])
    pcheck --> unsatOut(["✅ unsat + checked evidence"])
    tcheck --> unsatOut
    acheck --> unsatOut
    lean --> unsatOut

    classDef u fill:#e8eeff,stroke:#3355aa;
    classDef t fill:#e7f6e7,stroke:#2e7d32;
    classDef out fill:#fff7e0,stroke:#b8860b;
    class pre,blast,cnf,sat u;
    class model,replay,prop,pcheck,theory,tcheck,alethe,acheck,lean t;
    class satOut,unsatOut,lower,unknown,alarm out;
```

The UNSAT arrows are alternatives, not one mandatory
DRAT → LRAT → Alethe → Lean pipeline. A checked clausal proof establishes the
CNF; a source-level claim additionally needs a checked or explicitly trusted
source-to-CNF boundary.

**Why the boundary matters.** The SAT core, the bit-blaster, and the
preprocessor are large and fast. Their candidate results need the evidence and
assurance report of the selected route:

- A claimed **`sat`** is only returned after its model is lifted to IR values
  and **evaluated against the original assertions**. A bad model fails the replay
  and becomes a soundness alarm, never a wrong `sat`.
- A claimed **`unsat`** is only as trusted as the evidence behind it. Selected
  routes re-check a DRAT/LRAT proof, a theory certificate, an Alethe proof, or a
  reconstructed term. The default BatSat-backed clausal route instead records
  its proof status as `Unchecked`; it must not be described as certificate-
  checked.
- When search runs out of budget or the encoding is too large, the answer is
  **`unknown`** — a valid, deliberate outcome, not a failure.

## The same idea, as a sequence

```mermaid
sequenceDiagram
    autonumber
    participant U as You
    participant S as Solver (untrusted)
    participant E as Evaluator (trusted)
    participant K as Checker / Kernel (trusted)

    U->>S: solve(assertions)
    S->>S: preprocess · bit-blast · CNF · SAT
    alt SAT
        S-->>E: candidate model
        E->>E: eval every original assertion
        E-->>U: ✅ sat (model verified) — or soundness alarm
    else UNSAT
        S-->>K: verdict + route-specific evidence status
        opt certificate-bearing route
            K->>K: validate the available certificate
        end
        K-->>U: unsat + explicit assurance report
    else out of budget
        S-->>U: unknown (honest)
    end
```

## Worked example

```smt2
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x #x01) #x00))
(check-sat)
(get-model)
```

1. **Parse → IR.** `x` becomes an 8-bit symbol; `bvadd`, the constant `#x01`,
   and the equality become nodes in a shared DAG.
2. **Preprocess.** Nothing to simplify here (a real query often shrinks a lot).
3. **Bit-blast.** Each 8-bit value becomes 8 Boolean wires; `bvadd` becomes a
   ripple-carry adder circuit (see [bit-blasting](04-bit-vectors-and-bit-blasting.md)):

   ![Bit-blasting bvadd(x,1) into a ripple-carry adder circuit](../assets/bit-blasting.svg)
4. **CNF → SAT.** The circuit + the constraint `x + 1 = 0` is handed to the SAT
   core, which finds an assignment.
5. **Lift + replay.** The bits decode to `x = #xff` (255). Axeyum evaluates
   `bvadd(#xff, #x01) == #x00` in the **trusted** ground evaluator: `255 + 1`
   wraps to `0` in 8 bits ✅. The model is returned only because it replayed.

The contradictory version returns `unsat`. The dedicated
[QF_BV proof exporter](../user-guide/unsat-evidence.md) can solve this shape with
the proof-producing core and emit a DRAT proof that `check_drat` re-validates:

```smt2
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x00))
(assert (= x #x01))
(check-sat)
```

`x` cannot be both `0` and `1`, so no model exists — `unsat`, with a small
checkable certificate rather than "trust me."

## Where to go next

- The pieces of the untrusted band: [bit-blasting](04-bit-vectors-and-bit-blasting.md),
  and the internals [CNF & SAT](../internals/cnf-and-sat.md).
- The pieces of the trusted band: [proofs, certificates & trust](06-proofs-certificates-and-trust.md),
  and the internals [proof stack](../internals/proof-stack.md) and
  [Lean kernel](../internals/lean-kernel.md).
- Run it yourself: [first SMT-LIB query](../user-guide/first-smtlib-query.md), or
  the in-browser [playground](../playground/README.md).
