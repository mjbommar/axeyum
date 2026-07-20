# Reflection semantics gate

Status: standing CI gate (ADR-0290)

## Contract

Every checked LLVM or MIR semantic enum variant must be owned by evidence with
both sides below:

1. a symbolic equivalence or independently constructed specification proof;
2. a deterministic differential, exhaustive-fuzz, or source-replay test.

The versioned inventory is
[`reflection-semantics-gate.json`](reflection-semantics-gate.json). The checker
derives variants from the registered Rust enum declarations rather than trusting
a hand-maintained count. A new variant, removed evidence row, duplicate owner,
unknown test, path escape, or changed test-binary list fails closed.

Run the complete bounded gate with:

```sh
python3 scripts/check-reflection-semantics-gate.py --run
```

`just reflection-semantics-gate` invokes that same command, and the dedicated
stable CI job does likewise. The runner first executes the checker's ten
fail-closed mutation tests, then the exact manifest-owned Rust test binaries.
Validation alone (without those mutation/evidence suites) is:

```sh
python3 scripts/check-reflection-semantics-gate.py
```

The validation report is deterministic JSON. At ADR-0290 acceptance the source
inventory contains 12 enums and 62 variants, owned by 14 evidence groups.

## What the gate executes

The manifest owns the exact ordered test-binary list. The current bounded set
is:

- `reflection_semantics_gate`: independent finite truth-table specifications
  plus exhaustive concrete checks for every LLVM scalar opcode, predicate,
  cast, intrinsic, semantic flag, `select`, and every checked MIR scalar binary
  opcode;
- `cross_ir_equivalence`: all 11 ordinary admitted MIR/LLVM pairs under
  deterministic `DiffFuzz`, plus the exact defined domain of the
  hypothesis-bounded `lut3`/`unreachable` pair;
- `cross_ir_refutation`: five deliberately wrong transforms whose solver
  countermodels are replay-checked;
- `llvm_checked_cfg`, `llvm_checked_memory`, `mir_checked_memory`, and
  `checked_bounds`: exact control-flow, definedness/panic, byte-memory, final
  state, and source-replay evidence.

For LLVM operations that can produce poison or immediate undefined behavior,
the scalar matrix compares definedness separately and compares values only
under that guard. Division by zero, signed minimum divided by minus one,
oversized shifts, wrap flags, `exact`, `disjoint`, truncation flags, and `nneg`
therefore cannot pass by observing Axeyum's total BV placeholder value.

## Adding semantics

An operation or instruction is not admitted by parser/lowerer code alone. Its
change must include, in one reviewable commit:

1. the strict typed enum/parser/lowerer addition with a precise unsupported or
   malformed error boundary;
2. a manifest member under exactly one evidence group;
3. an all-input bounded spec/equivalence proof appropriate to the construct;
4. deterministic fuzz, differential, or source replay that exercises the real
   checked path; and
5. a negative/refutation control when a plausible wrong lowering can be stated.

Do not satisfy the gate with a coercion, skipped unsupported function, unguarded
undefined value, prose-only claim, ignored test, or test name that does not
exist. The gate protects the reviewer-visible strength identified by Glaurung:
strict typing and precise errors must remain a correctness oracle, not become a
best-effort importer.

## Scope

This is exact coverage of the currently admitted checked semantic variants, not
a proof of arbitrary rustc/LLVM correctness. Parser noise tests establish
non-panicking rejection, while the semantic cells establish meaning only for
accepted input. The gate does not admit cycles, general MIR places,
wide/aliased memory, `stable_mir`, Glaurung LLIR lowering, or a shared frontend
crate.
