# SAT in 15 Minutes

**Boolean satisfiability**, usually shortened to **SAT**, asks whether a formula
built from `true`/`false` variables can be made true.

That sounds narrow. It is also the foundation of a remarkable amount of
automated reasoning: circuits, bounded program executions, scheduling choices,
and fixed-width machine arithmetic can all be translated into Boolean
constraints.

## Variables, connectives, and formulas

A Boolean variable such as `p` has two possible values. Connectives build
larger formulas:

| Notation | Meaning | True when |
|---|---|---|
| `not p` | negation | `p` is false |
| `p and q` | conjunction | both are true |
| `p or q` | disjunction | at least one is true |
| `p xor q` | exclusive or | exactly one is true |
| `p -> q` | implication | `p` is false or `q` is true |

Consider:

```text
(p or q) and (not p or q) and (p or not q)
```

The assignment `p = true, q = true` makes every parenthesized part true, so the
formula is **satisfiable**. That assignment is a **model** (or witness).

Now add `not p or not q`. The four clauses require at least one of `p` and `q`,
forbid each of the three assignments where one or both are false, and also
forbid the remaining all-true assignment. No model exists, so the result is
**unsatisfiable**.

For two variables we can check all four assignments by hand. A useful SAT
solver applies the same semantics without enumerating all `2^n` possibilities.

## Clauses and CNF

SAT solvers commonly accept **conjunctive normal form** (CNF):

- a **literal** is a variable (`p`) or its negation (`not p`);
- a **clause** is an `or` of literals;
- a CNF formula is an `and` of clauses.

The example above is already CNF:

```text
(p or q)                 clause 1
and (not p or q)         clause 2
and (p or not q)         clause 3
```

CNF is an interchange format, not a restriction on what can be expressed.
Helper variables can encode larger Boolean expressions while preserving
satisfiability. Axeyum uses a **Tseitin encoding** for this step: it gives each
relevant circuit node a SAT variable and adds small clauses that enforce the
node's meaning.

## What a SAT solver does

A modern conflict-driven solver repeatedly:

1. assigns a variable;
2. propagates values forced by clauses;
3. detects a conflict when a clause becomes false;
4. learns a clause explaining why that region cannot work;
5. backtracks and continues from a better point.

If it assigns every variable without falsifying a clause, it returns `sat` with
a model. If learned constraints close every possibility, it returns `unsat`.
Resource-bounded systems may instead return `unknown`; Axeyum keeps that third
outcome explicit.

The search procedure can be complex and heavily optimized. The result need not
be accepted on trust:

- a `sat` assignment is cheap to replay against every original clause;
- an `unsat` search can emit a proof trace for an independent checker.

This separation between search and checking is the central Axeyum design idea.

## From SAT to useful problems

Suppose two one-bit inputs feed an XOR gate. A circuit encoder introduces a
Boolean variable for the output and clauses that enforce its truth table. A
larger circuit repeats that construction and shares common subexpressions.

An 8-bit adder is just a network of such gates. To ask whether `x + 1` can wrap
to zero, encode the adder, constrain its output bits to zero, and ask SAT for
input bits. The satisfying assignment is `x = 255`.

You do not normally write those gates or clauses yourself. SMT lets you state
the machine-word equation directly; Axeyum's bit-vector path performs the
lowering and retains the maps needed to lift and replay the answer.

## What SAT does not know

Raw SAT variables have no built-in meaning beyond true and false. SAT does not
intrinsically know that:

- integers are unbounded;
- array reads follow array writes;
- equal function arguments have equal results;
- floating-point addition rounds;
- strings have lengths and concatenation.

Those meanings come from **theories**. The next chapter explains how SMT
combines Boolean search with theory semantics.

## Next

Continue to [SMT and theories](03-smt-and-theories.md), or see how fixed-width
words are reduced to SAT in [Bit-vectors and bit-blasting](04-bit-vectors-and-bit-blasting.md).
