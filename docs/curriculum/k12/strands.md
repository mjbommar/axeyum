# The Four Strands, Across the Grades

A spiral curriculum: the same four strands — **logic & reasoning, math, computer
science** — revisited each band with widening tools, every skill tagged with the
axeyum capability that lets the platform *self-check* it (✅ = self-checked end to
end today; 🧮 = compute-and-verify; 🔭 = Lean-horizon / aspirational).

The unifying move, at every band: **make a claim → the platform checks it against
the real math → see a proof or a counterexample.**

## K–2 · "the computer follows exact rules"

| Strand | Skills | Self-check engine |
| --- | --- | --- |
| Logic & reasoning | true/false; *and / or / not* as games ("true AND true"); "is there a way?" | Bool/SAT ✅ |
| Math | counting; even/odd (parity); same/different; more/less | tiny BV / equality ✅ |
| Computer science | a rule is followed *exactly*; sequences/steps; on/off = 1/0 | — (concept) |

Big idea: a statement is either **true** or **false**, and a machine can check
which — perfectly, every time.

## 3–5 · "if-then, and how computers count"

| Strand | Skills | Self-check engine |
| --- | --- | --- |
| Logic & reasoning | **if-then promises** (when is one *broken*?); proof by checking all cases; "find an example / find a counterexample" | Bool/SAT ✅ |
| Math | place value; factors & multiples; remainders; the number line | LIA / modular ✅ 🧮 |
| Computer science | **binary numbers**; base-2 ↔ base-10; "computers count with two fingers"; a bit | BV ✅ |

Big idea: the **same** number can be written different ways (ten, `1010`), and an
"if-then" is a promise with exactly one way to break it
([explained simply](modules/truth-and-counterexamples.md)).

## 6–8 · "satisfiability, bits, and clock arithmetic"

| Strand | Skills | Self-check engine |
| --- | --- | --- |
| Logic & reasoning | **satisfiability vs validity**; counterexamples as disproof; spotting fallacies (straw man, false dilemma); De Morgan | Bool/SAT ✅, proofs (DRAT/Alethe) ✅ |
| Math | **modular ("clock") arithmetic**; negative numbers; fractions; simple equations | LIA ✅, modular ✅ |
| Computer science | **bits, bytes, overflow**; how a computer *adds* (ripple-carry); fixed precision; why `255 + 1 = 0` | **bit-vectors** ✅ |

Big idea: "is there a value that makes this true?" is a question a machine can
**settle** — and when the answer is "no," it can **prove it**. Worked module:
[Binary & wraparound](modules/binary-and-wraparound.md).

## 9–12 · "validity, proof, and verifying programs"

| Strand | Skills | Self-check engine |
| --- | --- | --- |
| Logic & reasoning | **validity vs soundness**; proof by contradiction; quantifiers (∀/∃); reading a formal proof | SAT/SMT ✅, quantifiers (finite) ✅, Lean reconstruction 🔭 |
| Math | linear systems; polynomials; inequalities; intro real analysis; nonlinear facts (e.g. `a²+b² ≥ 2ab`) | LIA/LRA ✅ (Farkas-certified), NRA 🧮🔭 |
| Computer science | algorithms & complexity; **program verification** ("can we *prove* this code never crashes?"); symbolic execution; SAT/SMT as a tool | EUF, BV, BMC/k-induction ✅, proof export 🔭 |

Big idea: mathematics, logic, and computing **converge** — proving a theorem and
proving a program correct are the *same act*, and you can watch a machine do it
and check the proof yourself.

## How a skill becomes a self-checking exercise

Every cell above becomes exercises the same way `axeyum-scenarios` already builds
them — **no answer key**:

- **A "true" claim** (e.g. a tautology, an identity, a valid argument) is checked
  by asserting its **negation** and confirming the platform finds **no** way to
  satisfy it — and can emit a re-checkable proof of that.
- **A "false" claim** is refuted by a **concrete counterexample** the student can
  plug back in and see fail.
- **A "find an x"** task is checked by **replaying** the student's `x` through the
  original problem (it either works or it visibly doesn't).
- **Honest "unknown"** is allowed — for the hard/Lean-horizon cells, the platform
  says so rather than bluffing.

This is why the four strands fuse: *checking a claim* is simultaneously a math
fact, a logical decision, a computation, and an exercise in justification.

## Mapping to the rigorous backbone

Each band's math skills are early stops on the
[Formal Mathematics Tour](../README.md) DAG (e.g. 6–8 modular arithmetic →
`02-structures/modular-arithmetic`; 9–12 linear systems → `03-destinations/linear-algebra`).
The K-12 layer doesn't replace that graph — it provides the **on-ramp and the
pedagogy**, and hands students off to the rigorous nodes when they're ready.

See the [vision](README.md) for the why, and the
[modules](modules/binary-and-wraparound.md) for the template in action.
