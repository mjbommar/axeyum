# Proof Assistants & the Lean-Horizon Curriculum

The deep, `∀`-quantified material our curriculum flags as **Lean-horizon** (ε-δ
analysis, induction-bearing arithmetic, program-correctness proofs) is the home
turf of *proof assistants*. This page records the reference curriculum and tools
for deepening Axeyum's bounded kernel/reconstruction work — see
[../DEPTH.md](../DEPTH.md). The in-tree checker and selected reconstruction
routes are real; general theorem authoring and full Lean workflow compatibility
remain separate horizons.

## Software Foundations (Pierce et al.) — *now being translated to Lean*

<https://softwarefoundations.cis.upenn.edu/>

The canonical textbook series on **formal proof and the foundations of
programming languages** — Logical Foundations, Programming Language Foundations,
Verified Functional Algorithms, and more — historically formalized in **Rocq
(Coq)**. As of mid-2026, Benjamin Pierce announced a serious **translation to
Lean**, aimed at Fall courses at Penn and elsewhere (small team; a public call
for contributors and alpha-testers went out via the Lean Zulip
*#Lean for teaching*).

Why it's *the* reference for our educational axis: SF teaches exactly the trio
this curriculum cares about — **logic & proof, formal verification, and proof
assistants** — but on the *proving* side of the ladder that SMT self-checking
cannot reach. Concretely:

- Our **software-verification family** (`Family::Verification`: abs/max/overflow
  as decidable BV instances) is the SMT-decidable shadow of SF's
  program-correctness proofs.
- Our **Lean-horizon nodes** (`calculus`, `reals`, induction, `cardinality`) are
  exactly what SF-in-Lean *proves* with a kernel-checked proof rather than
  decides.
- **SF-in-Lean is a curriculum to align future reconstruction targets with**:
  it emphasizes the definitions, induction principles, and program semantics
  that bounded SMT exercises intentionally omit.

## Verso — Lean's documentation authoring system

<https://verso.lean-lang.org/>

Verso writes Lean-checked documents/books with live elaboration — the natural
toolchain for authoring kernel-checked educational content, and the likely
substrate for SF-in-Lean. If axeyum ever emits Lean-checked curriculum artifacts
(reconstructed proofs as readable lessons), Verso is the target format.

## Relation to the axeyum curriculum

| Layer | axeyum today | Proof-assistant counterpart |
|---|---|---|
| Decidable shadow | self-checking scenarios + certificate tests (this curriculum) | the "easy" exercises SF can also discharge by `decide`/automation |
| Lean-horizon | target statements plus selected bounded reconstruction slices | **Software Foundations in Lean** (kernel-checked proofs) |
| Tooling | in-tree Lean-core checker, selected reconstruction, Alethe/Carcara checking | Lean 4 + **Verso** |

This is direction-setting, not a parity claim: it names the proof-assistant
curriculum that should shape deeper `lean-horizon` work.
