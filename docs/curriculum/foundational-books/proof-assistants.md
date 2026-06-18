# Proof Assistants & the Lean-Horizon Curriculum

The deep, `∀`-quantified material our curriculum flags as **Lean-horizon** (ε-δ
analysis, induction-bearing arithmetic, program-correctness proofs) is the home
turf of *proof assistants*. This page records the reference curriculum and tools
to align with if/when axeyum's proof track (P3.6 in-tree Lean kernel, P3.7
Alethe→Lean reconstruction) matures — see [../DEPTH.md](../DEPTH.md).

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
- When P3.6/P3.7 land, **SF-in-Lean is the curriculum to align reconstruction
  targets with** (and a potential collaboration/alignment point — the project is
  actively seeking contributors as of 2026).

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
| Lean-horizon | flagged, not built | **Software Foundations in Lean** (kernel-checked proofs) |
| Tooling | `check_alethe` / Carcara / planned Lean kernel | Lean 4 + **Verso** |

This is direction-setting, not a build item: it names where the `lean-horizon`
nodes go when the proof track is ready.
