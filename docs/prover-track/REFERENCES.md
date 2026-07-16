# References — index

**87 arXiv papers, 29 repositories, 265 unique URLs** across the track. This is the
index; the notes carry the citations and the arguments. Where a claim's *meaning*
matters more than its URL, the note is the authority — this file exists so nobody
has to grep for a source.

**Coverage boundary is stated at the bottom.** It is not complete, and the gaps are
named rather than left for a reader to discover.

## By note

| Note | Sources | Covers |
|---|---:|---|
| [`01-itp-anatomy.md`](research/01-itp-anatomy.md) | 41 | de Bruijn criterion; LCF; kernels measured from source; Coq's 78 critical bugs; Pollack-consistency |
| [`02-ai-assisted-proving.md`](research/02-ai-assisted-proving.md) | 42 | Neural proof search; AlphaProof/DeepSeek/Goedel/Kimina; hammers; the Mathlib network effect |
| [`03-atp-itp-seam.md`](research/03-atp-itp-seam.md) | 38 | Proof reconstruction; Alethe/CPC/LFSC/Ethos; `bv_decide`; **SMT instability (Mariposa/Shake/Cazamariposas)** |
| [`04-software-ir-verification.md`](research/04-software-ir-verification.md) | 53 | Rust verification; Alive2/Vellvm; the crypto vertical; seL4/CompCert; **Verification Theatre** |
| [`05-education-and-agentic.md`](research/05-education-and-agentic.md) | 57 | Lean in teaching; browser provers; **agent surfaces (Pantograph, LeanDojo, MCP)**; counterexamples |
| [`06-kernel-gap-analysis.md`](research/06-kernel-gap-analysis.md) | — | *Our code.* Cites `file:line`, correctly |
| [`07-reconstruction-assets.md`](research/07-reconstruction-assets.md) | — | *Our code.* |
| [`08-solver-automation-assets.md`](research/08-solver-automation-assets.md) | — | *Our code.* |
| [`09-P0-kernel-unsoundness.md`](research/09-P0-kernel-unsoundness.md) | — | *Our incident.* |
| [`10-autoformalization.md`](research/10-autoformalization.md) | 17 | Faithfulness gap; benchmark contamination; **SPEAC/UCLID5**; scope laundering |
| [`11-dedukti-and-substrates.md`](research/11-dedukti-and-substrates.md) | 29 | λΠ-modulo/Dedukti/Lambdapi/Logipedia/hol2dk; **Metamath Zero** |
| `12-elaboration-egraphs-fmf.md` *(in progress)* | — | **Lean elaborator (Ullrich & de Moura); egg/equality saturation; finite model finding** — the three load-bearing gaps this audit found |

## The sources that actually changed a decision

Not the most-cited — the ones that moved something.

| Source | What it decided |
|---|---|
| **Mariposa** (FMCAD 2023) + **Shake** (FMCAD 2024) | Instability is a property of *undecidable encodings*, not SMT: `KomodoD` 5.01% vs `KomodoS` (decidable) **0.52%**. And 96–99.94% of context is irrelevant, causing **78.3%** of instability → T6.3.6's ratchet design |
| **Cebeci, Bjørner, Candea, Pit-Claudel**, *A Conjecture Regarding SMT Instability* | **Z3's own author** says instability is "often caused by fixable engineering problems… **not fundamental**" → *don't sell "SMT is broken"* |
| **SPEAC/Eudoxus** (NeurIPS 2024) | **0/33 across 660 attempts** on a low-resource formal language → **never invent a surface syntax**; goals are data |
| **Kobeissi**, *Verification Theatre* (ePrint 2026/192) | 13 vulns escaped, **4 inside verified code**, from an undocumented boundary → every slice ships its TCB statement |
| **Carneiro**, Metamath Zero | The producer/consumer split *is* this design → binary certificates; throughput as a defended gate |
| **Deducteam** / Logipedia / hol2dk | Dedukti **grows** the TCB → rejected; *"don't build the universal thing, build the bridge someone wants"* |
| **Mohamed et al.**, lean-smt (CAV 2025) | `lean-smt` targets **CPC, not Alethe**; cvc5's Alethe has **no bit-vectors** → **[ADR-0166](../research/09-decisions/adr-0166-alethe-target-reassessment.md)** |
| **Barendregt & Geuvers** (Handbook, 2001) | The de Bruijn criterion *and* its tension with the **Poincaré principle** → why kernel accelerators cost soundness (Coq: 20 of 78 bugs in conversion machines) |
| **Wiedijk**, *Pollack-inconsistency* (ENTCS 285) | A sound kernel is not enough — the printer is in scope → **T6.0.9** |
| **Carneiro**, `native_decide` leakage (Zulip, 2023-10-10) | The **only** empirical win for independent checkers: `lean4checker` rejected a proof of `False` the kernel accepted |
| **Keep the Proof State Live** | **~99.9%** of agent per-branch time is import + re-elaboration → we have nothing to import; the agent surface is structurally cheap for us |
| **MCP-Solver** (SAT 2025) | *"Fewer tools perform better"* → P6.4 ships a narrow surface |

## Repositories read or measured (29)

**Kernels/checkers:** `leanprover/lean4` · `ammkrn/nanoda_lib` · `leanprover/lean4checker` ·
`digama0/lean4lean` · `digama0/mm0` · `rocq-prover/rocq` · `jrh13/hol-light` ·
`Deducteam/Dedukti` · `Deducteam/lambdapi` · `Deducteam/Logipedia` ·
`Deducteam/hol2dk` · `Deducteam/isabelle_dedukti` · `david-a-wheeler/mmverify.py`

**Solvers/proofs:** `cvc5/ethos` · `leanprover/leansat` · `secure-foundations/mariposa` ·
`viperproject/smt-scope` · `gburel/lrat2dk`

**Verification:** `AeneasVerif/aeneas` · `AliveToolkit/alive2` · `creusot-rs/creusot` ·
`cryspen/hax` · `awslabs/aws-lc-verification` · `microsoft/SymCrypt` (`feature/verifiedcrypto`)

**Agents/education:** `lean-dojo/LeanDojo-v2` · `leanprover/Pantograph` ·
`leanprover-community/lean4web` · `leanprover-community/NNG4` ·
`trishullab/PutnamBench` · `roozbeh-yz/miniF2F_v2`

## What is NOT covered — the boundary

Named per *Verification Theatre*'s own lesson.

| Gap | Status |
|---|---|
| **Isabelle** | **Essentially nothing verified.** Kunčar & Popescu's overloading inconsistency is cited once; no measured TCB; no kernel-bug record. Isabelle has no public equivalent of Coq's `critical-bugs.md` — itself a citable asymmetry. **The largest remaining hole.** |
| **Systems-verification economics** | A thread on seL4 adoption (NASA/cFS, NIO SkyOS, Cog Systems, the seL4 Foundation) and the CACM Woodcock/Larsen material was **started and killed mid-flight**. Note 04's person-year figures stand; the *adoption/economics* picture does not exist and must not be inferred. |
| **Mtac, Andromeda, Nuprl** | Not covered. Alternative tactic/prover designs; Nuprl is in Barendregt & Geuvers' own table. |
| **Dedukti quantitatives** | Kernel LoC, per-translator coverage %, Cousineau–Dowek primary citation — search-only. |
| **Metamath quantitatives** | The "5 verifiers" rule, Metamath 100 count, set.mm size — search-derived. Only `mmverify.py`'s 708 lines is measured. |
| **arXiv 2606.29493** (Biderman et al., *Faults in Our Formal Benchmarking*) | PDF extraction failed twice. **Probably the best single citation for benchmark contamination** and we cite it as a gap, not a source. |
| **hal-04861898** (Lambdapi SMT reconstruction) | Fetch-blocked. If it covers bit-vectors, note 11's Dedukti rejection needs revisiting. |
| **Faithfulness audits of the large corpora** | Goedel-Prover's 1.64M, DeepSeek-Prover-V1's 8M — none found. Load-bearing for note 10's central claim, and unconfirmed as a genuine *absence* rather than a search failure. |

## Claims checked and found FALSE — do not re-derive

| Claim | Reality |
|---|---|
| Coq **#7825** is a kernel bug | It is a **tactics/unification PR**. Use #20413 / #21053 / #22024 instead. |
| `nanoda_lib` is a Lean-3-era artifact | **Lean 4**, actively maintained (last commit 2026-06-02), 9,203 lines Rust. |
| "Lean 4 cannot compile to WASM" | **Unverified.** What is known: Lean4Web runs Lean *server-side behind gVisor*. |
| HOL Light's kernel is "~400 lines" | Wiedijk's 2010 figure. **548 non-blank today.** |
| `mmverify.py` is "350 lines" | The 2002 original. **708 today.** |
| Lean Workbook has ~140K pairs | **~57K.** The 140K conflates it with Lean-Workbook-Plus. |
| arXiv 2606.16541 *The Faithfulness Gap* | **Uncitable pending review** — unknown authors, no venue, unusually tidy numbers. |
| `coqchk` is an independent checker | It **links `rocq-runtime.kernel`** — the kernel it checks. Coq ships no independent kernel. |
| `lean4lean` is an independent implementation | Its own README: *"not really an independent implementation."* |
