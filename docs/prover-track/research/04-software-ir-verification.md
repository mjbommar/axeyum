# Software / IR Verification Landscape (2024–2026)

Research note for the prover track. Survey date: 2026-07-15. Scope: Rust
verification, LLVM/IR-level tooling, the crypto vertical, systems verification,
and the bounded-vs-unbounded economics question. Written to answer one question:
**is there a defensible position for axeyum between push-button-but-bounded and
sound-but-person-years?**

Sources are cited inline. Where a claim is soft (adoption, "traction"), it is
marked as such — most public "adoption" claims in this space are unmeasured.

---

## 1. Rust verification tools

### 1.1 The tool matrix

| Tool | IR level | Logic / method | Backend | Unbounded? | Notes |
|---|---|---|---|---|---|
| **Kani** (AWS) | rustc **MIR** | bounded model checking; assertions + function/loop contracts | rustc→GOTO (`cprover-bindings`)→**CBMC**→SAT/SMT (MiniSat, Z3, cvc5, Bitwuzla) | Only via loop/function contracts | Most-deployed. See §1.2. |
| **Verus** | MIR-ish (own front-end over Rust syntax) | SMT-based deductive; linear/ghost state, spec/proof/exec modes | **Z3** | Yes | Fastest deductive Rust tool; ~5 lines proof per impl line in case studies |
| **Creusot** | MIR | prophecy-based deductive verification of mutable borrows; Pearlite specs | **Why3** → SMT (Z3/CVC5/Alt-Ergo) | Yes | Active; new features + case studies presented Jan 2026 |
| **Prusti** | MIR | Viper separation logic; ownership-as-permission | **Viper** (Silicon/Carbon) → Z3 | Yes | Oldest of the deductive set; effectively the reference point others cite |
| **Flux** | MIR | **refinement/liquid types**, annotation-light | Z3/Fixpoint | Yes (type-level) | Accepted tool in the std-lib challenge; lowest annotation cost of the sound tools |
| **RefinedRust** | MIR (via Radium) | **Iris/RefinedC-style** semantic type system, foundational | **Rocq/Coq** (foundational proof) | Yes | Highest assurance, highest cost. Foundational: no SMT in TCB. |
| **Aeneas** + **Charon** | **LLBC** (Charon's low-level borrow calculus, from MIR) | translate safe Rust → *pure functional* model; no separation logic needed | **Lean 4** (also F*, Rocq, HOL4) | Yes | The SymCrypt path. See §3. |
| **hax** (Cryspen) | THIR/MIR-ish | annotation-driven extraction, multi-backend | **F\***, **Lean 4**, Rocq, ProVerif, SSProve | Yes | F* backend mature; Lean backend actively catching up |

References:
- Kani: <https://arxiv.org/html/2607.01504v1>, <https://github.com/model-checking/kani>
- Verus: <https://www.microsoft.com/en-us/research/publication/verus-a-practical-foundation-for-systems-verification/>, <https://www.microsoft.com/en-us/research/wp-content/uploads/2024/09/verus.pdf>, <https://verus-lang.github.io/verus/guide/>
- Creusot: <https://github.com/creusot-rs/creusot>
- Prusti / hybrid comparison: <https://arxiv.org/pdf/2403.15122>
- RefinedRust: <https://plv.mpi-sws.org/refinedrust/paper-refinedrust.pdf>
- Aeneas/Charon: <https://aeneasverif.github.io/projects/>, <https://github.com/AeneasVerif>, <https://lean-lang.org/use-cases/aeneas/>
- hax: <https://github.com/cryspen/hax>, <https://eprint.iacr.org/2025/142.pdf>, <https://hax.cryspen.com/blog/>
- Rust Formal Methods Interest Group (the community hub): <https://rust-formal-methods.github.io/>

**The IR-level split is the important structural fact.** Everything serious in
Rust verification has converged on **MIR** (or an MIR derivative: Charon's LLBC).
The Kani paper is explicit about why: MIR "preserves Rust-specific type
invariants that are lost at the LLVM level." This is a direct hit on any design
that plans to verify Rust *at LLVM IR*. Rust's ownership/aliasing information —
the thing that makes Rust verification tractable at all — is gone by the time you
reach LLVM. **This is the single most important architectural finding in this
note for axeyum** (see §7).

### 1.2 Who is actually gaining traction in 2026?

Ranked by *evidence*, not enthusiasm:

1. **Kani — by a wide margin, on adoption.** In production CI at:
   - Firecracker: 34 harnesses, 21 min
   - s2n-quic: 102 harnesses, 23 min (same harness runs as both Bolero fuzz test
     and Kani proof via one attribute — this dual-use trick is a real adoption
     lever)
   - Rust std library: 16,748 harnesses per code change, 69 min
   - AWS blog on OSS users: <https://aws.amazon.com/blogs/opensource/how-open-source-projects-are-using-kani-to-write-better-software-in-rust/>

   Kani found **11 bugs across production codebases that testing and fuzzing
   missed** (s2n-quic encoding boundary/packet-number overflow; Firecracker
   rate-limiter rounding + VirtIO protocol violations; Cedar string-processing
   logic bugs; hifitime six bugs incl. normalization overflow and Eq/Ord
   inconsistency). That is the strongest *bounded* value evidence in the note.
   Source: <https://arxiv.org/html/2607.01504v1>

2. **Aeneas/Charon → Lean — gaining fastest on the "credible high assurance"
   axis**, because Microsoft put production crypto behind it (§3).

3. **Verus** — strongest *research* traction for systems code (distributed
   systems, OS page table, NR concurrent replication, crash-safe storage,
   concurrent allocator: 6.1K impl + 31K proof lines). Under review for
   std-lib challenge inclusion, not yet accepted. Industrial deployment
   evidence: thin.

4. **Flux, VeriFast** — accepted std-lib tools, real but niche contribution.

5. **Prusti, Creusot, RefinedRust** — healthy research, no visible industrial
   pull.

### 1.3 The industrial picture: the Rust std library verification challenge

The most informative single datapoint in this whole survey.

- Run by AWS + Rust Foundation: <https://aws.amazon.com/blogs/opensource/verify-the-safety-of-the-rust-standard-library/>,
  <https://github.com/model-checking/verify-rust-std>
- Results paper: <https://arxiv.org/html/2606.17374v1> (also
  <https://link.springer.com/chapter/10.1007/978-3-032-28079-4_19>); WIP lessons:
  <https://arxiv.org/html/2510.01072v1>

Numbers (as of the nightly-2025-10-08 snapshot / 2026 paper):

- **33,955 functions** in core+alloc+std.
- **Four tools in CI**: Kani, VeriFast, Flux, ESBMC (via GOTO Transcoder). Four
  more under review: Verus, Creusot, KRust, RAPx.
- **Autoharness**: 16,748 harnesses generated, **11,970 verified** against Kani's
  supported UB classes. 4,645 for unsafe fns; 1,126 for safe abstractions over
  unsafe.
- **Manual**: 725 harnesses w/ contracts (694 Kani), 50+ VeriFast proofs.
  Combined **989 functions with formal contracts**.
- 450+ PRs, 21+ external contributors. 3.97× compile speedup needed to make CI
  viable.

**And the punchline, which everyone should sit with: after 16+ months and this
much machinery, ZERO previously-unknown memory-safety vulnerabilities were
found.** What it produced instead: incorrect SAFETY comments, missing `unsafe`
annotations, documentation errors — i.e., **specification defects, not code
defects**. This drove function contracts toward being an experimental Rust
language feature.

Honest reading: the Rust std library was already very good. Verification's
delivered value here was *specification hygiene* and *regression protection*, not
bug-finding. Anyone pitching "verification finds bugs" into a mature Rust
codebase is selling against this datapoint.

Stated blockers from the paper (these are the real research frontier):
- **Generics**: 9,635 functions (56% of skipped) have unresolved type params —
  Rust monomorphizes at compile time, so contracts verify per-monomorphization.
- **Intrinsics**: 71 unsupported intrinsics, 813 unmodeled functions block
  downstream verification.
- **UB coverage is incomplete**: Kani does *not* detect Stacked/Tree Borrows
  aliasing violations, data races, or all provenance UB. Aliasing is the
  *primary* UB class in unsafe Rust. This is a soundness gap in the marketing
  sense, not just a coverage gap.
- **Manual contracts plateaued ~October 2025.** Automation kept climbing; human
  annotation did not. Read that as a market signal.
- **"No single tool suffices"** — linked structures need separation logic; model
  checking suits non-heap-intensive code. The campaign's own conclusion is
  *tool pluralism*, not a winner.
- Proof maintenance across Rust's six-week release cycle is a live cost.

---

## 2. LLVM / IR-level verification

### 2.1 Alive2

- Paper: PLDI 2021, <https://dl.acm.org/doi/10.1145/3453483.3454030>;
  slides <https://web.ist.utl.pt/nuno.lopes/pres/alive2-pldi21.pdf>;
  repo <https://github.com/AliveToolkit/alive2>; funding
  <https://nlnet.nl/project/Alive2/> (grant deadline 2026-08-01 — i.e. still
  funded and active).

**Architecture** (worth internalizing, it's close to axeyum's shape):
- Consumes **two LLVM IR functions** (src, tgt) — typically pre/post an
  optimization pass.
- Encodes both into a logical refinement check: `tgt` must **refine** `src`
  (poison/undef/UB refinement lattice, not plain equality — this is the subtle,
  hard part and where most of the intellectual content lives).
- **Bounded**: unrolls all loops to a user-supplied global bound.
- Memory model: a block-based model handling pointer/integer mixing.
- Discharges to an **SMT solver** (Z3). No LLVM changes required. Designed to
  **avoid false alarms** — a deliberate soundness-vs-completeness trade in the
  *opposite* direction from most academic tools, and a big part of why LLVM devs
  tolerate it.
- Runs over LLVM's own unit test suite → this is the key deployment trick: it
  piggybacks on an existing test corpus rather than demanding new specs.

**Real bugs**: 47 new LLVM bugs reported at publication (28 fixed); ~54 by the
time of the slide deck. Plus **eight patches to the LLVM Language Reference** —
Alive2 found that the *spec itself* was ambiguous/wrong. That's the same
"verification finds spec bugs, not code bugs" pattern as the Rust std campaign.

Extensions: adapted for **AArch64 translation validation**, handling unstructured
pointer/integer mixes typical of assembly.

### 2.2 The rest of the LLVM-level stack — status honestly assessed

- **Vellvm** — foundational Coq semantics for LLVM IR. Research vehicle; the
  authoritative *semantics* reference. Not a tool anyone ships with.
- **SeaHorn** — LLVM-bitcode → CHC → PDR/Spacer. Architecturally the closest
  public analogue to axeyum's PDR/IMC/CHC engines. Related recent work:
  **SEABMC** (<https://repositum.tuwien.at/bitstream/20.500.12708/219563/1/Tafese%20Joseph%20-%202025%20-%20A%20Tale%20of%20Two%20Case%20Studies%20A%20Unified%20Exploration%20of%20Rust...pdf>)
  explicitly explores Rust verification through a SeaHorn/BMC lens.
- **SMACK** — LLVM → Boogie. Long-lived, low-activity.
- **KLEE** — symbolic execution over LLVM bitcode. Still the reference symbolic
  executor; substantial ongoing academic use, thin industrial deployment.
- **Crux-LLVM** (Galois) — symbolic execution over LLVM; part of the Galois
  SAW/Crucible family. Lives inside the crypto vertical (§3) rather than as a
  general tool.

### 2.3 Is IR-level translation validation growing or shrinking?

**Neither — it's consolidating, and being re-targeted.** Read carefully:

- *Growing* as a **substrate for other things**: TV has become the standard
  correctness oracle for LLM-generated/LLM-generalized compiler work.
  See "Leveraging LLMs for Generalizing Peephole Optimizations"
  (<https://arxiv.org/pdf/2603.18477>), "LLM Translation of Compiler
  Intermediate Representation" (<https://arxiv.org/pdf/2605.08247>),
  "Galapagos: Automated N-Version Programming with LLMs"
  (<https://arxiv.org/pdf/2408.09536>). This is the actual growth vector, and
  it's a *derived demand*: LLMs generate plausible-but-wrong IR at volume, and
  something has to check it. TV is that something.
- *Not growing* as a **standalone product category**. Alive2 remains
  essentially one tool, one small team, grant-funded, unreplaced in 5 years. If
  the category were commercially hot, there'd be competitors.
- Re-targeting downward: AArch64/assembly TV, where the payoff (hand-written
  crypto assembly) is concentrated.

**The honest conclusion for axeyum: "IR-level TV" is not a market. It is a
technique with exactly one durable customer profile — compiler/crypto teams who
already believe — plus one emerging one (checking machine-generated IR).** The
second is real and new, and is the more interesting reading.

---

## 3. The crypto vertical — and the Lean shift

Crypto is where verification has an actual, repeated, decade-long commercial
record. It is the only vertical where "we verified it" changes procurement
outcomes. Understand *why*: specs are short, stable, standardized (FIPS/NIST/
IETF), adversarial, and the code is small, loop-simple, and performance-critical
enough to be hand-written and therefore bug-prone.

### 3.1 The incumbents

- **HACL\* / F\*** (INRIA/MSR) — verified C crypto, shipped in Firefox NSS,
  Linux kernel, WireGuard, mbedTLS, Tezos. The decade-long success case.
- **fiat-crypto** (MIT) — Coq-synthesized field arithmetic. Shipped in
  **BoringSSL, Chrome, Firefox, Go, AWS-LC**. Arguably the most widely-deployed
  formally verified code on earth. The killer property: *synthesis*, not
  verification — you don't verify hand-written code, you generate correct code
  from a spec.
- **Jasmin + EasyCrypt** — crypto-oriented assembly language with a Coq-verified
  compiler; EasyCrypt for functional + game-based security proofs.
  Cloudflare used it for PQ work:
  <https://blog.cloudflare.com/post-quantum-easycrypt-jasmin/>. "The Last Mile"
  is the canonical paper: <https://arxiv.org/pdf/1904.04606>.
- **SAW / Cryptol** (Galois) — spec language + symbolic-execution-based
  equivalence checking against LLVM/JVM/x86. Deployed in
  **aws-lc-verification**: <https://github.com/awslabs/aws-lc-verification>.
  This is CI-integrated: "portions of AWS-LC have been formally verified … with
  checks run in AWS-LC's CI on every change."
- **s2n-bignum** (AWS) — x86_64 + AArch64 assembly verified in **HOL Light**,
  including ML-KEM/ML-DSA assembly components. AWS uses *different provers for
  different layers*: HOL Light for assembly, Coq/fiat-crypto for field
  arithmetic, Coq for group properties.
  Overview: <https://www.amazon.science/publications/formal-verification-of-cryptographic-software-at-aws-current-practices-and-future-trends>,
  <https://www.nist.gov/system/files/documents/2024/06/11/01-ChapmanPHPLBK.pdf>
- **libcrux** (Cryspen) — Rust ML-KEM verified via **hax → F\***, compiled to C
  via Eurydice for Mozilla NSS; in production since ~late 2023.
  <https://cryspen.com/post/ml-kem-verification/>,
  <https://cryspen.com/post/ml-kem-implementation/>

Skeptical counterweight — **now confirmed, and it is sharper than expected**:
**"Verification Theatre: False Assurance in Formally Verified Cryptographic
Libraries"**, Nadim Kobeissi (Symbolic Software), IACR ePrint 2026/192, received
2026-02-05 (<https://eprint.iacr.org/2026/192>).

Its thesis: the vulnerability is not in the proofs, it is in the **verification
boundary** — the undocumented interface between machine-checked code and the
trusted-but-unverified code around it. Users cannot tell where the guarantee
stops, so they assume it doesn't.

The receipts: **13 vulnerabilities that escaped formal verification** in
**libcrux** and **hpke-rs** (Cryspen), with AWS's libcrypto as comparison:
- **9 in unverified code adjacent to verified code** — an endianness bug causing
  **real Signal decryption failures**, missing X25519 validation, nonce reuse via
  integer overflow, FIPS 204 spec violations.
- **4 inside the verified code itself** — wrong decompression constants, a
  missing inverse operation, a **false serialization proof**, and a
  multiplication *specification* error that undermined the AVX2 proofs.

Read that last group carefully. Four bugs *in verified code* means the proofs
were checked and still wrong, because **the specs were wrong** — the same
"verification finds spec defects" pattern as §1.3 and §2.1, but here it runs in
the other direction: the spec defect *survived* the proof and shipped.

Kobeissi's remedies are, notably, artifact-engineering remedies, not proof-theory
ones: systematic boundary documentation, **proofs executed in CI/CD**, explicit
scope communication. That is an evidence-artifact agenda, and it is the same one
SymCrypt's README implements (§3.2) and the same one §7.3 recommends for us.
Cite this paper every time someone says "it's verified" — including us.

### 3.2 microsoft/SymCrypt `feature/verifiedcrypto` — the headline event

This is the most important artifact in this note. Researched directly.

Sources:
- <https://www.microsoft.com/en-us/research/blog/verifying-rust-cryptography-in-symcrypt-from-standards-to-code/> (2026-07-13 — **two days before this survey**)
- <https://www.microsoft.com/en-us/research/blog/rewriting-symcrypt-in-rust-to-modernize-microsofts-cryptographic-library/> (2025-06)
- <https://github.com/microsoft/SymCrypt/tree/feature/verifiedcrypto>
- `README-VERIFIEDCRYPTO.md` (raw:
  <https://raw.githubusercontent.com/microsoft/SymCrypt/feature/verifiedcrypto/README-VERIFIEDCRYPTO.md>)

**What it is**: SymCrypt is *the* core crypto library for Windows and Azure
Linux. The branch carries Rust implementations (`SymCRust/`) with formal proofs
of **functional correctness against FIPS/NIST/IETF specs, plus panic-freedom**,
via **Rust → Charon → Aeneas → Lean 4**.

**Scale — the hard numbers from the README (these are gold):**

| Component | Rust LOC | Proof LOC | Ratio |
|---|---|---|---|
| SHA-3 / SHAKE | 1,656 | 15,211 | **9.2:1** |
| ML-KEM | 2,125 | 37,989 | **17.9:1** |
| HW intrinsics (shared model) | 1,748 | 5,177 | 3.0:1 |
| **Total** | **~5,529** | **~58,377** | **~10.6:1** |

**Status**: not a demo. The ML-KEM and SHA-3 Rust code being proven **is running
in Windows Insider builds today**. Roadmap: AES-GCM, FrodoKEM, ML-DSA, into
production Windows and Linux.

**Trusted base** (README is admirably explicit — this is a model of honest
claiming, worth imitating):
- Lean kernel soundness
- Charon/Aeneas extraction fidelity (Rust → LLBC → pure Lean model)
- Rust compiler + platform backends (x86_64, AArch64)
- Specs faithfully matching the standards
- "Constant-time" coding practices — **and note: leakage resistance is
  explicitly NOT verified.** Functional correctness and safety only.

**Reproducibility** (this is the part axeyum should copy): **the extracted Lean
code is committed to the repo.** Reviewing the proofs needs *only Lean 4* —
`lake build`, **~15 minutes**. You only need Charon/Aeneas installed if you want
to re-run extraction from Rust. That is a deliberate, sophisticated
**evidence-artifact design decision**: they separated *producing* the proof
(needs the whole exotic toolchain) from *checking* it (needs one widely-installed
checker, 15 min). Untrusted fast search, trusted small checking — this is
literally axeyum's identity sentence, executed by Microsoft, in production, this
month.

Also notable: the toolchain **compiles the code several times, once per
compilation target**, then merges the models — that's how they handle
multi-architecture intrinsics.

### 3.3 Why Lean and not F\*, given HACL\* history?

This is the question worth the most. **Caveat up front, now verified by direct
fetch of both posts (2025-06 and 2026-07): neither Microsoft blog contains an
explicit "we rejected F\* because X" statement. The 2025-06 post does not mention
F\* or HACL\* at all.** For a Microsoft/INRIA effort whose personnel and problem
domain *are* the HACL\* lineage, that silence is itself information: this is
being presented as a new pipeline, not as a migration away from something. So
what follows is inference from stated rationale + structural facts. Treat it as
argued, not sourced.

The stated reason (MSR blog, 2025-06 — full quote, direct fetch):
> "We chose Aeneas because it helps provide a clean separation between code and
> proofs. Developed by Microsoft Azure Research in partnership with Inria … Aeneas
> connects to proof assistants like Lean, allowing us to draw on a large body of
> mathematical proofs—especially valuable given the mathematical nature of
> cryptographic algorithms—and benefit from Lean's active user community."

Note the grammar of that sentence: **the choice being defended is _Aeneas_, and
Lean arrives as its consequence.** That is the whole answer, and it is easy to
miss. Condensed:
> "Aeneas connects to proof assistants like Lean, allowing us to draw on a large
> body of mathematical proofs—especially valuable given the mathematical nature
> of cryptographic algorithms"

The 2026 post adds Lean's "small trusted kernel" and "extensibility" for custom
automation, plus two limitations worth recording: intrinsics need "small,
carefully reviewed Lean specifications" rather than automated verification, and
multi-target compilation requires translating the code once per architecture.

The real drivers, as best I can reconstruct:

0. **The question is slightly wrong: they didn't choose Lean over F\*, they chose
   Aeneas — and Lean came with it.** Aeneas ships backends for F\*, Rocq, HOL4,
   and Lean, but **Lean is the main backend**; Lean and HOL4 are the only mature
   ones, because they carry what Aeneas's output actually needs: support for
   partial functions, extrinsic proofs of termination, and tactics specialized
   for monadic programs (<https://aeneasverif.github.io/projects/>,
   <https://github.com/AeneasVerif/aeneas>). So once you have decided the source
   of truth is **Rust** rather than F\* (driver 4 below), and therefore that you
   need a Rust→model translator, and therefore Aeneas — **Lean is the default,
   not a comparison you run.** F\* was never a live option at the point the
   decision was actually made; it was excluded one step upstream. This reframing
   matters for us: the leverage in this pipeline is in *which translator wins*,
   not which prover wins, and drivers 1–3 explain why the translator that won
   points at Lean.

1. **Mathlib is the moat, and PQC is the forcing function.** HACL*/F* was built
   for an era where crypto meant curves and hashes — bounded machine-integer
   reasoning F* handles fine. **ML-KEM/ML-DSA changed the math**: lattices,
   NTTs, polynomial rings, module-LWE. You now need actual algebra. Lean has
   **Mathlib4**; F* has nothing comparable and never will, because Mathlib is
   ~a decade of thousands of contributors. The zkEVM pipeline paper makes the
   same point explicitly, connecting "production Rust to Mathlib4-level formal
   cryptographic specifications" via **ArkLib** (SNARKs) and **CompPoly**
   (polynomial theory). **The verification target moved to where the math
   library is.** F* didn't lose on proof-assistant merit; it lost on library
   gravity.

2. **`bv_decide` closes the automation gap that used to be F\*'s advantage.**
   Historically you chose F* because SMT automation made bounded-integer/bitvector
   grunt work tractable, and you paid for it with Z3 in your TCB and Z3's
   flakiness in your dev loop. Lean 4.12.0 (2024-10-01) shipped **`bv_decide`**:
   the *first end-to-end verified bitblaster in a dependently-typed ITP*
   (<https://dl.acm.org/doi/10.1145/3763167>,
   <https://lean-lang.org/doc/reference/latest/releases/v4.12.0/>). Architecture:
   a **verified AIG** implementation for subterm sharing, goals bit-blasted to
   SAT, refuted by an **external high-performance solver (CaDiCaL)**, and the
   resulting **LRAT certificate checked inside Lean by a verified checker**.
   Caveat worth recording: it goes through `Lean.ofReduceBool`, so **the Lean
   compiler enters the TCB** — not free. Ongoing work: LRAT-Catcher
   (<https://arxiv.org/pdf/2607.00815>) imports LRAT by reflection;
   `BitVec.clz` circuits added 2025.

   **This is the pivotal fact.** Lean got F*'s automation *without* F*'s
   trust cost — untrusted CaDiCaL does the search, a verified checker does the
   checking, the kernel re-checks everything. Once that landed, F*'s main
   engineering advantage over Lean for crypto evaporated, and Lean's Mathlib
   advantage remained. **The choice made itself in October 2024.**

3. **Aeneas's functional translation removes the need for separation logic.**
   Aeneas turns safe Rust into a *pure functional Lean model* — no heap, no
   separation logic, no ghost permissions. That means the proof burden is
   ordinary math, which means Mathlib applies, which means (1) compounds. This
   is the design insight the whole SymCrypt result rests on.

4. **Rust-first, not extract-to-C.** HACL* writes F* and extracts C — the source
   of truth is F*, which no systems engineer reads. SymCrypt/libcrux write
   **Rust** and extract *models*. The shipped artifact is code engineers can
   read, review, and modify. That's a maintainability and hiring argument, and
   it's probably the strongest non-technical driver. Note Cryspen's Eurydice
   (Rust→C) and Aeneas's **Scylla** (C→Rust) exist to migrate the *existing* C
   corpus (HACL*, SymCrypt, EverParse CBOR, bzip2 — all "partial translation
   capability" as of 2025-07) onto the Rust-first path.

**Nuance that cuts against over-reading the shift**: Cryspen's **hax** targets
F\*, Lean, **and** Rocq, and as of 2026 the **F\* backend is still the more
mature one** — libcrux's ML-KEM verification uses F\*, not Lean. The Lean backend
is "under active development" and only approaching parity (better for-loops,
more core models, better pre/post tactics). So this is **not** "F* is dead."
It's: *new* high-assurance crypto work with heavy math is choosing Lean;
established F* work is staying put. The shift is real but directional, not
completed.

### 3.4 The AI-prover thread (relevant, and mostly overhyped)

"A Rust-to-Lean Verification Pipeline with AI Provers: An Experience Report"
(<https://arxiv.org/html/2605.30106>) — Ethereum Foundation zkEVM Verification
Project. Charon/Aeneas + hax → Lean 4, with **Aristotle** (Harmonic) and
**Aleph** (Logical Intelligence) closing obligations. Targets: Plonky3 (FRI
folding, Mersenne31/KoalaBear field arithmetic, polynomial evaluation,
round-scheduling), RISC Zero Merkle inclusion, a 32-bit adder.

**The honest result: the AI provers closed exactly two theorems completely**
(the `compute_log_arity_for_round` bounds). The authors' own framing: AI is "a
productivity multiplier rather than a complete solution."

AI succeeded on: control-flow lemmas/monadic reasoning; linear arithmetic with
mild side conditions; simplification-closeable boilerplate.
AI failed on: domain-specific algebraic identities; loop invariants on recursive
functions; obligations needing external-interface axiomatization.

Their stated limitations map exactly onto SymCrypt's: Lean toolchain version
drift, Aeneas/hax extraction gaps (generics with trait bounds, external crate
calls), **no coverage of unsafe Rust**.

The one durable structural point: **"the kernel re-checks all proofs regardless
of generation method, preserving soundness."** This is why AI + Lean is
architecturally sound and AI + "trust me" is not. It is also *exactly* axeyum's
thesis. Compare the broader claims — Kleppmann, "AI will make formal
verification go mainstream" (<https://martin.kleppmann.com/2025/12/08/ai-formal-verification.html>)
and rewire.it, "When AI Writes Code, Verification Is the Job"
(<https://rewire.it/blog/when-ai-writes-the-code-verification-becomes-the-job/>)
— against this evidence: two theorems. Discount accordingly, but note the
direction of travel is not in dispute.

---

## 4. Systems verification: person-year costs

| System | Size | Effort | Prover |
|---|---|---|---|
| **seL4** | 8,700 SLOC C | **~12–20 person-years**, ~200K lines Isabelle. ~$350/SLOC. ~**20 lines proof per line of code**; ~half a person-day per LOC | Isabelle/HOL |
| **CompCert** | C compiler | **~6 person-years** in Rocq/Coq | Rocq/Coq |
| **CakeML** | ML compiler | comparable order | HOL4 |
| **Verus case studies** | 6.1K impl | **31K proof** (~5:1) | Z3 |
| **SymCrypt Rust crypto** | 5.5K Rust | **58K Lean** (~10.6:1) | Lean 4 |
| **RefinedC/RefinedRust** | — | foundational, highest cost | Rocq |

seL4: <https://sel4.systems/Verification/proofs.html>,
<https://sel4.systems/Verification/certification.html>,
<https://www.sigops.org/s/conferences/sosp/2009/papers/klein-sosp09.pdf>

**The scaling law is the load-bearing fact**: seL4's team reported **verification
effort scales with the SQUARE of specification size.** That single result
explains the entire structure of this field. It means whole-system interactive
proof does not scale, cannot scale, and no amount of tooling improvement changes
the exponent — you can only change the constant, or **shrink the spec**.

**Has whole-system interactive proof shifted to automated/bounded?** Mostly yes,
but state it precisely — three distinct things happened:

1. **The seL4 ecosystem is alive but has changed shape**: the effort went into
   *building systems on top of* the verified kernel (**LionsOS**,
   <https://arxiv.org/pdf/2501.06234>) rather than verifying more kernels. You
   verify the microkernel once, then amortize.
2. **The target shrank from "whole system" to "critical core."** Nobody is
   proposing seL4-for-Linux. The zkEVM paper says it outright: the Rust-to-proof-
   assistant pipeline requires "substantially smaller per-engagement effort, in
   exchange for verifying **specific critical-core components rather than whole
   systems**." SymCrypt is the archetype: not "verify Windows," but "verify the
   5,529 lines of Rust that matter most."
3. **Automation moved up, not in.** The proof:code ratio went from seL4's ~20:1
   to SymCrypt's ~10:1 to Verus's ~5:1 — real progress, but note it's *one order
   of magnitude across ~15 years*, and the SymCrypt number is for code that's
   maximally friendly to verification (small, loop-simple, spec'd by NIST). Do
   not extrapolate 5:1 to general software.

**Iris/RefinedC/CN**: Iris remains *the* separation-logic framework and the
intellectual center of gravity; RefinedC/RefinedRust are its Rust/C
manifestations; CN (CHERI/Cerberus lineage) is the C-with-lightweight-specs bet.
All are foundational (no SMT in TCB) and all are correspondingly expensive. They
are where the ideas come from, not where the deployments are.

---

## 5. Bounded vs unbounded: where does effort actually pay?

The single clearest picture in this note. Line the evidence up:

**Bounded (Kani/CBMC) delivered:**
- 11 real bugs in production code that **testing and fuzzing missed** (s2n-quic,
  Firecracker, Cedar, hifitime)
- CI-viable: 21–69 minutes at std-library scale
- **Zero specification effort** for the default properties (UB, panics,
  overflow, div-by-zero, unwrap, memory safety)
- Harnesses look like unit tests → engineers write them without a PhD
- Dual-use with fuzzing (s2n-quic/Bolero: one attribute, two tools)

**Bounded's ceiling:**
- Loop bounds must be supplied or proven; input-dependent bounds → intractable
- **Doesn't cover aliasing (Stacked/Tree Borrows) — the primary UB class in
  unsafe Rust**
- No concurrency, no relaxed memory
- Generics need monomorphization
- **A "proof" is only a proof up to the bound**, and the bound is where the bugs
  you didn't think of live

**Unbounded/functional correctness delivered:**
- SymCrypt: production crypto in Windows with machine-checked FIPS conformance —
  a **procurement/regulatory artifact**, not a bug-finding one
- fiat-crypto: correct-by-construction field arithmetic in BoringSSL/Chrome/
  Firefox/Go/AWS-LC — the widest deployment of verified code anywhere, achieved
  by **synthesis, not proof-about-code**
- seL4: certification, one kernel, once, amortized forever
- **Cost: 5:1 to 20:1 proof:code, indefinitely, plus maintenance**

**Where effort actually pays — the pattern, stated flatly:**

Unbounded functional correctness pays **iff** at least one holds:
1. **The spec is external, short, stable, and someone else wrote it** (NIST/FIPS/
   IETF). Crypto. You are not paying spec-authoring cost, which is the dominant
   hidden cost everywhere else.
2. **The artifact is amortized across enormous deployment** (a kernel, a
   compiler, a crypto primitive shipped to a billion devices).
3. **The proof is the product** — regulatory/certification value independent of
   whether it finds bugs (seL4 certification, FIPS).
4. **You can synthesize instead of verify** (fiat-crypto). Categorically better
   whenever available and structurally underrated.

Bounded pays **everywhere else** — and the Rust std campaign is the proof: the
automated bounded tools kept scaling (16,748 harnesses) while **manual contract
effort plateaued in October 2025.** When you let engineers choose, they choose
bounded. Every time.

**The uncomfortable synthesis**: for *general software*, verification's realized
value in 2024–2026 is (a) bounded UB/panic checking in CI, and (b) finding
**specification** defects. Both the Rust std campaign (zero new memory-safety
bugs; found bad SAFETY comments) and Alive2 (8 patches to the LLVM LangRef)
independently landed on (b). That's a strong, twice-replicated finding and it is
*not* the story either community leads with.

---

## 6. The unserved middle: is there a real niche? (skeptical)

The pitch: something between "push-button but bounded/unsound" (Kani, fuzzing)
and "sound but person-years" (Coq/Lean/F*). **Kani's own paper writes the pitch
for us** — developers want to "start with high automation and low annotation cost,
then scale incrementally toward stronger correctness guarantees."

So: is the middle real? **Partly. But it is not empty, and the graveyard is
large. Anyone claiming "gap in the market" here has not counted the bodies.**

### 6.1 The graveyard — everything that already tried to occupy the middle

This is the important section. Every one of these was a smart, funded attempt at
exactly the "automated but sound" middle:

- **ESC/Java (1990s–2000s)** — the ur-attempt. Explicitly "extended static
  checking": neither sound nor complete, automated, annotation-light. Rational,
  well-engineered, DEC/Compaq-funded. Died. Reason: **annotation burden crept up
  to meet the value**, and users couldn't reason about what the tool's warnings
  meant because it was neither sound nor complete. **The middle is epistemically
  awkward — "probably right" is hard to price.**
- **Spec# (Microsoft, 2000s)** — C# + contracts + Boogie/Z3. Excellent
  engineering, real users, shipped as **Code Contracts** into .NET. Deprecated.
  Reason: contract-writing cost exceeded perceived benefit for mainstream devs.
- **Dafny** — arguably the *most* successful middle occupant, and instructive:
  it succeeded by **not being a verifier for existing code**. It's a new
  language. That's the tax the middle charges: you can have automation, but you
  must control the language. AWS uses it internally, notably; it is a real
  success but a narrow one.
- **VCC / Frama-C / SPARK Ada** — SPARK is the real, durable, profitable middle:
  automated, sound-ish, deployed in avionics/rail for 30 years. **And it's a
  restricted language subset in a regulated industry.** Same tax: language
  control + regulatory forcing function. SPARK is the existence proof *and* the
  boundary condition.
- **Infer (Meta)** — separation-logic-based, at Facebook scale. Went the *other*
  way deliberately: abandoned soundness for signal-to-noise, became a bug-finder.
  **The most instructive data point in the graveyard, because it didn't die — it
  survived by leaving the middle.**
- **Prusti/Creusot/Verus/Flux** — the current cohort, all aiming at the middle.
  Real research, real progress, and **the Rust std campaign's own contract
  effort plateaued in October 2025.**
- **Whiley, Why3-as-a-product, KeY, JML tooling** — all technically sound, all
  perpetually near-adoption.

**The pattern is brutal and consistent**: the middle gets occupied only when you
(a) control the language (Dafny, SPARK, Whiley), or (b) have a regulator forcing
spend (SPARK/DO-178C, FIPS), or (c) abandon soundness and become a linter
(Infer). **Nobody has occupied the middle for arbitrary existing code in a
language they don't control.** That's ~30 years of attempts.

### 6.2 Why is the middle structurally hard? Four reasons, in order

1. **The spec is the cost, not the proof.** This is the finding that dominates
   everything. Crypto works *because NIST wrote the spec*. General software has
   no spec, and writing one costs more than the code. Middle-tier tools quietly
   assume the spec is free. **It never is.** Every graveyard entry above died of
   this.
2. **Soundness is discontinuous in value, not gradual.** "Sound modulo 12
   assumptions you must audit" is worth much less than half of "sound," and it's
   *harder to explain* than either endpoint. Kani wins partly *because* it's
   honestly bounded — you know exactly what you got. The middle's problem is that
   its value proposition requires a paragraph.
3. **The two ends are actively eating inward.** Kani grew contracts, loop
   invariants, quantifiers, stubbing — it is *becoming* the middle from below.
   Lean grew `bv_decide` + Aeneas + AI provers — it is *becoming* the middle
   from above, and it keeps the kernel. **The middle is being squeezed by both
   endpoints, and both endpoints have distribution the middle doesn't.** A new
   middle entrant must beat Kani on effort and Lean on assurance,
   simultaneously, in 2026 rather than 2016.
4. **Maintenance, not construction, kills it.** Rust's 6-week release cycle
   breaks proofs. Middle-tier proofs are too expensive to rebuild and too cheap
   to have an owner.

### 6.3 So where IS there something real?

Being specific rather than hopeful. Three candidates, honestly rated:

- **Weak (avoid): "sound-ish general Rust verification."** Occupied,
  contested, and squeezed. Verus/Creusot/Flux are good and free and haven't
  broken through. Don't.

- **Moderate: verification-condition discharge as infrastructure.** Every tool
  above bottlenecks on the same thing — Verus→Z3, Creusot→Why3→SMT, Prusti→
  Viper→Z3, Kani→CBMC→SAT/SMT, Flux→Z3, `bv_decide`→CaDiCaL+LRAT. **Nobody in
  this list is building the solver; everybody is renting Z3.** A solver that is
  faster on their VC shapes *and emits checkable certificates* sells to the
  entire cohort without competing with any of them. This is picks-and-shovels,
  and it is where axeyum already is. The catch: it's an infrastructure market —
  small, slow, and mostly non-commercial. Rate it real but modest.

- **Strongest: certificate production for the Lean/Rust pipeline, and
  machine-generated-code checking.** Two converging facts:
  (a) `bv_decide` already proves the architecture works and is **already in
  Lean's TCB story** — verified AIG + external SAT + LRAT checked in-kernel;
  (b) the AI-prover thread means the *volume* of machine-generated proof
  obligations and machine-generated IR is about to go up a lot, and **the
  kernel re-checks regardless of generation method** is the only thing making
  that safe. TV's growth vector (§2.3) is the same phenomenon.
  **The demand for "untrusted fast search + trusted small checking" is derived
  from AI code generation, and that demand is growing regardless of whether
  formal methods "goes mainstream."**

**Blunt summary: the middle is mostly a trap; the picks-and-shovels layer under
both ends is not. Axeyum's advantage is that it is already positioned in the
latter and its identity sentence is already the right one.**

---

## 7. What this implies for axeyum

Ordered by how much they should change what we do. This is the section to argue
with.

**1. `bv_decide` is simultaneously the strongest validation and the sharpest
threat we have found — treat it as both.**
Lean's `bv_decide` is: a **verified AIG** for subterm sharing → bit-blast to SAT
→ **external CaDiCaL** → **LRAT certificate checked by a verified checker in
Lean**. That is a component-for-component match with `axeyum-aig`
(deterministic structural hashing) + `axeyum-cnf` (Tseitin, DRAT/`check_drat`,
`solve_with_drat_proof`). It **validates the architecture completely** — the
same design independently won inside the most credible proof assistant, and
Microsoft is shipping Windows crypto on it. It also means **the obvious niche is
occupied by the incumbent**, and the incumbent is inside the kernel we'd be
selling to. Concrete asks:
   - Read <https://dl.acm.org/doi/10.1145/3763167> ("Interactive Bitvector
     Reasoning using Verified Bit-Blasting") **before** the next prover-track
     design decision. It is the closest published thing to our stack.
   - **Prioritize LRAT over DRAT**, or at least DRAT→LRAT. `bv_decide` consumes
     LRAT; LRAT-Catcher (<https://arxiv.org/pdf/2607.00815>) imports LRAT by
     reflection. LRAT is where the Lean ecosystem's checkers actually are. Our
     `check_drat` is the right idea one format-generation behind the demand.
   - Note the seam we could exploit: `bv_decide` routes through
     `Lean.ofReduceBool`, **putting the Lean compiler in the TCB**. A smaller
     independent-checking story is a genuine differentiator — if anyone cares,
     which is an open question.
   - Corollary: our BV/AIG/CNF core is not a commodity we happen to have built.
     It is the exact component the highest-credibility verification pipeline in
     production depends on. Fund it accordingly.

**2. Reconsider LLVM IR as the Rust verification level. The field says it's the
wrong altitude.**
Kani's stated reason for MIR: it "preserves Rust-specific type invariants that
are lost at the LLVM level." Every serious Rust tool — Kani, Verus, Creusot,
Prusti, Flux, RefinedRust, Charon(LLBC) — is at **MIR or an MIR derivative**.
Zero are at LLVM. `axeyum-verify` doing "symbolic execution over acyclic rustc
MIR text" is **at the right level and should be leaned into**; the LLVM IR path
is a *different product* serving a different customer (compiler/TV work per §2),
and per §2.3 that's a technique, not a market — with the real exception that it's
the natural home for checking **machine-generated IR**. Decide which one we are,
explicitly, and write it down. Doing both by default is the failure mode.

**3. The SymCrypt evidence design is the artifact spec we should be building
against. Copy it directly.**
They **commit the extracted Lean to the repo** so that *checking* needs only
Lean 4 and 15 minutes of `lake build`, while *producing* needs the full exotic
toolchain. Untrusted fast search, trusted small checking — shipped, in
production, this month, by Microsoft. Our evidence artifacts should meet that
bar concretely: (a) checkable by a widely-installed checker, (b) checkable in
minutes, (c) checkable **without** the producer's toolchain installed, (d) with
an explicitly enumerated TCB (their README is the template — including what is
*not* covered: they say plainly that leakage resistance is out of scope). This
is a bar we can hit and it's more actionable than any theory work on the list.

**4. Do not enter the middle. Sell to both ends.**
§6's graveyard is 30 years long and every occupant died of the same thing —
assuming the spec is free. Axeyum should **not** become "a sound-ish Rust
verifier." It should be **the VC-discharge + certificate layer under the tools
that already have distribution**: Verus→Z3, Creusot→Why3→SMT, Prusti→Viper→Z3,
Kani→CBMC→SAT/SMT, Flux→Z3, Lean→CaDiCaL+LRAT. **Not one of them builds their
own solver. All of them rent Z3.** That is our customer list, it is written down
above, and none of them are competitors. Being a *better Z3 with certificates*
for these specific VC shapes is a coherent, defensible, unglamorous position —
and it's the one we're already in.

**5. Our PDR/IMC/CHC engines are the differentiated asset — the *unbounded*
gap is the one that's actually open.**
Kani's ceiling is loop bounds; the std-lib campaign shows manual contract effort
**plateaued in October 2025** precisely because humans won't write invariants.
`axeyum-verify` producing **verify-gated unbounded inductive invariants** attacks
exactly the thing the largest verification campaign in the world got stuck on.
SeaHorn (LLVM→CHC→Spacer) is the public analogue and it is not a competitor with
distribution. **Automated invariant inference that emits a checkable certificate
is the single most valuable thing in our tree**, and it is more differentiated
than the BV/SAT core (which, per (1), Lean already has a version of). If effort
is fungible, move it here.

**6. Software/IR is a better market than pure math — but for a narrower reason
than "software is bigger."**
Crypto is the only vertical with a repeated commercial record, and §5 explains
why: **NIST writes the spec.** The spec-authoring cost — the thing that killed
every entry in §6.1 — is externally subsidized. Any vertical axeyum targets
should be filtered on that one question: **who wrote the spec, and did we have
to pay for it?** Candidates that pass: crypto (FIPS/NIST/IETF), compilers
(LangRef + an existing test corpus — note Alive2's trick of piggybacking on
LLVM's *existing* unit tests rather than demanding new specs), consensus/zkEVM
(protocol specs, and ArkLib/CompPoly now exist as Lean-side targets), regulated
embedded (DO-178C). Candidates that fail: "general application code," forever.
This test should be applied before any vertical decision, and it disqualifies
most of them.

**7. Watch the derived demand from AI codegen — it's the only growth vector in
the note, and it points at us.**
§2.3: translation validation is growing *as a substrate for checking
LLM-generated IR* (<https://arxiv.org/pdf/2605.08247>,
<https://arxiv.org/pdf/2603.18477>, <https://arxiv.org/pdf/2408.09536>). §3.4:
AI provers closed **two theorems** — but the load-bearing line is *"the kernel
re-checks all proofs regardless of generation method, preserving soundness."*
That sentence is axeyum's thesis, written by someone else, and it is the reason
the AI-codegen wave creates demand for checkers rather than destroying it. The
demand for untrusted-search/trusted-check is **derived from AI code generation
volume**, and grows whether or not formal methods "goes mainstream"
(<https://martin.kleppmann.com/2025/12/08/ai-formal-verification.html> — discount
the enthusiasm, keep the direction). Our in-tree Lean-kernel port + certificates
is aimed at exactly this. **This is the strategically important sentence in the
whole note.**

**8. Calibrate the claims. Honesty is a differentiator here, and it's cheap.**
Two independent findings — the Rust std campaign (**zero new memory-safety bugs**
after 16 months and 16,748 harnesses; what it found was bad SAFETY comments and
doc errors) and Alive2 (**8 patches to the LLVM LangRef**) — say verification's
realized value is *specification defects*, not code defects. Neither community
leads with this. And Kobeissi's "Verification Theatre" (ePrint 2026/192,
**confirmed**, <https://eprint.iacr.org/2026/192>) supplies the third: **13
vulnerabilities escaped verification in libcrux/hpke-rs, four of them _inside_
verified code**, because the specs were wrong. His diagnosis is precisely the
**verification boundary** — users can't see where the guarantee stops.

Take this personally rather than as gossip about a competitor. Axeyum will make
claims of exactly this shape, and the failure mode is not "our proofs are wrong,"
it's "nobody could tell what our proofs covered." SymCrypt's README is the
counter-model: enumerate the TCB, say what you don't cover (they state plainly
that leakage resistance is out of scope). Kobeissi's remedies — documented
boundaries, **proofs run in CI**, explicit scope — are things we can just do, and
(1)/(3) above are how. Axeyum's existing hard rules (`unknown` is first-class; every
`sat` checkable by replay; never ship a wrong sat/unsat) are **already** this
posture. Keep it, and make it explicit in the prover-track's public claims —
in a field this full of overclaiming, a precisely-scoped claim is a feature.

---

## Open questions / follow-ups

- ~~Confirm ePrint 2026/192~~ **CLOSED (2026-07-15).** Confirmed: Kobeissi,
  "Verification Theatre," ePrint 2026/192, 2026-02-05. 13 escaped
  vulnerabilities in libcrux/hpke-rs, **4 of them inside verified code** (bad
  specs, incl. a false serialization proof). See §3.1. Directly relevant to how
  we scope evidence claims — and its remedy (documented verification boundary +
  proofs in CI) is an artifact-engineering agenda we can execute.
- ~~No sourced "why Lean not F\*" statement~~ **CLOSED as far as it can be
  (2026-07-15).** Direct fetch of both MSR posts confirms no explicit comparison
  exists; the 2025-06 post never mentions F\*/HACL\*. But the framing was wrong:
  the quoted rationale defends **Aeneas**, and Lean is Aeneas's main (and, with
  HOL4, only mature) backend. F\* was excluded one step upstream, by choosing
  Rust-as-source-of-truth. See §3.3 driver 0. **Residual question, now the more
  useful one: is the Aeneas-vs-hax translator choice the real contested seam?**
  Cryspen's hax still leads with F\* and its Lean backend is catching up — so
  the same "Rust-first" premise yields *different* provers depending on which
  translator you pick. That, not Lean-vs-F\*, is where the decision lives.
- **Unfetched, worth one retry**: Fromherz, "Verification of Rust Cryptographic
  Primitives with Aeneas" (2026-01, Creach Labs,
  <https://www.creachlabs.fr/sites/default/files/public/media/document/2026-02/2026_01_fromherz.pdf>)
  — PDF fetch returned raw binary. Most likely public source for SymCrypt
  person-effort numbers, which no blog post discloses.
- **`bv_decide` performance vs. axeyum on BV goals** — is there measurable
  headroom, or is this already good enough that nobody's shopping? This is a
  measurable question and it gates recommendation (1) and (4). Answer it before
  investing further in the BV/SAT core.
- **LRAT support**: scope DRAT→LRAT for `axeyum-cnf`. Concrete, bounded, and
  unlocks the Lean-ecosystem story.
- **Charon/LLBC as an ingestion path** for `axeyum-verify` — Charon is the
  de-facto standard Rust→formal-tool front-end (SymCrypt, Aeneas, and adjacent
  to hax). Reusing it beats writing our own MIR ingestion, and would put us on
  the same input as the credible pipeline.
- **Scylla** (Aeneas's C→Rust translator) — partial as of 2025-07 on HACL*,
  SymCrypt, EverParse, bzip2. If the world's C is migrating to Rust to get
  verified, that migration path is worth tracking.
