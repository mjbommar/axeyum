# Provable Security Integration Note

Status: planning scout
Date: 2026-07-08

## Purpose

Record how the ideas in Mike Rosulek's
[The Joy of Cryptography](https://joyofcryptography.com/) should influence
Axeyum's planning without detouring the current Z3 + Lean parity queue.

The useful lesson is not "add a crypto library." The useful lesson is a proof
discipline:

- model the adversary-facing interface as a small program or library;
- make the victim's secret state, randomness, and key-management assumptions
  explicit in that program;
- prove a real/ideal equivalence, usually by a sequence of small game hops;
- keep every hop small enough to audit, replay, or eventually reconstruct in a
  proof kernel.

That maps directly onto Axeyum's identity: untrusted fast search, trusted small
checking.

## Source Read

The book is an undergraduate text on provable security. The online table of
contents covers unconditional security, pseudorandomness, encryption, hashing,
asymmetric cryptography, encrypted messaging, authenticated key exchange,
zero-knowledge, post-quantum cryptography, and binary finite fields.

Planning-relevant motifs:

- **Attack scenarios as programs.** The OTP chapter formalizes security by
  assigning victim and adversary roles to a subroutine interface. This is a
  natural shape for Axeyum scenario generators and verification harnesses.
- **No-matter-how adversaries.** Inputs visible to or chosen by the adversary
  should be modeled as symbolic inputs, not friendly fixtures.
- **Real/ideal libraries and hybrids.** The provable-security chapter uses
  library equivalence and hybrid sequences. This is a proof-cookbook pattern for
  reductions, rewrites, and protocol verification.
- **Algebraic attack shapes.** OTP reuse and xor cancellation are tiny BV
  examples with exact countermodels. Universal hashing and GF(2^k) arithmetic
  generate finite-field and polynomial workloads.
- **Verifier-centric cryptography.** Sigma protocols, Fiat-Shamir transcripts,
  signatures, and zero-knowledge examples emphasize small public verification
  procedures with hidden witnesses. Axeyum should first check transcripts and
  implementation obligations, not claim full cryptographic security.
- **Post-quantum pressure.** LWE-style toy examples are finite modular linear
  algebra with bounded error. They are good future corpus material, but not a
  reason to reorder the current solver roadmap.

Use the maintained online edition as the source. The old PDF available from the
site marks itself as unmaintained as of January 2026.

## Roadmap Placement

### Track 5: Verified Systems And Protocols

This is the best primary home.

Add a small "provable-security micro-suite" after the current P5.3/P5.4
obligations start stabilizing:

1. Constant-time crypto kernels by self-composition.
   Extend the existing branch-leakage check toward memory-index leakage, because
   table lookups and secret-dependent array indices are the concrete crypto
   pain point.
2. Real/ideal protocol harnesses.
   Encode tiny games as reflected Rust functions or finite-state protocols:
   OTP one-use vs two-use, a challenge-response toy protocol, and transcript
   verification.
3. Transcript checkers first.
   For Schnorr/Fiat-Shamir-shaped examples, verify the public `Verify` routine,
   replay counterexamples, and record any zero-knowledge or extraction claim as
   a Lean/proof horizon unless its game hops are independently checked.

This complements P5.3 rather than replacing it: the existing kernel obligations
stay first, and crypto examples exercise the same 2-safety, FSM-refinement, and
fuzz-oracle machinery.

### Track 4: Scenario And Benchmark Demand

Add a scenario family only when it produces checked, oracle-free workloads:

- OTP correctness and finite distribution checks for tiny widths;
- two-time-pad reuse distinguisher via xor cancellation;
- universal-hash collision examples over small domains;
- toy RSA and modular arithmetic round trips, extending the existing
  `rsa_roundtrip` scenario;
- toy LWE consistency/noise-bound rows once modular linear algebra packs need
  more solver pressure.

SAT rows must carry concrete witnesses. UNSAT rows must be exhaustive,
certificate-backed, or clearly lower-assurance. Computational assumptions such
as PRG security are not SMT facts; represent them only as game interfaces,
toy distinguishers, or explicit assumptions in a reduction ledger.

### Track 3: Proofs And Lean

Create a proof-cookbook route for **game-hop certificates**:

- source game and target game;
- transformation class: exact equivalence, statistical bound, or computational
  assumption;
- trusted assumption, if any;
- checker route: evaluator replay, finite counting, DRAT/Alethe/Farkas, or Lean;
- model/witness projection for attacks.

This mirrors the reduction trust ledger: a game hop is not trusted because it is
written in prose. It is trusted only when the hop has a checker or a counted
trust entry.

### Track 2: Theory Breadth

Do not move finite fields ahead of the current priority queue. The current
priority remains performance, MBQI sat-direction, CDCL(T) migration, strings,
dominance audits, and arithmetic residue.

But this book strengthens the demand signal for P2.10.4 finite fields once the
keystones are ready:

- GF(2^k) arithmetic is a direct cryptographic substrate;
- universal hashing and GCM/GHASH-style examples need polynomial arithmetic
  over binary fields;
- post-quantum toy examples need modular matrix/vector arithmetic and small
  error constraints.

The right near-term move is corpus and metadata, not a public `FF` solver
surface.

### Foundational Resources

Add the book to the "foundational books through the decidability lens" lane:

- decidable/checkable: finite games, BV xor algebra, modular arithmetic,
  finite-field tables, small transcript verification, finite probability tables;
- proof horizon: asymptotic negligible bounds, reductions under assumptions,
  zero-knowledge simulation/extraction, and real post-quantum hardness claims.

This gives a learner path that is useful to the solver: every lesson has either
a replayable witness, a checked finite proof, or an explicitly labeled horizon.

## Concrete Increment Sequence

1. **Docs-only intake.**
   Link this note from the plan and foundational-books index. Do not change
   solver priorities.
2. **Crypto game examples v0.**
   Add `artifacts/examples/crypto/provable-security-v0/` with OTP one-use,
   OTP two-use attack, xor cancellation, and small finite distribution checks.
   Validator: exact finite enumeration.
3. **Scenario family v0.**
   Add `Family::ProvableSecurity` only after the artifact pack exists and has
   deterministic expected outcomes. Keep it inside QF_BV and finite counting.
4. **Proof-cookbook recipe.**
   Add a "game-hop certificate anatomy" recipe: exact game equivalence, bad-event
   bound, and assumption-backed hop as three separate trust levels.
5. **Track 5 crypto micro-suite.**
   Add reflected examples for constant-time and transcript verification. Use
   replayed witnesses for refutations and label any broader security claim as a
   horizon.
6. **Finite-field demand packet.**
   When P2.10.4 becomes eligible, use the crypto examples as one of the demand
   packets: GF(2^k), UHF/GHASH-style polynomial rows, and toy LWE rows.

## Non-Goals

- Do not implement production cryptography.
- Do not claim PRG, PRF, encryption, signature, ZK, or post-quantum security
  from bounded SMT checks.
- Do not add random-oracle semantics to the trusted core.
- Do not reorder the current parity queue based on educational appeal.
- Do not treat computational assumptions as checked facts. They belong in an
  assumption ledger unless discharged by an independent formal route.

## Decision Triggers

Open an ADR only when one of these becomes true:

- a game-hop evidence format becomes a public artifact;
- a computational assumption is represented in an evidence envelope;
- finite fields move from corpus pressure to public solver surface;
- random-oracle or probabilistic semantics is proposed as an IR-level concept;
- Track 5 starts reporting a cryptographic security property beyond bounded
  constant-time, transcript validity, or finite protocol safety.
