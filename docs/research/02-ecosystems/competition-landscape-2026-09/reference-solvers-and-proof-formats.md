# The Reference-Solver and Proof-Format Landscape, 2025–2026

A catalog for **axeyum** — a Rust-first SMT/SAT stack whose identity is *untrusted fast
search, trusted small checking*, and which uses external solvers **strictly as measurement
yardsticks, never as engines**.

Compiled 2026-09-06. Every claim carries a URL. Claims are tagged:

- **[M]** — *measured here*: computed directly from a primary data file downloaded during this
  research (chiefly the SMT-COMP raw per-benchmark result dumps). Reproduction commands given.
- **[C]** — *confirmed*: read from a primary source (spec, rules PDF, repo, release API).
- **[I]** — *inferred*: derived from secondary sources or by analogy; not independently verified.

> **The one-paragraph finding.** SMT-COMP has *no proof track* — it was discontinued in 2024 and
> has not returned through 2026 [C]. The proof-exhibition frontier has moved out of the competition
> and into two places: the **SAT** Competition, where an UNSAT certificate is mandatory and a wrong
> certificate is a disqualification [C]; and individual **certified pipelines**, of which the
> load-bearing datapoint for axeyum is Lean's `bv_decide`, which entered SMT-COMP 2026's QF_BV
> division and solved 94.5% of it with every UNSAT checked into the Lean kernel — versus 97.4% for
> Bitwuzla [M]. The trusted checking is *not* what costs: the kernel check is a median +6.9% on
> wall time [M]. The proof-*producing* search is what costs — the whole certified pipeline runs a
> median 8.7x slower than Bitwuzla [M].

---

## 0. Method, and what is reusable without re-running anything

SMT-COMP publishes **raw per-benchmark results** as gzipped JSON in the competition's own
repository. This is the single most important logistical fact in this document for axeyum: you can
compute head-to-heads, virtual-best-solver curves, and per-logic frontiers against every reference
solver **without ever running one**.

```
https://raw.githubusercontent.com/SMT-COMP/smt-comp.github.io/master/data/results-sq-<YEAR>.json.gz
```

| File pattern | Track | Years available (as of 2026-09-06) |
|---|---|---|
| `results-sq-<year>.json.gz` | Single Query | 2018–2026 [C] |
| `results-inc-<year>.json.gz` | Incremental | 2024–2026 [C] |
| `results-uc-<year>.json.gz` | Unsat Core | 2024–2026 [C] |
| `results-mv-<year>.json.gz` | Model Validation | 2024–2026 [C] |
| `results-parallel-<year>.json.gz` | Parallel | 2024–2026 [C] |
| `results-cloud-2024.json.gz` | Cloud | 2024 only [C] |
| `benchmarks-<year>.json.gz` | benchmark inventory (logic, family, name, `check_sats`) | 2024–2026 [C] |

Directory listing: <https://github.com/SMT-COMP/smt-comp.github.io/tree/master/data> [C]

**Row schema** (verified by reading `results-sq-2026.json.gz` [M]):

```json
{"track":"SingleQuery","solver":"Bitwuzla",
 "file":{"incremental":false,"logic":"ABV","family":["20190429-UltimateAutomizerSvcomp2019"],
         "name":"alternating_list_...smt2"},
 "result":"Timeout","cpu_time":1200.8,"wallclock_time":1201.0,"memory_usage":882278400.0}
```

`result` ∈ {`sat`, `unsat`, `unknown`, `Timeout`} for the single-query track [M]. The
model-validation file additionally carries the **Dolmen verdicts** as result codes —
`ModelParsingError`, `ModelPartialFunctionMissing`, `ModelUnsat`,
`ModelValidatorBenchmarkStrictTyping` [M]. Note the files carry **no expected status**, so an
"error" count must be reconstructed (majority vote, or the SMT-LIB `:status` annotation).

Scale, measured [M]: `results-sq-2026.json.gz` is 12.7 MB compressed, 488,264 rows, 44 solver
entries, 88 logics, 45,905 distinct benchmarks. `results-sq-2025.json.gz` is 21.8 MB and covers
129,361 benchmarks — SMT-COMP 2026 selected a **much smaller** benchmark set than 2025 [M], so
cross-year solved-counts are not comparable.

All numbers tagged [M] below were computed from these files with short Python scripts; the
aggregation is a group-by on `(logic, family, name)` — **note that `name` alone is not unique
across families** and using it undercounts (QF_BV: 2,540 distinct vs 2,489 by name) [M].

### Other reusable corpora

| Resource | What it gives you | URL |
|---|---|---|
| **SMT-LIB benchmark library** | The benchmarks themselves; latest releases hosted on Zenodo under the SMT-LIB community [C] | <https://zenodo.org/communities/smt-lib> |
| SMT-LIB releases 2013–2023 | Older benchmark releases, still on StarExec [C] | <https://www.starexec.org/starexec/secure/explore/spaces.jsp?id=239> |
| **Global Benchmark Database (GBD)** | Per-instance SAT metadata **including solver runtimes** (`runtime-kissat`, `verified-result`) as a queryable DB; `pip install gbd-tools`, then download `meta.db` [C] | <https://github.com/Udopia/gbd>, <https://benchmark-database.de/getdatabase/meta.db>, paper [10.4230/LIPIcs.SAT.2024.18](https://doi.org/10.4230/LIPIcs.SAT.2024.18) |
| GBD web instance | Browse/download instances + prebuilt feature DBs [C] | <https://benchmark-database.de/> |
| SMT-COMP solver binaries | Every entrant must upload its final binary to Zenodo [C] — the submission JSONs carry direct Zenodo URLs and SHA-256 hashes [M] | <https://github.com/SMT-COMP/smt-comp.github.io/tree/master/submissions> |
| `smtcomp` Python tool | The competition's own tooling: benchmark selection, scrambling, BenchExec generation, **scoring** (including every scoring system used since 2015), `check-model-locally` [C] | <https://github.com/SMT-COMP/smt-comp.github.io> |

The `smtcomp` tool matters for axeyum beyond data access: it contains the reference implementation
of the scoring rules, so a self-reported score can be computed by the *same code the competition
uses* rather than a reimplementation [C].

---

## 1. The solver landscape

### 1.1 Established SMT solvers

Release dates from the GitHub Releases API, queried 2026-09-06 [C].

| Solver | Language | License | Latest release | Active? | Strongest divisions | Proofs |
|---|---|---|---|---|---|---|
| **Z3** ([repo](https://github.com/Z3Prover/z3)) | C++ | MIT | **z3-5.1.0**, 2026-08-16 | Yes (pushed 2026-09-06) | Broad; in practice competes only through derivatives (below) | Internal proof objects (`proof=true`); no standard external certificate |
| **cvc5** ([repo](https://github.com/cvc5/cvc5)) | C++ | BSD-3-Clause (modified) | cvc5-1.3.4, 2026-05-07 | Yes | Quantified UF / arith / datatypes; the broadest single solver | **Yes** — Alethe, LFSC, Cpc/AletheLF (Ethos), Lean 4 |
| **Bitwuzla** ([repo](https://github.com/bitwuzla/bitwuzla)) | C++ | MIT | 0.9.1, 2026-05-21 | Yes | QF_BV, QF_ABV, QF_FP, FP, BV | No external checkable format |
| **Boolector** ([repo](https://github.com/Boolector/boolector)) | C | MIT | — | **ARCHIVED 2024-08-23** [C] | superseded by Bitwuzla | — |
| **Yices 2** ([repo](https://github.com/SRI-CSL/yices2)) | C | **GPL-3.0** | yices-2.7.0, 2025-07-16 | Yes | QF_UF, QF_UFLRA, QF_RDL, QF_ALIA, QF_UFNIA; very strong 24s scores | No |
| **MathSAT 5** ([site](https://mathsat.fbk.eu/)) | C++ | **Non-commercial / research only** | 5.6.15, 2025-12-07 | Yes, as a library | Interpolation, FP; competes only inside `UltimateEliminator+MathSAT` | Interpolants, unsat cores; no certificate format |
| **OpenSMT2** ([repo](https://github.com/usi-verification-and-security/opensmt)) | C++ | MIT (repo SPDX unresolved) | v2.9.2, 2025-06-16 | Yes | QF_LIA, QF_LRA, QF_UF, QF_AX, QF_UFIDL | Interpolation; DRAT + theory trail |
| **SMTInterpol** ([repo](https://github.com/ultimate-pa/smtinterpol)) | Java | LGPL-3.0 | rolling | Yes | QF_UFLIA, QF_ALIA, QF_ANIA; interpolation | **Yes** — RESOLUTE resolution proof format |
| **veriT** ([site](https://www.verit-solver.org/)) | C | BSD [I] | 2026.05, 2026-05-18 | Yes as a project; **not an SMT-COMP entrant** | — | **Yes** — originated Alethe |
| **STP** ([repo](https://github.com/stp/stp)) | C++ | MIT | 2.4.1, 2026-08-01 | Yes | QF_BV via CryptoMiniSat/CaDiCaL; competes only in portfolios | No |
| **Alt-Ergo** ([repo](https://github.com/OCamlPro/alt-ergo)) | OCaml | Dual: non-commercial + Apache-2.0 (`alt-ergo-free`) | v2.6.3, 2026-04-14 | Yes | Why3/SPARK backend; **not an SMT-COMP entrant** since 2019 | No |
| **Princess** ([repo](https://github.com/uuverifiers/princess)) | Scala | BSD-3 [I] | snapshot-2026-05-20 | Yes; **not an SMT-COMP entrant** | Presburger + uninterpreted predicates | Certificates for its fragment |
| **Vampire** ([repo](https://github.com/vprover/vampire)) | C++ | BSD-3 (since 2020) | v5.1.0, 2026-08-13 | Yes | **CASC, not SMT-COMP**; accepts SMT-LIB input | TPTP proofs |
| **SMT-RAT** ([repo](https://github.com/ths-rwth/smtrat)) | C++ | unresolved SPDX | 26.08, 2026-08-24 | Yes | **NRA** (won the quantified NRA logic in 2026 [M]); QF_NRA mid-field | No |
| **COLIBRI / colibri2** ([site](https://colibri.frama-c.com/)) | OCaml | LGPL-2.1 (colibri2) | colibri2 0.3.3 | Yes (CEA List) | **QF_FP, QF_FPLRA** — the only serious non-bitblasting FP entrant | No (interval/propagation based) |

**A correction worth stating plainly.** "Mainstream SMT solver" and "SMT-COMP entrant" are now different
sets. **veriT, Vampire, Alt-Ergo, Princess, standalone MathSAT 5, CVC4 and Boolector do not compete**
[C]. Neither does plain **Z3** under its own name: in 2026 the Z3 lineage appears only as
`Z3-GEX`, `Z3-Z3++`, `Z3-alpha2`, `Z3-siri`, `z3-BooledASS`, `Z3-Noodler` [M]. Any statement of the
form "we beat Z3 on division X" therefore cannot be sourced from a competition result table — it has
to be measured by axeyum directly, or read off the `-base` rows (SMT-COMP records the *base solver*
of each derived entrant as a separate non-competitive row, and those rows are in the JSON [M]).

### 1.2 Where each solver actually leads, measured

Computed from `results-sq-2026.json.gz` [M]. Ranking is by **benchmarks solved** (`sat`+`unsat`)
under the 20-minute wall limit; `-base`/`-debug` rows excluded as non-competitive. This is the `n`
component of SMT-COMP's parallel score, and is the winner whenever error scores tie at zero. It is
**per SMT-LIB logic**, which is finer than SMT-COMP's own *divisions* (a division bundles several
logics), so these are not identical to the official division winners.

| Logic | #bench | 1st | 2nd | 3rd | 24s-score leader |
|---|---|---|---|---|---|
| QF_SLIA | 5146 | **Z3-Noodler** (5123) | OSTRICH (4941) | cvc5 (4865) | Z3-Noodler (5114) |
| QF_NIA | 2855 | **Z3-Z3++** (2408) | Z3-alpha2 (2407) | Z3-GEX (2358) | Z3-GEX (2140) |
| QF_BV | 2540 | **Bitwuzla-MachBV** (2495) | Bitwuzla (2475) | Yices2 (2472) | Bitwuzla-MachBV (2401) |
| QF_S | 2496 | **Z3-Noodler** (2111) | OSTRICH (2019) | cvc5-cvc5-xyz (378); base cvc5 364 | Z3-Noodler (2081) |
| QF_ABV | 1914 | **Bitwuzla** (1909) | bitwuzla-dandelion (1908) | Yices2 (1904) | Bitwuzla (1898) |
| QF_LIA | 1317 | **QiuQi** (1262) | OpenSMT-SMTS-seq (1240) | OpenSMT (1229) | Yices2 (1123) |
| QF_UF | 1104 | **OpenSMT / Yices2 / cvc5** (1104, all) | — | — | Yices2 (1104) |
| QF_NRA | 1020 | **Z3-GEX** (953) | Z3-alpha2 (946) | Z3-siri (943) | Z3-GEX (894) |
| ABV | 896 | **Bitwuzla** (615) | cvc5 (542) | — | Bitwuzla (592) |
| FP | 664 | **Bitwuzla** (637) | cvc5 (618) | — | Bitwuzla (562) |
| QF_IDL | 641 | **QiuQi** (545) | Z3-GEX (536) | Z3-alpha2 (531) | Yices2 (456) |
| BV | 608 | **Bitwuzla** (559) | cvc5 (552) | — | Bitwuzla (543) |
| LRA | 602 | **YicesQS** (599) | Z3-GEX (570) | z3-BooledASS (569) | YicesQS (599) |
| AUFBV | 552 | **bitwuzla-dandelion** (374) | Bitwuzla (371) | — | Bitwuzla (296) |
| QF_UFBV | 552 | **bitwuzla-dandelion** (513) | Bitwuzla (505) | Yices2 (459) | bitwuzla-dandelion (368) |
| QF_ABVFP | 525 | **Bitwuzla** (525) | cvc5 (518) | — | Bitwuzla (518) |
| QF_LRA | 519 | **OpenSMT-SMTS-seq** (502) | OpenSMT (501) | Yices2 (484) | OpenSMT-SMTS-seq (431) |
| QF_UFLRA | 508 | **Yices2** (507) | SMTInterpol (506) | cvc5 (506) | Yices2 (506) |
| QF_AUFLIA | 505 | **OpenSMT / SMTInterpol** (505) | — | — | Yices2 (505) |
| QF_BVFP | 505 | **Bitwuzla** (504) | cvc5 (503) | — | bitwuzla-dandelion (500) |
| QF_DT | 344 | **Z3-Z3++** (336) | cvc5 (225) | — | Z3-Z3++ (306) |
| QF_UFNIA | 339 | **Yices2** (286) | Z3-alpha2 (272) | — | Yices2 (249) |
| LIA | 300 | **Z3-alpha2** (214) | YicesQS (202) | Z3-GEX (201) | Z3-alpha2 (198) |
| QF_AX | 300 | **OpenSMT / SMTInterpol** (300) | — | — | OpenSMT (300) |
| QF_UFLIA | 300 | **SMTInterpol** (291) | Yices2 (289) | — | z3-BooledASS (283) |
| QF_FP | 275 | **bitwuzla-dandelion** (256) | Bitwuzla (255) | **COLIBRI** (239) | **COLIBRI** (220) |
| NIA | 254 | **Z3-GEX / Z3-alpha2** (238) | cvc5 (231) | — | Z3-GEX (233) |
| QF_RDL | 247 | **Yices2** (216) | cvc5 (210) | — | Yices2 (199) |
| QF_ALIA | 176 | **SMTInterpol** (168) | Yices2 (162) | — | SMTInterpol (163) |
| QF_ANIA | 155 | **SMTInterpol** (132) | Yices2 (131) | — | SMTInterpol (129) |
| NRA | 99 | **SMT-RAT** (96) | Z3-alpha2 (96) | — | SMT-RAT (96) |
| QF_FPLRA | 55 | **Bitwuzla** (55) | **COLIBRI** (54) | — | **COLIBRI** (54) |

Reproduce: download `results-sq-2026.json.gz`, group by `(logic, family, name)`, count
`result in {sat,unsat}` per solver, and for the 24s column filter `wallclock_time <= 24`.

**Reading this for axeyum's current yardsticks:** the choices already made are right.
cvc5 is the correct reference for arithmetic/UF, Bitwuzla for BV/ABV/FP, and the CNF-level
Kissat/CaDiCaL comparison is the right layer. The gaps: **Yices2 and OpenSMT beat cvc5 on the
quantifier-free arithmetic and equality logics** that axeyum's arithmetic lanes actually target
(QF_LRA, QF_UFLRA, QF_LIA, QF_UF, QF_AX, QF_RDL), and **SMTInterpol** leads QF_ALIA/QF_ANIA/QF_UFLIA.
cvc5's lead is in the *quantified* and datatype logics.

### 1.3 New entrants, 2026 cohort

Verified from the competition's own submission JSONs
(<https://github.com/SMT-COMP/smt-comp.github.io/tree/master/submissions>) [M] and repo metadata [C].

| Entrant | Who | Language | License | Logics entered | Result [M] |
|---|---|---|---|---|---|
| **bv_decide** ([Leanwuzla](https://github.com/hargoniX/Leanwuzla)) | Böving, Bhat, Keizer, Cicolini, Frenot, Mohamed, Stefanesco, Khan, Clune, Barrett, Grosser (Lean FRO / Cambridge / Stanford) | Lean | Apache-2.0 | QF_BV (single query + **model validation**) | 2401/2540 QF_BV; **0 model-validation errors** |
| **plat-smt** ([repo](https://github.com/dewert99/plat-smt)) | David Ewert | **Rust** | — | QF_UF (all four tracks) | 1102/1104 QF_UF; 703 MV sat, 11 parse errors |
| **Roole** ([repo](https://github.com/onderjan/roole)) | Jan Onderka, **Armin Biere** | **Rust** | Apache-2.0 | QF_BV | 677/2540 |
| **Amaya** ([repo](https://github.com/MichalHe/amaya)) | Havlena, Hečko, Holík, Lengál (VeriFIT Brno) | Python | MPL-2.0 | LIA, NIA — **automata-based** | LIA 200/300, NIA 208/254 |
| **QiuQi** | Lei, Yuan, Zhang, Qian, Lu (Huawei) | — | — | QF_LIA, QF_IDL | **1st in both** |
| **Xolver** | Fuqi Jia (ISCAS) | — | — | QF_NIA/NRA family | mid-field |
| **NeuroSym** | Swain, Godboley, Krishna, Das, Cordeiro | wrapped | — | QF_LIA, QF_BV, QF_ABV | **92.6% of QF_BV within 24 s** — near-best 24s score |
| **Samet** | Martin Blicha | — | — | QF_LRA | 400/519 |
| **YicesQS** ([repo](https://github.com/disteph/yicesQS)) | Graham-Lengrand (SRI) | OCaml | — | BV, LIA, LRA, NIA, NRA (**quantified**) | **1st in LRA** (599/602) |
| **colibri2** | Bobot, Ait El Hara, Junke (CEA List) | OCaml | LGPL-2.1 | FP divisions | 1st on 24s QF_FP and QF_FPLRA |
| **Z3-Noodler** ([repo](https://github.com/VeriFIT/z3-noodler)) | Havlena, Síč, Chocholatý, Holík, Lengál, Hečko | C++ | (custom) | QF_Strings | **1st, decisively** |

Three of these are worth axeyum's direct attention: **bv_decide** (§6.2), **plat-smt** and
**Roole** (Rust; §1.4).

### 1.4 The Rust-native ecosystem — including two direct peers

crates.io data queried 2026-09-06 via `https://crates.io/api/v1/crates/<name>` [C]; repo metadata
via the GitHub API [C].

#### SAT in Rust

| Crate / repo | Version, date | Downloads | License | Status | Notes |
|---|---|---|---|---|---|
| **varisat** ([repo](https://github.com/jix/varisat)) | 0.2.2, **2020-09-09** | 7.53 M | Apache-2.0/MIT | **Unmaintained** (last push 2022-11) | Still the reference for *Rust CDCL with LRAT output*; `varisat-lrat` crate exists |
| **batsat** ([repo](https://github.com/c-cube/batsat)) | 0.6.0, 2025-01-20 | 98 K | (unresolved) | Maintained (push 2026-05) | MiniSat-derived; the crate axeyum is retiring per ADR-1703 |
| **splr** ([repo](https://github.com/shnarazk/splr)) | 0.19.0, **2026-08-22** | 50 K | MPL-2.0 | **Active** | The most actively developed pure-Rust CDCL |
| **rustsat** ([repo](https://github.com/chrjabs/rustsat)) | 0.7.5, 2026-01-30 | 96 K | MIT | **Active** (push 2026-09-05) | Christoph Jabs, Helsinki; SAT 2024 tool paper. Adapters: `rustsat-cadical`, `-kissat`, `-minisat`, `-glucose`, `-batsat`, `-ipasir`. **Ships VeriPB proof logging.** |
| **CreuSAT** ([repo](https://github.com/sarsko/CreuSAT)) | — (not on crates.io) | — | MIT | **Active** (push 2026-08-20), 698 stars | **A formally verified CDCL SAT solver in Rust**, verified with Creusot/Why3. Also contains "Friday" and "Robinson". The single most relevant Rust artifact to axeyum's trust story. |
| **rate** ([repo](https://github.com/krobelus/rate)) | — | — | MIT | **Stale** (last push 2022-02) | Rust **DRAT/DPR checker** that *emits* trimmed DRAT, DPR, **LRAT** or **GRAT**. The only standalone Rust DRAT→LRAT converter found. |
| `cadical` ([repo](https://github.com/mmaroti/cadical-rs)) | 0.1.16, 2025-04-24 | 46 K | MIT | Maintained | Bindings, not pure Rust |
| `kissat` ([repo](https://github.com/jleahy/kissat-rs)) | 0.1.0, 2021-10-10 | 2.5 K | MIT | **Dead** | One release, never updated |
| `minisat`, `ipasir`, `screwsat` | 2019–2021 | — | MIT | **Dead** | — |

#### SMT in Rust

| Crate / repo | Version, date | Downloads | License | Notes |
|---|---|---|---|---|
| **z3** / **z3-sys** ([repo](https://github.com/prove-rs/z3.rs)) | 0.21.0, **2026-08-28** | 1.77 M / 1.86 M | MIT | The de facto Rust SMT route; actively maintained |
| **cvc5** ([repo](https://github.com/cvc5/cvc5-rs)) | 0.5.0, **2026-09-01** | 2.2 K | BSD-3 | **NEW (first published 2026-04-15)** — *official* cvc5-org Rust bindings. Did not exist a year ago. |
| **easy-smt** ([repo](https://github.com/elliottt/easy-smt)) | 0.3.2, 2025-07-24 | 1.31 M | MIT/Apache | Subprocess SMT-LIB driver — the low-friction way to wire a yardstick |
| `bitwuzla-sys` | 0.8.0, 2025-06-25 | 24 K | MIT | Low-level only; no high-level crate |
| `yices2` / `yices2-sys` | 0.1.4, 2023-09-01 | 6 K | — | Stale |
| `boolector` / `boolector-sys` | 0.4.3 / 0.7.2 | 36 K / 60 K | — | Upstream archived |
| **Smithril** ([repo](https://github.com/smithril/smithril)) | not on crates.io | — | MIT | 0 stars, last push 2025-02. **A parallel/resource-limited *container* over Bitwuzla and Z3, not an engine.** |
| **egg** / **egglog** ([org](https://github.com/egraphs-good)) | 0.11.0 / 3.0.0, 2026-08-19 | 3.14 M / 146 K | MIT | E-graph rewriting infrastructure |

> **"z4" does not exist.** A targeted search across GitHub, the web and SerpAPI found no Rust SMT
> project by that name [C, negative]. Treat the name as spurious.

#### Two direct peers — read these before claiming novelty

| Project | What it is | Overlap with axeyum |
|---|---|---|
| **Ordeal** — [github.com/pulseengine/ordeal](https://github.com/pulseengine/ordeal), crates `ordeal` 0.19.0 / `ordeal-lrat` 0.19.0 (2026-08-20) | Repo's own description [C]: *"a pure-Rust, certificate-checked QF_BV SMT solver… Untrusted solver + formally-verified LRAT checker (CompCert pattern), wasm32-wasip2-native."* `ordeal-lrat` is described as *"the sole trusted component."* Apache-2.0, created 2026-07-01, 1 star. Consumed by `synth-verify` for compiler translation validation. | **This is axeyum's thesis sentence, nearly verbatim, shipped.** Same theory (QF_BV), same architecture (untrusted search + small trusted LRAT checker), same language, same WASM target. |
| **OxiZ** — [github.com/cool-japan/oxiz](https://github.com/cool-japan/oxiz), ~17 crates at 0.3.3 (2026-08-26) | Repo description [C]: *"a high-performance SMT solver written entirely in Rust… part of an initiative to reimplement Z3 in Pure Rust. Pure Rust is a fundamental requirement — no C/C++ dependencies, no FFI bindings."* Apache-2.0, created 2025-12-28, 56 stars. Crate family: `oxiz-core`, `-sat`, `-theories`, `-nlsat`, `-proof`, `-spacer`, `-opt`, `-smtcomp`, `-wasm`, `-py`, `-ml`. | Same no-C/C++ constraint as ADR-0002, and an almost identical crate decomposition. **Caveat [I]:** the publishing account ships many "pure Rust reimplementation of X" crate families at high cadence; treat quality as unassessed. Neither OxiZ nor Ordeal appears in SMT-COMP 2026 [M]. |

Neither is a reason to change course, but both mean the *architecture* is no longer distinguishing on
its own. What still distinguishes axeyum is the flywheel — the kernel/library cycle above the solver —
not "Rust + certificates".

---

## 2. Proof formats and checkers

### 2.1 SAT level

| Format | What it adds | Verified checker? | Producers |
|---|---|---|---|
| **RUP → DRUP → DRAT** | RUP = clause redundant by unit propagation; DRUP adds deletion; **DRAT** requires the stronger RAT property so blocked-clause elimination and inprocessing are expressible | drat-trim (C, **unverified**) — [repo](https://github.com/marijnheule/drat-trim), MIT, last push 2024-11 [C] | Effectively every competitive CDCL solver |
| **LRAT** | DRAT + **explicit hints** naming the clauses to propagate against ⇒ near-linear checking instead of RAT search | **Yes, several**: `cake_lpr` (CakeML-verified *down to the binary*), an ACL2 checker, a Coq checker — all from Cruz-Filipe/Heule/Hunt/Kaufmann/Schneider-Kamp, CADE-26, [arXiv:1612.02353](https://arxiv.org/abs/1612.02353) | Produced by *elaboration* from DRAT, not usually emitted natively |
| **FRAT** | A solver→elaborator format carrying what the solver already knows, so DRAT→LRAT elaboration is cheap. Reports **>84% median cut in elaboration time, >94% in peak memory** vs. the DRAT toolchain — Baek, Carneiro, Heule, TACAS 2021, [arXiv:2109.09665](https://arxiv.org/pdf/2109.09665) | via `frat-rs` → LRAT | [digama0/frat](https://github.com/digama0/frat) |
| **PR / DPR / LPR** | Propagation redundancy — admits *substitution*-based redundancy, giving exponentially shorter proofs of pigeonhole/parity/Tseitin principles that DRAT cannot compress. LPR = LRAT + PR hints | `cake_lpr` checks LRAT **and** LPR | `dpr-trim` |
| **GRAT** | An elaborated certificate format; split into unverified `gratgen` elaborator + **Isabelle/HOL-verified `gratchk`**. Reported **faster than unverified drat-trim** — Lammich, TACAS 2017 / JAR 2020, [project](https://www21.in.tum.de/~lammich/grat/) | **Yes — `gratchk`, Isabelle/HOL** | from DRAT |
| **VeriPB** | Pseudo-Boolean, **cutting planes** — strictly subsumes resolution/RAT, expresses cardinality and symmetry-breaking reasoning natively. Checker itself is **written in Rust** [C, [veripb.org](https://veripb.org/)] | **Yes — CakePB (CakeML)** | CaDiCaL, RoundingSat, Exact, Glasgow solvers, +12 more |

**What the SAT Competition actually requires (2025).** From the competition's own output-format
page [C, <https://satcompetition.github.io/2025/output.html>]: *"All participants in the Main track
of this competition must output proofs of unsatisfiability, which must be written to a file called
`proof.out`."* The solver-facing format **is still DRAT**, unchanged since 2014, with a specified
binary encoding (~3x smaller than text). LRAT/LPR/GRAT are the *elaborated* intermediates. The
checking is done by one of **three verified pipelines** the entrant selects:
`dpr-trim` → **cake_lpr**, `gratgen` → **gratchk**, or `veripb` → **CakePB**.

Sanctions differ sharply from SMT-COMP: *"A solver will be disqualified if it produces a wrong
answer or a wrong certificate"* [C, <https://satcompetition.github.io/2025/rules.html>]. Limits:
**5000 s wall, 30 GB, 8 cores**, on the SoSy-Lab BenchCloud in Munich [C,
<https://satcompetition.github.io/2025/benchcloud.html>].

### 2.2 SMT level

| Format | Theories covered | Checker | Verified? | Produced by |
|---|---|---|---|---|
| **Alethe** ([spec](https://verit.loria.fr/documentation/alethe-spec.pdf), [PxTP 2021](https://arxiv.org/abs/2107.02354)) | veriT: broad. **cvc5's Alethe output is explicitly partial** — "only EUF, parts of arithmetic and parts of quantifiers" [C, cvc5 docs] | **Carcara** — Rust, TACAS 2023, [repo](https://github.com/ufmg-smite/carcara) (Apache-2.0, active 2026-09) | **No** — fast and trusted, not machine-checked. Also an *elaborator*, which is its real value for downstream reconstruction | veriT, cvc5 (`--proof-format-mode=alethe`) |
| **LFSC** | CVC4/cvc5's older rule set | `LFSC` checker ([repo](https://github.com/cvc5/LFSC)) | No | cvc5 — **no longer the default** |
| **CPC / Eunoia / Ethos** — cvc5's current stack | **All "safe" cvc5 features across 59 SMT-LIB logics. FP is the hole** — cvc5 produces no proofs for the SymFPU word-blaster [C] | **Ethos**, C++ ([repo](https://github.com/cvc5/ethos), v0.2.3 2026-05) | Not itself machine-verified; but cross-validated three ways (below) | cvc5 — **default format since v1.3.0** |
| **RESOLUTE** | SMTInterpol's resolution proofs | — | No | SMTInterpol |
| **Z3 proof objects** | whatever Z3 solved with | none in wide use | No | Z3 |

**CPC is the state of the art and the number to know.** Reynolds et al., *The Cooperating Proof
Calculus*, CAV 2026 [C, [PDF](https://www.hanielbarbosa.com/papers/2026cav.pdf)]:

> "the trusted computing base (TCB) of cvc5 shrinks from its more than **360k lines of C++** to one
> consisting of the external proof checker Ethos (**about 10k lines of C++**) and the CPC signature
> (**about 8k lines of Eunoia**)."

585 proof rules; 427 used across 913.4 M generated steps [C]. Cross-validation, all three partial:
`lean-smt` reimplements **180** CPC rules in Lean and checks through the Lean kernel (~20x slower
than Ethos) [C]; IsaRare verifies **338** rules as Isabelle lemmas — *and found 6 faulty rules* [C];
a Eunoia→SMT-LIB verification-condition translation covers 571 rules and "was instrumental in
discovering several soundness bugs" [C].

### 2.3 Reconstruction into proof assistants

| Route | From | Trust anchor | Status |
|---|---|---|---|
| **SMTCoq** ([repo](https://github.com/smtcoq/smtcoq)) | veriT, CVC4, ZChaff | Coq kernel | Maintained |
| **Isabelle `smt` / Sledgehammer** | cvc5 **via Alethe**, veriT, Z3 | Isabelle kernel | Active — ITP 2025, [DROPS](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.26) |
| **lean-smt** ([repo](https://github.com/ufmg-smite/lean-smt), 309 stars, active) | cvc5 **via CPC** | Lean 4 kernel | Active — [arXiv:2505.15796](https://arxiv.org/html/2505.15796v1) |
| **Dedukti / Lambdapi** | many, via `Carcara-LP` (Alethe→Lambdapi) | λΠ-modulo kernel | Active (EuroProofNet) |

### 2.4 Proof exhibition in SMT-COMP — the track is gone

| Year | Status |
|---|---|
| 2022 | Proof Exhibition Track **introduced**; no predefined format or checker — submit solver *and* your own checker [C, [page](https://smt-comp.github.io/2022/proof-track.html)] |
| 2023 | Ran again, **no ranking, no winner**. Example datum: `cvc5-lfsc` solved 1317/1428 BV vs plain `cvc5` 1103/1428 [C, [results](https://smt-comp.github.io/2023/results/bitvec-proof-exhibition)] |
| **2024** | **Discontinued.** The rules say why, verbatim [C, `2024/rules.pdf`]: *"we were unable to find a way of turning the proof track into a competition that would not lead to an unmanageable amount of overhead… we have collected vast amounts of data in the last two years and thoroughly evaluating it takes time… this year we would need to restrict the allowed proof size due to hardware limits of the new execution platform."* |
| 2025 | Absent. The word "proof" does not occur **anywhere** in `2025/rules.pdf` [M, `grep -i proof` → 0 matches] |
| **2026** | Still absent [M, same check on `2026/rules.pdf` → 0 matches] |

**The consequence for axeyum is concrete: there is no proof-exhibition setting in SMT-COMP to be
"comparable in."** If axeyum wants an external proof-exhibition venue today, the venue is the **SAT
Competition main track** (DRAT in, verified checker out), not SMT-COMP. Within SMT, the comparable
artifact is not a competition placing but the cvc5/CPC TCB-and-overhead table above, and the
`bv_decide` result in §6.2.

---

## 3. Model validation

### 3.1 The format

SMT-LIB **2.7** is current — released 2026-03-27 [C, <https://smt-lib.org/>], superseding 2.6.
SMT-COMP still specifies input in **2.6** concrete syntax [C, `2026/rules.pdf`].

A model is the response to `(get-model)` after `sat`, and per the rules must "consist of definitions
specifying **all and only** the current user-declared function symbols, in the format prescribed by
the SMT-LIB standard" [C]. The Model-Validation Track sets `(set-option :produce-models true)` as
the benchmark's second command [C]. Experimental divisions (non-linear arithmetic, arrays,
datatypes) need extra model syntax, proposed at
<https://smt-comp.github.io/2024/model.html> [C].

### 3.2 Dolmen is the official validator

[github.com/Gbury/dolmen](https://github.com/Gbury/dolmen) — OCaml, **BSD-2-Clause**, latest tagged
release v0.10 (2024-06-17), actively developed (push 2026-08-18) [C]. It parses, typechecks and
*evaluates* SMT-LIB, TPTP, DIMACS and Alt-Ergo input; Alt-Ergo uses it for SMT-LIB support. Its
three verdicts, per the SMT-COMP rules [C]:

- **VALID** — sat plus a full satisfying model;
- **INVALID** — an `unsat` answer, or a model that does not satisfy the input;
- **UNKNOWN** — no output, `unknown`, or a malformed/**partial** model.

Time limits: 20 min to solve, ~15 min to check [C].

### 3.3 Who actually passes — measured

From `results-mv-2026.json.gz`, 101,360 rows [M]. Dolmen's verdicts surface as result codes; here is
every 2026 entrant's full distribution:

| Solver | sat (VALID) | ModelParsingError | ModelPartialFunctionMissing | **ModelUnsat** | StrictTyping | Timeout | unknown |
|---|---|---|---|---|---|---|---|
| **bv_decide** | 1844 | 0 | 0 | **0** | 0 | 65 | 0 |
| **bv_decide-nokernel** | 1845 | 0 | 0 | **0** | 0 | 64 | 0 |
| **plat-smt** (Rust) | 703 | 11 | 0 | **0** | 0 | 0 | 0 |
| **OpenSMT** | 3784 | 0 | 0 | **0** | 1 | 188 | 0 |
| **Bitwuzla** | 10009 | 4 | 1 | **0** | 3 | 20 | 0 |
| **cvc5** | 17007 | 199 | 357 | **0** | 1 | 1521 | 9 |
| SMTInterpol | 7216 | 510 | 1 | **0** | 3 | 1751 | 3364 |
| SMT-RAT | 722 | 165 | 0 | **0** | 0 | 49 | 0 |
| **Yices2** | 10884 | 194 | 66 | **81** | 4 | 514 | 9 |
| **z3-BooledASS** | 9671 | 1708 | 240 | **7** | 4 | 866 | 6598 |

`ModelUnsat` is the hard failure — a model Dolmen evaluated to false. Only **Yices2 (81)** and
**z3-BooledASS (7)** produced any [M]. Yices2 also returned `unsat` on 3 sat benchmarks in this
track [M]. `ModelParsingError` and `ModelPartialFunctionMissing` are *well-formedness* failures —
these are much more common, and are pure output-format debt: cvc5 alone lost 556 benchmarks to them.

**Two lessons for axeyum.** First, more solvers lose model-validation points to **malformed or
partial models** than to wrong ones — the SMT-LIB model printer is a real, separately-tested
deliverable, not a formatting afterthought. Second, `dolmen --check-model` is a cheap, off-the-shelf,
*independent* validator that axeyum can run in CI on every `sat` result. That is a stronger
self-checking route than replay against the original term alone, because it is an outside implementation
of SMT-LIB semantics.

---

## 4. Benchmark methodology worth mirroring

All from the SMT-COMP rules PDFs, read with `pdftotext -layout` [C]:
[2024](https://smt-comp.github.io/2024/rules.pdf) · [2025](https://smt-comp.github.io/2025/rules.pdf) · [2026](https://smt-comp.github.io/2026/rules.pdf).

### 4.1 Limits and infrastructure

| | SMT-COMP 2024 | SMT-COMP 2025 | SMT-COMP 2026 | SAT Comp 2025 |
|---|---|---|---|---|
| Wall limit | 20 min | 20 min | 20 min | **5000 s** |
| Memory | **30 GB** | ~30 GB | ~30 GB | 30 GB |
| Cores | 4 per processor | 4 | 4 | **8** |
| Parallel track limit | — | **2 min** | **20 min** | — |
| Platform | **BenchExec** (moved off StarExec) | BenchExec, 168 `apollon` nodes, SoSy-Lab | same; +256-proc/2 TB box for Parallel | BenchCloud, SoSy-Lab Munich |

**StarExec is being decommissioned** — that is the stated reason for the 2024 move, and the reason
the memory limit *dropped* to 30 GB [C]. Solvers run with the filesystem read-only and a RAM disk
whose usage counts against the memory limit [C]. Every entrant must upload its final binary to
**Zenodo** [C]. There is no AWS cloud track in 2025/2026; `results-cloud-2024.json.gz` is the last
one [M].

### 4.2 Scoring — SMT-COMP does *not* use PAR-2

This is the most common mistake to avoid. **PAR-2** (penalized average runtime, unsolved instances
charged 2x the timeout) is the **SAT Competition's** measure. SMT-COMP uses a **lexicographic tuple**
[C, §7.1]:

```
parallel benchmark score = ⟨e, n, aw, w, ac, c⟩
```

`e` = erroneous results, `n` = correct results, `w`/`c` = wall/CPU time scores that are **set to zero
unless the benchmark was correctly solved**. Division scores sum componentwise, and are compared
**lexicographically**:

> "fewer errors takes precedence over more correct solutions, which takes precedence over less
> wall-clock time taken, which takes precedence over less CPU time taken." [C]

The **sequential score** re-derives a single-core number by imposing a *virtual CPU-time limit equal
to the wall limit* — if `c > T`, the result is discarded entirely (`e=n=c=0`) [C]. That is how a
parallel solver is prevented from buying its score with cores.

Four derived scores on the Single Query Track [C]:

| Score | Definition |
|---|---|
| **24-seconds score** | the parallel division score recomputed with **T = 24 s wall** |
| **sat score** | parallel score over satisfiable instances only |
| **unsat score** | parallel score over unsatisfiable instances only |
| sequential score | as above |

The 24 s score is what a downstream user of a solver-in-a-loop actually feels, and it is where the
rankings move most: in QF_BV 2026, Bitwuzla-MachBV holds first place on both measures but the gap
between solvers widens enormously at 24 s [M] — see §6.2.

### 4.3 Competition-wide rankings, including the VBS one

- **Best Overall** — Σ over divisions of `nn^D · log₁₀ N^D` where `nn^D = (n^D/N^D)²` if error-free,
  and **`nn^D = −2` if `e^D > 0`** [C]. The rules spell out the calibration: the −2 "subtracts an
  equivalent of two other completely solved divisions… Entering a possibly buggy solver that can
  solve all benchmarks has a positive expected value if the probability of some soundness bug in each
  of the divisions is below 1/(1+2) ≈ 33%." [C] That is an explicitly *priced* soundness risk.
- **Biggest Lead** — `(n₁+1)/(n₂+1)` over divisions [C].
- **Largest Contribution — this is the VBS ranking.** [C, §7.3.3] Define
  `vbs_n(D,S) = Σ_b max{n_b^s : s∈S, n_b^s>0}` and `vbs_w(D,S) = Σ_b min{w_b^s : …}`, where the
  minimum over an empty set is **1200 s**. A solver's contribution is
  `1 − vbs_n(D, S−s)/vbs_n(D, S)` — the fraction of the virtual best solver that vanishes when you
  remove it. **Unsound solvers (`e^D > 0`) are excluded from the VBS entirely**, and a division with
  ≤2 sound solvers is excluded [C].

This is the right shape for axeyum's own head-to-head reporting: *"how much of the VBS would be lost
without axeyum"* is a claim that survives a solver being slower than the field.

### 4.4 How disagreements and soundness bugs are handled

Two distinct mechanisms — do not conflate them [C, §7.2 and §5.5]:

1. **Removal of disagreements.** Benchmarks whose status is *unknown* are **removed from scoring** if
   two or more solvers that are sound on known-status benchmarks disagree. "Two solvers disagree on a
   benchmark if one of them reported sat and the other reported unsat." The organizers still *report*
   the disagreements for information.
2. **Error score.** For known-status benchmarks, a disagreeing answer sets `e=1`, which loses the
   division outright under lexicographic comparison and scores −2 in Best Overall and exclusion from
   the VBS ranking. In the Unsat-Core Track `e` also counts cores that are not actually unsat; in the
   Model-Validation Track it counts models that are not full satisfying models.

**SMT-COMP does not disqualify.** SAT Competition does: *"A solver will be disqualified if it
produces a wrong answer or a wrong certificate… Disqualified solvers will be marked as such on the
competition results page."* [C]

### 4.5 How often reference solvers actually disagree — measured

Directly relevant to using Z3/cvc5/Bitwuzla as differential oracles. Computed by grouping every
benchmark and looking for a `sat`/`unsat` split among the entrants [M]:

| Year | Benchmarks | Disagreeing | Rate | Concentration |
|---|---|---|---|---|
| SMT-COMP **2026** | 45,905 | **103** | 0.22% | QF_S 79, QF_BVFP 8, ABV 4, QF_AUFLIA 4, QF_ABVFP 3, QF_BV 3, FPLRA 1, QF_ABVFPLRA 1 |
| SMT-COMP **2025** | 129,361 | **59** | 0.046% | QF_S 55, NIA 2, QF_ABVFP 1, UFDTLIRA 1 |

Concrete instances [M]:

- `QF_ABVFP/query.32.smt2` (2026): **COLIBRI says unsat, Bitwuzla and cvc5 say sat.**
- `FPLRA/float-div1_true-unreach-call.i_574.smt2` (2026): **colibri2 unsat**, Bitwuzla, cvc5, MathSAT
  and Z3 all sat.
- `QF_S/wildcard-matching-regex-{03,05,06}.smt2` (2025): **OSTRICH sat, Z3-Noodler unsat.**
- `ABV/packet_filter.i_{19,26,31}.smt2` (2026): a cvc5 *derivative* says sat where base cvc5,
  SMTInterpol and Z3 say unsat.

**Read this carefully before trusting a single oracle.** The disagreement rate is low but structured,
not random: it clusters in **strings** and in **floating-point**, and the FP disagreements are
between the bit-blasting solvers and the interval/propagation solver (COLIBRI). A differential fuzz
against one oracle in QF_S or FP is measuring agreement with that oracle's bugs. The
mitigation the competition itself uses is a **quorum**, and axeyum should mirror it: for the string
and FP routes, disagreement with Z3 alone is not evidence of an axeyum bug, and agreement with Z3
alone is not evidence of correctness.

---

## 5. Reference-solver activity summary

| Tool | Latest release | Date | Verdict |
|---|---|---|---|
| Z3 | z3-5.1.0 | 2026-08-16 | Active; **major version bump to 5.x** |
| cvc5 | cvc5-1.3.4 | 2026-05-07 | Active |
| Bitwuzla | 0.9.1 | 2026-05-21 | Active |
| Yices 2 | yices-2.7.0 | 2025-07-16 | Active |
| OpenSMT | v2.9.2 | 2025-06-16 | Active |
| STP | 2.4.1 | 2026-08-01 | Active |
| Alt-Ergo | v2.6.3 | 2026-04-14 | Active |
| **Boolector** | — | archived **2024-08-23** | **Retired** → Bitwuzla |
| CaDiCaL | rel-3.0.1 | 2026-07-20 | Active |
| Kissat | rel-4.0.4 | 2025-10-16 | Active |
| Ethos | ethos-0.2.3 | 2026-05-06 | Active |
| Dolmen | v0.10 | 2024-06-17 | Active (unreleased commits since) |
| Carcara | carcara-1.1.0 | **2023-08-29** | Repo active (2026-09) but **no tagged release in 3 years** |
| Golem | v0.9.0 | 2025-08-08 | Active |
| drat-trim | — | push 2024-11 | Maintained |
| `rate` (Rust DRAT/LRAT) | — | push **2022-02** | **Stale** |
| varisat | 0.2.2 | **2020-09-09** | **Unmaintained** |

---

## 6. What proofs cost — the published numbers

### 6.1 cvc5 / CPC / Ethos — the definitive 2026 measurement

Reynolds, Schurr, Soldevila, Barbosa, Tinelli, Barrett, *The Cooperating Proof Calculus*, CAV 2026
[C, [PDF](https://www.hanielbarbosa.com/papers/2026cav.pdf)]. Whole SMT-LIB library minus FP;
310,830 benchmarks; 60 s solve timeout, 600 s for proof/check; Xeon E5-2686 v4. **Overhead is the
runtime ratio on commonly solved instances.**

| Category | Solved | `+Proof` ratio | `+Proof+Check` ratio | Avg proof steps |
|---|---|---|---|---|
| QF+UF (UF/arrays/datatypes) | 8,971 | 4.12x | **15.85x** | 22,700 |
| QF+Arith | 14,515 | 2.58x | 4.04x | 19,000 |
| **QF+BV** | 27,840 | **11.94x** | **16.28x** | 9,900 |
| QF+Str | 26,793 | **1.75x** | **2.77x** | 500 |
| Q+UF (quantified) | 65,015 | 2.44x | 3.12x | 2,200 |
| Q−UF | 10,054 | 3.38x | 6.37x | 1,100 |
| **Overall** | **153,188** | **5.11x** | **7.11x** | 6,100 |

Other numbers from the same paper [C]:

- **Coverage**: proofs generated for 99.4% of what cvc5 solved; 98.9% also checked. 913.4 M proof
  steps; 427 of 585 rules exercised.
- **TCB**: 360k+ lines of C++ → **~10k lines of Ethos C++ + ~8k lines of Eunoia signature**.
- **The cost of being proof-capable at all**: cvc5's proof-producing "safe" configuration disables
  CaDiCaL for BV, QF_UF symmetry breaking, and CAD coverings for NRA. It solves **2.1% fewer** unsat
  benchmarks and is **17.1% slower on average** — or **9.9% slower excluding QF_BV** [C]. The whole
  17.1% − 9.9% gap is bit-vectors losing CaDiCaL.
- **FP has no proofs at all.** cvc5 cannot prove its SymFPU word-blasting step, and the paper says
  writing the Eunoia rules first would be "a somewhat futile exercise" [C].
- **Reconstruction into Lean is ~20x slower than Ethos**, and `lean-smt` currently covers **180 of
  585** CPC rules [C].

### 6.2 The measurement that matters most to axeyum: `bv_decide` in SMT-COMP 2026

`bv_decide` is Lean 4's bitvector decision procedure, entered as
[Leanwuzla](https://github.com/hargoniX/Leanwuzla) by the Lean FRO with Cambridge and Stanford [C].
It bit-blasts inside Lean, calls CaDiCaL, and **checks the returned LRAT certificate through the Lean
kernel**. `bv_decide-nokernel` is the identical pipeline with kernel checking switched off — the
competition ran both, which gives a clean isolation of the cost of trusted checking. Computed from
`results-sq-2026.json.gz`, QF_BV, 2,540 benchmarks [M]:

| Solver | Solved (1200 s) | Solved within 24 s |
|---|---|---|
| Bitwuzla-MachBV | 2495 (98.2%) | 2401 (94.5%) |
| Bitwuzla | 2475 (97.4%) | 2385 (93.9%) |
| Yices2 | 2472 (97.3%) | 2332 (91.8%) |
| **bv_decide-nokernel** | **2404 (94.6%)** | — |
| **bv_decide** (kernel-checked) | **2401 (94.5%)** | **1554 (61.2%)** |
| cvc5 | 2375 (93.5%) | 1997 (78.6%) |
| Z3-GEX | 2294 (90.3%) | 1962 (77.2%) |
| Roole (Rust) | 677 (26.7%) | 470 (18.5%) |

Head-to-head, `bv_decide` vs Bitwuzla [M]: **both solve 2391; Bitwuzla-only 84; bv_decide-only 10;
neither 55.** On the 2,391 commonly solved, `bv_decide` is a **median 8.73x slower**, p90 **278x**.

Isolating the trusted step — `bv_decide` vs `bv_decide-nokernel` on the 2,401 both solve [M]:

| | median | p90 | p99 | max |
|---|---|---|---|---|
| wall-time ratio (kernel / no-kernel) | **1.069** | 2.05 | 3.06 | 7.5 |
| memory ratio | 1.02 | 4.13 | — | — |

> **The finding, stated plainly: trusted checking costs a median 6.9%. Proof-producing search costs
> 8.7x.** The Lean kernel is not the bottleneck in a certified BV pipeline — the certified bitblast
> and the certificate-producing SAT call are. This is the single strongest available evidence for
> axeyum's architecture, *and* the clearest statement of where its engineering effort has to go.

Corroborating: cvc5's proof-producing safe mode loses CaDiCaL on BV and pays 17.1% for it [C], and
cvc5's own QF+BV proof overhead is the worst of any category at 11.94x [C]. Bit-vectors are where
certification is most expensive across every system measured.

### 6.3 SAT-level proof logging

| Claim | Number | Source |
|---|---|---|
| FRAT vs DRAT elaboration | **>84% median reduction in elaboration time, >94% in peak memory** | [arXiv:2109.09665](https://arxiv.org/pdf/2109.09665), TACAS 2021 [C] |
| Binary vs text DRAT | ~**3x** smaller files | [SAT Comp 2025 output spec](https://satcompetition.github.io/2025/output.html) [C] |
| GRAT (`gratgen`+verified `gratchk`) | reported **faster than the unverified drat-trim** | [GRAT project](https://www21.in.tum.de/~lammich/grat/), JAR 2020 [C] |
| SAT Comp 2024 checker timeouts | **no wrong certificates found**; GRAT 2 timeouts, DPR-trim 17, VeriPB 25 | 2024 results slides — **[I]**, snippet only, PDF did not extract |
| CaDiCaL/Kissat DRAT logging slowdown | **no authoritative published figure found** | — [I, negative] |

I could not find a citable measured slowdown for DRAT proof logging in CaDiCaL or Kissat. If axeyum
needs that number, it has to measure it — and that is a cheap, genuinely publishable experiment,
because the field appears not to have a current one.

---

## 7. Implications for axeyum's yardsticks

### 7.1 Reference solver per division family

Current choices are right; the corrections are in bold. All rankings measured from SMT-COMP 2026 [M].

| Family | Reference | Second opinion (required for a soundness claim) | Note |
|---|---|---|---|
| **QF_BV** | **Bitwuzla** | Yices2 | Bitwuzla-MachBV is the frontier; base Bitwuzla is within 20 benchmarks and is what you can actually build |
| **QF_ABV, ABV, QF_AUFBV** | **Bitwuzla** | Yices2 | Bitwuzla wins all three |
| **QF_UF, QF_AX, QF_AUFLIA** | **OpenSMT** *or* **Yices2** | SMTInterpol | **cvc5 is not the leader here.** All three saturate QF_UF (1104/1104) |
| **QF_LRA, QF_LIA, QF_IDL, QF_RDL** | **OpenSMT** (LRA/LIA), **Yices2** (RDL, 24 s LIA) | cvc5 | **Change from cvc5.** QiuQi leads QF_LIA/QF_IDL but is a 2026 newcomer with no public source yet |
| **QF_UFLRA, QF_UFLIA, QF_ALIA, QF_ANIA** | **SMTInterpol** or **Yices2** | cvc5 | SMTInterpol leads three of four |
| **QF_NIA, QF_NRA, NIA** | **Z3** (via its 2026 derivatives) | cvc5, Yices2 | Z3's lineage owns nonlinear arithmetic outright |
| **NRA** (quantified) | **SMT-RAT** | Z3-alpha2 | |
| **LRA** (quantified) | **YicesQS** | Z3 | 599/602 |
| **Quantified UF / datatypes / mixed** | **cvc5** | Z3 | cvc5's real territory — it wins ~20 quantified logics |
| **QF_S / QF_SLIA** | **Z3-Noodler** | **OSTRICH** — mandatory | cvc5 is far behind (364/2496 on QF_S). **Never use a single string oracle**: 79 of 103 disagreements in 2026 were QF_S [M] |
| **FP, QF_FP, QF_FPLRA** | **Bitwuzla** | **COLIBRI / colibri2** — mandatory | COLIBRI leads the 24 s score on QF_FP and QF_FPLRA, and is the *disagreeing* party in the FP soundness splits [M] |
| **CNF / SAT** | **Kissat**, **CaDiCaL** | — | Correct as is |

Three concrete changes to axeyum's current set-up: **add Yices2 and OpenSMT** as the quantifier-free
arithmetic/equality yardsticks (cvc5 is not the frontier there); **add OSTRICH** alongside any string
oracle; **add COLIBRI** for FP. Keep cvc5 for quantified logics and Bitwuzla for BV/ABV.

Practical routes into Rust: `easy-smt` (subprocess SMT-LIB, 1.3 M downloads, no FFI, keeps the
no-C/C++-dependency promise for the default build) is the right way to wire *any* of these as a
yardstick. `cvc5-rs` (official, BSD-3, first published 2026-04) and `z3.rs` exist if in-process is
needed later.

### 7.2 Which certificate format a Rust checker should accept or emit

**Emit DRAT, elaborate to LRAT, check LRAT.** That is the settled, verified-checker-backed pipeline,
and it is the only proof-exhibition setting with a live external venue.

| Layer | Emit | Accept | Why |
|---|---|---|---|
| **SAT core** | **DRAT** (text + the specified binary encoding) | — | It is what the SAT Competition main track requires, unchanged since 2014 [C]. Emitting DRAT makes axeyum's core externally checkable by `drat-trim`, `dpr-trim`→`cake_lpr`, `gratgen`→`gratchk`, all today. |
| **SAT core, second step** | **LRAT** natively, if axeyum can | **LRAT** | LRAT is what the *verified* checkers actually consume. A solver that emits LRAT directly skips the elaboration step that dominates DRAT checking cost. Prior art: `varisat` (Rust, has `varisat-lrat`) and `bv_decide`. |
| **Elaboration** | — | consider **FRAT** | If axeyum's core cannot emit full LRAT hints, FRAT is the designed middle: >84% median cut in elaboration time [C]. `frat-rs` already converts FRAT→LRAT. |
| **BV / theory layer** | **LRAT over the bit-blasted CNF**, with a checkable lowering map | — | This is exactly what `bv_decide` does, and §6.2 measures its price. It is the shortest path to a genuinely trusted QF_BV unsat, and axeyum already keeps lowering/lift maps by hard rule. |
| **SMT layer, long term** | **Alethe** (partial) or **CPC/Eunoia** | — | Alethe is the open, multi-producer format with a **Rust** checker (Carcara) — the natural target if axeyum wants an existing Rust checker to validate against. CPC/Ethos is more complete but is cvc5's calculus with a C++ checker. |
| **Pseudo-Boolean** | **VeriPB** if cardinality/symmetry reasoning is ever added | — | Verified checker (CakePB); the checker is itself Rust; `rustsat` already has VeriPB proof-logging support [C] |

**Existing Rust pieces to reuse or study rather than rebuild:**

- **`rate`** ([repo](https://github.com/krobelus/rate)) — Rust DRAT/DPR checker that *emits* trimmed
  DRAT, DPR, **LRAT** or **GRAT**. Stale since 2022, MIT — but it is the reference for a Rust
  DRAT→LRAT converter and worth reading before writing one.
- **`varisat-lrat`** — Rust LRAT emission from a Rust CDCL core; the closest prior art to what
  axeyum's own core needs.
- **`Carcara`** ([repo](https://github.com/ufmg-smite/carcara)) — Rust Alethe checker *and
  elaborator*, Apache-2.0, active. If axeyum ever emits Alethe, this is the free external validator.
- **`CreuSAT`** ([repo](https://github.com/sarsko/CreuSAT)) — a **Creusot-verified** CDCL SAT solver
  in Rust, 698 stars, active. The single most relevant artifact to axeyum's trust story: it is the
  *other* way to get a trusted SAT answer (verify the solver) versus axeyum's way (check the
  certificate). Worth an explicit ADR paragraph on why axeyum takes the certificate route.
- **`ordeal-lrat`** ([repo](https://github.com/pulseengine/ordeal)) — someone else's
  "untrusted QF_BV solver + verified LRAT checker as the sole trusted component," in Rust, shipped
  2026-08. Read it before writing axeyum's checker.

### 7.3 Method notes axeyum should adopt

1. **Score the SMT-COMP way, not the PAR-2 way.** The lexicographic `⟨e, n, w, c⟩` tuple with `w=0`
   on an incorrect or unsolved benchmark makes a soundness error *dominate* — which matches axeyum's
   own stated metric far better than an averaged runtime penalty. Report the **24 s score** alongside
   the 20-minute score; the two rank solvers differently and the 24 s number is the one a
   solver-in-a-loop feels.
2. **Report a VBS contribution, not a win rate.** `1 − vbs(S−axeyum)/vbs(S)` is defensible even while
   axeyum is slower than the field, and it is the competition's own formula [C, §7.3.3].
3. **Never use one differential oracle in strings or FP.** 79 of 103 disagreements in 2026 were
   QF_S [M]; the FP disagreements split bit-blasting solvers against COLIBRI [M].
4. **Run `dolmen --check-model` in CI on every `sat`.** It is BSD-2, off-the-shelf, and an
   *independent* implementation of SMT-LIB semantics. The 2026 data shows well-formedness failures
   (parse errors, partial models) outnumber wrong models by roughly 30:1 across entrants [M] — this
   is the cheap failure mode to close first.
5. **Do not re-run reference solvers to build a head-to-head.** Every per-benchmark runtime for
   2018–2026 is a 12–22 MB gzipped JSON download (§0). Re-running is expensive, is contended on the
   dev box, and produces numbers that are not comparable to anyone else's frame.
6. **Beware the cross-year comparison.** 2025 selected 129,361 benchmarks; 2026 selected 45,905 [M].
   Solved-counts do not transfer between years.
7. **The proof-exhibition claim needs care.** SMT-COMP has had no proof track since its
   discontinuation in **2024** [C] (an earlier draft of this line said "since 2023"; the table in
   §2.4 and the 2024 rules PDF are the authority), so
   "proof exhibition" cannot be won there. The honest framings available are: an entry in the **SAT
   Competition main track** with a DRAT proof and a verified checker; a **TCB comparison** against
   cvc5's published 10k+8k lines [C]; or a **`bv_decide`-style head-to-head** on QF_BV, where the
   reference cost of a kernel-checked pipeline is now publicly measured [M].

---

## Sources

### Competition primary sources (rules, results, data)
- SMT-COMP 2024 rules — https://smt-comp.github.io/2024/rules.pdf
- SMT-COMP 2025 rules — https://smt-comp.github.io/2025/rules.pdf
- SMT-COMP 2026 rules — https://smt-comp.github.io/2026/rules.pdf
- SMT-COMP 2025 site / results — https://smt-comp.github.io/2025/ , https://smt-comp.github.io/2025/results/
- SMT-COMP 2026 results — https://smt-comp.github.io/2026/results/
- SMT-COMP 2024 results — https://smt-comp.github.io/2024/results/
- SMT-COMP participants — https://smt-comp.github.io/2024/participants/ , https://smt-comp.github.io/2025/participants/
- **Raw per-benchmark data** — https://github.com/SMT-COMP/smt-comp.github.io/tree/master/data
- Solver submission JSONs — https://github.com/SMT-COMP/smt-comp.github.io/tree/master/submissions
- `smtcomp` tooling + README — https://github.com/SMT-COMP/smt-comp.github.io
- Scrambler — https://github.com/SMT-COMP/scrambler ; Trace executor — https://github.com/SMT-COMP/trace-executor
- SMT-COMP model syntax for experimental divisions — https://smt-comp.github.io/2024/model.html
- Proof Exhibition Track (2022) — https://smt-comp.github.io/2022/proof-track.html
- Proof Exhibition results (2023, Bitvec) — https://smt-comp.github.io/2023/results/bitvec-proof-exhibition
- BenchExec — https://github.com/sosy-lab/benchexec ; competition machines — https://vcloud.sosy-lab.org/cpachecker/webclient/master/info
- SAT Competition 2025 — https://satcompetition.github.io/2025/ , /rules.html , /output.html , /benchcloud.html
- SAT Competition verified-checker docs — https://satcompetition.github.io/2025/downloads/checkers/cakelpr.pdf , /veripb.pdf ; https://satcompetition.github.io/2023/checkers.html
- CHC-COMP — https://chc-comp.github.io/ , https://chc-comp.github.io/2024/CHC-COMP%202024%20Report%20-%20HCSV.pdf , https://chc-comp.github.io/2025/
- PB Competition 2024 rules — http://www.cril.univ-artois.fr/PB24/

### SMT-LIB and benchmarks
- SMT-LIB (standard 2.7, released 2026-03-27) — https://smt-lib.org/
- SMT-LIB benchmarks — https://smt-lib.org/benchmarks.shtml ; https://zenodo.org/communities/smt-lib
- Older releases on StarExec — https://www.starexec.org/starexec/secure/explore/spaces.jsp?id=239
- Global Benchmark Database — https://github.com/Udopia/gbd , https://benchmark-database.de/ , https://benchmark-database.de/getdatabase/meta.db , https://doi.org/10.4230/LIPIcs.SAT.2024.18 , https://udopia.github.io/gbd/

### Solvers
- Z3 — https://github.com/Z3Prover/z3 ; proof/unsat-core issue https://github.com/z3prover/z3/issues/7538
- cvc5 — https://github.com/cvc5/cvc5 , NEWS.md https://github.com/cvc5/cvc5/blob/main/NEWS.md ; Rust bindings https://github.com/cvc5/cvc5-rs
- Bitwuzla — https://github.com/bitwuzla/bitwuzla
- Boolector (archived) — https://github.com/Boolector/boolector
- Yices 2 — https://github.com/SRI-CSL/yices2 , https://yices.csl.sri.com/
- MathSAT 5 — https://mathsat.fbk.eu/ , https://mathsat.fbk.eu/releasenotes.html
- OpenSMT — https://github.com/usi-verification-and-security/opensmt
- SMTInterpol — https://github.com/ultimate-pa/smtinterpol , https://ultimate.informatik.uni-freiburg.de/smtinterpol/proof-format.html
- veriT — https://www.verit-solver.org/ , https://verit.loria.fr/
- STP — https://github.com/stp/stp
- Alt-Ergo — https://github.com/OCamlPro/alt-ergo , https://alt-ergo.ocamlpro.com/
- Princess — https://github.com/uuverifiers/princess
- Vampire — https://github.com/vprover/vampire
- SMT-RAT — https://github.com/ths-rwth/smtrat
- COLIBRI / colibri2 — https://colibri.frama-c.com/ , https://git.frama-c.com/pub/colibrics
- Z3-Noodler — https://github.com/VeriFIT/z3-noodler , https://arxiv.org/abs/2310.08327
- OSTRICH / OSTRICH2 — https://github.com/uuverifiers/ostrich , https://arxiv.org/abs/2506.14363
- Z3-alpha — https://github.com/JohnLyu2/z3alpha , https://arxiv.org/html/2401.17159v2
- Amaya — https://github.com/MichalHe/amaya , https://arxiv.org/pdf/2403.18995
- Q3B — https://github.com/martinjonas/Q3B
- Yaga — https://github.com/d3sformal/yaga , https://d3s.mff.cuni.cz/files/software/yaga/yaga.pdf
- YicesQS — https://github.com/disteph/yicesQS , https://www.csl.sri.com/users/sgl/Work/Reports/2026-yicesQS.pdf
- dReal — https://github.com/dreal/dreal4
- Eldarica — https://github.com/uuverifiers/eldarica ; Golem — https://github.com/usi-verification-and-security/golem , https://link.springer.com/article/10.1007/s10703-025-00470-9
- smt-switch — https://github.com/stanford-centaur/smt-switch , https://arxiv.org/pdf/2007.01374 ; pySMT — https://github.com/pysmt/pysmt
- **bv_decide / Leanwuzla** — https://github.com/hargoniX/Leanwuzla , system description https://github.com/hargoniX/Leanwuzla/releases/download/smtcomp2026/bv_decide.pdf , binary https://zenodo.org/records/20600607
- **plat-smt** — https://github.com/dewert99/plat-smt , https://zenodo.org/records/20681145
- **Roole** — https://github.com/onderjan/roole , https://zenodo.org/records/20584485
- QiuQi — https://github.com/YZhang322/QiuQi-for-SMT-COMP-2026 ; Xolver — https://github.com/fuqi-jia/Xolver ; NeuroSym — https://github.com/VishalKumarSwain/NeuroSym ; Samet — https://zenodo.org/records/20629779
- **OxiZ** — https://github.com/cool-japan/oxiz
- **Ordeal** — https://github.com/pulseengine/ordeal ; consumer https://github.com/pulseengine/synth

### Rust ecosystem
- crates.io API — `https://crates.io/api/v1/crates/<name>` for varisat, batsat, splr, rustsat (+ adapters), cadical, kissat, minisat, ipasir, screwsat, z3, z3-sys, cvc5, easy-smt, egg, egglog, bitwuzla-sys, boolector, yices2, oxiz*, ordeal, ordeal-lrat
- RustSAT — https://github.com/chrjabs/rustsat (SAT 2024 tool paper)
- varisat — https://github.com/jix/varisat , manual https://jix.github.io/varisat/manual/0.2.1/print.html
- splr — https://github.com/shnarazk/splr ; batsat — https://github.com/c-cube/batsat
- **CreuSAT** — https://github.com/sarsko/CreuSAT
- **rate** (Rust DRAT/DPR→LRAT/GRAT) — https://github.com/krobelus/rate
- Smithril — https://github.com/smithril/smithril
- egg / egglog — https://github.com/egraphs-good/egg , https://github.com/egraphs-good/egglog

### Proof formats and checkers
- DRAT / drat-trim — https://github.com/marijnheule/drat-trim , https://www.cs.utexas.edu/~marijn/drat-trim/
- LRAT (+ Coq and ACL2 certified checkers) — https://arxiv.org/abs/1612.02353 ; ACL2 books https://github.com/acl2/acl2/tree/master/books/projects/sat/lrat
- cake_lpr — https://github.com/tanyongkiam/cake_lpr , https://pmc.ncbi.nlm.nih.gov/articles/PMC7984575/ , https://link.springer.com/article/10.1007/s10009-022-00690-y
- GRAT — https://www21.in.tum.de/~lammich/grat/ , https://link.springer.com/chapter/10.1007/978-3-319-66263-3_29 , https://link.springer.com/article/10.1007/s10817-019-09525-z
- FRAT — https://arxiv.org/pdf/2109.09665 , https://github.com/digama0/frat
- PR / DPR — https://link.springer.com/chapter/10.1007/978-3-030-24258-9_5 , https://arxiv.org/pdf/1909.00520
- VeriPB / CakePB — https://veripb.org/ , https://github.com/StephanGocht/VeriPB
- Alethe — https://verit.loria.fr/documentation/alethe-spec.pdf , https://arxiv.org/abs/2107.02354
- **Carcara** — https://github.com/ufmg-smite/carcara , https://team.inria.fr/veridis/files/2023/05/carcara.pdf
- LFSC — https://github.com/cvc5/LFSC , https://cvc5.github.io/docs/cvc5-1.0.8/proofs/output_lfsc.html
- cvc5 Alethe output — https://cvc5.github.io/docs/cvc5-1.0.0/proofs/output_alethe.html
- **CPC / Eunoia / Ethos** — https://www.hanielbarbosa.com/papers/2026cav.pdf (CAV 2026) ; https://cvc5.github.io/docs/cvc5-1.2.1/proofs/output_cpc.html ; https://github.com/cvc5/ethos ; Ethos paper https://link.springer.com/chapter/10.1007/978-3-032-32589-1_19 ; user manual https://github.com/cvc5/ethos/blob/main/user_manual.md
- Barbosa et al., *Flexible Proof Production in an Industrial-Strength SMT Solver*, IJCAR 2022 (cited as [2] in the CPC paper)
- SMTCoq — https://github.com/smtcoq/smtcoq
- Isabelle reconstruction — https://cvc5.github.io/blog/2024/03/15/isabelle-reconstruction.html , https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITP.2025.26
- **lean-smt** — https://github.com/ufmg-smite/lean-smt , https://arxiv.org/html/2505.15796v1
- Dedukti / Lambdapi / EuroProofNet tools — https://europroofnet.github.io/tools/ , https://radar.inria.fr/report/2023/deducteam
- Ekstrakto (TSTP→Dedukti; superseded by GDV-LP) — https://cgi.cse.unsw.edu.au/~eptcs/paper.cgi?PxTP2019.5.pdf
- Barrett, Fontaine, Tinelli, *Proofs in Satisfiability Modulo Theories* — https://people.montefiore.uliege.be/pfontain/Barrett18.pdf
- Dolmen — https://github.com/Gbury/dolmen

---

## Open questions this catalog could not close

1. **No published DRAT proof-logging slowdown figure for CaDiCaL or Kissat** was found [I, negative].
   Axeyum measuring this would fill a real gap.
2. The **SAT Comp 2024 checker-timeout statistics** (GRAT 2, DPR-trim 17, VeriPB 25, no wrong
   certificates) come from a slide deck that would not text-extract — treat as [I] until the PDF is
   read properly.
3. **When VeriPB became mandatory** in the PB Competition certificate tracks is undated [I].
4. **SMT-COMP 2026 official division winners** were not read from the results pages; §1.2 gives
   *per-logic solved counts computed from the raw data* [M], which is a different (finer) cut than
   the official per-division sequential ranking. Do not quote §1.2 as "won division X".
5. **OxiZ's actual quality is unassessed** [I]. It ships a large crate family at high cadence from an
   account that publishes many "pure Rust reimplementation" projects; it did not enter SMT-COMP 2026.
