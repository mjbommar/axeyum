# References

Shallow clones of reference projects used while designing and implementing
Axeyum. The clones themselves are gitignored; run
[`../scripts/fetch-references.sh`](../scripts/fetch-references.sh) to
(re)populate this directory.

| Project | Why it is here |
|---|---|
| `rustsat` | Rust SAT ecosystem: encodings, solver interfaces, DIMACS/WCNF I/O. |
| `varisat` | Rust CDCL solver with DRAT/LRAT proof output; unmaintained since 2019, so a design reference more than a dependency. |
| `splr` | Modern Rust CDCL solver; algorithmic reference. |
| `batsat` | MiniSat-derived Rust solver; simplest adapter candidate. |
| `CreuSAT` | Formally verified Rust SAT solver; evidence/checking reference. |
| `z3.rs` | Z3 Rust bindings; M0 backend path and lifetime-design cautionary tale. |
| `egg` | E-graph rewriting; optional optimizer research path. |
| `egglog` | Successor to egg; where active e-graph development moved. |
| `carcara` | Alethe SMT proof checker in Rust; proof-checking reference. |
| `drat-trim` | DRAT proof checker and DRAT->LRAT elaboration reference. |
| `cadical` | C++ CDCL design reference (clause arena, IPASIR, IPASIR-UP). |
| `kissat` | C CDCL performance reference (memory layout, propagation). |
| `bitwuzla` | BV/array solver reference (preprocessing, prop local search). |
| `minisat` | Foundational CDCL design; the educational baseline for our own SAT core. |
| `cryptominisat` | Richer inprocessing and XOR reasoning; infosec workload reference. |
| `btor2tools` | BTOR2 format parser/tools reference. |
| `cvc5` | Broad SMT solver; the strongest proof-production reference (CPC/Alethe/LFSC). |
| `vampire` | Leading first-order superposition prover; proving-horizon reference. |
| `eprover` | E superposition prover; cleaner/smaller saturation architecture reference. |
| `lean4` | Proof assistant; trusted-kernel architecture and future interop target. |

Z3 itself is not cloned (very large); use the system package or the `z3.rs`
bundled build, and the upstream repo https://github.com/Z3Prover/z3 for
source reading.
