# render/out -- the P0 deliverables

**Generated. Do not edit anything in this directory.** Every file here is
produced by `render/build-p0-outputs.sh` from committed Doc-IR manifests and
committed run records; re-running that script over an unchanged tree reproduces
the whole directory byte for byte, the PDF included.

```sh
./render/build-p0-outputs.sh
```

| file | what it is |
|---|---|
| `certificate.md` | the NoH-p2 weight certificate, Markdown (folds for `detail`, links for `archive`) |
| `certificate.tex` | the same document as a LaTeX fragment a paper would `\input{}` |
| `certificate-standalone.tex` | a minimal wrapper that `\input`s the fragment, so it compiles alone |
| `axeyum.sty` | the macro package the fragment needs (`\axclaim`, `\axtable`, `\axcert`, ...) |
| `certificate.pdf` | `pdflatex certificate-standalone.tex`, renamed |
| `certificate.html` | the same document as one self-contained page |
| `facts-pilot.html` | fact pilot: the 9-fact Fibonacci frontier (two status axes, import backlog) |
| `facts-pilot-arith.html` | fact pilot: the 17-fact arithmetic closure (dense DAG, 34 checked evidence rows) |
| `facts-atlas.html` | the whole ledger: 324 facts, 135 edges, 37 component graphs, full index |
| `facts.md` | the atlas as Markdown |

Every HTML page is a single file with **zero external requests** -- no fonts, no
scripts, no images fetched -- enforced twice, by the Rust lint inside the
emitter and by an independent grep gate in `render/check.sh` step 9.

Nothing on these pages is transcribed. Every number, table, badge and figure is
read from a run record or the fact ledger by `axeyum-render`, and a claim whose
evidence did not run green cannot render as established: see
`docs/render-2026-08/01-goals-and-requirements.md` for the fail-closed law and
`docs/render-2026-08/14-p0-exit-report.md` for the measurements that say it
holds.
