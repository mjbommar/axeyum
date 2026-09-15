# z3 on the UFNIA and AUFLIRA Tier 1 lists — the gap table's two blank rows

**2026-09-15.** z3 4.13.3 on the pinned Tier 1 200-file lists for the two
divisions that had no reference on those lists. Same envelope as the board:
24 s wall (`-T:23` inside a 24 s `timeout`), 8 GiB `ulimit -v`, one pinned
core per worker, four workers on **s4 while five lanes were building** — so
this is a single-arm reference under load, and a `none` here is a kill at
24 s, not an `unknown`. Ours is the 1,400-row ledger sweep on `db31113fa`.

| division | ours | z3 | z3 sat / unsat / unknown / none | behind |
|---|---:|---:|---|---:|
| UFNIA | 54/200 | **94** | 19 / 75 / 5 / 101 | **40** |
| AUFLIRA | 178/200 | **197** | 1 / 196 / 0 / 3 | **19** |

UFNIA's 101 `none` says half the list is hard for z3 too at 24 s; the 40 we
trail are inside its 94. AUFLIRA is nearly closed.

## The first run of `run-z3.sh` was a broken instrument

400 of 400 rows read `none`, each after exactly 24 s. The lists carry ABSOLUTE
paths, so the runner built a nonexistent `$ROOT/$path`; z3 handed a bad path
does not exit — under `xargs` the children inherit the list pipe as stdin, and
z3 read the remaining list lines as SMT-LIB until the timeout. Fixed by using
the list path as-is and giving z3 `</dev/null`; a one-file smoke test printed
`unsat` before the relaunch. Kept here because "400 timeouts" would have been
read as "z3 cannot do these either".
