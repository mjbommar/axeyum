# Artifact repo build log (append-only)

Task: build /home/mjbommar/projects/personal/axeyum-rado-artifacts; fix evidence defects.

## 2026-08-12T22:32:47-04:00  session start

## Environment survey (2026-08-12T22:35)
```
$ git -C /home/mjbommar/projects/personal/axeyum rev-parse HEAD
620ceec898229ee98e089e9c6b65f6fb57a83149   # NOTE: moved from 175372bdc during session (another agent commits here)
$ rustc --version
rustc 1.94.1 (e408947bf 2026-03-25)
$ nproc -> 4 ; free -g total 61 ; df . -> 64G free
$ ls target/release/examples -> EMPTY (nothing prebuilt in release)
$ ls references/ -> present locally but gitignored (kissat, drat-trim, ...) => verification script must NOT require them
$ cat rust-toolchain.toml -> absent ; Cargo.toml rust-version = "1.88"
```

## Verifying review finding #1 and #4 (2026-08-12T22:40)
```
$ cd /home/mjbommar/projects/personal/axeyum-rado-paper
$ tar tzf build/arxiv/shell-colourings-for-a-x-y-bz-arxiv.tar.gz | grep -E 'a4-b3|a2-b3'
anc/claims/rado-r3-a2-b3/...   anc/claims/rado-r3-a4-b3/...
anc/claims/rado-r4-a2-b3/claim.json
anc/claims/rado-r4-a2-b3/witness-front-door.txt
anc/claims/rado-r4-a2-b3/witness.txt
```
CONFIRMED: the BUILT arXiv tarball (mtime 20:34) has NO rado-r4-a4-b3 (the 313 claim)
and its rado-r4-a2-b3 lacks cube-cover.tsv (so no upper-bound artifact at all for 226).
NUANCE (honesty): the on-disk anc/ tree was refreshed at 22:33 and DOES now contain
rado-r4-a4-b3 with 5 cover TSVs + witness. Working tree is git-clean, so the refresh is
committed content (2a817e7). => the defect that remains is exactly review #4: the tarball
does not depend on the artifacts step and had drifted. I did not modify the paper repo.

## Regeneration measurements (2026-08-12T22:45)
radocert = artifact-repo tool, thin CLI over axeyum-cnf + axeyum-search.
```
$ radocert gen 2 3 4 226 rust_F226.cnf ; sha256sum
d8aefe75e5426e0c71bfb48193ed1ef90052389f19926f2c419758c1fa392cd1   == ledger sha256 for F_226.cnf  OK
$ python3 axeyum/scripts/gen-rado-instance.py 2 3 4 226 -> same sha256                        OK
$ radocert gen 4 3 4 313 ; sha256 5ce2ad94c712faace512652e0d940664e77c4511c950f6afa2667d9548a77aab
   == python generator output.  NOTE: no F_313.cnf exists in the ledger to compare against.
$ radocert gen 4 3 3 73 F73.cnf ; radocert refute F73.cnf F73.drat
   -> 127 steps; cmp against gunzip of ledger F_73.drat.gz => BYTE-IDENTICAL
$ radocert gen 4 2 4 56 ; refute -> 1674 steps, 52913 bytes => BYTE-IDENTICAL to ledger
$ radocert gen 3 2 4 103 ; refute -> 14.643 s, 1202198 steps, 74818033 bytes => BYTE-IDENTICAL to ledger
```
FINDING: the DRAT proofs are themselves a deterministic function of (a,b,k,n) at this
toolchain+commit. Archival of proof bytes is therefore strictly redundant with the recipe.
