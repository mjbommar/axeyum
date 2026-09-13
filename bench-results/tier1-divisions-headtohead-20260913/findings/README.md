# Findings

Three things this board found that are not board rows. None is fixed here —
this is a measurement lane, and a board row and a behaviour change in one
branch cannot be told apart afterwards.

---

## 1. Four ABV verdicts that nothing confirms

**What.** We return `sat` on four ABV files. Nothing else does, and nothing
else contradicts us either:

| file | ours | `:status` | z3 @24 s | cvc5 @24 s | z3 @600 s | cvc5 @600 s |
|---|---|---|---|---|---|---|
| `ABV/20230321-UltimateAutomizerSvcomp2023/memleaks_test17_3.i_6.smt2` | sat | unknown | unknown | unknown | unknown (0.1 s) | unknown (0.1 s) |
| `ABV/20230321-UltimateAutomizerSvcomp2023/memleaks_test20-2.i_4.smt2` | sat | unknown | unknown | unknown | unknown (0.1 s) | unknown (0.1 s) |
| `ABV/20230321-UltimateAutomizerSvcomp2023/memleaks_test7-2.i_4.smt2` | sat | unknown | unknown | unknown | unknown (0.1 s) | unknown (0.1 s) |
| `ABV/20230321-UltimateAutomizerSvcomp2023/tree_cnstr.i_1.smt2` | sat | unknown | unknown | unknown | unknown (0.1 s) | unknown (0.1 s) |

Raw data: `../confirm-ABV.tsv`, produced by `../confirm-unchecked.sh` at a
**600 s** budget — 25× the board's — whose exit status depends on the finding.

**Why it is worth a section.** ABV declares `:status unknown` on **199 of its
200 sampled files**, so the board's usual ground truth is absent for the whole
division. Both references return `unknown` on all four — and they do it in
**0.1 s**, not by exhausting 600 seconds, so this is a capability decline on
their side rather than a budget difference. The consequence is that the number
of our ABV verdicts anything else can speak to is **zero**, and the board's
`DISAGREEMENTS: 0` for ABV is therefore vacuous. That is what ADR-1957 is
about, and why the board now prints the vacuity on the line itself.

**What this is and is not.** It is four files we decide that two reference
solvers decline — the good version of this result. It is *not* a confirmed
result: nothing has checked it. This lane did not model-check them.

**The follow-up, for a different lane.** A `sat` is checkable without any
oracle by evaluating the original term under the lifted model, which CLAUDE.md
already requires of every `sat` we produce. These four files are the natural
first target: they are the only verdicts on this board with no external check
at all, and a model-replay pass over them would convert "unconfirmed" into
"confirmed" or find a wrong answer. The repro is the `smtcomp_cli` invocation
the board used; the paths are above.

> Note on what is *not* claimed: `smtcomp_cli.rs` carries a comment saying
> "every `sat` is still replay-checked against the original terms". That
> comment is about the CNF/BV inprocessing path. This lane did not observe a
> replay on these files and does not inherit the claim for them.

---

## 2. `parity-lists/FP.txt` is a plain integer stride

**What.** The committed `bench-results/parity-lists/FP.txt` was built with
`[files[i * (n // 200)] for i in range(200)]`, not the full-span spacing the
board protocol requires. Verified by construction, not by eye — `../mklist.py`
asserts it matches the stride exactly and does not match full-span, and aborts
if that ever stops being true.

It stops at index **2,587 of 2,668**.

**Why it was not simply fixed.** Other lanes' committed artifacts reference
that file by name. Overwriting it would retroactively change what those boards
say they measured. This lane pinned `FP-fullspan.txt` beside it and left the
stride list alone.

**How much it matters, measured rather than asserted.** `mklist.py` prints the
family coverage of both constructions for every division:

| division | full-span families | plain-stride families | stride stops at |
|---|---|---|---|
| ALIA | 2 / 2 | **1 / 2** | 2,985 of 3,097 |
| AUFNIRA | 4 / 4 | **3 / 4** | 1,393 of 1,479 |
| AUFBV | 3 / 3 | **2 / 3** | 1,393 of 1,522 |
| AUFLIRA | 4 / 5 | 4 / 5 | 19,900 of 20,010 |
| UFNIA | 8 / 11 | 8 / 11 | 13,333 of 13,463 |
| ABV | 2 / 2 | 2 / 2 | 4,776 of 4,974 |
| FP | 3 / 4 | 4 / 4 | 2,587 of 2,668 |

**Three of seven divisions would have lost a whole family.** The protocol's
insistence on full-span is not ceremony on this corpus. FP is the one division
where the stride happens to reach one more family than full-span does; the
family full-span misses is 8 files of 2,669, which is what 200 draws from 2,669
is expected to miss.

---

## 3. A checker that reported green over a live fleet while detecting nothing

**What.** `../check-core-collisions.sh` printed `NO-CORE-COLLISIONS on: s5 s6
s7` on its first run, against the real boxes, while being incapable of
reporting a collision. Two independent defects:

1. `split(holders[c], a, " ")` with a **single-space** separator is awk's
   default splitting rule, which strips leading blanks — so the accumulated
   string `" 0,8 0"` yields 2 fields, not 3. The test was `n > 2`, which
   required **three** pin specs on one physical core. The actual failure mode,
   and the one this lane hit twice, is two.
2. Fixing that, the explanatory comment contained `awk's`. `AWKPROG` is
   single-quoted, so that apostrophe ended the string and the script stopped
   parsing entirely — and `controls/core-collision-control.sh` still passed,
   because it extracted the awk program and never ran the subject. It now runs
   `bash -n` on the subject first.

**Why it is a finding and not just a bug.** Neither defect was found by running
the checker on the fleet; both were found by fixtures with known answers. The
fleet run produced the same green in all three states: correct, off-by-one, and
syntactically broken.

The same shape appeared a second time in this lane, in `../frame-summary.py`: a
range pin spec (`0-7`) made it raise `ValueError` while formatting its summary,
**after** recording the frame violation but **before** printing it — so the
control saw a non-zero exit with no finding in it. Also found by a fixture,
also unreachable on any clean run.

**The blind spot that remains, stated rather than left to be rediscovered.**
Two jobs pinned to the *identical* spec are indistinguishable in `uniq -c`
output from one shard's three sequential solvers, so `check-core-collisions.sh`
cannot see that case. It is asserted as a known-blind fixture in the control.
That case is covered instead by `launch-shard.sh` and `census-launch.sh`
refusing to write into a non-empty output file.
