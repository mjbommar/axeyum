# Lane: frontier-split — split "unproved" from "cannot be stated" in `fact-frontier.py`

<!-- plan-section: lane-status -->

**Your lane's block (`WIP`, frontier-split, 2026-08-28).** Landed the kernel
declaration coverage check `docs/research/11-design-review/
2026-08-28-is-the-open-frontier-stale.md`'s addendum asked for:
`fact-frontier.py` used to print `proof route only -- needs a kernel proof`
for both an unproved-but-statable fact and a fact naming a function that
does not exist under any name in this kernel. Now the second state is
reported as `BLOCKED -- statement names undeclared kernel definition(s):
<names> (build these first; this is not a proof task)`, with the missing
name(s) printed.

**The check is derived from the kernel, never a hand list**, per the
brief's non-negotiable: it reads `kernel_declaration_projection`'s
unfiltered TSV emit (the prebuilt `--release` binary at
`target/release/examples/kernel_declaration_projection`, run DIRECTLY --
no `cargo run`, no cargo lock, so `just next` never triggers a build) plus
every SETTLED fact's own `formal.statement` in this ledger, as a
corroborating signal. A candidate identifier is reported missing only when
its namespace is one this kernel implements, it is not itself a declared
name, AND no proved fact's statement has ever used it either.

**The corroboration clause was not in the brief and turned out to be
load-bearing.** A naive name-check (namespace known + not declared) flags
`Nat.Prime`/`Nat.Coprime` on every `nat.prime`/`nat.coprime` fact, because
primality and coprimality are built INLINE in this kernel (no `Nat.Prime`
declaration exists) rather than as named declarations -- CLAUDE.md's
"hiding place 2". Without corroboration this check would have manufactured
23 new false positives (7 `nat.prime` + 8 `nat.coprime`... measured: 15
open facts across those two families) on top of the real 30, which is
exactly the "checker that cannot fail" defect this repository keeps
finding, just inverted (crying wolf instead of staying silent). Read from
the ledger itself: a name used in an already-PROVED fact's statement is
corroborated, so it is never flagged even though it carries no kernel
declaration.

Detail moved to [`../notes/202-frontier-split.md`](../notes/202-frontier-split.md).

