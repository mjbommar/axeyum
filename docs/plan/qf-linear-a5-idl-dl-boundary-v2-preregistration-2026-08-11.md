# QF linear A5 IDL DL-boundary v2 preregistration — 2026-08-11

## Evidence boundary

The [loss-mechanism result](qf-linear-a5-idl-loss-mechanism-v1-result-2026-08-11.md)
rejects search-free fallback atom admission: BubbleSort remained a construction
timeout in 3/3 observations and the code was removed. The same result shows the
unchanged difference-logic route deciding GraphPartitioning SAT in 3/3 at a
32,000 ms query setting, after losing that case with the shipped 24,000 ms
setting and its 18-second probe slice.

Source history adds a bounded question but not a causal conclusion. The two
cases were decisions at the accepted 2026-08-06 checkpoint. Later changes made
Boolean and DL walks iterative, enforced construction deadlines, and added
pre-SAT safety boundaries. BubbleSort's current trace therefore does not prove
that fallback construction is the best repair target: the preceding DL probe
may also have a nearby decision boundary.

This note authorizes only an unchanged-binary BubbleSort timeout ladder. It
does not authorize production code, a timeout-policy change, a census, QF_RDL,
or credit.

## D2 — unchanged-route BubbleSort ladder

Use exact clean source
`d0e0d6ceac779b5cc3e2c1b5f3096c77780aecf9` and its retained 11,859,344-byte
release `explain_corpus` binary with SHA-256
`eec4813b557165ec95afc43912ad9fc2b5400ec94db5b7134ecacd50b100867d`.
Use only
`QF_IDL/Averest/buble_sort/BubbleSort_safe_blmc016.smt2`, one fresh worker per
observation, inherited 8 GiB `RLIMIT_AS`, zero stderr, exact JSON identity, and
a group-start one-minute load at most 12.

1. Run one observation with a 32,000 ms query setting.
2. If it returns replay-checked UNSAT through `dl-online`, repeat twice at the
   same setting and stop.
3. If it remains typed `unknown`, run one observation at 48,000 ms. If that is
   replay-checked UNSAT through `dl-online`, repeat twice there and stop.
4. Stop immediately on `unknown` at 48 seconds, any other verdict, stderr,
   malformed output, identity mismatch, process failure, or 8 GiB breach.

Retain source/binary identity, route trace, wall time, peak RSS, exit status,
stderr size, and output digest for every observation. Do not mix these files
with the failed V2 census or the prior G1 directory.

## Interpretation

- UNSAT in 3/3 at one rung establishes only that the current DL route has a
  nearby BubbleSort boundary. Together with G1 it permits a separate
  structural-budget diagnostic; it does not select or retain a policy.
- `unknown` at 48 seconds closes the shared nearby-DL hypothesis. The next
  BubbleSort work must profile bounded fallback construction without changing
  production behavior.
- Mixed outcomes require a stability discriminator and prohibit a production
  candidate.

## Later production gate

Any later DL-slice candidate must be based on stable scan structure rather than
benchmark identity, preserve the accepted equality-heavy 12/12 split, and run
the original allocation-abort controls plus every retained QF_IDL/QF_RDL
decision. It must keep SAT replay, checked DL conflicts, the 8 GiB limit, and a
nonzero fallback slice. A target gain cannot compensate for one lost control.
Only after that candidate is exact-pushed and passes an uninterrupted external-
frontier `just check` may V2 restart from QF_LRA row 1.
