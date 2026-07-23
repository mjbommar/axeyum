# TL0.7.4 R2 plan — close installer-identity merge drift

Status: **preregistered offline repair; no external process authorized**

Date: 2026-07-23

Parent:
[accepted TL0.7.4 result](lean-execution-acceptance-tl0.7.4-2026-07-22.md).

## 1. Trigger and provenance

TL0.7.4 was developed from a parent where
`scripts/install-pinned-lean.sh` had SHA-256
`75acb49a48e18b43523257ac22bc82889d614a6678c1cc3a457b3a150e1c7f71`.
The independent official-Lean gate repair `b2cb259a` changed that file to
SHA-256
`8a48e25ee2d2fb6d364dcbe0505b8a2fd660237e18e536d52117dc947d4c71ee`
by resolving `elan which lean` under the pinned toolchain, checking that the
resolved path is executable, invoking that exact binary for `--version`, and
reporting its path. Merge `75022ee2` combined both branches without a textual
conflict but retained TL0.7.4's older frozen hash. The resulting semantic merge
drift makes the accepted authority fail its repository-input gate.

This is not a changed retained control, a new Lean observation, or evidence
corruption. The two completed TL0.7.4 controls already bind the exact Lean
binary hash/version and the official exporter build independently of the
installer helper. All retained evidence bytes and logical seals remain
unchanged.

## 2. Authorized repair

After this plan is committed and pushed:

1. update only TL0.7.4's frozen installer identity to the current `8a48...`
   value;
2. add a focused regression proving the current installer is frozen and that
   mutating its bytes is rejected;
3. rebuild the result authority and generated summaries from the unchanged
   retained evidence, preserving implementation revision `679f4b9d`, all
   control/build/evidence identities, and every zero-credit field;
4. document that the new authority seal is a post-merge validator/input repair,
   not an evidence-producing revision or process rerun;
5. refresh the complete-parity registry's affected source/evidence identities;
   and
6. run the focused TL0.7.4, complete-parity, parity-prose, and link gates.

Do not run `run-pair`, rebuild the exporter, reinstall Lean, alter either
evidence root, change a control or process record, change an observed count, or
grant U2/outcome/pair/performance/parity credit.

## 3. Invariants and acceptance

The repair is acceptable only if:

- the registered evidence directories are byte-identical before and after;
- the accepted build record, failed-attempt manifest, two completion seals,
  two stable-projection seals, process counts, and retained byte/file totals do
  not change;
- repository-input validation and deterministic authority reproduction pass;
- mutation tests still reject repository-input, evidence, schema, control,
  credit, and generated-output drift;
- complete Lean parity remains 0/10 populations, 0/12 axes, zero pairs, zero
  satisfied gates, and `terminal_ready=false`; and
- the complete `just parity-docs` recipe advances past TL0.7.4, with any later
  unrelated failure reported separately rather than hidden.

This correction closes one gate-integrity defect. It establishes no new Lean
compatibility, execution, dependency, native-support, or parity fact.
