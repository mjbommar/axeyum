# Pinned external checker guards

`carcara-6624ea80-unary-minus-source-binding.patch` applies to upstream Carcara
commit `6624ea80cf1985ada473c0705869c78353e4282d`. It excludes unary subtraction
from the comparator's singleton left-associative identity shortcut. Unary
subtraction is negation; matching it to its positive operand can accept a proof
against a different, satisfiable source problem.

This is a local reference-checker patch, not a change to Axeyum's default build
or an upstream release. The original shared reference checkout stays intact.
Source review of upstream `96c00843eb157cb475796483b2ed30a51fb82852` found the
same shortcut. No upstream communication has been sent.

Create an isolated checkout at the pinned base, verify its commit, and apply
this patch with `git apply` from its root. From the Axeyum checkout, build using
`scripts/cargo-serialized.sh build --release --manifest-path
<isolated-checkout>/Cargo.toml --bin carcara`, with an isolated CARGO_TARGET_DIR.
Then run:

```sh
python3 scripts/check-carcara-source-binding.py --checker <target>/release/carcara
```

The gate requires a genuine negative-coefficient refutation to pass and the
same refutation against a positive-coefficient SAT source to fail specifically
at premise binding. A timeout, parse error or absent binary does not count as a
negative control. It prints the binary SHA-256 on success. The unpatched pinned
binary fails this gate. This narrow guard test does not establish general
external-checker soundness.
