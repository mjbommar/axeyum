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

## DRAT-trim empty-clause guard

`drat-trim-empty-clause-rup.patch` applies to upstream commit
`2e3b2dc0ecf938addbd779d42877b6ed69d9a985`. Its unmodified `lrat-check.c`
accepts `3 0 1 2 0` against satisfiable CNF `p cnf 1 2; 1 0; 1 0`, and
also accepts an empty clause without hints. The no-conflict path falls through
to the vacuous RAT branch with a zero pivot. An empty clause has no RAT pivot:
the patch requires its hints to establish an actual RUP conflict. It changes
only the isolated external reference checker, never the default Rust build.

Build in a private checkout (substitute an absolute Axeyum checkout path):

```sh
git clone https://github.com/marijnheule/drat-trim.git <private-checkout>
git -C <private-checkout> checkout 2e3b2dc0ecf938addbd779d42877b6ed69d9a985
git -C <private-checkout> apply <axeyum>/scripts/patches/drat-trim-empty-clause-rup.patch
cc -O2 -o <private-checkout>/lrat-check-guarded <private-checkout>/lrat-check.c
python python/examples/sat_certificate_export.py --output <new-output-dir> \
  --lrat-check <private-checkout>/lrat-check-guarded
AXEYUM_LRAT_CHECK=<private-checkout>/lrat-check-guarded \
  python -m pytest -q python/tests/test_sat_certificate_export.py
```

The example requires exact external success and rejection verdicts, with process
timeouts. It exports Boolean and BV certificates, exercises satisfiable-CNF and
missing-hint controls, and records the checker binary hash. Source-to-CNF
translation is explicitly **not independently checked**. This guard does not
establish global checker soundness or EVD-5 completion. No upstream message
has been sent. The unmodified checker fails the single external regression.
