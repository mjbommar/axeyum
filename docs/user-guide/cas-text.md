# Exact CAS text input

Rust callers can use `axeyum_cas::text_parser::parse("x^-2 + 0.125")`.
The result is a `CasExpr`; parsing constructs syntax and does not establish
nonzero assumptions or certify a simplification. `ParseError` reports a reason
and a half-open UTF-8 byte span. Python's `cas.parse` uses the same native grammar and reports character
spans, translating native byte diagnostics. Unpaired surrogates reject.

The grammar accepts exact integers and decimals, ASCII identifiers, π/`pi`,
parentheses, `+ - * /`, and signed integer powers with `^` or `**`.
`-x^2` means `-(x^2)`, division associates left, and chained powers require
parentheses. Exponents have magnitude at most4294967295. Functions are `sin`,
`cos`, `tan`, `atan`, `ln`, `exp`, `sqrt`, `cbrt`, `abs`, `sign`, `floor`, and
`ceiling`. A constructor-built variable named `pi` remains distinct from π.

Native intake limits are8192 source bytes,512 tokens,1024 numeral digits,
64 syntax nodes and depth32, with16384-bit coefficients. The final lowered
expression is also bounded; subtraction and negative powers add nodes. Exhaustion
returns a parse error. These native byte/final-AST bounds also apply in Python;
non-ASCII text and subtraction can reach them earlier than the former Python
character/builder limits. Division and reciprocal powers retain their domain
requirements; `1/0` can be parsed but is not thereby defined.

Build the Rust JSON-export example with:

```sh
scripts/cargo-serialized.sh build -p axeyum-cas --example parse_text
```

The binary reads one expression per line from standard input and emits canonical
expression JSON. Malformed input prints a diagnostic and exits nonzero. With a
fresh Python extension, `python/examples/cas_native_text.py --parser-binary
/path/to/parse_text` imports the native expression bytes, compares exact payment
arithmetic against Python Fraction, and produces/replays a wide certified trace.

## Nested conditional rewrite evidence

A symbolic quotient needs an explicit nonzero assumption before cancellation.
The nested API carries checked local quotient witnesses together with each
rewrite's path, full before/after expressions and ordered context:

```python
from axeyum import cas

x = cas.Expr.var("x")
q = (x * x) / x
source = q + (-q)
produced = cas.cancel_nested_trace(source, nonzero=[x])
assert produced.status == "produced"
assert produced.step_count == 2
assert produced.json is not None and produced.result is not None

# Save produced.json; reconstruct the original and endpoint in another process.
checked = cas.replay_conditional_trace(
    produced.json, source, produced.result, nonzero=[x],
)
assert checked.status == "checked"
assert cas.replay_conditional_trace(
    produced.json, source, produced.result, nonzero=[],
).status == "rejected"
```

The context means that `x` is nonzero; the certificate does not prove that fact.
Under that context, each cancellation preserves rational value and definedness.
If an outer quotient remains, its denominator must still be defined and nonzero;
the trace does not claim the surrounding expression is total. Local numerator
and denominator operands must fit the supported polynomial witness fragment.
Unsupported cancellations decline instead of returning a partial certificate.

Replay checks the caller's source, endpoint and ordered assumptions, local
witnesses, rewrite locations, unchanged surrounding expressions and step
continuity. It does not invoke cancellation production. The checker shares
bounded exact arithmetic with the producer; validity is separate from kernel
admission. Use `normalize_trace` for unconditional polynomial traces and
`cancel_trace` for an isolated root quotient witness.

`produced` and `checked` outcomes carry complete JSON and a typed endpoint.
`rejected`, `unsupported` and `resource_limited` carry neither. The defaults
permit 128 steps, 256 nodes per expression, depth 32, polynomial degree 32,
1,000,000 aggregate declared witness-work units and 1 MiB of complete evidence.
`max_steps` and `max_work` can lower the local policy; an untrusted envelope
cannot raise it. Promoted rational coefficients retain their 16,384-bit cap.
These witness-work units bound the carried identity budgets; they are not a
wall-clock deadline or a measurement of every surrounding validation operation.
