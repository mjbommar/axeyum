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
