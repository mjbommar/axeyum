#!/usr/bin/env python3
"""Pin existing Python grammar results for native Rust differential tests."""
import hashlib
import json
from pathlib import Path
from axeyum._cas_reference_parser import ParseError, parse
import axeyum._native as native

texts = [
    "0", "0001", "0.125", "12.5000", "-2^2", "(-2)^2", "2^-3", "2**+3",
    "x", "x_2", "pi", "π", "pi+x", "sin(x)+x^-2", "cbrt(8)", "floor(-1.2)",
    "8/2/2", "1+2*3", "(1+2)*3", "0^0", "(1/0)^0", "x^4294967295",
    "300000*(1/240)/(1-(1+1/240)^-360)",
    "1606938044258990275541962092341162602522202993782792835301376",
    "", "x+", "x^y", "2^2^3", "x^4294967296", "foo(x)", "1e3", "x[0]",
    "sin(x,y)", ".5", "1.", "π(x)", "x**--2",
]
rows = []
for text in texts:
    try:
        rows.append({"source": text, "expression": json.loads(parse(text).to_json())})
    except ParseError:
        rows.append({"source": text, "rejected": True})
path = Path(native.__file__).resolve()
out = Path(__file__).resolve().parents[1] / "crates/axeyum-cas/tests/data/python_text_parser.json"
out.write_text(json.dumps({"reference": "existing Python parser; native expression wire only",
                           "native_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
                           "cases": rows}, sort_keys=True, indent=2) + "\n")
print(f"PARSER_FIXTURES|cases={len(rows)}|accepted={sum('expression' in r for r in rows)}")
