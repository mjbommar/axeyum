#!/usr/bin/env python3
"""SKELETON-REACH -- size the SECOND cause hiding under the `fd:parse` label.

`apply_op` in `crates/axeyum-smtlib/src/parse.rs` is one large `match op {…}`
whose theory-operator arms are tried BEFORE the `_ =>` fall-through that
consults `arena.find_function(other)`.  So a benchmark that declares a function
whose NAME equals a theory operator has its applications captured by the
operator arm and never reaches its own declaration.

`UFNIA/vcc-havoc/verisoft-baby.c.10.privileged.smt2` declares

    (declare-fun fp (Int Int Int) Int)

and dies at ingest with `parse error: syntax error: fp exponent field must be a
bit-vector` in 44 ms of a 24 s budget.  `fp` is a FloatingPoint theory symbol;
the script's logic is `UFNIA`, which has no FloatingPoint theory, so the name is
a legal user symbol there and both z3 and cvc5 accept it.

THE OPERATOR SET IS DERIVED FROM THE AUTHORITY, NEVER TYPED OUT.  A test named
"every operator" that carries a literal list measures the maintainer's memory.
This parses the match arms out of `apply_op`'s own source, and prints the count
so a parse that silently matched nothing is visible rather than reported as a
clean zero.

    scan-shadowed-ops.py <corpus-root> <file-list> [out.tsv]
"""
import pathlib
import re
import sys


def operator_names(src_path):
    """The literal heads of `apply_op`'s match arms, read from the source.

    BOUNDED AT BOTH ENDS, and the second bound was bought with a wrong answer.
    Reading from `fn apply_op(` to end-of-file also swept `apply_parameterized`'s
    INDEXED arms -- `is`, `repeat`, `to_fp`, `divisible`, `rotate_left` -- which
    are only ever reached for an `((_ name …) x)` head and cannot capture a bare
    `(name x)` application.  That made the first scan report 59 shadowed files
    when 57 of them were shadowed by `is`, which shadows nothing.

    The closing bound is `arena.find_function(other)` -- the fall-through that
    consults the user's own declaration.  Every arm ABOVE that line is tried
    first and is therefore a genuine capture; nothing below it is.
    """
    src = pathlib.Path(src_path).read_text(encoding="utf-8", errors="replace")
    start = src.index("fn apply_op(")
    end = src.index("arena.find_function(other)", start)
    body = src[start:end]
    ops = set()
    for m in re.finditer(r'^\s+((?:"[^"]+"\s*\|\s*)*"[^"]+")\s*(?:if [^=\n]*)?=>', body, re.M):
        ops.update(re.findall(r'"([^"]+)"', m.group(1)))
    # Control: the extraction must contain an operator known to be in this
    # match and must NOT contain one known to be in `apply_parameterized`.
    assert "fp" in ops, "extraction lost `fp` -- the bounds are wrong"
    assert "is" not in ops, "extraction swept apply_parameterized -- bounds too wide"
    return ops


DECL = re.compile(r"\(\s*(?:declare-fun|declare-const|define-fun|define-fun-rec)\s+([^\s()|]+)")


def main():
    corpus = pathlib.Path(sys.argv[1])
    listing = pathlib.Path(sys.argv[2])
    out = sys.argv[3] if len(sys.argv) > 3 else None

    ops = operator_names("crates/axeyum-smtlib/src/parse.rs")
    if len(ops) < 50:
        print(f"ABORT: only {len(ops)} operator arms parsed -- the extraction broke", file=sys.stderr)
        sys.exit(2)
    print(f"operator arms parsed from apply_op: {len(ops)}", file=sys.stderr)

    rows = []
    for rel in listing.read_text().split():
        p = corpus / rel
        if not p.exists():
            rows.append((rel, "MISSING", ""))
            continue
        text = p.read_text(encoding="utf-8", errors="replace")
        hits = sorted({n for n in DECL.findall(text) if n in ops})
        rows.append((rel, "SHADOWED" if hits else "clean", ",".join(hits)))

    shadowed = [r for r in rows if r[1] == "SHADOWED"]
    print(f"scanned {len(rows)} files; {len(shadowed)} declare a name the operator table claims",
          file=sys.stderr)
    if out:
        with open(out, "w") as fh:
            fh.write("file\tstatus\tshadowed_names\n")
            for r in rows:
                fh.write("\t".join(r) + "\n")
    for r in shadowed:
        print(f"{r[2]}\t{r[0]}")


main()
