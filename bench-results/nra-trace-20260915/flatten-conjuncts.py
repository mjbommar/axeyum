#!/usr/bin/env python3
"""Flatten one QF_NRA benchmark's assertion into one `assert` per conjunct.

ADR-2110, lane NRA-TRACE. Used to bisect WHICH conjunct takes a query out of
the exact decider's reach: emit the flattened file, then emit prefixes of it
and see where the verdict changes.

`let` bindings are expanded (the exact decider sees the arena's expanded form
anyway, so a `let` in the file is not the thing under test), the top-level
`and` spine is flattened, and each conjunct becomes its own `assert`. Nothing
is dropped or weakened: the emitted file is the SAME conjunction, so a verdict
on it is a verdict on the original.

    flatten-conjuncts.py IN.smt2 OUT.smt2 [--first N]

`--first N` keeps only the first N conjuncts, which is a WEAKER query -- a
`sat` on it says nothing about the original and an `unsat` on it transfers.
The bisection uses that direction on purpose.
"""

from __future__ import annotations

import sys
import threading
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))


def _load_reader():
    import importlib.util

    path = Path(__file__).resolve().parent / "shape-features.py"
    spec = importlib.util.spec_from_file_location("shape_features", path)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def expand(term, env: dict):
    if isinstance(term, str):
        return env.get(term, term)
    if not term:
        return term
    head = term[0]
    if head == "let" and len(term) >= 3:
        inner = dict(env)
        for binding in term[1]:
            inner[binding[0]] = expand(binding[1], env)
        return expand(term[2], inner)
    return [expand(a, env) for a in term]


def conjuncts(term, out: list) -> None:
    if isinstance(term, list) and term and term[0] == "and":
        for a in term[1:]:
            conjuncts(a, out)
        return
    out.append(term)


def render(term) -> str:
    if isinstance(term, str):
        return term
    return "(" + " ".join(render(a) for a in term) + ")"


def main(argv: list[str]) -> int:
    if len(argv) < 3:
        print(__doc__, file=sys.stderr)
        return 2
    sf = _load_reader()
    src = Path(argv[1]).read_text(encoding="utf-8", errors="replace")
    forms = sf.parse(sf.tokenize(src))

    first = None
    if "--first" in argv:
        first = int(argv[argv.index("--first") + 1])

    head_lines: list[str] = []
    body: list = []
    for form in forms:
        if not isinstance(form, list) or not form:
            continue
        if form[0] in ("set-logic", "declare-fun", "declare-const", "set-info"):
            head_lines.append(render(form))
        elif form[0] == "assert" and len(form) >= 2:
            conjuncts(expand(form[1], {}), body)

    kept = body if first is None else body[:first]
    lines = [line for line in head_lines if not line.startswith("(set-info :status")]
    lines += [f"(assert {render(c)})" for c in kept]
    lines += ["(check-sat)", "(exit)"]
    Path(argv[2]).write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"{len(body)} conjuncts, wrote {len(kept)}")
    return 0


def _run(argv: list[str]) -> int:
    sys.setrecursionlimit(200_000)
    threading.stack_size(512 * 1024 * 1024)
    box: list[int] = []
    worker = threading.Thread(target=lambda: box.append(main(argv)))
    worker.start()
    worker.join()
    return box[0] if box else 3


if __name__ == "__main__":
    sys.exit(_run(sys.argv))
