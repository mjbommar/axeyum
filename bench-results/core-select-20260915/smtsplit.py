#!/usr/bin/env python3
"""CORE-SELECT -- split an SMT-LIB script into a prefix and a list of conjuncts.

The unit of SELECTION in this lane is a conjunct: a top-level `assert` body,
with every `(assert (and a b c))` split into separate asserts.  That split is an
EQUIVALENCE, not a weakening, and callers re-check it before anything else runs.
It is the right unit because [ADR-2050]'s haystacks (268, 633, 682 conjuncts)
live INSIDE one `and`, not spread over 268 `assert` forms -- a census that
counted `assert` FORMS would report those files as 1-conjunct haystacks and
conclude there is nothing to select.

Dropping conjuncts WEAKENS the formula, so `subset unsat => whole unsat`.  That
is the sound direction and the only one this lane uses; the converse is never
claimed.

Used as a module (`split_script`) and as a CLI that prints one TSV row:

    smtsplit.py <file.smt2>
    file<TAB>bytes<TAB>forms<TAB>asserts<TAB>conjuncts<TAB>mode<TAB>declared
"""

import sys

# Full flattening is finer-grained and therefore a smaller needle, but a file
# whose `and` tree holds tens of thousands of leaves would be handed to z3 as
# that many NAMED assertions, which is a different measurement (of z3's core
# machinery) than the one this lane wants.  Above this many leaves the split
# falls back to depth-1 and the row records `mode=shallow`, so a capped row is
# visible rather than silently different.
FLATTEN_CAP = 4000


def scan(text, i):
    """Index just past the s-expression starting at `text[i] == '('`."""
    n, depth, j = len(text), 0, i
    while j < n:
        ch = text[j]
        if ch == ';':
            k = text.find('\n', j)
            j = n if k < 0 else k + 1
            continue
        if ch == '"':
            j += 1
            while j < n:
                if text[j] == '"':
                    if j + 1 < n and text[j + 1] == '"':
                        j += 2
                        continue
                    j += 1
                    break
                j += 1
            continue
        if ch == '|':
            k = text.find('|', j + 1)
            j = n if k < 0 else k + 1
            continue
        if ch == '(':
            depth += 1
        elif ch == ')':
            depth -= 1
            if depth == 0:
                return j + 1
        j += 1
    return n


def forms(text):
    """Every top-level form, as source strings, comments dropped."""
    out, i, n = [], 0, len(text)
    while i < n:
        c = text[i]
        if c == ';':
            j = text.find('\n', i)
            i = n if j < 0 else j + 1
            continue
        if c.isspace():
            i += 1
            continue
        if c != '(':
            j = i
            while j < n and not text[j].isspace():
                j += 1
            i = j
            continue
        j = scan(text, i)
        out.append(text[i:j])
        i = j
    return out


def _atom_end(text, i):
    """Index just past the atom starting at `text[i]`.

    `|...|` quoting matters and is not decoration: `(assert |def_B definitions|)`
    appears verbatim in the CLEARSY families, and a splitter that treats the
    space inside the bars as a separator reads that assert as TWO arguments and
    reports the whole file `unparsed`.  Measured: exactly 2 of 1,400 files hit
    this, in `UF/20190906-CLEARSY` and `UFNIA/20190909-CLEARSY`.
    """
    n = len(text)
    if text[i] == '|':
        k = text.find('|', i + 1)
        return n if k < 0 else k + 1
    if text[i] == '"':
        j = i + 1
        while j < n:
            if text[j] == '"':
                if j + 1 < n and text[j + 1] == '"':
                    j += 2
                    continue
                return j + 1
            j += 1
        return n
    j = i
    while j < n and not text[j].isspace() and text[j] not in '()':
        j += 1
    return j


def args_of(form):
    """Split `(head a1 a2 ...)` into the head token and argument source strings."""
    inner = form[1:-1]
    i, n = 0, len(inner)
    while i < n and inner[i].isspace():
        i += 1
    j = _atom_end(inner, i) if i < n and inner[i] != '(' else i
    head = inner[i:j]
    out, i = [], j
    while i < n:
        if inner[i].isspace():
            i += 1
            continue
        if inner[i] == '(':
            k = scan(inner, i)
            out.append(inner[i:k])
            i = k
        elif inner[i] == ';':
            k = inner.find('\n', i)
            i = n if k < 0 else k + 1
        else:
            k = _atom_end(inner, i)
            out.append(inner[i:k])
            i = k
    return head, out


def flatten(body, cap=FLATTEN_CAP, byte_cap=None):
    """Split a top-level `and` tree into its leaves.  Iterative: a right-nested
    `and` chain of 10k leaves would blow a recursive splitter's stack, and the
    files this lane censuses are exactly the ones with 10k-leaf conjunctions.

    `byte_cap` bounds the live substring set, not the leaf COUNT.  Each `and`
    level copies its arguments, so a deeply nested tree costs O(bytes x depth)
    even when the leaf count is small: one 163 KB `UFLIA` file exhausted a
    16 GiB address-space cap this way.  A `None` return means "too big, use the
    shallow split", not "no conjuncts".
    """
    if byte_cap is None:
        byte_cap = max(4 << 20, 64 * len(body))
    out, stack, live = [], [body.strip()], len(body)
    while stack:
        b = stack.pop()
        live -= len(b)
        if not b.startswith('('):
            out.append(b)
            continue
        head, a = args_of(b)
        if head == 'and' and len(a) > 1:
            # reversed so the output preserves source order
            stack.extend(reversed(a))
            live += sum(len(x) for x in a)
        else:
            out.append(b)
        if len(out) + len(stack) > cap or live > byte_cap:
            return None
    return out


def split_script(text):
    """-> (prefix_forms, conjunct_bodies, n_assert_forms, mode).

    `mode` is `full` when the `and` tree was flattened to its leaves and
    `shallow` when FLATTEN_CAP forced depth-1 splitting instead.
    """
    fs = forms(text)
    prefix, bodies, n_assert, mode = [], [], 0, 'full'
    pending = []
    for f in fs:
        if not f.startswith('('):
            continue
        h = args_of(f)[0]
        if h == 'assert':
            n_assert += 1
            a = args_of(f)[1]
            pending.append(a[0] if len(a) == 1 else None)
        elif h in ('check-sat', 'exit', 'get-unsat-core', 'get-model',
                   'get-info', 'get-proof', 'echo'):
            continue
        else:
            prefix.append(f)
    for b in pending:
        if b is None:
            # an `assert` this parser could not read as a single body: keep the
            # whole form in the prefix rather than dropping or guessing it
            mode = 'unparsed-assert'
            continue
        leaves = flatten(b)
        if leaves is None:
            mode = 'shallow'
            head, a = args_of(b) if b.startswith('(') else ('', [])
            leaves = a if head == 'and' and len(a) > 1 else [b]
        bodies.extend(leaves)
    return prefix, bodies, n_assert, mode


def declared_status(text):
    i = text.find(':status')
    if i < 0:
        return 'ABSENT'
    tail = text[i + 7:i + 40].split()
    return tail[0].strip(')') if tail else 'ABSENT'


def main():
    path = sys.argv[1]
    raw = open(path, encoding='utf-8', errors='replace').read()
    prefix, bodies, n_assert, mode = split_script(raw)
    print('\t'.join(str(x) for x in (
        path, len(raw), len(prefix) + n_assert, n_assert, len(bodies), mode,
        declared_status(raw))))


if __name__ == '__main__':
    main()
