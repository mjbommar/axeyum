#!/usr/bin/env python3
"""Boolean-shape report for the `non-conjunctive` NRA rows of size-A.tsv.

Self-contained: tokenizer + s-expression reader + `let`/`define-fun` expansion,
no third-party dependencies.  Every input row produces an output row; nothing is
skipped silently.  The exit status depends on the controls at the bottom.
"""

import os
import resource
import statistics
import sys
import threading

# --------------------------------------------------------------------------
# Hard limits.  This repository has OOM-killed live sessions on unbounded
# expansion, so the address-space ceiling is set before any work happens.
# --------------------------------------------------------------------------
AS_LIMIT = 8 * 1024 * 1024 * 1024  # 8 GB
try:
    _soft, _hard = resource.getrlimit(resource.RLIMIT_AS)
    _new = AS_LIMIT if _hard == resource.RLIM_INFINITY else min(AS_LIMIT, _hard)
    resource.setrlimit(resource.RLIMIT_AS, (_new, _hard))
except (ValueError, OSError) as exc:  # pragma: no cover - defensive
    print(f"WARNING: could not set RLIMIT_AS: {exc}", file=sys.stderr)

NODE_BUDGET = 2_000_000       # expanded nodes per file before we call it capped
VISIT_BUDGET = 20_000_000     # syntactic nodes visited; memory/time backstop
TEXT_NODE_LIMIT = 20_000      # max expanded nodes we will materialise as text
ATOM_SET_LIMIT = 200_000      # max distinct atom strings tracked per record

_HERE = os.path.dirname(os.path.abspath(__file__))          # .../nra-clause-loop-*
REPO = os.path.dirname(os.path.dirname(_HERE))              # repo root
IN_TSV = os.path.join(_HERE, "size-A.tsv")
OUT_TSV = os.path.join(_HERE, "shape-34.tsv")
# The expected size of the ceiling population, overridable with
# `--expect-undecided N`.  A literal here would measure the author's memory, so
# it is an ARGUMENT with a default that the committed run passes; a rerun on a
# different sweep passes its own number.
EXPECT_UNDECIDED = 34

CORPUS = "/nas3/data/axeyum/corpus/smtlib-2024/non-incremental/non-incremental"

COMPARISONS = {"=", "<", "<=", ">", ">="}

COLUMNS = [
    "file", "verdict",
    "n_assert", "n_or", "widest_or", "n_and", "widest_and",
    "has_ite", "has_implies", "has_xor", "has_not", "has_distinct",
    "n_atoms", "over_48", "n_bool_vars",
    "expanded_nodes", "visited_nodes", "expansion", "lower_bound", "error",
]


class ParseError(Exception):
    pass


# --------------------------------------------------------------------------
# Tokenizer
# --------------------------------------------------------------------------
def tokenize(src):
    toks = []
    i = 0
    n = len(src)
    while i < n:
        c = src[i]
        if c in " \t\r\n\f":
            i += 1
            continue
        if c == ";":
            j = src.find("\n", i)
            i = n if j < 0 else j + 1
            continue
        if c == "(" or c == ")":
            toks.append(c)
            i += 1
            continue
        if c == "|":
            j = src.find("|", i + 1)
            if j < 0:
                raise ParseError("unterminated |quoted symbol|")
            toks.append(src[i:j + 1])
            i = j + 1
            continue
        if c == '"':
            j = i + 1
            while True:
                k = src.find('"', j)
                if k < 0:
                    raise ParseError("unterminated string literal")
                if k + 1 < n and src[k + 1] == '"':
                    j = k + 2
                    continue
                break
            toks.append(src[i:k + 1])
            i = k + 1
            continue
        j = i
        while j < n and src[j] not in ' \t\r\n\f()|;"':
            j += 1
        if j == i:
            raise ParseError(f"stuck on character {c!r} at offset {i}")
        toks.append(src[i:j])
        i = j
    return toks


def read_forms(toks):
    """Yield top-level forms as nested lists of token strings."""
    pos = 0
    n = len(toks)
    while pos < n:
        t = toks[pos]
        if t == ")":
            raise ParseError("unbalanced ')' at top level")
        if t != "(":
            raise ParseError(f"bare token {t!r} at top level")
        stack = [[]]
        pos += 1
        while True:
            if pos >= n:
                raise ParseError("unbalanced '(' at end of file")
            t = toks[pos]
            pos += 1
            if t == "(":
                new = []
                stack[-1].append(new)
                stack.append(new)
            elif t == ")":
                done = stack.pop()
                if not stack:
                    yield done
                    break
            else:
                stack[-1].append(t)


# --------------------------------------------------------------------------
# Compositional shape record.
#
# We never materialise the fully let-expanded tree (that is what blows memory
# up).  Instead each subterm gets a record that its parent combines.  All the
# requested metrics are composable: occurrence counts add, widest-arity maxes,
# the has_* flags or together, distinct-atom sets union.  A `let` binding is
# evaluated once and its record reused at every occurrence, so the OCCURRENCE
# counts reported here are exact even where naive substitution would explode.
# --------------------------------------------------------------------------
class Rec:
    __slots__ = ("nodes", "n_or", "widest_or", "n_and", "widest_and",
                 "has_ite", "has_implies", "has_xor", "has_not", "has_distinct",
                 "atoms", "atoms_trunc", "bool_syms", "text")

    def __init__(self):
        self.nodes = 1
        self.n_or = 0
        self.widest_or = 0
        self.n_and = 0
        self.widest_and = 0
        self.has_ite = False
        self.has_implies = False
        self.has_xor = False
        self.has_not = False
        self.has_distinct = False
        self.atoms = set()
        self.atoms_trunc = False
        self.bool_syms = set()
        self.text = None

    def absorb(self, other):
        self.nodes += other.nodes
        self.n_or += other.n_or
        self.n_and += other.n_and
        if other.widest_or > self.widest_or:
            self.widest_or = other.widest_or
        if other.widest_and > self.widest_and:
            self.widest_and = other.widest_and
        self.has_ite |= other.has_ite
        self.has_implies |= other.has_implies
        self.has_xor |= other.has_xor
        self.has_not |= other.has_not
        self.has_distinct |= other.has_distinct
        self.atoms_trunc |= other.atoms_trunc
        if len(self.atoms) < ATOM_SET_LIMIT:
            self.atoms |= other.atoms
            if len(self.atoms) > ATOM_SET_LIMIT:
                self.atoms_trunc = True
        elif other.atoms:
            self.atoms_trunc = True
        self.bool_syms |= other.bool_syms


class Capped(Exception):
    pass


class Analyzer:
    def __init__(self, bool_syms, defines):
        self.bool_syms = bool_syms      # declared Bool-sorted symbol names
        self.defines = defines          # name -> (params, body)
        self.visits = 0                 # syntactic nodes visited
        self.expanded = 0               # expanded nodes committed by finished asserts
        self.capped = False
        self.define_depth = 0

    def charge(self, k=1):
        """Charge one VISITED syntactic node (memory/time backstop)."""
        self.visits += k
        if self.visits > VISIT_BUDGET:
            self.capped = True
            raise Capped()

    def check_expanded(self, rec):
        """Charge the EXPANDED size of a finished subterm against NODE_BUDGET.

        `rec.nodes` is the node count of the fully let-expanded subtree, which is
        what the budget is specified over.  Checking it at every subterm means we
        stop the moment expansion passes 2,000,000 nodes rather than after.
        """
        if self.expanded + rec.nodes > NODE_BUDGET:
            self.capped = True
            raise Capped()

    def leaf(self, tok, env):
        if tok in env:
            return env[tok]
        r = Rec()
        self.charge()
        r.text = tok
        if tok in self.bool_syms:
            r.bool_syms.add(tok)
        return r

    def run(self, term, env):
        if isinstance(term, str):
            return self.leaf(term, env)
        if not term:
            raise ParseError("empty s-expression in term position")
        head = term[0]

        if isinstance(head, str):
            if head == "let":
                return self.do_let(term, env)
            if head in ("forall", "exists"):
                return self.do_quant(term, env)
            if head == "!":
                if len(term) < 2:
                    raise ParseError("malformed ! annotation")
                return self.run(term[1], env)
            if head == "_":
                return self.leaf(" ".join(x for x in term if isinstance(x, str)), {})
            if head == "as":
                if len(term) < 2:
                    raise ParseError("malformed as")
                return self.run(term[1], env)
            if head in self.defines and head not in env:
                return self.do_define_call(term, env)

        if isinstance(head, str):
            hrec = None
            hname = head
        else:
            hrec = self.run(head, env)      # ((_ f i) args ...) style head
            hname = None

        kids = [self.run(a, env) for a in term[1:]]
        r = Rec()
        self.charge()
        if hrec is not None:
            r.absorb(hrec)
        elif hname in env:
            r.absorb(env[hname])
        elif hname in self.bool_syms:
            r.bool_syms.add(hname)
        for k in kids:
            r.absorb(k)

        arity = len(kids)
        if hname == "or":
            r.n_or += 1
            if arity > r.widest_or:
                r.widest_or = arity
        elif hname == "and":
            r.n_and += 1
            if arity > r.widest_and:
                r.widest_and = arity
        elif hname == "ite":
            r.has_ite = True
        elif hname in ("=>", "implies"):
            r.has_implies = True
        elif hname == "xor":
            r.has_xor = True
        elif hname == "not":
            r.has_not = True
        elif hname == "distinct":
            r.has_distinct = True

        if (r.nodes <= TEXT_NODE_LIMIT and hname is not None
                and all(k.text is not None for k in kids)):
            r.text = "(" + hname + " " + " ".join(k.text for k in kids) + ")"
        else:
            r.text = None

        if hname in COMPARISONS:
            if r.text is not None:
                if len(r.atoms) < ATOM_SET_LIMIT:
                    r.atoms.add(r.text)
                else:
                    r.atoms_trunc = True
            else:
                # could not canonicalise this atom -> distinct count is a floor
                r.atoms_trunc = True
        self.check_expanded(r)
        return r

    def do_let(self, term, env):
        if len(term) != 3 or not isinstance(term[1], list):
            raise ParseError("malformed let")
        new_env = dict(env)
        for b in term[1]:
            if not isinstance(b, list) or len(b) != 2 or not isinstance(b[0], str):
                raise ParseError("malformed let binding")
            new_env[b[0]] = self.run(b[1], env)   # parallel binding semantics
        return self.run(term[2], new_env)

    def do_quant(self, term, env):
        if len(term) != 3 or not isinstance(term[1], list):
            raise ParseError("malformed quantifier")
        new_env = dict(env)
        for b in term[1]:
            if not isinstance(b, list) or len(b) < 1 or not isinstance(b[0], str):
                raise ParseError("malformed quantifier binder")
            v = Rec()
            v.text = b[0]
            new_env[b[0]] = v
        return self.run(term[2], new_env)

    def do_define_call(self, term, env):
        params, body = self.defines[term[0]]
        args = [self.run(a, env) for a in term[1:]]
        if len(args) != len(params):
            raise ParseError(f"arity mismatch calling {term[0]!r}")
        if self.define_depth > 64:
            raise ParseError("define-fun nesting deeper than 64")
        new_env = dict(zip(params, args))
        self.define_depth += 1
        try:
            return self.run(body, new_env)
        finally:
            self.define_depth -= 1


# --------------------------------------------------------------------------
def sort_is_bool(sort):
    return isinstance(sort, str) and sort == "Bool"


def analyze_file(path):
    row = {c: "" for c in COLUMNS}
    row["expansion"] = "exact"
    row["lower_bound"] = "False"
    row["error"] = ""

    with open(path, "r", encoding="utf-8", errors="replace") as fh:
        src = fh.read()

    bool_syms = set()
    defines = {}
    asserts = []
    for form in read_forms(tokenize(src)):
        if not form or not isinstance(form[0], str):
            continue
        cmd = form[0]
        if cmd == "assert":
            if len(form) != 2:
                raise ParseError("malformed assert")
            asserts.append(form[1])
        elif cmd == "declare-fun":
            if len(form) != 4:
                raise ParseError("malformed declare-fun")
            if sort_is_bool(form[3]):
                bool_syms.add(form[1])
        elif cmd == "declare-const":
            if len(form) != 3:
                raise ParseError("malformed declare-const")
            if sort_is_bool(form[2]):
                bool_syms.add(form[1])
        elif cmd == "define-fun":
            if len(form) != 5 or not isinstance(form[2], list):
                raise ParseError("malformed define-fun")
            params = []
            for p in form[2]:
                if not isinstance(p, list) or len(p) != 2 or not isinstance(p[0], str):
                    raise ParseError("malformed define-fun parameter")
                params.append(p[0])
            defines[form[1]] = (params, form[4])
        elif cmd in ("define-fun-rec", "define-funs-rec", "par"):
            raise ParseError(f"unsupported command {cmd!r}")

    an = Analyzer(bool_syms, defines)
    total = Rec()
    total.nodes = 0
    try:
        for a in asserts:
            rec = an.run(a, {})
            an.expanded += rec.nodes
            total.absorb(rec)
    except Capped:
        row["expansion"] = "capped"
        row["lower_bound"] = "True"

    if total.atoms_trunc:
        row["lower_bound"] = "True"

    row["expanded_nodes"] = str(total.nodes)
    row["visited_nodes"] = str(an.visits)

    row["n_assert"] = str(len(asserts))
    row["n_or"] = str(total.n_or)
    row["widest_or"] = str(total.widest_or)
    row["n_and"] = str(total.n_and)
    row["widest_and"] = str(total.widest_and)
    row["has_ite"] = str(total.has_ite)
    row["has_implies"] = str(total.has_implies)
    row["has_xor"] = str(total.has_xor)
    row["has_not"] = str(total.has_not)
    row["has_distinct"] = str(total.has_distinct)
    row["n_atoms"] = str(len(total.atoms))
    row["over_48"] = str(len(total.atoms) > 48)
    row["n_bool_vars"] = str(len(total.bool_syms))
    return row


# --------------------------------------------------------------------------
def numeric_summary(rows, col):
    vals = []
    for r in rows:
        try:
            vals.append(int(r[col]))
        except (ValueError, KeyError):
            pass
    if not vals:
        return "n=0"
    return (f"n={len(vals):<4} min={min(vals):<8} "
            f"median={statistics.median(vals):<10g} max={max(vals)}")


def bool_count(rows, col):
    return sum(1 for r in rows if r.get(col) == "True")


def report(label, rows):
    print(f"\n=== {label} (rows={len(rows)}) ===")
    ok = [r for r in rows if not r["error"]]
    bad = [r for r in rows if r["error"]]
    print(f"parsed ok: {len(ok)}   errored: {len(bad)}   "
          f"capped: {sum(1 for r in ok if r['expansion'] == 'capped')}   "
          f"lower-bound-marked: {sum(1 for r in ok if r['lower_bound'] == 'True')}")
    for col in ("n_assert", "n_or", "widest_or", "n_and", "widest_and",
                "n_atoms", "n_bool_vars", "expanded_nodes", "visited_nodes"):
        print(f"  {col:<13} {numeric_summary(ok, col)}")
    for col in ("has_ite", "has_implies", "has_xor", "has_not", "has_distinct",
                "over_48"):
        print(f"  {col:<13} True in {bool_count(ok, col)} / {len(ok)}")

    hist = {}
    for r in ok:
        try:
            hist[int(r["widest_or"])] = hist.get(int(r["widest_or"]), 0) + 1
        except ValueError:
            pass
    print("  widest_or histogram:")
    for k in sorted(hist):
        print(f"    {k:>6} : {hist[k]:>4}  {'#' * min(hist[k], 60)}")

    nb = sum(1 for r in ok if r["n_bool_vars"] not in ("", "0"))
    over = sum(1 for r in ok if r["over_48"] == "True")
    neither = sum(1 for r in ok
                  if r["n_bool_vars"] in ("", "0") and r["over_48"] == "False")
    print(f"  HEADLINE n_bool_vars>0 (clause loop CANNOT take) : {nb}")
    print(f"  HEADLINE n_atoms>48    (over the atom cap)       : {over}")
    print(f"  HEADLINE neither       (admissible subset)       : {neither}")


# --------------------------------------------------------------------------
def main():
    failures = []

    if not os.path.exists(IN_TSV):
        print(f"CONTROLS FAILED: input TSV missing: {IN_TSV}")
        return 1

    with open(IN_TSV, "r", encoding="utf-8") as fh:
        lines = fh.read().splitlines()
    header = lines[0].split("\t")
    try:
        i_file = header.index("file")
        i_verdict = header.index("verdict")
        i_cause = header.index("nra_real_root_cause")
    except ValueError as exc:
        print(f"CONTROLS FAILED: input header lacks a required column: {exc}")
        return 1

    global EXPECT_UNDECIDED
    for i, a in enumerate(sys.argv):
        if a == "--expect-undecided" and i + 1 < len(sys.argv):
            EXPECT_UNDECIDED = int(sys.argv[i + 1])

    selected = []
    for ln in lines[1:]:
        if not ln.strip():
            continue
        f = ln.split("\t")
        while len(f) < len(header):
            f.append("")
        if f[i_cause] == "non-conjunctive":
            selected.append((f[i_file], f[i_verdict]))

    print(f"selected rows with nra_real_root_cause == 'non-conjunctive': {len(selected)}")

    rows = []
    unreadable = []
    for path_rel, verdict in selected:
        full = os.path.join(CORPUS, path_rel)
        row = {c: "" for c in COLUMNS}
        row["file"] = path_rel
        row["verdict"] = verdict
        if not os.path.isfile(full):
            row["error"] = "missing-file"
            unreadable.append(path_rel)
            rows.append(row)
            continue
        try:
            got = analyze_file(full)
            got["file"] = path_rel
            got["verdict"] = verdict
            rows.append(got)
        except (ParseError, RecursionError, MemoryError, OverflowError) as exc:
            row["error"] = f"{type(exc).__name__}: {exc}".replace("\t", " ")[:200]
            rows.append(row)
        except OSError as exc:
            row["error"] = f"OSError: {exc}".replace("\t", " ")[:200]
            unreadable.append(path_rel)
            rows.append(row)

    os.makedirs(os.path.dirname(OUT_TSV), exist_ok=True)
    with open(OUT_TSV, "w", encoding="utf-8") as fh:
        fh.write("\t".join(COLUMNS) + "\n")
        for r in rows:
            fh.write("\t".join(str(r.get(c, "")) for c in COLUMNS) + "\n")
    print(f"wrote {OUT_TSV} ({len(rows)} data rows)")

    missing_cells = []
    for r in rows:
        if r["error"]:
            continue  # an errored row legitimately has blank measurement cells
        for c in COLUMNS:
            if c == "error":
                continue
            if r.get(c, "") == "":
                missing_cells.append(f"{r['file']}:{c}")
    if unreadable:
        failures.append(f"{len(unreadable)} file(s) could not be read: "
                        + ", ".join(unreadable[:5]))
    if missing_cells:
        failures.append(f"{len(missing_cells)} output cell(s) missing: "
                        + ", ".join(missing_cells[:5]))

    errored = [r for r in rows if r["error"]]

    report("ALL non-conjunctive rows", rows)

    unknown = [r for r in rows if r["verdict"] == "unknown"]
    # THE POPULATION THE SIZING QUESTION IS ABOUT, and it is not the cause filter
    # alone.  `non-conjunctive` is recorded by the single-cell route on every
    # file it refuses for that shape -- INCLUDING the 84 that a LATER rung of the
    # ladder then decides.  The clause loop cannot gain those; they are already
    # answered.  So the ceiling is the intersection with "we do not decide it",
    # and it is that count the control is on.
    print(f"\nNOTE: the cause filter alone yields {len(selected)} rows, of which "
          f"{len(selected) - len(unknown)} are DECIDED by a later rung and can "
          f"gain nothing.\n      The {len(unknown)} undecided ones are the "
          f"population the ceiling is computed over.")
    report("non-conjunctive AND verdict == unknown  [THE CEILING POPULATION]",
           unknown)
    if EXPECT_UNDECIDED is not None and len(unknown) != EXPECT_UNDECIDED:
        failures.append(
            f"undecided non-conjunctive count is {len(unknown)}, not the "
            f"expected {EXPECT_UNDECIDED}")

    print("\n--- errored files ---")
    if errored:
        for r in errored:
            print(f"  {r['file']}\t{r['error']}")
    else:
        print("  (none)")

    print()
    if failures:
        print("CONTROLS FAILED")
        for f in failures:
            print(f"  - {f}")
        return 1
    print("CONTROLS PASSED")
    return 0


if __name__ == "__main__":
    sys.setrecursionlimit(200000)
    threading.stack_size(512 * 1024 * 1024)
    rc = {}
    t = threading.Thread(target=lambda: rc.setdefault("rc", main()))
    t.start()
    t.join()
    sys.exit(rc.get("rc", 2))
