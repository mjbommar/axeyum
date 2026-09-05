#!/usr/bin/env python3
"""Measure and ratchet a per-function trust registry for `axeyum-cas` (roadmap
item 10, first half; `docs/math-department/13-computer-algebra.md`).

Why this exists
----------------
The capability table in `docs/research/10-cas/README.md` carries a
"Certified" column that is prose -- nothing counts which of the crate's
public functions actually return a certificate, a checker, or neither. File
13 chair 12 names this directly: "a proof-carrying CAS with no real
quantifier elimination... no gate counts which of the 691 public functions
carry a certificate." This gate is that count, and a ratchet on it, so the
claim in the README can be checked against the source rather than trusted.

What "certified" means here is deliberately narrow: a function's RETURN
TYPE names a type from the certificate vocabulary (directly, or wrapped in
`Option`/`Result`/`Vec`/a tuple). It does not mean the function is correct,
only that its signature promises a checkable artifact. A `checker` function
(name starts with `verify`/`check`/`replay`/`certify`) is the other half of
that promise -- something that consumes a certificate and returns a
pass/fail. Everything else is `uncertified`: an honest label, not a
violation (mirrors `check-cas-internal-residue.py`'s treatment of
`cas-internal` -- a growing uncertified count is not itself a defect, only a
regression of a function that WAS certified is).

The certificate vocabulary is derived from the source, not typed by hand:
every `pub struct`/`pub enum` under `crates/axeyum-cas/src` whose name ends
in `Certificate`, `Evidence`, `Report`, or `Witness`, or is exactly
`ZeroTest` or `CertifiedIntegral`, or has an inherent method named exactly
`verify` or `check`. A hand-typed list goes stale the day a new certificate
type ships under a different name; this recomputes it every run.

The scanner
-----------
`crates/axeyum-cas/src` is ~110k lines across 70 files including `lib.rs` at
~29.5k lines. Regex over whole files is not safe here: string and comment
bodies are full of braces (format strings, doc comments describing Rust
code), and `#[cfg(test)]` module bodies contain their own `pub fn`s that
must not be counted (ADR-0601's own residue gate hit an analogous class of
mistake, reading a package name out of unstructured text instead of
deriving it). So this file masks comments and string/char literals to
blanks (preserving length and newlines, so nothing outside a literal moves),
then walks braces with a small stack, classifying each `{`'s preceding
"header" text (the text since the last `;`/`{`/`}` at that depth) as a
module, an impl block, a function signature, or something else. Only two
classifications keep their descendants visible to the scanner: a `mod` that
is not `#[cfg(test)]`/named `tests`, and an inherent `impl` of a `pub`
struct/enum. Everything else (a function body, a struct/enum body, a trait
body, a trait impl -- which cannot legally contain `pub fn` at all) is
opaque past that point, which is what keeps a `pub fn` written inside a
`#[cfg(test)] mod tests { ... }` from ever being enumerated.

Exit status: 0 when the ratchet floor holds, 1 on any violation, 2 on a
usage error.
"""

from __future__ import annotations

import argparse
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
DEFAULT_SRC_ROOT = REPO_ROOT / "crates" / "axeyum-cas" / "src"
DEFAULT_RATCHET = REPO_ROOT / "scripts" / "check-cas-trust-registry.ratchet"

VOCAB_SUFFIXES = ("Certificate", "Evidence", "Report", "Witness")
VOCAB_EXACT_NAMES = ("ZeroTest", "CertifiedIntegral")
CHECKER_PREFIXES = ("verify", "check", "replay", "certify")

RATCHET_HEADER = """\
# Per-function trust registry for `crates/axeyum-cas` (math-department file
# 13, Next Ten item 10, first half). One row per record:
#
#   FN\t<function path>\t<return type>
#   VOCAB\t<type name>\t<struct|enum>
#
# `FN` rows are every function this gate classified `certified` as of the
# last --write. `VOCAB` rows are every certificate-vocabulary type the
# source defined at that time. Regenerate with:
#   python3 scripts/check-cas-trust-registry.py --write
#
# The floor: every recorded FN row must still classify `certified` today
# (not `checker`, not `uncertified`, not gone), the total certified count
# must not fall below the number of FN rows recorded, and every recorded
# VOCAB row's type must still exist. A NEW certified function not recorded
# here is refused too (run --write to accept it deliberately, so the floor
# only rises on purpose) -- but a new UNCERTIFIED function is never refused;
# that label is honest, not a violation. See
# docs/math-department/13-computer-algebra.md item 10.
"""


# --------------------------------------------------------------------------
# Source masking: blank out comment and string/char literal bodies so brace
# counting and keyword matching never trip over `"{"`, `// mod tests {`, etc.
# Length and newline positions are preserved so line numbers stay correct.
# --------------------------------------------------------------------------


def mask_source(text: str) -> str:
    out = list(text)
    n = len(text)
    i = 0

    def blank(a: int, b: int) -> None:
        for k in range(a, b):
            if out[k] != "\n":
                out[k] = " "

    while i < n:
        c = text[i]

        # line comment
        if c == "/" and i + 1 < n and text[i + 1] == "/":
            j = i
            while j < n and text[j] != "\n":
                j += 1
            blank(i, j)
            i = j
            continue

        # block comment, nested
        if c == "/" and i + 1 < n and text[i + 1] == "*":
            depth = 1
            j = i + 2
            while j < n and depth > 0:
                if text[j : j + 2] == "/*":
                    depth += 1
                    j += 2
                elif text[j : j + 2] == "*/":
                    depth -= 1
                    j += 2
                else:
                    j += 1
            blank(i, min(j, n))
            i = j
            continue

        # raw string, optionally byte-prefixed: r"...", r#"..."#, br#"..."#
        m = re.match(r'b?r(#*)"', text[i : i + 12])
        if m:
            hashes = m.group(1)
            prefix_len = m.end()
            j = i + prefix_len
            closing = '"' + hashes
            end = text.find(closing, j)
            end = n if end == -1 else end + len(closing)
            blank(i, min(end, n))
            i = end
            continue

        # regular string literal
        if c == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                    continue
                if text[j] == '"':
                    j += 1
                    break
                j += 1
            blank(i, min(j, n))
            i = j
            continue

        # char literal (and byte char b'x') -- guarded against lifetimes
        # ('a, 'static used as generic params) by requiring a closing quote
        # within a short, escape-aware lookahead.
        if c == "'" or (c == "b" and i + 1 < n and text[i + 1] == "'"):
            start = i if c == "'" else i + 1
            j = start + 1
            if j < n and text[j] == "\\":
                j += 2
                if j < n and text[j] == "'":
                    j += 1
                    blank(i, j)
                    i = j
                    continue
            elif j < n and text[j] != "'" and j + 1 < n and text[j + 1] == "'":
                j += 2
                blank(i, j)
                i = j
                continue
            # not a char literal (e.g. a lifetime) -- fall through untouched

        i += 1

    return "".join(out)


# --------------------------------------------------------------------------
# Header classification
# --------------------------------------------------------------------------

_ATTR_RE = re.compile(r"#!?\s*\[.*?\]", re.S)
_CFG_TEST_RE = re.compile(r"#\s*\[\s*cfg\s*\(\s*test\s*\)\s*\]")
_MOD_RE = re.compile(r"^(?:pub(?:\([^)]*\))?\s+)?mod\s+(\w+)\s*$")
_IMPL_RE = re.compile(r"^impl\b")
_FOR_RE = re.compile(r"\bfor\s+\w")
_FN_RE = re.compile(
    r"^(pub(?:\([^)]*\))?\s+)?"
    r"(?:(?:async|const|unsafe)\s+)*"
    r"(?:extern\s+\"[^\"]*\"\s+)?"
    r"fn\s+(\w+)"
)
_STRUCT_RE = re.compile(r"^(?:pub(?:\([^)]*\))?\s+)?struct\s+(\w+)")
_ENUM_RE = re.compile(r"^(?:pub(?:\([^)]*\))?\s+)?enum\s+(\w+)")


def _strip_generics_and_params(core: str, name_end: int) -> str:
    """From just after `fn NAME`, skip `<...>` generics then `(...)` params.

    Returns the remainder of `core` after the parameter list's closing
    paren -- the return-type-or-empty tail.
    """
    j = name_end
    n = len(core)
    while j < n and core[j] in " \t\n":
        j += 1
    if j < n and core[j] == "<":
        depth = 0
        while j < n:
            if core[j] == "<":
                depth += 1
            elif core[j] == ">":
                depth -= 1
                if depth == 0:
                    j += 1
                    break
            j += 1
    while j < n and core[j] in " \t\n":
        j += 1
    if j < n and core[j] == "(":
        depth = 0
        while j < n:
            if core[j] == "(":
                depth += 1
            elif core[j] == ")":
                depth -= 1
                if depth == 0:
                    j += 1
                    break
            j += 1
    return core[j:]


def extract_return_type(core: str, fn_match: "re.Match[str]") -> str:
    name_end = fn_match.end(2)
    tail = _strip_generics_and_params(core, name_end).strip()
    where_pos = re.search(r"\bwhere\b", tail)
    if where_pos:
        tail = tail[: where_pos.start()].strip()
    if tail.startswith("->"):
        return tail[2:].strip()
    if tail == "":
        return "()"
    # Anything else left over (stray attribute text, etc.) -- treat as unit
    # rather than mis-record; this path is not expected to fire on real code.
    return "()"


def _impl_target_name(core: str) -> tuple[str | None, bool]:
    """Returns (type name, is_trait_impl) for an `impl ...` header."""
    body = core[len("impl") :].lstrip()
    # skip a leading generic parameter list: impl<T, U: Bound> ...
    if body.startswith("<"):
        depth = 0
        j = 0
        for j, ch in enumerate(body):
            if ch == "<":
                depth += 1
            elif ch == ">":
                depth -= 1
                if depth == 0:
                    break
        body = body[j + 1 :].lstrip()
    is_trait = bool(_FOR_RE.search(body))
    if is_trait:
        after_for = re.search(r"\bfor\s+", body)
        rest = body[after_for.end() :] if after_for else body
    else:
        rest = body
    m = re.match(r"[A-Za-z_][A-Za-z0-9_]*", rest)
    name = m.group(0) if m else None
    return name, is_trait


# --------------------------------------------------------------------------
# Data model
# --------------------------------------------------------------------------


@dataclass
class PubType:
    name: str
    kind: str  # "struct" | "enum"
    file: str


@dataclass
class PubFn:
    path: str
    file: str
    line: int
    return_type: str
    impl_type: str | None


@dataclass
class Scope:
    kind: str
    skip: bool  # True: descendants are never recorded
    module_path: list[str] = field(default_factory=list)


def _line_of(text: str, pos: int) -> int:
    return text.count("\n", 0, pos) + 1


def scan_file(
    masked: str,
    module_base: list[str],
    pub_type_names: set[str] | None = None,
) -> tuple[list[PubType], list[PubFn]]:
    """Walk one masked source file, returning its pub types and pub fns.

    Every `pub fn` recorded here already passed the visibility check (plain
    `pub`, not `pub(crate)`/`pub(super)`/`pub(in ...)`) and the ancestor
    `skip` check: not inside a `#[cfg(test)]`/`tests` module, and either at
    module scope or inside an inherent `impl` of a type named in
    `pub_type_names`.

    `pub_type_names` is `None` on the crate's first pass (gathering pub
    struct/enum names is order-independent across files, so that pass does
    not yet know the full set and must not use it to gate anything -- every
    inherent impl is treated as visible there, since only struct/enum
    collection matters). `scan_crate` re-walks every file a second time with
    the completed set so an inherent `impl` of a genuinely private type
    never contributes its methods, even when the `impl` block precedes the
    (non-pub) type's own declaration in the file.
    """
    n = len(masked)
    stack = [Scope(kind="file", skip=False, module_path=list(module_base))]
    pub_types: list[PubType] = []
    pub_fns: list[PubFn] = []
    header_start = 0
    # Depth of unmatched `(`/`[` opened since `header_start`. A `;` only ends
    # a header at depth 0 -- otherwise a return-type array length like
    # `Option<[MvPoly; 2]>` (a `;` inside unbalanced brackets, well before
    # the real `{`) would truncate the header and silently drop the item
    # whose signature it belongs to. Found via `same_point`/`curl`/`cross`
    # vanishing from the scan entirely (not misclassified -- absent).
    bracket_depth = 0
    i = 0
    while i < n:
        c = masked[i]
        if c in "([":
            bracket_depth += 1
            i += 1
            continue
        if c in ")]":
            if bracket_depth > 0:
                bracket_depth -= 1
            i += 1
            continue
        if c == "{":
            header = masked[header_start:i]
            core = _ATTR_RE.sub(" ", header).strip()
            has_cfg_test = bool(_CFG_TEST_RE.search(header))
            top = stack[-1]

            mod_m = _MOD_RE.match(core)
            fn_m = _FN_RE.match(core)
            impl_m = _IMPL_RE.match(core)

            if mod_m:
                name = mod_m.group(1)
                is_test = has_cfg_test or name == "tests"
                stack.append(
                    Scope(
                        kind="mod",
                        skip=top.skip or is_test,
                        module_path=top.module_path + [name],
                    )
                )
            elif impl_m:
                target, is_trait = _impl_target_name(core)
                if pub_type_names is None:
                    not_pub_type = False
                else:
                    not_pub_type = target is not None and target not in pub_type_names
                stack.append(
                    Scope(
                        kind="impl",
                        skip=top.skip or is_trait or not_pub_type,
                        module_path=top.module_path
                        + ([target] if target else []),
                    )
                )
            elif fn_m:
                pub_group, fname = fn_m.group(1), fn_m.group(2)
                if pub_group is not None and pub_group.strip() == "pub" and not top.skip:
                    ret = extract_return_type(core, fn_m)
                    impl_type = top.module_path[-1] if top.kind == "impl" else None
                    path = "::".join(top.module_path + [fname])
                    pub_fns.append(
                        PubFn(
                            path=path,
                            file="",  # filled in by caller
                            line=_line_of(masked, header_start),
                            return_type=ret,
                            impl_type=impl_type,
                        )
                    )
                stack.append(Scope(kind="fn", skip=True, module_path=top.module_path))
            else:
                struct_m = _STRUCT_RE.match(core)
                enum_m = _ENUM_RE.match(core)
                is_pub_hdr = re.match(r"^pub(\([^)]*\))?\s", core) is not None
                if struct_m and is_pub_hdr and not top.skip:
                    pub_types.append(
                        PubType(name=struct_m.group(1), kind="struct", file="")
                    )
                elif enum_m and is_pub_hdr and not top.skip:
                    pub_types.append(
                        PubType(name=enum_m.group(1), kind="enum", file="")
                    )
                stack.append(Scope(kind="other", skip=True, module_path=top.module_path))
            header_start = i + 1
            bracket_depth = 0
            i += 1
            continue
        if c == "}":
            if len(stack) > 1:
                stack.pop()
            header_start = i + 1
            bracket_depth = 0
            i += 1
            continue
        if c == ";":
            if bracket_depth == 0:
                header_start = i + 1
            i += 1
            continue
        i += 1
    return pub_types, pub_fns


def iter_source_files(src_root: Path) -> list[Path]:
    return sorted(src_root.rglob("*.rs"))


def module_path_for(src_root: Path, file_path: Path) -> list[str]:
    rel = file_path.relative_to(src_root)
    parts = list(rel.parts)
    parts[-1] = parts[-1][: -len(".rs")]
    if parts[-1] in ("lib", "mod"):
        parts = parts[:-1]
    return parts


def scan_crate(src_root: Path) -> tuple[list[PubType], list[PubFn]]:
    """Two passes over every `.rs` file under `src_root`.

    Pass 1 gathers every `pub struct`/`pub enum` name crate-wide (a type can
    be declared anywhere in the crate relative to an inherent `impl` of it --
    lexical order within or across files is not guaranteed). Pass 2 re-walks
    the same masked text with that complete name set, so an inherent `impl`
    of a type that turns out NOT to be `pub` never contributes its methods,
    regardless of whether the `impl` block appears before or after the
    type's own declaration.
    """
    files: list[tuple[Path, str, list[str]]] = []
    pass1_types: list[PubType] = []
    for file_path in iter_source_files(src_root):
        text = file_path.read_text(encoding="utf-8", errors="replace")
        masked = mask_source(text)
        module_base = module_path_for(src_root, file_path)
        files.append((file_path, masked, module_base))
        types, _fns = scan_file(masked, module_base, pub_type_names=None)
        pass1_types.extend(types)

    pub_type_names = {t.name for t in pass1_types}

    all_types: list[PubType] = []
    all_fns: list[PubFn] = []
    for file_path, masked, module_base in files:
        rel_str = str(file_path.relative_to(src_root))
        types, fns = scan_file(masked, module_base, pub_type_names=pub_type_names)
        for t in types:
            t.file = rel_str
            all_types.append(t)
        for f in fns:
            f.file = rel_str
            all_fns.append(f)
    return all_types, all_fns


def find_verify_or_check_methods(
    src_root: Path, all_fns: list[PubFn]
) -> set[str]:
    """Type names with an inherent method literally named `verify` or `check`."""
    result: set[str] = set()
    for fn in all_fns:
        if fn.impl_type and fn.path.rsplit("::", 1)[-1] in ("verify", "check"):
            result.add(fn.impl_type)
    return result


def derive_vocabulary(
    all_types: list[PubType], all_fns: list[PubFn]
) -> dict[str, PubType]:
    vocab: dict[str, PubType] = {}
    for t in all_types:
        if t.name.endswith(VOCAB_SUFFIXES) or t.name in VOCAB_EXACT_NAMES:
            vocab[t.name] = t
    for name in find_verify_or_check_methods(Path("."), all_fns):
        # find its PubType record (any file) to attach a kind
        for t in all_types:
            if t.name == name and name not in vocab:
                vocab[name] = t
                break
    return vocab


_WRAPPER_RE = re.compile(r"^(Option|Result|Vec)\s*<(.*)>$")


def _return_type_names_vocab(return_type: str, vocab_names: set[str]) -> bool:
    rt = return_type.strip()
    # peel Option<...>/Result<...>/Vec<...> wrappers, and tuple elements
    seen_any = False

    def names_vocab(t: str) -> bool:
        t = t.strip()
        if not t:
            return False
        if t.startswith("(") and t.endswith(")"):
            inner = t[1:-1]
            return any(names_vocab(part) for part in _split_top_level(inner))
        m = _WRAPPER_RE.match(t)
        if m:
            inner = m.group(2)
            if m.group(1) == "Result":
                parts = _split_top_level(inner)
                return any(names_vocab(p) for p in parts)
            return names_vocab(inner)
        # strip references and generics-of-non-wrapper by checking bare name
        bare = t.lstrip("&").split('<', 1)[0].strip()
        # allow e.g. "&ExtremumCertificate" or leading lifetime "&'a Foo"
        bare = re.sub(r"^'\w+\s*", "", bare)
        return bare in vocab_names

    return names_vocab(rt)


def _split_top_level(s: str) -> list[str]:
    parts: list[str] = []
    depth = 0
    cur = []
    for ch in s:
        if ch in "<(":
            depth += 1
        elif ch in ">)":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append("".join(cur))
            cur = []
        else:
            cur.append(ch)
    if cur:
        parts.append("".join(cur))
    return parts


def classify_fn(fn: PubFn, vocab_names: set[str]) -> str:
    name = fn.path.rsplit("::", 1)[-1]
    if _return_type_names_vocab(fn.return_type, vocab_names):
        return "certified"
    if any(name.startswith(p) for p in CHECKER_PREFIXES):
        return "checker"
    return "uncertified"


# --------------------------------------------------------------------------
# Ratchet I/O
# --------------------------------------------------------------------------


def read_ratchet(
    path: Path,
) -> tuple[dict[str, str], dict[str, str], int] | None:
    """Returns (fn_path -> return_type, vocab_name -> kind, recorded floor
    count), or None if absent.

    The floor count is its own `COUNT` row rather than `len(fn rows)` --
    deliberately decoupled, so a floor regression is a distinct,
    independently mutable check from "this named function stopped being
    certified" (G2) or "this named function vanished" (G3). If a `COUNT`
    row is somehow missing from an otherwise well-formed ratchet, fall back
    to the FN row count so the gate still has a floor to check against.
    """
    if not path.is_file():
        return None
    fns: dict[str, str] = {}
    vocab: dict[str, str] = {}
    count: int | None = None
    for line in path.read_text().splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) == 3 and parts[0] == "FN":
            fns[parts[1]] = parts[2]
        elif len(parts) == 3 and parts[0] == "VOCAB":
            vocab[parts[1]] = parts[2]
        elif len(parts) == 2 and parts[0] == "COUNT":
            try:
                count = int(parts[1])
            except ValueError:
                count = None
    return fns, vocab, (count if count is not None else len(fns))


def write_ratchet(
    path: Path, certified: dict[str, str], vocab: dict[str, str]
) -> None:
    lines = [RATCHET_HEADER, f"COUNT\t{len(certified)}\n"]
    for p in sorted(certified):
        lines.append(f"FN\t{p}\t{certified[p]}\n")
    for v in sorted(vocab):
        lines.append(f"VOCAB\t{v}\t{vocab[v]}\n")
    path.write_text("".join(lines))


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------


def _report(
    all_fns: list[PubFn], vocab_names: set[str]
) -> tuple[dict[str, list[PubFn]], dict[str, int]]:
    by_module: dict[str, list[PubFn]] = {}
    counts = {"certified": 0, "checker": 0, "uncertified": 0}
    for fn in all_fns:
        cls = classify_fn(fn, vocab_names)
        counts[cls] += 1
        by_module.setdefault(fn.file, []).append(fn)
    return by_module, counts


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument(
        "--src-root",
        default=str(DEFAULT_SRC_ROOT),
        help="crates/axeyum-cas/src, or an equivalent fixture root for tests",
    )
    parser.add_argument(
        "--ratchet", default=str(DEFAULT_RATCHET), help="ratchet file to check/write"
    )
    parser.add_argument(
        "--report", action="store_true", help="print per-module and overall counts"
    )
    parser.add_argument(
        "--write", action="store_true", help="rewrite the ratchet from the current scan"
    )
    args = parser.parse_args(argv)

    src_root = Path(args.src_root)
    if not src_root.is_dir():
        print(f"FAIL: no source directory at {src_root}", file=sys.stderr)
        return 2

    all_types, all_fns = scan_crate(src_root)
    vocab = derive_vocabulary(all_types, all_fns)
    vocab_names = set(vocab)

    certified = {
        fn.path: fn.return_type
        for fn in all_fns
        if classify_fn(fn, vocab_names) == "certified"
    }
    vocab_rows = {name: t.kind for name, t in vocab.items()}

    total = len(all_fns)
    by_module, counts = _report(all_fns, vocab_names)

    print(
        f"axeyum-cas pub fn: {total} total -- certified {counts['certified']}, "
        f"checker {counts['checker']}, uncertified {counts['uncertified']}"
    )
    print(f"certificate vocabulary: {len(vocab_names)} type(s): {', '.join(sorted(vocab_names))}")

    if args.report:
        print()
        header = f"  {'module':45s} {'certified':>9s} {'checker':>9s} {'uncertified':>11s}"
        print(header)
        for file_rel in sorted(by_module):
            fns = by_module[file_rel]
            c = sum(1 for f in fns if classify_fn(f, vocab_names) == "certified")
            k = sum(1 for f in fns if classify_fn(f, vocab_names) == "checker")
            u = sum(1 for f in fns if classify_fn(f, vocab_names) == "uncertified")
            print(f"  {file_rel:45s} {c:>9d} {k:>9d} {u:>11d}")
        print()
        print("uncertified functions by module:")
        for file_rel in sorted(by_module):
            fns = sorted(
                (f for f in by_module[file_rel] if classify_fn(f, vocab_names) == "uncertified"),
                key=lambda f: f.path,
            )
            if not fns:
                continue
            print(f"  {file_rel}:")
            for f in fns:
                print(f"    {f.path} -> {f.return_type}  (line {f.line})")

    if args.write:
        write_ratchet(Path(args.ratchet), certified, vocab_rows)
        print(
            f"recorded {len(certified)} certified fn(s) and {len(vocab_rows)} "
            f"vocabulary type(s) in {args.ratchet}"
        )
        return 0

    ratchet_path = Path(args.ratchet)
    recorded = read_ratchet(ratchet_path)
    if recorded is None:
        print(
            f"FAIL: no ratchet at {ratchet_path}. Without it this gate cannot "
            f"notice a certified function regressing. Run --write to record "
            f"the current floor.",
            file=sys.stderr,
        )
        return 1
    recorded_fns, recorded_vocab, floor = recorded

    errors: list[str] = []

    current_by_path = {fn.path: fn for fn in all_fns}
    for path in sorted(recorded_fns):
        fn = current_by_path.get(path)
        if fn is None:
            errors.append(
                f"{path}: recorded as a certified function and is gone from "
                f"the source now. If the removal is deliberate, run --write "
                f"so the diff is visible."
            )
            continue
        cls = classify_fn(fn, vocab_names)
        if cls != "certified":
            errors.append(
                f"{path}: recorded as certified and now classifies as "
                f"{cls!r} (return type now {fn.return_type!r}). This is the "
                f"trust registry regressing at a function that used to "
                f"carry a certificate."
            )

    if counts["certified"] < floor:
        errors.append(
            f"certified count {counts['certified']} fell below the recorded "
            f"floor {floor}."
        )

    for vname in sorted(recorded_vocab):
        if vname not in vocab_names:
            errors.append(
                f"{vname}: recorded as a certificate-vocabulary type and no "
                f"longer exists in the source (renamed, removed, or no "
                f"longer matches the vocabulary rule)."
            )

    new_certified = sorted(set(certified) - set(recorded_fns))
    if new_certified:
        errors.append(
            f"{len(new_certified)} new certified function(s) not recorded in "
            f"the ratchet, run --write to accept: {', '.join(new_certified)}"
        )

    if errors:
        print(f"FAIL: {len(errors)} cas-trust-registry violation(s)")
        for error in errors:
            print(f"  - {error}")
        return 1

    print(
        f"OK: {counts['certified']} certified fn(s) (floor {floor}, all held), "
        f"{counts['checker']} checker, {counts['uncertified']} uncertified"
    )
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
