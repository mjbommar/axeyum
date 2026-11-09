#!/usr/bin/env python3
"""Lift one GovInfo U.S. Code section (HTML) into a computable provision graph.

The input is the GPO "USCODE-<edition>-title<N>-...-sec<S>.htm" rendering that
GovInfo publishes for every section. The output is a deterministic JSON object
(`axeyum.uscode.lifted/v1`) holding:

- `provisions`: the outline tree, one node per enumerated unit, keyed by a
  USLM-style identifier such as `/us/usc/t18/s1030/c/4/A/i/I`, with the node's
  own text (chapeau or body), its trailing flush text, and editorial footnotes;
- `cross_references`: every reference the text makes, resolved to provision
  identifiers when it points inside the section, or kept as an external
  citation when it does not;
- `definitions` and `term_uses`: defined terms ("the term X means") and the
  provisions whose text uses each one;
- `quantities`: money amounts with their comparator, imprisonment maxima,
  periods of time, and counts, each attached to the provision that states it.

The lift is mechanical. It does not interpret the law; it records structure the
text states explicitly so that a human-authored rule model can be checked
against it (see `scripts/rules_ir.py`). Usage:

    python3 scripts/uscode_lift.py SOURCE.htm OUT.json [--check]

`--check` exits nonzero when OUT.json differs from a fresh lift.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import json
import re
import sys
from pathlib import Path
from typing import Any

SCHEMA = "axeyum.uscode.lifted/v1"

LEVELS = ["subsection", "paragraph", "subparagraph", "clause", "subclause"]
ROMAN_LOWER = ["i", "ii", "iii", "iv", "v", "vi", "vii", "viii", "ix", "x", "xi", "xii"]
ROMAN_UPPER = [value.upper() for value in ROMAN_LOWER]
NUMBER_WORDS = {
    "one": 1,
    "two": 2,
    "three": 3,
    "four": 4,
    "five": 5,
    "six": 6,
    "seven": 7,
    "eight": 8,
    "nine": 9,
    "ten": 10,
    "fifteen": 15,
    "twenty": 20,
}


class LiftError(Exception):
    pass


def level_sequence(level: str) -> list[str]:
    if level == "subsection":
        return [chr(code) for code in range(ord("a"), ord("z") + 1)]
    if level == "paragraph":
        return [str(value) for value in range(1, 100)]
    if level == "subparagraph":
        return [chr(code) for code in range(ord("A"), ord("Z") + 1)]
    if level == "clause":
        return ROMAN_LOWER
    if level == "subclause":
        return ROMAN_UPPER
    raise LiftError(f"unknown level {level}")


def candidate_levels(token: str) -> list[str]:
    levels = []
    if re.fullmatch(r"[a-z]", token) or re.fullmatch(r"[a-z]{2}", token):
        levels.append("subsection")
    if token.isdigit():
        levels.append("paragraph")
    if re.fullmatch(r"[A-Z]{1,2}", token):
        levels.append("subparagraph")
    if token in ROMAN_LOWER:
        levels.append("clause")
    if token in ROMAN_UPPER:
        levels.append("subclause")
    return levels


def clean_inline(fragment: str, footnotes: dict[str, str]) -> tuple[str, list[str]]:
    """Strip markup, returning visible text and the footnote ids it anchors."""
    anchored = re.findall(r'<sup><a href="#([^"]+)_target"', fragment)
    fragment = re.sub(r"<sup>.*?</sup>", "", fragment, flags=re.S)
    text = html.unescape(re.sub(r"<[^>]+>", "", fragment))
    text = text.replace(" ", " ")
    text = re.sub(r"\s+", " ", text).strip()
    notes = [footnotes[anchor] for anchor in anchored if anchor in footnotes]
    return text, notes


def parse_footnotes(source: str) -> dict[str, str]:
    notes = {}
    for match in re.finditer(
        r'<p class="footnote"><a href="#([^"]+)" name="[^"]+"><sup>\d+</sup>(.*?)</a></p>',
        source,
        re.S,
    ):
        text = html.unescape(re.sub(r"<[^>]+>", "", match.group(2)))
        notes[match.group(1)] = re.sub(r"\s+", " ", text.replace(" ", " ")).strip()
    return notes


class Outline:
    """Assigns enumerators to outline levels with a sequence-aware stack."""

    def __init__(self) -> None:
        self.stack: list[tuple[str, str]] = []  # (level, enumerator)

    def place(self, token: str) -> list[tuple[str, str]]:
        options = []
        for level in candidate_levels(token):
            depth = LEVELS.index(level)
            seq = level_sequence(level)
            # Continuing a sibling at an open level.
            for index, (open_level, open_token) in enumerate(self.stack):
                if open_level == level:
                    position = seq.index(open_token) if open_token in seq else -1
                    if position + 1 < len(seq) and seq[position + 1] == token:
                        options.append((index, level))
            # Opening the first child of the deepest open level.
            if token == seq[0] and depth == len(self.stack):
                options.append((len(self.stack), level))
        if not options:
            raise LiftError(f"enumerator ({token}) does not continue the outline {self.stack}")
        if len({level for _, level in options}) > 1:
            raise LiftError(f"enumerator ({token}) is ambiguous at {self.stack}: {options}")
        index, level = options[0]
        self.stack = self.stack[:index] + [(level, token)]
        return list(self.stack)


def provision_id(base: str, path: list[tuple[str, str]]) -> str:
    return base + "".join(f"/{token}" for _, token in path)


def citation_for(section_cite: str, path: list[tuple[str, str]]) -> str:
    return section_cite + "".join(f"({token})" for _, token in path)


def lift(source_path: Path) -> dict[str, Any]:
    raw = source_path.read_bytes()
    source = raw.decode("utf-8")
    title_match = re.search(r"usckey:(\d+)", source)
    doc_match = re.search(r"documentid:(\d+)_(\w+)", source)
    current_match = re.search(r"currentthrough:(\d{8})", source)
    edition_match = re.search(r"United States Code, (\d{4}) Edition", source)
    if not (title_match and doc_match and current_match and edition_match):
        raise LiftError("source is not a GovInfo USCODE section rendering")
    title, section = doc_match.group(1), doc_match.group(2)
    current = current_match.group(1)
    base = f"/us/usc/t{title}/s{section}"
    section_cite = f"{title} U.S.C. § {section}"

    head = re.search(r'<h3 class="section-head">(.*?)</h3>', source, re.S)
    if not head:
        raise LiftError("section heading not found")
    heading = html.unescape(re.sub(r"<[^>]+>", "", head.group(1))).replace(" ", " ")
    heading = re.sub(r"^§\s*\d+\w*\.\s*", "", re.sub(r"\s+", " ", heading).strip())

    footnotes = parse_footnotes(source)
    body = source.split('class="source-credit"', 1)[0]
    outline = Outline()
    nodes: dict[str, dict[str, Any]] = {}
    order: list[str] = []
    last_id: str | None = None

    for match in re.finditer(
        r'<p class="(statutory-body[^"]*)"[^>]*>(.*?)</p>', body, re.S
    ):
        css, fragment = match.group(1), match.group(2)
        text, notes = clean_inline(fragment, footnotes)
        if css == "statutory-body-block":
            if last_id is None:
                raise LiftError("flush text before any provision")
            # Flush text closes the enclosing list; attach it to the parent
            # whose chapeau opened that list (the shallowest open level).
            parent = provision_id(base, outline.stack[:1])
            nodes[parent]["continuation"] = text
            nodes[parent]["footnotes"].extend(notes)
            continue
        tokens = []
        rest = text
        while True:
            enum = re.match(r"\(([0-9]+|[a-zA-Z]{1,4})\)\s*", rest)
            if not enum:
                break
            tokens.append(enum.group(1))
            rest = rest[enum.end():]
        if not tokens:
            raise LiftError(f"unenumerated statutory paragraph: {text[:80]}")
        for position, token in enumerate(tokens):
            path = outline.place(token)
            node_id = provision_id(base, path)
            if node_id in nodes:
                raise LiftError(f"duplicate provision {node_id}")
            parent_id = provision_id(base, path[:-1]) if len(path) > 1 else base
            node = {
                "id": node_id,
                "parent": parent_id,
                "level": path[-1][0],
                "enumerator": path[-1][1],
                "citation": citation_for(section_cite, path),
                "text": rest if position == len(tokens) - 1 else "",
                "footnotes": notes if position == len(tokens) - 1 else [],
            }
            nodes[node_id] = node
            order.append(node_id)
            last_id = node_id

    children: dict[str, list[str]] = {}
    for node_id in order:
        children.setdefault(nodes[node_id]["parent"], []).append(node_id)
    provisions = []
    for node_id in order:
        node = nodes[node_id]
        node["children"] = children.get(node_id, [])
        provisions.append(node)

    lifted = {
        "schema": SCHEMA,
        "generated_by": "python3 scripts/uscode_lift.py",
        "source": {
            "publisher": "U.S. Government Publishing Office (GovInfo)",
            "edition": f"United States Code, {edition_match.group(1)} Edition",
            "current_through": f"{current[:4]}-{current[4:6]}-{current[6:]}",
            "file": source_path.name,
            "sha256": hashlib.sha256(raw).hexdigest(),
        },
        "section": {
            "id": base,
            "citation": section_cite,
            "heading": heading,
            "top_level": children.get(base, []),
        },
        "provisions": provisions,
    }
    known = {node["id"] for node in provisions}
    lifted["cross_references"] = extract_cross_references(provisions, base, known)
    definitions = extract_definitions(provisions)
    lifted["definitions"] = definitions
    lifted["term_uses"] = extract_term_uses(provisions, definitions)
    lifted["quantities"] = extract_quantities(provisions)
    lifted["summary"] = {
        "provisions": len(provisions),
        "by_level": {
            level: sum(1 for node in provisions if node["level"] == level) for level in LEVELS
        },
        "internal_references": sum(
            1 for ref in lifted["cross_references"] if ref["scope"] == "internal"
        ),
        "external_references": sum(
            1 for ref in lifted["cross_references"] if ref["scope"] == "external"
        ),
        "resolved_targets": sum(
            len(ref["targets"]) for ref in lifted["cross_references"] if ref["scope"] == "internal"
        ),
        "definitions": len(definitions),
        "quantities": len(lifted["quantities"]),
        "editorial_footnotes": sum(len(node["footnotes"]) for node in provisions),
    }
    return lifted


# ---------------------------------------------------------------------------
# Cross-references

KEYWORD_LEVEL = {
    "subsection": "subsection",
    "subsections": "subsection",
    "paragraph": "paragraph",
    "paragraphs": "paragraph",
    "subparagraph": "subparagraph",
    "subparagraphs": "subparagraph",
    "clause": "clause",
    "clauses": "clause",
    "subclause": "subclause",
    "subclauses": "subclause",
}
CHAIN = r"(?:\([0-9A-Za-z]{1,4}\))+"
ITEM_LIST = (
    rf"{CHAIN}(?:\s*(?:,\s*(?:or|and)?|,|or|and|through)\s*{CHAIN})*"
)
INTERNAL_REF = re.compile(
    rf"\b(subsections?|paragraphs?|subparagraphs?|clauses?|subclauses?)\s+"
    rf"(?P<items>{ITEM_LIST})"
    rf"(?:\s+of\s+(?P<ofkw>subsection|paragraph|subparagraph|clause)\s+(?P<of>{CHAIN}))?"
)
EXTERNAL_REF = re.compile(
    r"\bsection\s+(?P<sec>\d+[a-zA-Z]?)(?P<sub>(?:\([0-9A-Za-z]+\))*)"
    r"(?:\s+of\s+(?:title\s+(?P<title>\d+)|(?P<act>the [A-Z][A-Za-z ]+?Act(?: of \d{4})?)))?"
)


def split_chain(chain: str) -> list[str]:
    return re.findall(r"\(([0-9A-Za-z]{1,4})\)", chain)


def path_of(node_id: str, base: str) -> list[str]:
    rest = node_id[len(base):]
    return [part for part in rest.split("/") if part]


def resolve_chain(
    level: str, tokens: list[str], origin: list[str], anchor: list[str] | None
) -> list[str]:
    """Return the path for a reference whose first token sits at `level`."""
    depth = LEVELS.index(level)
    if anchor is not None:
        prefix = anchor
    else:
        # A relative reference shares the origin's ancestors above `level`.
        prefix = origin[:depth]
    if len(prefix) != depth:
        raise LiftError(f"cannot anchor {level} {tokens} from {origin}")
    return prefix + tokens


def expand_items(items: str) -> list[list[str]]:
    chains = re.findall(CHAIN, items)
    connectors = re.split(CHAIN, items)[1:-1]
    expanded: list[list[str]] = []
    for index, chain in enumerate(chains):
        tokens = split_chain(chain)
        if index > 0 and connectors[index - 1].strip() == "through":
            start = expanded[-1]
            stop = tokens
            if len(start) != 1 or len(stop) != 1:
                raise LiftError(f"range over chains is not supported: {items}")
            for level in LEVELS:
                seq = level_sequence(level)
                if start[0] in seq and stop[0] in seq and seq.index(start[0]) < seq.index(stop[0]):
                    lo, hi = seq.index(start[0]), seq.index(stop[0])
                    expanded.extend([[token] for token in seq[lo + 1 : hi + 1]])
                    break
            else:
                raise LiftError(f"cannot expand range {items}")
        else:
            expanded.append(tokens)
    return expanded


def extract_cross_references(
    provisions: list[dict[str, Any]], base: str, known: set[str]
) -> list[dict[str, Any]]:
    refs: list[dict[str, Any]] = []
    for node in provisions:
        text = " ".join(part for part in [node["text"], node.get("continuation", "")] if part)
        origin = path_of(node["id"], base)
        for match in INTERNAL_REF.finditer(text):
            if re.match(r"\s+of\s+section\b", text[match.end():]):
                # "paragraphs (1) and (3) of section 1(b) of the ... Act" names
                # units of another provision; EXTERNAL_REF records it.
                continue
            level = KEYWORD_LEVEL[match.group(1)]
            anchor = None
            if match.group("of"):
                of_level = KEYWORD_LEVEL[match.group("ofkw")]
                anchor = resolve_chain(of_level, split_chain(match.group("of")), origin, None)
            targets = []
            for tokens in expand_items(match.group("items")):
                if anchor is not None:
                    path = anchor + tokens
                else:
                    path = resolve_chain(level, tokens, origin, None)
                target = base + "".join(f"/{token}" for token in path)
                targets.append(target)
            unresolved = [target for target in targets if target not in known]
            refs.append(
                {
                    "from": node["id"],
                    "raw": match.group(0),
                    "scope": "internal",
                    "targets": targets,
                    "unresolved": unresolved,
                }
            )
        for match in EXTERNAL_REF.finditer(text):
            sec = match.group("sec")
            sub = match.group("sub") or ""
            if match.group("title"):
                cite = f"{match.group('title')} U.S.C. § {sec}{sub}"
            elif match.group("act"):
                cite = f"{match.group('act').removeprefix('the ')} § {sec}{sub}"
            else:
                # "section 25 or section 25(a) of the Federal Reserve Act": a
                # bare section coordinated with a qualified one shares its source.
                shared = re.match(
                    r"\s*(?:,|or|and)\s+(?:or\s+|and\s+)?section\s+\S+?\s+of\s+"
                    r"(?:title\s+(?P<title>\d+)|(?P<act>the [A-Z][A-Za-z ]+?Act(?: of \d{4})?))",
                    text[match.end():],
                )
                if shared and shared.group("title"):
                    cite = f"{shared.group('title')} U.S.C. § {sec}{sub}"
                elif shared and shared.group("act"):
                    cite = f"{shared.group('act').removeprefix('the ')} § {sec}{sub}"
                else:
                    cite = f"{base.split('/')[3][1:]} U.S.C. § {sec}{sub}"
            refs.append(
                {
                    "from": node["id"],
                    "raw": match.group(0),
                    "scope": "external",
                    "citation": cite,
                    "targets": [],
                    "unresolved": [],
                }
            )
    return refs


# ---------------------------------------------------------------------------
# Definitions and term uses

DEFINITION = re.compile(r'the term "(?P<term>[^"]+)" (?P<verb>means|includes|shall include)')


def extract_definitions(provisions: list[dict[str, Any]]) -> list[dict[str, Any]]:
    definitions = []
    for node in provisions:
        for match in DEFINITION.finditer(node["text"]):
            definitions.append(
                {"term": match.group("term"), "verb": match.group("verb"), "provision": node["id"]}
            )
    return definitions


def extract_term_uses(
    provisions: list[dict[str, Any]], definitions: list[dict[str, Any]]
) -> list[dict[str, Any]]:
    terms = sorted({entry["term"] for entry in definitions}, key=lambda term: (-len(term), term))
    defining = {entry["provision"] for entry in definitions}
    uses: dict[str, list[str]] = {term: [] for term in terms}
    for node in provisions:
        if node["id"] in defining:
            continue
        text = " ".join(part for part in [node["text"], node.get("continuation", "")] if part)
        masked = text
        for term in terms:
            # Plural only for common nouns; "State" must not match "United States".
            plural = "s?" if term[0].islower() else ""
            pattern = re.compile(rf"(?<!United )\b{re.escape(term)}{plural}\b")
            if pattern.search(masked):
                uses[term].append(node["id"])
                # Longest match wins: "protected computer" is not also a use
                # of "computer" at the same span.
                masked = pattern.sub(" ", masked)
    return [{"term": term, "provisions": uses[term]} for term in terms]


# ---------------------------------------------------------------------------
# Quantities

MONEY = re.compile(
    r"(?P<cmp>exceeds|aggregating at least|at least|more than|less than|not more than|not less than)?"
    r"\s*\$(?P<amount>[\d,]+)"
)
PRISON = re.compile(
    r"imprisonment for (?:not more than (?P<n>\w+) years?|(?P<life>any term of years or for life))"
)
PERIOD = re.compile(r"\bwithin (?P<n>\w+) (?P<unit>days?|months?|years?)\b")
COUNT = re.compile(r"\b(?P<n>\d+) or more (?P<what>[a-z ]+?computers)\b")


def number(token: str) -> int:
    if token.isdigit():
        return int(token)
    if token.lower() in NUMBER_WORDS:
        return NUMBER_WORDS[token.lower()]
    raise LiftError(f"unrecognized number word {token}")


def extract_quantities(provisions: list[dict[str, Any]]) -> list[dict[str, Any]]:
    out: list[dict[str, Any]] = []
    for node in provisions:
        text = node["text"]
        for match in MONEY.finditer(text):
            comparator = {
                None: "eq",
                "exceeds": ">",
                "more than": ">",
                "aggregating at least": ">=",
                "at least": ">=",
                "not less than": ">=",
                "less than": "<",
                "not more than": "<=",
            }[match.group("cmp")]
            out.append(
                {
                    "provision": node["id"],
                    "kind": "money_usd",
                    "comparator": comparator,
                    "value": int(match.group("amount").replace(",", "")),
                    "raw": match.group(0).strip(),
                }
            )
        for match in PRISON.finditer(text):
            if match.group("life"):
                value, raw_unit = None, "life"
            else:
                value, raw_unit = number(match.group("n")), "years"
            out.append(
                {
                    "provision": node["id"],
                    "kind": "imprisonment_max",
                    "comparator": "<=",
                    "value": value,
                    "unit": raw_unit,
                    "raw": match.group(0),
                }
            )
        for match in PERIOD.finditer(text):
            out.append(
                {
                    "provision": node["id"],
                    "kind": "period",
                    "comparator": "<=",
                    "value": number(match.group("n")),
                    "unit": match.group("unit").rstrip("s"),
                    "raw": match.group(0),
                }
            )
        for match in COUNT.finditer(text):
            out.append(
                {
                    "provision": node["id"],
                    "kind": "count",
                    "comparator": ">=",
                    "value": int(match.group("n")),
                    "unit": match.group("what"),
                    "raw": match.group(0),
                }
            )
    return out


def render(lifted: dict[str, Any]) -> str:
    return json.dumps(lifted, indent=2, ensure_ascii=False) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("source", type=Path)
    parser.add_argument("out", type=Path)
    parser.add_argument("--check", action="store_true", help="fail if OUT differs")
    args = parser.parse_args()
    try:
        lifted = lift(args.source)
    except LiftError as error:
        print(f"error: {error}", file=sys.stderr)
        return 1
    unresolved = [
        (ref["from"], ref["raw"], ref["unresolved"])
        for ref in lifted["cross_references"]
        if ref["unresolved"]
    ]
    text = render(lifted)
    if args.check:
        current = args.out.read_text(encoding="utf-8") if args.out.exists() else ""
        if current != text:
            print(f"error: {args.out} is stale; rerun scripts/uscode_lift.py", file=sys.stderr)
            return 1
    else:
        args.out.write_text(text, encoding="utf-8")
    summary = lifted["summary"]
    print(
        f"lifted {lifted['section']['citation']}: {summary['provisions']} provisions, "
        f"{summary['internal_references']} internal references "
        f"({summary['resolved_targets']} targets), {summary['external_references']} external, "
        f"{summary['definitions']} definitions, {summary['quantities']} quantities, "
        f"{len(unresolved)} unresolved"
    )
    for origin, raw, targets in unresolved:
        print(f"  unresolved: {origin}: {raw!r} -> {targets}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
