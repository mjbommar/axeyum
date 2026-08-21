#!/usr/bin/env python3
"""Build the DESIGN preview document from the REAL fact ledger.

Why this exists rather than a hand-written JSON file: the preview page is the
visual benchmark for the HTML emitter, and a benchmark whose numbers, statuses,
evidence rows and replay commands were typed by hand is the exact drift this
strand was created to kill (README, "Motivating incident"). Every badge,
statement, checker command and hash on the page is read out of
`artifacts/facts/*.json` here, at build time.

Prose IS hand-written, and is marked as such: narrative blocks carry no
provenance, which is the schema's honest signal that a human wrote them
(render/src/ir.rs, `Block::provenance`).

Usage, from the repository root:

    python3 render/assets/preview/build-preview-doc.py \
        > render/assets/preview/preview-doc.json
"""

import hashlib
import json
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
FACTS = ROOT / "artifacts" / "facts"

# The connected component of the ledger that the Nat/Int/Rat prelude forms,
# discovered rather than listed: everything reachable from Euclid's theorem
# through `depends_on` in either direction.
SEED = "F:nat-exists-prime-gt"
# Two facts shown alongside it for status contrast. Both are genuinely isolated
# in the ledger (`depends_on: []`), so drawing them as isolated nodes is the
# truth, not a layout convenience.
EXTRA = ["F:rado-r4-a5-b3", "F:fp8-add-not-associative"]
CARDS = [
    "F:nat-exists-prime-gt",
    "F:nat-gcd-bezout",
    "F:rado-r4-a5-b3",
    "F:fp8-add-not-associative",
]


def load():
    out = {}
    for p in sorted(FACTS.glob("F-*.json")):
        d = json.loads(p.read_text())
        d["_path"] = str(p.relative_to(ROOT))
        out[d["id"]] = d
    return out


def component(db, seed):
    adj = {}
    for k, d in db.items():
        for x in d.get("depends_on", []):
            adj.setdefault(k, set()).add(x)
            adj.setdefault(x, set()).add(k)
    seen, stack = set(), [seed]
    while stack:
        n = stack.pop()
        if n in seen or n not in db:
            continue
        seen.add(n)
        stack.extend(adj.get(n, ()))
    return sorted(seen)


def label(fact_id):
    return fact_id.removeprefix("F:").replace("-", " ")


def anchor(fact_id):
    return "card-" + fact_id.removeprefix("F:")


def evidence_rows(fact):
    """Copy evidence rows VERBATIM. No field here is computed or reworded."""
    rows = []
    for e in fact.get("evidence", []):
        row = {
            "id": e["id"],
            "kind": e["kind"],
            "supports": e["supports"],
            "check_status": e["check_status"],
        }
        for k in ("checker_command", "checkers", "artifact", "notes"):
            if k in e:
                row[k] = e[k]
        rows.append(row)
    return rows


def card(fact, tag="essential"):
    body = {
        "label": fact["title"],
        "ref": fact["id"],
        "statement": fact["statement"],
        "status": fact["epistemic_status"],
        "evidence": evidence_rows(fact),
        "formal": {
            "language": fact["formal"]["language"],
            "statement": fact["formal"]["statement"],
            "fragment": fact["formal"].get("fragment"),
        },
    }
    for k in ("external_status", "proof_route", "axiom_footprint", "notes"):
        if k in fact:
            body[k] = fact[k]
    return {
        "id": anchor(fact["id"]),
        "tag": tag,
        "kind": {"Claim": body},
        "provenance": {"generator": fact["_path"]},
    }


def sha256(rel):
    p = ROOT / rel
    if not p.is_file():
        return None
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    db = load()
    comp = component(db, SEED)
    graph_ids = comp + [f for f in EXTRA if f in db]

    nodes = [
        {
            "key": f,
            "label": label(f),
            "status": db[f]["epistemic_status"],
            "href": anchor(f) if f in CARDS else None,
        }
        for f in graph_ids
    ]
    edges = [
        {"from": dep, "to": f}
        for f in graph_ids
        for dep in db[f].get("depends_on", [])
        if dep in set(graph_ids)
    ]

    # A real run, recorded with its real exit status. This is the whole point of
    # a certificate box: the badge below is this number, not a decision.
    proc = subprocess.run(
        [sys.executable, "scripts/validate-facts.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        check=False,
    )
    novel = [
        line.strip()
        for line in proc.stdout.splitlines()
        if "NOVEL" in line
    ]

    rado = db["F:rado-r4-a5-b3"]
    cert_inputs = []
    for e in rado.get("evidence", []):
        if "artifact" in e:
            cert_inputs.append(
                {"path": e["artifact"], "sha256": sha256(e["artifact"]) or "(missing)"}
            )

    # Cumulative proved-fact count by the date each fact records. Real ledger
    # data; no smoothing, no interpolation.
    dates = sorted(
        d["provenance"]["date"]
        for d in db.values()
        if d["epistemic_status"] == "proved" and "date" in d.get("provenance", {})
    )
    series, running = [], 0
    day0 = dates[0] if dates else None
    for i, day in enumerate(dates):
        running += 1
        if i + 1 == len(dates) or dates[i + 1] != day:
            series.append([day_index(day0, day), running])

    cone = component_upward(db, SEED)
    table_rows = [
        [
            label(f),
            db[f]["epistemic_status"],
            db[f].get("proof_route", ""),
            len(db[f].get("depends_on", [])),
            len(db[f].get("axiom_footprint", [])),
            len(db[f].get("evidence", [])),
        ]
        for f in cone
    ]

    doc = {
        "schema_version": 1,
        "meta": {
            "kicker": "axeyum fact atlas / render preview",
            "title": "The Nat prelude, and what stands on it",
            "subtitle": "One connected component of the fact ledger, rendered. "
            "Every badge, statement, hash and replay command on this page was "
            "read out of `artifacts/facts/` at build time; only the narrative "
            "was written by a person.",
            "doc_id": "preview-nat-atlas",
            "genre": "result (R2)",
            "generator": "`render/assets/preview/build-preview-doc.py`",
            "footer_note": "Rendered by `render/src/emit_html.rs`. "
            "Regenerate with the command in the document header, then "
            "`cargo test --features html -- preview`.",
        },
        "blocks": [],
    }
    B = doc["blocks"]

    B.append(
        {
            "id": "intro",
            "tag": "essential",
            "kind": {
                "Prose": {
                    "text": "A rendered document here is a checker output, not prose about "
                    "one. That distinction is the whole design, and it is visible on this "
                    "page: nothing below carries a green badge because a person decided it "
                    "deserved one. Each badge is the `epistemic_status` field of a file in "
                    "`artifacts/facts/`, each replay command is that file's "
                    "`checker_command`, and a claim that arrived without evidence renders "
                    "saying so.\n\n"
                    "What follows is one connected component of the ledger's dependency "
                    "graph -- the naturals, the integers, the rationals built over them, "
                    "and Euclid's theorem at the bottom of the chain -- with two "
                    "deliberately unrelated facts alongside it for contrast. Read it at "
                    "*summary* to see only the argument, at *full* for the evidence, at "
                    "*forensic* for everything the ledger carries."
                }
            },
        }
    )

    B.append(
        {
            "id": "fig-dag",
            "tag": "essential",
            "kind": {
                "Figure": {
                    "DepGraph": {
                        "caption": "**The prelude component.** An edge runs from a "
                        "prerequisite to the result that uses it, so everything a node "
                        "rests on is what sits above it. The four nodes with cards below "
                        "link to them. Layered in Rust -- longest-path ranking, median "
                        "sweeps, isotonic coordinates -- and drawn as inline SVG; no "
                        "graph library is involved, and none could be, since the page "
                        "may not fetch one.",
                        "nodes": nodes,
                        "edges": edges,
                    }
                }
            },
        }
    )

    B.append(
        {
            "id": "cards-head",
            "tag": "essential",
            "kind": {
                "Prose": {
                    "heading": "Four facts, four kinds of standing",
                    "text": "The ledger keeps two status axes on purpose: what *this system* "
                    "established, and what mathematics knows. They are different questions, "
                    "and their disagreement in our favour is a result rather than a "
                    "bookkeeping error. The four cards below are one of each interesting "
                    "case."
                }
            },
        }
    )

    B.append(card(db["F:nat-exists-prime-gt"]))
    B.append(
        {
            "id": "note-euclid",
            "tag": "detail",
            "kind": {
                "Prose": {
                    "text": "The empty axiom footprint above is the strong claim, not a "
                    "missing field: `Kernel::axiom_footprint` walked this declaration's "
                    "transitive dependencies and found no `Axiom`, `Opaque` or `Quotient` "
                    "in the closure. The schema requires the field when a fact is `proved` "
                    "precisely so that absence and emptiness cannot be confused."
                }
            },
        }
    )
    B.append(card(db["F:nat-gcd-bezout"]))
    B.append(card(db["F:rado-r4-a5-b3"]))
    B.append(card(db["F:fp8-add-not-associative"]))

    B.append(
        {
            "id": "argument",
            "tag": "detail",
            "kind": {
                "Steps": {
                    "heading": "The argument for the bottom node",
                    "caption": "This block carries **no provenance**, which is the schema's "
                    "signal that a person wrote it: it is the human argument, not a captured "
                    "machine trace. The machine's version of it is the proof term the kernel "
                    "checked, and the card above is where that is recorded.",
                    "steps": [
                        {
                            "op": "suppose",
                            "input": "n : Nat",
                            "output": "consider N = n! + 1",
                            "note": "Any prime dividing N is larger than n, if one exists.",
                        },
                        {
                            "op": "apply",
                            "input": "N >= 2",
                            "output": "N has a prime divisor p",
                            "note": "This is `F:nat-exists-prime-dvd`, one layer up in the graph.",
                        },
                        {
                            "op": "suppose for contradiction",
                            "input": "p <= n",
                            "output": "p divides n!",
                            "note": "p is one of the factors of n!.",
                        },
                        {
                            "op": "apply",
                            "input": "p | n! and p | n! + 1",
                            "output": "p | 1",
                            "note": "This is `F:nat-dvd-add`, which is why that node is an "
                            "ancestor of this one and not merely nearby.",
                        },
                        {
                            "op": "conclude",
                            "input": "p | 1 and p prime",
                            "output": "contradiction; so p > n",
                            "note": "There is no largest prime.",
                        },
                    ],
                }
            },
        }
    )

    B.append(
        {
            "id": "tbl-cone",
            "tag": "detail",
            "kind": {
                "Table": {
                    "heading": "The trust base of Euclid's theorem, row by row",
                    "caption": "Every fact in the upward cone of `F:nat-exists-prime-gt`. "
                    "Generated from the ledger files; the `axioms` column counts "
                    "`axiom_footprint` entries, so a zero is a measured claim.",
                    "columns": [
                        {"label": "fact"},
                        {"label": "status"},
                        {"label": "route"},
                        {"label": "depends on", "align": "right"},
                        {"label": "axioms", "align": "right"},
                        {"label": "evidence rows", "align": "right"},
                    ],
                    "rows": table_rows,
                    "source": {"generator": "artifacts/facts/*.json"},
                }
            },
        }
    )

    B.append(
        {
            "id": "cert-ledger",
            "tag": "essential",
            "kind": {
                "Certificate": {
                    "kind": "ReportRun",
                    "summary": "The fact-ledger validator, run while this page was built",
                    "generator": "scripts/validate-facts.py",
                    "exit_status": proc.returncode,
                    "verdict": "checked" if proc.returncode == 0 else "refuted",
                    "replay": "python3 scripts/validate-facts.py",
                    "inputs": [
                        {"path": "artifacts/facts/", "sha256": ledger_digest(db)},
                        {
                            "path": "artifacts/ontology/fact.schema.json",
                            "sha256": sha256("artifacts/ontology/fact.schema.json"),
                        },
                    ],
                    "raw": {
                        "command": "python3 scripts/validate-facts.py",
                        "exit_status": proc.returncode,
                        "novel_lines": novel,
                        "stdout_tail": proc.stdout.strip().splitlines()[-6:],
                    },
                }
            },
        }
    )

    B.append(
        {
            "id": "cert-rado",
            "tag": "detail",
            "kind": {
                "Certificate": {
                    "kind": "SearchCertificate",
                    "summary": "The pinned artifacts behind R_4(5(x-y)=3z) = 625",
                    "generator": "axeyum native proof-producing CDCL (ADR-0002)",
                    "verdict": rado["evidence"][0]["check_status"],
                    "no_exit_reason": "a four-hour re-check cannot be a gate; the three "
                    "cheap checkers on the card above are the ones that run",
                    "replay": rado["evidence"][1]["checker_command"],
                    "inputs": cert_inputs,
                    "raw": {
                        "note": "Hashes computed from the checked-in artifacts at build "
                        "time. There is deliberately no exit status here: this "
                        "certificate is not re-run per commit, and the fact says so in "
                        "its axiom_footprint rather than implying it is.",
                        "axiom_footprint": rado["axiom_footprint"],
                    },
                }
            },
        }
    )

    B.append(
        {
            "id": "fig-growth",
            "tag": "detail",
            "kind": {
                "Figure": {
                    "Plot": {
                        "caption": "**Proved facts in the ledger, cumulative.** One point "
                        "per day on which at least one fact reached `proved`, taken from "
                        "each file's `provenance.date`. The x axis is days since the first "
                        "such date. Vertices carry their value as a native tooltip, so it "
                        "works with scripting disabled.",
                        "x_label": "days since the first proved fact",
                        "y_label": "facts at status proved",
                        "series": [{"name": "proved", "kind": "step", "points": series}],
                    }
                }
            },
        }
    )

    B.append(
        {
            "id": "archive-ledger",
            "tag": "archive",
            "kind": {
                "Include": {
                    "path": "artifacts/facts/",
                    "note": "the whole ledger, %d files, of which this page renders %d"
                    % (len(db), len(graph_ids)),
                }
            },
        }
    )

    B.append(
        {
            "id": "outro",
            "tag": "essential",
            "kind": {
                "Prose": {
                    "heading": "What this file is",
                    "text": "One file. The stylesheet, the script, both figures and every "
                    "glyph are inside it, and opening it makes no network request -- a "
                    "property checked by `lint_self_contained`, which has a unit test per "
                    "violation class so that it can actually fail. Print it and the "
                    "reading-level control disappears, every fold opens, and the badges "
                    "stay distinguishable because each one carries a shape as well as a "
                    "colour."
                }
            },
        }
    )

    json.dump(doc, sys.stdout, indent=2, sort_keys=False)
    sys.stdout.write("\n")


def component_upward(db, seed):
    seen, stack = set(), [seed]
    while stack:
        n = stack.pop()
        if n in seen or n not in db:
            continue
        seen.add(n)
        stack.extend(db[n].get("depends_on", []))
    return sorted(seen)


def day_index(day0, day):
    import datetime

    a = datetime.date.fromisoformat(day0)
    b = datetime.date.fromisoformat(day)
    return (b - a).days


def ledger_digest(db):
    """One digest over every fact file, so the input row names real bytes."""
    h = hashlib.sha256()
    for fid in sorted(db):
        h.update((ROOT / db[fid]["_path"]).read_bytes())
    return h.hexdigest()


if __name__ == "__main__":
    main()
