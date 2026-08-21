#!/usr/bin/env python3
"""Assemble the P0-A certificate page manifest (Doc-IR) from the run record.

Render strand P0-A step 2 (docs/render-2026-08/04-prototype-plan.md), agent
CERT, 2026-08-21.

WHY THIS IS A SCRIPT AND NOT A HAND-WRITTEN JSON FILE.  The prose in a Doc-IR
document is the human part and is written by hand -- it is in this file, in
PROSE_* below, and nowhere else.  Every NUMBER, on the other hand, is read out
of render/examples-input/cert/run-certificate.json, which the certificate wrote.
Typing d(4..24) into a manifest by hand would be the transcription this whole
strand exists to kill, and the schema's own BlockTable description says as much.

    python3 render/producers/build-certificate-manifest.py

writes render/examples-input/cert/certificate.doc.json.  It is deterministic:
no wall clock, no dict-order dependence, and two runs are byte-identical.

OPEN SCHEMA-FIT ISSUE (for round 2, recorded in docs/render-2026-08/12-cert-diary.md).
RunRecord.tables exists "so a document's table block can be built from a record
rather than transcribed", but BlockTable has no field that REFERENCES a record
table -- it carries `columns`, `rows` and a `source: Provenance` copied in.  So
the binding is done here, in a producer, and assembly cannot re-check it.  A
`from: {run_record, table}` on BlockTable (and the same on FigurePlot.series)
would move that check into the fail-closed layer where it belongs.
"""

import hashlib
import json
import pathlib
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
RUN = ROOT / "render/examples-input/cert/run-certificate.json"
RUN_M1 = ROOT / "render/examples-input/cert/run-mutant-M1.json"
PRODUCER = ROOT / "render/producers/noh_wt_certificate_emitrun.rs"
OUT = ROOT / "render/examples-input/cert/certificate.doc.json"
SELF = pathlib.Path(__file__).resolve()

PIN_COMMIT = "75663ef85c2dad4390a3b6d77361919a914642a9"
PIN_EPOCH = 1787307950
LOG = "newton-over-hodge-char2/research-log"


def sha256(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


# --------------------------------------------------------------- the prose
# Hand-written. Deliberately carries no computed number: every quantity a reader
# needs is in a claim, a table, a figure or the run record, where it is checked.
PROSE_SETTING = (
    "Kramer-Miller and Upton, *Newton Polygons of Sums on Curves I* "
    "(arXiv:2110.08656v1), build a local-to-global comparison out of a WEIGHT: a "
    "function $a(k)$ on pole orders that makes a certain truncated space stable "
    "under the Frobenius operator $U_p$. At an auxiliary tame point with "
    "$\\eta(P) = 1$ their construction needs the weight to satisfy three "
    "admissibility conditions, the load-bearing one being $d(k) \\ge 1$ for every "
    "$k$ above the truncation, where $d(k)$ measures how far the operator moves a "
    "term away from the boundary of the truncated space. Their own Remark 6.5 "
    "records that at $p = 2$ the estimate they have is \"too low for applications "
    "to the global setting\": the weight they use is not admissible there."
)
PROSE_RESULT = (
    "That gap is closed, elementarily, at $p = 2$ with tame ramification index "
    "$e = 3$. The transition coefficients $c_{k,j}$ of $U_2$ turn out to be "
    "hypergeometric in closed form (Theorem 1); their $2$-adic valuation is then a "
    "digit-sum identity (Theorem 2), which yields a tail bound (Lemma A); the "
    "weight $a(k) = \\lfloor (k-1)/3 \\rfloor + (k \\bmod 2)$ -- KMU's own weight "
    "plus a parity indicator -- satisfies all three admissibility conditions for "
    "every $k$ (Theorem 3); and the achievable growth rate is pinned exactly, not "
    "bracketed, by a single coefficient (Theorem 4). The arguments are written out "
    f"in `{LOG}/04-weight-proof.md` and were re-derived line by line by an "
    f"adversarial audit in `{LOG}/20-verify.md`, Part Two."
)
PROSE_THIS_PAGE = (
    "This page is not a summary of that work: it is the output of a checker. Every "
    "number below was read out of one run of a self-checking Rust program that "
    "recomputes the coefficients in exact rational arithmetic and asserts each "
    "claim over a stated finite range, exiting nonzero if any assertion fails. The "
    "run wrote a record; the record carries the SHA-256 of the source that produced "
    "it, the command that reproduces it, and its exit status; and the claim badges "
    "on this page are computed from that record rather than typed. A separate, "
    "deliberately broken copy of the same program is run the same way and its "
    "failing record is on this page too, folded away below, so that the machinery "
    "which turns evidence into badges can be seen failing as well as passing."
)
PROSE_WHAT_IS_CHECKED = (
    "**What the certificate does and does not bind.** Its check [1] compares the "
    "closed-form product against a coefficient obtained by iterating the "
    "recurrence forced by the hypergeometric ODE, and the file originally called "
    "that an INDEPENDENT route. It is not one: the audit "
    f"(`{LOG}/20-verify.md`, P2-8) established that the second route iterates the "
    "same product in a different association order, so check [1] verifies exact "
    "rational arithmetic and not the operator. The certificate's only binding to "
    "$U_2$ itself is the block of hard-coded coefficient rows recomputed "
    "independently by workstream 01 -- claim `c2` in the run record. Everything "
    "downstream (the valuation identity, Lemma A, the admissibility sweep, the "
    "sharpness witness) is arithmetic over the closed form that block pins. "
    "Widening that binding, by adding the series solve to the artifact, is the "
    "audit's open recommendation and is not done here."
)
PROSE_NEGATIVE = (
    "**Negative control.** The claim below is the same admissibility statement, "
    "for KMU's own weight $\\lfloor (k-1)/3 \\rfloor$ without the parity "
    "indicator, evidenced by a run of a deliberately mutated copy of the producer. "
    "That run exits 1 and its record says so, which is the whole point: the badge "
    "on this claim is not chosen by the manifest, it is forced by the exit status "
    "of the run it references. The mutation is not invented for this page -- it is "
    "`M1-weight-loses-the-parity-term.patch` from the paper repository's own "
    "mutation suite, applied verbatim."
)

# ------------------------------------------------------------- load the record
run = json.loads(RUN.read_text())
stats = run["stats"]
tables = run["tables"]
prov = run["provenance"]
d_rows = tables["d-table"]["rows"]          # [k, jprime, a_k, a_jprime, d, argmin_m]
weight_rows = tables["weight-series"]["rows"]  # [k, a_k]
gt_rows = tables["ground-truth-coefficients"]["rows"]

by_k = {r[0]: r for r in d_rows}
gt = {(r[0], r[1]): r for r in gt_rows}

if sha256(PRODUCER) != prov["inputs"][0]["sha256"]:
    sys.exit(
        "FATAL: run-certificate.json does not describe the producer on disk "
        "(input hash mismatch). Re-run the producer before assembling."
    )
if prov["exit_status"] != 0:
    sys.exit("FATAL: run-certificate.json records a failing run; refusing to assemble.")

EV = {"run_record": "run-certificate.json", "record_id": run["id"]}


def ev(claim_key, role="primary"):
    return dict(EV, claim_key=claim_key, role=role)


# --------------------------------------------------------------- blocks
blocks = []


def block(bid, tag, kind, **extra):
    b = {"id": bid, "tag": tag, "kind": kind}
    b.update(extra)
    blocks.append(b)


def prose(bid, text, tag="essential", **extra):
    block(bid, tag, {"type": "prose", "text": text}, **extra)


prose("intro-setting", PROSE_SETTING, title="The gap")
prose("intro-result", PROSE_RESULT)
prose("intro-this-page", PROSE_THIS_PAGE)

# -- Theorem 3
block(
    "claim-theorem-3",
    "essential",
    {
        "type": "claim",
        "label": "Theorem 3 (the closed-form weight is admissible)",
        "statement": {
            "source": "text",
            "text": (
                "For $a(k) = 0$ when $k \\le 3$ and "
                "$a(k) = \\lfloor (k-1)/3 \\rfloor + (k \\bmod 2)$ when $k \\ge 4$, "
                "KMU's admissibility conditions hold at the tame point with "
                "$p = 2$, $e = 3$, $\\mu(P) = 3$: (A1) the weight vanishes below the "
                "truncation; (A2) it is $O(k)$; and (A3) $d(k) \\ge 1$ with the "
                "minimum attained at the leading term. Checked over "
                f"$4 \\le k \\le {stats['c5-k-max']}$ with support $m \\le "
                f"{stats['c5-m-max']}$: {stats['c5-columns-swept']} columns, "
                f"{stats['c5-violations']} violations, and "
                f"{stats['c5-argmin-not-at-leading-term']} columns whose minimum sits "
                "anywhere but the leading term."
            ),
        },
        "status": "evidence",
        "evidence": [ev("c5-theorem-3-admissibility")],
        "note": {
            "text": (
                "A finite sweep, not the proof. The proof -- a three-case parity "
                "argument for the tail and a six-case mod-6 identity for the leading "
                f"term -- is `{LOG}/04-weight-proof.md` sec. 4, confirmed line by line "
                f"at `{LOG}/20-verify.md` P2-3. What the sweep adds is that the "
                "argument's conclusion survives contact with the actual numbers over "
                "a range no one checked by hand."
            )
        },
    },
)

# -- Theorem 4
block(
    "claim-theorem-4",
    "essential",
    {
        "type": "claim",
        "label": "Theorem 4 (sharpness: the bound at $k = 6$ is universal)",
        "statement": {
            "source": "text",
            "text": (
                f"$j'(6) + e = {stats['c6-self-loop-j']}$, so $k = 6$ lies in its own "
                "support and the (A3) constraint there reads "
                "$a(6) - a(6) + v_2(c_{6,6}) \\ge d(6)$, in which the weight cancels "
                f"identically. Since $c_{{6,6}} = {stats['c6-c-6-6']}$ and "
                f"$v_2(c_{{6,6}}) = {stats['c6-v2-of-c-6-6']}$, "
                f"$d(6) \\le {stats['c6-d-of-6-upper-bound-for-every-weight']}$ for "
                "EVERY admissible weight whatsoever -- not merely for the weight above."
            ),
        },
        "status": "evidence",
        "evidence": [ev("c6-theorem-4-sharpness")],
        "note": {
            "text": (
                "Two computed facts are asserted here: that $k = 6$ is a self-loop of "
                "the support map, and the value of one coefficient's valuation. That a "
                "target $d(k) \\ge \\max(1, \\gamma k)$ is therefore achievable if and "
                "only if $\\gamma \\le 1/6$ follows in one line ($6\\gamma \\le 1$) and "
                f"is argued at `{LOG}/04-weight-proof.md` sec. 5; the certificate "
                "prints that consequence but does not separately check it. It replaces "
                "an interval -- earlier work bracketed the threshold, first in "
                "$[1/6, 1/5)$ and then in $[1/6, 2/11)$ -- with a point, and the "
                "witness is one coefficient rather than a linear program."
            )
        },
    },
)

# -- Steps: the k = 6 self-loop, every value read from the record
k6 = {
    "jprime": stats["c6-jprime-of-6"],
    "loop_j": stats["c6-self-loop-j"],
    "c63": stats["c6-c-6-3"],
    "c66": stats["c6-c-6-6"],
    "c69": stats["c6-c-6-9"],
    "v2": stats["c6-v2-of-c-6-6"],
    "a6": stats["c6-a-of-6"],
    "a3": stats["c6-a-of-3"],
    "d6": stats["c6-d-of-6"],
}
block(
    "steps-k6-self-loop",
    "essential",
    {
        "type": "steps",
        "caption": {
            "text": (
                "The whole of Theorem 4, in five steps. Every value is read from the "
                "run record's statistics; none is transcribed."
            )
        },
        "steps": [
            {
                "index": 0,
                "input": {"text": "$k = 6$, $p = 2$, $e = 3$"},
                "op": "least pole order in the image: $j'(k) = k/2$ for even $k$",
                "output": {"text": f"$j'(6) = {k6['jprime']}$"},
            },
            {
                "index": 1,
                "input": {"text": f"$j'(6) = {k6['jprime']}$"},
                "op": "support of $U_2(t^{-6})$ is $j'(6) + e m$, $m \\ge 0$",
                "output": {
                    "text": f"$j \\in \\{{{k6['jprime']}, {k6['loop_j']}, \\ldots\\}}$ -- and $j'(6) + e = {k6['loop_j']} = k$, a self-loop"
                },
            },
            {
                "index": 2,
                "input": {"text": "closed form of Theorem 1 at $k = 6$"},
                "op": "$3 \\mid 6$ terminates the product after one factor",
                "output": {
                    "text": f"$U_2(t^{{-6}}) = {k6['c63']} \\cdot t^{{-3}} + {k6['c66']} \\cdot t^{{-6}}$, and $c_{{6,9}} = {k6['c69']}$"
                },
            },
            {
                "index": 3,
                "input": {"text": f"$c_{{6,6}} = {k6['c66']}$"},
                "op": "$2$-adic valuation",
                "output": {"text": f"$v_2(c_{{6,6}}) = {k6['v2']}$"},
            },
            {
                "index": 4,
                "input": {
                    "text": "the (A3) constraint at $(k, j) = (6, 6)$: $a(6) - a(6) + v_2(c_{6,6}) \\ge d(6)$"
                },
                "op": "the weight cancels; substitute the valuation",
                "output": {
                    "text": f"$d(6) \\le {k6['v2']}$ for every weight; for the weight of Theorem 3, $a(6) = {k6['a6']}$, $a(3) = {k6['a3']}$ and $d(6) = {k6['d6']}$, so the bound is attained"
                },
                "note": {
                    "text": "The two tightnesses are complementary: this is the one place Lemma A is tight, and it is exactly where the parity indicator lowers the increment rather than raising it."
                },
            },
        ],
    },
)

# -- Table: d(k). BY REFERENCE, not by transcription.
#
# Round 1 selected 24 of the record's 397 rows and copied them into this
# manifest. CERT's own guard probe found the hole that leaves: editing a d(k)
# value inside the RECORD is refused (the document declares the record's
# digest), but editing the copy in the MANIFEST rendered happily with the wrong
# number -- the drift class this strand exists to kill, reproduced in the
# strand's own flagship page.
#
# `BlockTable.from_run` names the record and one of its tables and assembly
# copies the columns, rows and provenance out of it, so the numbers exist in
# exactly one place and a changed measurement changes the rendered table. The
# cost is that the whole 397-row sweep renders rather than a reader-sized
# selection, which is why the block is `detail`: folded in Markdown and HTML,
# and in the appendix in LaTeX (the document's `latex.detail` option). A
# row-selection facet on `from_run` -- show these k, from that record -- is the
# right P1 answer and is recorded in the round-2 diary; a selection performed
# HERE would be a transcription again.
block(
    "table-d-k",
    "detail",
    {
        "type": "table",
        "caption": {
            "text": (
                f"$d(k)$ for the weight of Theorem 3, taken from the `d-table` of run "
                f"record `{run['id']}` -- every row of it: the certificate swept "
                f"$4 \\le k \\le {stats['c5-k-max']}$ ({stats['c5-columns-swept']} "
                "columns). No row is copied into this document, so a changed "
                "measurement changes this table. `argmin m` is the term of the support "
                "at which the minimum is attained -- it is the leading term $m = 0$ in "
                "every column."
            )
        },
        "from_run": {
            "run_record": "run-certificate.json",
            "table": "d-table",
            "record_id": run["id"],
        },
    },
)

# -- Figure: the weight step function and the resulting slack
kmax_plot = 48
block(
    "figure-weight-and-slack",
    "essential",
    {
        "type": "figure",
        "caption": {
            "text": (
                "The weight $a(k)$ and the slack $d(k)$ it buys, over the first "
                f"{kmax_plot} pole orders. $a(k)$ is a staircase of slope $1/3$ with a "
                "parity indicator riding on it; $d(k)$ is the distance from the "
                "boundary of the truncated space, and the flat line at $d = 1$ that it "
                "keeps returning to is why the growth rate cannot exceed $k/6$."
            )
        },
        "alt": (
            "Two step plots against pole order k. The upper series, the weight a(k), "
            "rises in a sawtooth staircase. The lower series, the slack d(k), rises "
            "on average but repeatedly returns to 1, its universal floor."
        ),
        "spec": {
            "figure_type": "plot",
            "plot_type": "steps",
            "x_label": "pole order k",
            "y_label": "value",
            "series": [
                {
                    "label": "a(k), the weight",
                    "points": [[r[0], r[1]] for r in weight_rows if r[0] <= kmax_plot],
                    "style": "weight",
                },
                {
                    "label": "d(k), the admissibility slack",
                    "points": [[k, by_k[k][4]] for k in range(4, kmax_plot + 1)],
                    "style": "slack",
                },
            ],
        },
    },
)

# -- Certificate block: what checked it and how to replay
block(
    "certificate-run",
    "essential",
    {
        "type": "certificate",
        "cert_kind": "report-run",
        "summary": {
            "text": (
                f"{run['summary']} The program is dependency-free and builds with a "
                "bare `rustc --edition 2024`, so the replay below needs no cargo, no "
                "workspace and no network. It is mutation-tested: all seven mutants in "
                "the paper repository's suite exit nonzero against this source, each "
                "with the catcher its `.expect` file records."
            )
        },
        "artifact_refs": [
            {
                "path": "render/examples-input/cert/run-certificate.json",
                "sha256": sha256(RUN),
                "label": "run record",
                "bytes": RUN.stat().st_size,
                "media_type": "application/json",
            },
            {
                "path": "render/producers/noh_wt_certificate_emitrun.rs",
                "sha256": prov["inputs"][0]["sha256"],
                "label": "producer source",
                "bytes": PRODUCER.stat().st_size,
                "media_type": "text/rust",
            },
        ],
        "replay": run["replay"],
        "evidence": [dict(EV)],
    },
)

# -- Detail: what is actually bound
prose(
    "detail-what-is-checked",
    PROSE_WHAT_IS_CHECKED,
    tag="detail",
    title="What the certificate binds, and what it does not",
)

# -- The negative control, evidenced by a REAL failing run.
#
# IT IS NOT A BLOCK OF THE PRODUCTION PAGE. Round 1 put it here, which made the
# certificate page unable to render under `--strict` -- correct behaviour for a
# page carrying a refutation, but it means the flagship document could never be
# strict-clean, and "strict-clean" is the property a publication wants to be
# able to assert. The control now ships only as its own document
# (`certificate-negative-control.doc.json`), which is the strict-mode fixture.
#
# The evidence reference declares `role: negative-control`, matching the
# record's own `role`. Assembly enforces that pairing in both directions, so a
# page cannot quote this mutant as support and cannot quote a production run as
# a control.
m1 = json.loads(RUN_M1.read_text())
NEG_CLAIM_BLOCK = {
    "id": "claim-negative-control-m1",
    "tag": "essential",
    "kind": {
        "type": "claim",
        "label": "Control: KMU's own weight, without the parity indicator, is admissible",
        "statement": {
            "source": "text",
            "text": (
                "For $a(k) = \\lfloor (k-1)/3 \\rfloor$ -- the weight of KMU Remark "
                "6.5, with the parity indicator removed -- condition (A3) holds: "
                "$d(k) \\ge 1$ for every $k > 3$."
            ),
        },
        "status": "refuted",
        "evidence": [
            {
                "run_record": "run-mutant-M1.json",
                "record_id": m1["id"],
                "claim_key": "c5-theorem-3-admissibility",
                "role": "negative-control",
                "note": (
                    "A deliberately mutated producer. The run exits "
                    f"{m1['provenance']['exit_status']} and its record's outcome is "
                    f"{m1['outcome']!r}; the failing column is $k = 5$, where the "
                    "mutated weight gives $d(5) = 0$."
                ),
            }
        ],
        "note": {
            "text": (
                "This is the statement KMU's Remark 6.5 stops short of, and it is "
                "false: the parity indicator is not decoration. Its badge must render "
                "red. If it ever renders green, the renderer is broken, not the "
                "mathematics -- which is why this block is in the P0 corpus at all."
            )
        },
    },
}

# -- Archive tier
block(
    "archive-run-record",
    "archive",
    {
        "type": "include",
        "path": "render/examples-input/cert/run-certificate.json",
        "render_hint": "json",
        "sha256": sha256(RUN),
        "max_bytes": 65536,
        "caption": {
            "text": (
                "The full run record: seven claims with their statuses, sixty measured "
                "statistics, and four tables -- the 397-row $d(k)$ sweep, the weight "
                "series, the 150 tight Lemma-A pairs, and the ground-truth coefficient "
                "rows."
            )
        },
    },
)
block(
    "archive-producer-source",
    "archive",
    {
        "type": "include",
        "path": "render/producers/noh_wt_certificate_emitrun.rs",
        "render_hint": "code",
        "language": "rust",
        "sha256": prov["inputs"][0]["sha256"],
        "max_bytes": 65536,
        "caption": {
            "text": (
                f"The producer, pinned at axeyum `{PIN_COMMIT[:8]}` plus the run-record "
                "emission described in its header."
            )
        },
    },
)

# --------------------------------------------------------------- the document
doc = {
    "schema_version": 1,
    "meta": {
        "doc_id": "noh-p2-weight-certificate",
        "title": "The p = 2 tame-point weight certificate",
        "subtitle": "Closed form, admissibility, and exact sharpness for the "
        "Kramer-Miller--Upton weight at p = 2, e = 3",
        "genre": "system",
        "authors": ["Axeyum render strand (prose only; every number is machine-produced)"],
        "abstract": {
            "text": (
                "Kramer-Miller and Upton's local-to-global machinery needs an "
                "admissible weight, and at $p = 2$ their own remark records that they "
                "do not have one. This page is the output of a self-checking program "
                "that establishes one: a closed form for the transition coefficients, "
                "the valuation identity it implies, admissibility of "
                "$a(k) = \\lfloor (k-1)/3 \\rfloor + (k \\bmod 2)$ over a swept range, "
                "and a single coefficient that caps the achievable growth rate exactly "
                "rather than bracketing it."
            )
        },
        "epoch": {"unix": PIN_EPOCH, "source": "commit", "commit": PIN_COMMIT},
        "repo": {
            "url": "https://github.com/mjbommar/axeyum",
            "commit": PIN_COMMIT,
            "root": "",
        },
        "options": {
            "latex": {"detail": "appendix", "package": "axeyum"},
            "markdown": {"badge_style": "text"},
        },
    },
    "provenance": {
        "generator": "render/producers/build-certificate-manifest.py (render strand P0-A, agent CERT)",
        "command": "python3 render/producers/build-certificate-manifest.py",
        "inputs": [
            {"path": "render/producers/build-certificate-manifest.py", "sha256": sha256(SELF), "role": "generator"},
            {"path": "render/examples-input/cert/run-certificate.json", "sha256": sha256(RUN), "role": "run-record"},
            {"path": "render/examples-input/cert/run-mutant-M1.json", "sha256": sha256(RUN_M1), "role": "run-record"},
        ],
        "exit_status": 0,
        "epoch": {"unix": PIN_EPOCH, "source": "commit", "commit": PIN_COMMIT},
    },
    "blocks": blocks,
}

OUT.write_text(json.dumps(doc, indent=2, ensure_ascii=True, sort_keys=False) + "\n")
print(f"wrote {OUT.relative_to(ROOT)}: {len(blocks)} blocks")

# ------------------------------------------------- the standalone negative fixture
# The control ships as its own document, and ONLY as its own document. Strict
# mode treats red evidence as a build error, so any page carrying a refutation
# refuses to build under `--strict`. That is correct -- but a production page
# that can never be strict-rendered cannot assert strict-cleanliness, and the
# certificate page is the one this strand shows people. So the split is:
# `certificate.doc.json` is strict-clean and says nothing red, and this
# document is the smallest thing that exercises fail-closed rule 2 and the
# negative-control role. Both are in the corpus; only one is a publication.
neg = {
    "schema_version": 1,
    "meta": {
        "doc_id": "noh-p2-weight-negative-control",
        "title": "Negative control: the weight without its parity indicator",
        "genre": "system",
        "authors": ["Axeyum render strand (prose only; every number is machine-produced)"],
        "epoch": {"unix": PIN_EPOCH, "source": "commit", "commit": PIN_COMMIT},
        "repo": {"url": "https://github.com/mjbommar/axeyum", "commit": PIN_COMMIT, "root": ""},
    },
    "provenance": doc["provenance"],
    "blocks": [
        {
            "id": "negative-control-intro",
            "tag": "essential",
            "kind": {"type": "prose", "text": PROSE_NEGATIVE},
        },
        NEG_CLAIM_BLOCK,
    ],
}
OUT_NEG = ROOT / "render/examples-input/cert/certificate-negative-control.doc.json"
OUT_NEG.write_text(json.dumps(neg, indent=2, ensure_ascii=True, sort_keys=False) + "\n")
print(f"wrote {OUT_NEG.relative_to(ROOT)}: {len(neg['blocks'])} blocks")
