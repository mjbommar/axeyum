#!/usr/bin/env python3
"""Validate and render the proposed SMT-LIB session contract.

The JSON artifact contains declarative transcript fixtures.  This script runs
them through a deliberately small reference state machine and compares every
event byte-for-byte.  It is a planning prototype, not the production parser or
solver: its purpose is to freeze lifecycle, ordering, option, scope, and error
atomicity obligations before Rust implementation starts.
"""

from __future__ import annotations

import argparse
import copy
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "docs" / "plan" / "smtlib-session-contract-v1.json"
OUT_MD = ROOT / "docs" / "plan" / "generated" / "smtlib-session-contract.md"

MODES = {"start", "assert", "sat", "unsat", "terminated"}
START_ONLY_OPTIONS = {
    ":global-declarations",
    ":produce-assertions",
    ":produce-assignments",
    ":produce-models",
    ":produce-proofs",
    ":produce-unsat-assumptions",
    ":produce-unsat-cores",
    ":random-seed",
}
DEFAULT_OPTIONS: dict[str, Any] = {
    ":diagnostic-output-channel": "stderr",
    ":global-declarations": False,
    ":print-success": False,
    ":produce-assertions": False,
    ":produce-assignments": False,
    ":produce-models": False,
    ":produce-proofs": False,
    ":produce-unsat-assumptions": False,
    ":produce-unsat-cores": False,
    ":random-seed": 0,
    ":regular-output-channel": "stdout",
    ":reproducible-resource-limit": 0,
    ":verbosity": 0,
}


@dataclass
class State:
    mode: str = "start"
    epoch: int = 0
    logic: str | None = None
    options: dict[str, Any] = field(default_factory=lambda: copy.deepcopy(DEFAULT_OPTIONS))
    infos: dict[str, Any] = field(default_factory=dict)
    levels: list[set[str]] = field(default_factory=lambda: [set()])
    global_declarations: set[str] = field(default_factory=set)
    assertions: list[int] = field(default_factory=lambda: [0])
    query_id: int = 0
    last_query: int | None = None
    last_assumptions: tuple[str, ...] = ()

    def visible(self, symbol: str) -> bool:
        return symbol in self.global_declarations or any(
            symbol in level for level in self.levels
        )


def load_manifest() -> dict[str, Any]:
    with MANIFEST.open(encoding="utf-8") as handle:
        return json.load(handle)


def response_token(
    index: int,
    before: str,
    after: str,
    response: str,
    payload: str | None = None,
    channel: str | None = None,
) -> str:
    token = f"{index}:{before}>{after}:{response}"
    if payload is not None:
        token += f"={payload}"
    if channel is not None:
        token += f"@{channel}"
    return token


def canonical_value(value: Any) -> str:
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, str):
        return json.dumps(value, ensure_ascii=False)
    return str(value)


def success_response(state: State) -> tuple[str, str | None, str | None]:
    if state.options[":print-success"]:
        return "success", None, state.options[":regular-output-channel"]
    return "none", None, None


def error_response(state: State, reason: str) -> tuple[str, str, str]:
    return "error", reason, state.options[":regular-output-channel"]


def specific_response(
    state: State, kind: str, payload: str | None = None
) -> tuple[str, str | None, str]:
    return kind, payload, state.options[":regular-output-channel"]


def invalidate_query(state: State) -> None:
    state.mode = "assert" if state.logic is not None else "start"
    state.last_query = None
    state.last_assumptions = ()


def command_text(command: dict[str, Any]) -> str:
    op = command["op"]
    if op == "set-option":
        return f"(set-option {command['key']} {canonical_value(command['value'])})"
    if op == "get-option":
        return f"(get-option {command['key']})"
    if op == "set-info":
        return f"(set-info {command['key']} {canonical_value(command['value'])})"
    if op == "get-info":
        return f"(get-info {command['key']})"
    if op == "set-logic":
        return f"(set-logic {command['logic']})"
    if op == "declare":
        return f"(declare-const {command['name']} Bool)"
    if op == "assert-ref":
        return f"(assert {command['symbol']})"
    if op == "assert":
        return "(assert true)"
    if op in {"push", "pop"}:
        return f"({op} {command.get('count', 1)})"
    if op == "check":
        assumptions = command.get("assumptions", [])
        if assumptions:
            return f"(check-sat-assuming ({' '.join(assumptions)})) ; {command['result']}"
        return f"(check-sat) ; {command['result']}"
    if op == "get-value":
        return "(get-value (true))"
    if op == "echo":
        return f"(echo {json.dumps(command['text'])})"
    if op == "unsupported":
        return f"({command['name']})"
    return f"({op})"


def execute(state: State, command: dict[str, Any]) -> tuple[str, str | None, str | None]:
    op = command["op"]

    if op == "set-option":
        key = command["key"]
        if key not in DEFAULT_OPTIONS:
            return specific_response(state, "unsupported")
        if key in START_ONLY_OPTIONS and state.mode != "start":
            return error_response(state, "start-only-option")
        state.options[key] = command["value"]
        return success_response(state)

    if op == "get-option":
        key = command["key"]
        if key not in state.options:
            return specific_response(state, "unsupported")
        return specific_response(state, "option", canonical_value(state.options[key]))

    if op == "set-info":
        state.infos[command["key"]] = command["value"]
        return success_response(state)

    if op == "get-info":
        key = command["key"]
        if key == ":error-behavior":
            value = "continued-execution"
        else:
            value = state.infos.get(key)
            if value is None:
                return specific_response(state, "unsupported")
            value = canonical_value(value)
        return specific_response(state, "info", value)

    if op == "set-logic":
        if state.mode != "start":
            return error_response(state, "wrong-mode")
        state.logic = command["logic"]
        state.mode = "assert"
        return success_response(state)

    if op == "declare":
        if state.mode not in {"assert", "sat", "unsat"}:
            return error_response(state, "wrong-mode")
        name = command["name"]
        if state.visible(name):
            return error_response(state, "duplicate-symbol")
        if state.options[":global-declarations"]:
            state.global_declarations.add(name)
        else:
            state.levels[-1].add(name)
        invalidate_query(state)
        return success_response(state)

    if op in {"assert", "assert-ref"}:
        if state.mode not in {"assert", "sat", "unsat"}:
            return error_response(state, "wrong-mode")
        if op == "assert-ref" and not state.visible(command["symbol"]):
            return error_response(state, "symbol-out-of-scope")
        state.assertions[-1] += 1
        invalidate_query(state)
        return success_response(state)

    if op == "push":
        if state.mode not in {"assert", "sat", "unsat"}:
            return error_response(state, "wrong-mode")
        count = command.get("count", 1)
        for _ in range(count):
            state.levels.append(set())
            state.assertions.append(0)
        invalidate_query(state)
        return success_response(state)

    if op == "pop":
        if state.mode not in {"assert", "sat", "unsat"}:
            return error_response(state, "wrong-mode")
        count = command.get("count", 1)
        if count >= len(state.levels):
            return error_response(state, "pop-underflow")
        for _ in range(count):
            state.levels.pop()
            state.assertions.pop()
        invalidate_query(state)
        return success_response(state)

    if op == "reset-assertions":
        state.levels = [set()]
        state.assertions = [0]
        invalidate_query(state)
        return success_response(state)

    if op == "reset":
        old_print_success = state.options[":print-success"]
        old_channel = state.options[":regular-output-channel"]
        next_epoch = state.epoch + 1
        state.__dict__.update(State(epoch=next_epoch).__dict__)
        if old_print_success:
            return "success", None, old_channel
        return "none", None, None

    if op == "check":
        if state.mode not in {"assert", "sat", "unsat"}:
            return error_response(state, "wrong-mode")
        result = command["result"]
        if result not in {"sat", "unsat", "unknown"}:
            return error_response(state, "invalid-prototype-result")
        state.query_id += 1
        state.last_query = state.query_id
        state.last_assumptions = tuple(command.get("assumptions", []))
        state.mode = "unsat" if result == "unsat" else "sat"
        return specific_response(state, result)

    if op in {"get-model", "get-value", "get-assignment"}:
        if state.mode != "sat" or state.last_query is None:
            return error_response(state, "wrong-mode")
        option = {
            "get-model": ":produce-models",
            "get-value": ":produce-models",
            "get-assignment": ":produce-assignments",
        }[op]
        if not state.options[option]:
            return error_response(state, "option-not-enabled")
        kind = {"get-model": "model", "get-value": "values", "get-assignment": "assignment"}[op]
        return specific_response(state, kind, f"query-{state.last_query}")

    if op == "get-assertions":
        if state.mode not in {"assert", "sat", "unsat"}:
            return error_response(state, "wrong-mode")
        if not state.options[":produce-assertions"]:
            return error_response(state, "option-not-enabled")
        return specific_response(state, "assertions", str(sum(state.assertions)))

    if op in {"get-proof", "get-unsat-core", "get-unsat-assumptions"}:
        if state.mode != "unsat" or state.last_query is None:
            return error_response(state, "wrong-mode")
        option = {
            "get-proof": ":produce-proofs",
            "get-unsat-core": ":produce-unsat-cores",
            "get-unsat-assumptions": ":produce-unsat-assumptions",
        }[op]
        if not state.options[option]:
            return error_response(state, "option-not-enabled")
        if op == "get-proof" and state.last_assumptions:
            return error_response(state, "proof-after-assumptions")
        kind = {
            "get-proof": "proof",
            "get-unsat-core": "unsat-core",
            "get-unsat-assumptions": "unsat-assumptions",
        }[op]
        return specific_response(state, kind, f"query-{state.last_query}")

    if op == "echo":
        return specific_response(state, "echo", json.dumps(command["text"]))

    if op == "unsupported":
        return specific_response(state, "unsupported")

    if op == "exit":
        response = success_response(state)
        state.mode = "terminated"
        return response

    return error_response(state, "unknown-prototype-command")


def run_fixture(fixture: dict[str, Any]) -> list[str]:
    state = State()
    events: list[str] = []
    for index, command in enumerate(fixture["commands"]):
        if state.mode == "terminated":
            break
        semantic_before = copy.deepcopy(state)
        before = state.mode
        response, payload, channel = execute(state, command)
        if response in {"error", "unsupported"} and state != semantic_before:
            raise AssertionError(
                f"{fixture['id']} command {index}: {response} mutated session state"
            )
        if state.mode not in MODES:
            raise AssertionError(f"invalid state mode after command: {state.mode}")
        events.append(
            response_token(index, before, state.mode, response, payload, channel)
        )
    return events


def validate_manifest(data: dict[str, Any]) -> list[str]:
    failures: list[str] = []
    if data.get("version") != 1:
        failures.append("manifest version must be 1")
    standard = data.get("standard", {})
    if standard.get("version") != "2.7" or not standard.get("url"):
        failures.append("standard must pin SMT-LIB 2.7 and its official URL")

    invariants = data.get("invariants", [])
    invariant_ids = [item.get("id") for item in invariants]
    if len(set(invariant_ids)) != len(invariant_ids):
        failures.append("invariant ids must be unique")
    for item in invariants:
        for key in ("id", "rule", "source", "implementation_gate"):
            if not item.get(key):
                failures.append(f"invariant {item.get('id', '<unknown>')} missing {key}")

    source_cache: dict[Path, str] = {}
    for finding in data.get("implementation_findings", []):
        finding_id = finding.get("id", "<unknown>")
        path = ROOT / finding.get("path", "")
        if not path.is_file():
            failures.append(f"{finding_id}: missing source {path}")
            continue
        text = source_cache.setdefault(path, path.read_text(encoding="utf-8"))
        for marker in finding.get("contains", []):
            if marker not in text:
                failures.append(f"{finding_id}: {path.relative_to(ROOT)} missing {marker!r}")
        for marker in finding.get("excludes", []):
            if marker in text:
                failures.append(
                    f"{finding_id}: {path.relative_to(ROOT)} unexpectedly contains {marker!r}"
                )

    fixtures = data.get("fixtures", [])
    fixture_ids = [fixture.get("id") for fixture in fixtures]
    if len(set(fixture_ids)) != len(fixture_ids):
        failures.append("fixture ids must be unique")
    for fixture in fixtures:
        fixture_id = fixture.get("id", "<unknown>")
        if not fixture.get("purpose") or not fixture.get("commands"):
            failures.append(f"{fixture_id}: purpose and commands are required")
            continue
        actual = run_fixture(fixture)
        expected = fixture.get("expected")
        if actual != expected:
            failures.append(
                f"{fixture_id}: transcript mismatch\n"
                f"  expected={expected}\n"
                f"  actual={actual}"
            )
    return failures


def md_escape(value: str) -> str:
    return value.replace("|", "\\|").replace("\n", " ")


def render(data: dict[str, Any]) -> str:
    fixtures = data["fixtures"]
    command_count = sum(len(fixture["commands"]) for fixture in fixtures)
    error_count = sum(
        event.split(":", 3)[-1].startswith("error")
        for fixture in fixtures
        for event in fixture["expected"]
    )
    lines = [
        "# SMT-LIB session contract prototype",
        "",
        "> **Generated; do not edit by hand.** Source: "
        "[`docs/plan/smtlib-session-contract-v1.json`](../smtlib-session-contract-v1.json). "
        "Regenerate with `python3 scripts/gen-smtlib-session-contract.py`; use "
        "`--check` in validation.",
        "",
        "This is an executable planning model for command ordering, modes, options, "
        "declaration scope, query snapshots, output routing, reset, and error atomicity. "
        "It does not solve formulas and is not production SMT-LIB code.",
        "",
        "## Snapshot",
        "",
        f"- {len(data['invariants'])} contract invariants.",
        f"- {len(fixtures)} deterministic transcript fixtures / {command_count} commands.",
        f"- {error_count} expected fail-closed command errors with continued execution.",
        f"- Standard pin: SMT-LIB {data['standard']['version']} "
        f"({data['standard']['release']}).",
        "",
        "## Invariants",
        "",
        "| ID | Rule | Standard source | Rust implementation gate |",
        "|---|---|---|---|",
    ]
    for invariant in data["invariants"]:
        lines.append(
            "| {id} | {rule} | {source} | {gate} |".format(
                id=md_escape(invariant["id"]),
                rule=md_escape(invariant["rule"]),
                source=md_escape(invariant["source"]),
                gate=md_escape(invariant["implementation_gate"]),
            )
        )

    lines.extend(
        [
            "",
            "## Current implementation findings",
            "",
            "| Finding | Current source fact | Consequence |",
            "|---|---|---|",
        ]
    )
    for finding in data["implementation_findings"]:
        lines.append(
            f"| `{md_escape(finding['id'])}` | "
            f"`{md_escape(finding['path'])}`: {md_escape(finding['fact'])} | "
            f"{md_escape(finding['consequence'])} |"
        )

    lines.extend(
        [
            "",
            "## Transcript fixtures",
            "",
            "Event tokens are `index:before>after:response[=payload][@channel]`. "
            "A `none` response deliberately has no channel. Commands after a successful "
            "`exit` produce no event.",
            "",
            "| Fixture | Purpose | Commands | Expected events |",
            "|---|---|---|---|",
        ]
    )
    for fixture in fixtures:
        commands = "<br>".join(
            f"`{md_escape(command_text(command))}`" for command in fixture["commands"]
        )
        events = "<br>".join(f"`{md_escape(event)}`" for event in fixture["expected"])
        lines.append(
            f"| `{md_escape(fixture['id'])}` | {md_escape(fixture['purpose'])} | "
            f"{commands} | {events} |"
        )

    lines.extend(
        [
            "",
            "## Prototype boundary",
            "",
            "The reference model intentionally does not parse terms, invoke a solver, "
            "serialize models/proofs, or write files. Production work must preserve these "
            "control-plane traces while replacing placeholder payloads such as `query-1` "
            "with replay-checked typed results and canonical SMT-LIB rendering.",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()

    data = load_manifest()
    failures = validate_manifest(data)
    if failures:
        for failure in failures:
            print(f"SMTLIB_SESSION_CONTRACT_ERROR|{failure}", file=sys.stderr)
        return 1

    rendered = render(data)
    if args.check:
        if not OUT_MD.is_file() or OUT_MD.read_text(encoding="utf-8") != rendered:
            print(
                f"SMTLIB_SESSION_CONTRACT_ERROR|generated drift: {OUT_MD.relative_to(ROOT)}",
                file=sys.stderr,
            )
            return 1
    else:
        OUT_MD.parent.mkdir(parents=True, exist_ok=True)
        OUT_MD.write_text(rendered, encoding="utf-8")

    command_count = sum(len(fixture["commands"]) for fixture in data["fixtures"])
    print(
        "SMTLIB_SESSION_CONTRACT|"
        f"invariants={len(data['invariants'])}|"
        f"fixtures={len(data['fixtures'])}|"
        f"commands={command_count}|"
        "mismatches=0"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
