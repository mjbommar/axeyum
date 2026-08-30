#!/usr/bin/env python3
"""Validate `artifacts/facts/*.json` against fact.schema.json and its semantics.

Structural validation is deliberately local (no `jsonschema` dependency), matching
`validate-claims.py` and `validate-smt-fragment-atlas.py`.

The semantic rules are the point. A schema can say a fact HAS a status and HAS an
evidence array; only these rules say the two must agree:

  * `proved` / `computed` / `refuted` require evidence that was actually checked.
    A status asserting something was established, with nothing establishing it, is
    the defect this whole repository is built to prevent.
  * `proved` requires an `axiom_footprint`. An EMPTY array means axiom-free and is
    a strictly stronger claim than an absent field, so the absence must not read as
    the strong case.
  * `open` requires an EMPTY evidence array. An open fact carrying evidence is a
    contradiction, and the empty array is a statement rather than an omission.
  * `depends_on` must resolve to facts that exist. A dependency DAG with dangling
    edges is not a build order.
  * `claim-ref` evidence must point at a claim file that exists, since that is how
    a computed value becomes evidence for a proposition.
  * `external_status` of `proved` or `refuted` requires a `provenance.prior_art`
    citation. Asserting that mathematics has settled something, without saying who
    settled it, is an unverifiable claim about the literature -- and this project
    has already published one round of Zenodo self-deposits as though they were
    refereed results.
  * A settled fact must name its `proof_route`, and `axiom_footprint: []` is
    rejected on any route that cannot deliver axiom-freedom. Two incompatible
    footprint vocabularies were already coexisting -- 17 facts with `[]` from the
    kernel and 14 with `["axeyum-ir.bool-evaluator", ...]` from the SMT route,
    strings a lane invented because the schema offered none. Read side by side
    the first group looks like it rests on less. It does not; the two are
    different trust bases, and the routes are not even equally strong (the logic
    prelude is intuitionistic, so excluded middle is provable on the SMT route
    and unreachable in the kernel without a new axiom). Reporting one total
    across routes would restate exactly that error, so axiom-freedom is counted
    only where it is measurable.

It also REPORTS, without failing, any fact we have established that the wider
literature has not. That combination is not an error; it is the output this
project exists to produce, and a gate that stays silent about it is measuring
the wrong thing.

Like the claims checker, this prints what it examined and names what it could not
check rather than passing it silently.
"""

from __future__ import annotations

import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
FACTS = ROOT / "artifacts" / "facts"
SCHEMA = ROOT / "artifacts" / "ontology" / "fact.schema.json"
DEPENDS_DERIVED_SCRIPT = ROOT / "scripts" / "check-fact-depends-derived.py"

ID_RE = re.compile(r"^F:[a-z0-9]+(-[a-z0-9]+)*$")
# Same namespace class `theorem_of` (scripts/check-fact-depends-derived.py) reads
# checker_commands with, plus `null` for "explicitly no single subject" -- see
# `formal.kernel_theorem` in fact.schema.json. A garbage string here would be
# silently treated as a theorem name by every `theorem_of` consumer and would
# never be caught, since nothing else reads this field.
# `axeyum.string.<N>` is the string prelude's ACTUAL namespace -- the alphabet
# size is a name component, so `build_string_prelude(k, logic, 2)` declares
# `axeyum.string.2.append_assoc`. The allowlist below includes all actual
# kernel theorem namespaces (And, Decidable, Eq, Iff, Or added; Str was never used).
#
# The logic prelude also declares undotted names (bare identifiers), allowed
# by a separate LOGIC_UNDOTTED set. Widening to accept any bare identifier
# would weaken the typo guard this regex provides for other theorems; restricting
# to only these logic-prelude names maintains that guard while registering real
# declarations the kernel admits.
KERNEL_THEOREM_RE = re.compile(
    r"^(?:AxReal|AxNat|Nat|Int|Real|Rat|List|Bool|Prop|Acc|WellFounded|"
    r"And|Decidable|Eq|Iff|Or|"
    r"CReal|Complex|CPoint|axeyum\.string\.[0-9]+)"
    r"(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)

# Logic prelude declarations that are not namespaced (bare names from build_logic_prelude).
# These are the ONLY undotted names permitted in formal.kernel_theorem to avoid
# weakening the typo guard on dotted names. Verified from kernel.environment() 2026-08-27.
LOGIC_UNDOTTED = {
    'congrFun\'',
    'demorgan_not_or',
    'demorgan_not_or_converse',
    'demorgan_or_not_and',
    'dne_of_em',
    'em_of_dne',
    'em_of_peirce',
    'mt',
    'noncontradiction',
    'not_not_and',
    'not_not_em',
    'not_not_imp',
    'not_not_intro',
    'not_not_not',
    'not_not_not_intro',
    'peirce_of_em',
}

REQUIRED = {"schema_version", "id", "title", "statement", "formal",
            "epistemic_status", "depends_on", "evidence", "provenance"}
STATUSES = {"axiom", "proved", "computed", "empirical", "conjectured", "open", "refuted"}
EXTERNAL_STATUSES = {"proved", "refuted", "conjectured", "open", "unknown"}
# What the wider literature has settled. Asserting one of these means asserting
# something about the world, so it has to name a source.
EXTERNAL_SETTLED = {"proved", "refuted"}
# What WE established. Paired with an unsettled external status, this is novelty.
OURS_SETTLED = {"proved", "computed", "refuted"}
LANGUAGES = {"smtlib2", "lean4", "axeyum-ir"}
EVIDENCE_KINDS = {"kernel-term", "witness-replay", "unsat-certificate", "cube-cover",
                  "cube-tree-cover", "exhaustive-enumeration", "published-value-replication",
                  "bound-citation", "instance-pin", "claim-ref"}
CHECK_STATUSES = {"checked", "replay-only", "not-checked"}
LANGUAGES_ALL = {
    "smtlib2",
    "lean4",
    "lean4-surface",
    "axeyum-ir",
    "cas-term",
    "certificate-spec",
}
# `cas-certificate` is the computer-algebra route: an identity in Q(vars) re-derived
# by exact polynomial arithmetic that shares no code with the search that found it.
# It is deliberately NOT `search-certificate`: a replayed witness settles one finite
# instance, while a polynomial identity settles every instance at once, and their
# footprints differ in kind rather than in size.
# `imported-kernel-lean` passes through the SAME trusted gate as `kernel-lean`
# (`Kernel::add_declaration` re-derives the type from the proof term), and is a
# separate route anyway, for two reasons. (1) Authorship: a `kernel-lean` fact is
# one this project constructed a proof of, which is the number the self-extension
# loop exists to raise; an import raises no such number, and one shared label
# would let the headline count be inflated by ingestion. (2) Trust base: an
# import additionally assumes the exporter rendered the source environment
# faithfully, that our wire translation preserves meaning, and that the delivered
# bytes are the producer's intended export -- format 3.1 has no footer, so
# completion is relative to the bytes handed over. So `[]` is unavailable here.
ROUTES = {"kernel-lean", "imported-kernel-lean", "smt-term-level", "smt-clausal",
          "search-certificate", "cas-certificate", "none"}
# Only this route can deliver axiom-freedom, because only there does an empty
# footprint correspond to a measurable fact about a kernel environment.
AXIOM_FREE_CAPABLE = {"kernel-lean"}
# Routes on which the proof term was NOT authored here. Reported separately from
# the constructed count for exactly the reason above.
IMPORTED_ROUTES = {"imported-kernel-lean"}

# A status that asserts the statement was settled must be backed by something.
ESTABLISHED = {"proved", "computed", "refuted"}


def fail(errors: list[str], msg: str) -> None:
    errors.append(msg)


def kernel_theorem_is_valid(value: object) -> bool:
    """`formal.kernel_theorem`: `None` (an explicit "no single kernel theorem",
    for a package-level fact), a dotted namespaced kernel theorem name that
    `theorem_of` (scripts/check-fact-depends-derived.py) could plausibly have
    extracted itself, or an undotted logic prelude name.

    The undotted allowlist (LOGIC_UNDOTTED) is restricted to declarations the
    kernel actually admits, preserving the typo-catching function of the dotted
    regex for other theorem names. Anything outside these two forms is a value
    none of that field's consumers could use, and nothing else in the ledger
    would catch it."""
    if value is None:
        return True
    if not isinstance(value, str):
        return False
    return bool(KERNEL_THEOREM_RE.match(value)) or value in LOGIC_UNDOTTED


_GREP_INVOCATION_RE = re.compile(r"\bgrep\b((?:\s+(?:-[a-zA-Z]+|--[a-zA-Z-]+))*)")


def checker_command_uses_grep_dash_q(cmd: str) -> bool:
    """True if `cmd` invokes `grep` with a quiet flag (`-q`, `-qE`, `-Eq`,
    `--quiet`, or `-q`/`-E` as separate tokens) anywhere in a pipeline.

    Matches short-option clusters in ANY order (so `-qE` and `-Eq` both hit)
    and flags given as separate tokens (`-q -E`), not just one bundled
    cluster -- a narrower check that only caught the bundled form would leave
    the idiom's other spellings free to reappear.
    """
    for m in _GREP_INVOCATION_RE.finditer(cmd):
        flags = re.findall(r"(?:-[a-zA-Z]+|--[a-zA-Z-]+)", m.group(1))
        for f in flags:
            if f == "--quiet":
                return True
            if f.startswith("-") and not f.startswith("--") and "q" in f[1:]:
                return True
    return False


_GREP_QUOTED_PATTERN_RE = re.compile(r"\bgrep\b(?:\s+(?:-[a-zA-Z]+|--[a-zA-Z-]+))*\s+'([^']*)'")


def checker_command_uses_grep_backslash_t(cmd: str) -> bool:
    """True if `cmd` passes `grep` a single-quoted pattern containing the
    two-character escape `\\t`.

    In POSIX ERE (and BRE), `\\t` is NOT a tab -- GNU grep drops the backslash
    and matches a literal `t`. Measured on this host with `/usr/bin/grep`
    (GNU grep 3.12): `printf 'a\\tb\\n' | grep -cE 'a\\tb'` -> 0 (a real tab
    does not match), `printf 'atb\\n' | grep -cE 'a\\tb'` -> 1 (it matches the
    literal 't' instead). 54 facts / 68 checker_commands carried this before
    2026-08-25's rewrite to `[[:space:]]`, all silently reporting a PRESENT
    theorem as ABSENT -- fail-closed, not a wrong verdict, but the evidence
    does not re-derive under any script or CI run.

    Why it went unnoticed: on a host where an interactive shell's `grep` is a
    function wrapping `ugrep` (which DOES interpret `\\t` as a tab), the exact
    same checker_command passes by hand and fails from a script. Always test
    a fix with `/usr/bin/grep` explicitly, never a bare `grep`.

    Catches `\\t` both as a standalone separator (`'^Name\\t'`, fix:
    `[[:space:]]`) and inside a bracket expression (`'[^\\t]'`, fix:
    `[^[:space:]]` -- backslash is not special inside `[...]` either, so
    `[^\\t]` means "not backslash and not t", not "not tab"). A pattern that
    needs a literal tab specifically (not any whitespace) should build one
    with `$(printf '\\t')` outside the single-quoted literal instead, which
    this check does not flag because that substitution never appears inside
    a `'...'` pattern argument.
    """
    for m in _GREP_QUOTED_PATTERN_RE.finditer(cmd):
        if "\\t" in m.group(1):
            return True
    return False


_DEEP_STACK_INVENTORY_RE = re.compile(
    r"\bexample\s+(nat_axiom_inventory|prelude_theorem_inventory|theorem_dependency_inventory)\b"
)


def checker_command_needs_release_for_deep_stack(cmd: str) -> bool:
    """True if `cmd` runs a kernel-inventory example whose constructed-carrier
    build (CReal/Complex/CPoint) recurses deep enough through
    `Kernel::add_declaration` to overflow a debug build's default thread
    stack, without `--release`.

    Measured 2026-08-25 on this tree: `cargo run -q -p axeyum-lean-kernel
    --example nat_axiom_inventory -- --include-constructed
    --require-axiom-free creal` exits 134 (`thread 'main' has overflowed its
    stack`) without `--release`, exit 0 with it -- the same resource limit
    CLAUDE.md already documents for `prelude_theorem_inventory
    --include-constructed`. 19 committed `F-creal-*`/`F-complex-*` checker
    commands carried this before 2026-08-25's fix, all silently unrunnable in
    a debug build.

    `theorem_dependency_inventory` builds EVERY constructed prelude
    unconditionally (no flag gates it, per its own module doc), so any
    invocation without `--release` is flagged regardless of arguments.
    `nat_axiom_inventory` and `prelude_theorem_inventory` build the
    constructed carriers only when `--include-constructed` is passed --
    their Nat/Int/Rat/logic-only forms run fine in a debug build (measured:
    `nat_axiom_inventory -- --require-axiom-free nat` exits 0 without
    `--release`) -- so only that combination is flagged. Demanding
    `--release` on every invocation of these tools, unconditionally, would
    force a needless rewrite on 102 committed commands that do not crash,
    without catching any additional failure.
    """
    m = _DEEP_STACK_INVENTORY_RE.search(cmd)
    if not m:
        return False
    if "--release" in cmd:
        return False
    if m.group(1) == "theorem_dependency_inventory":
        return True
    return "--include-constructed" in cmd


# ADR-0601 SS2: "The `cas-certificate` route splits observably: evidence that
# reconstructs through the kernel ... versus evidence that terminates in the
# CAS's own normal form. The validator must distinguish these; a fact of the
# second kind is honest but is not `checked` in the sense the headline uses,
# and the ledger must not let the two read identically."
#
# Only `cargo test`/`cargo run` segments are inspected -- `cargo check`,
# `cargo build`, and `cargo doc` compile but never EXECUTE anything, so a
# package name appearing only after one of those subcommands consults
# nothing. This is deliberately narrower than "the string axeyum-cas appears
# anywhere in the command": CLAUDE.md documents a classifier that "flags a
# whole shape" nearly reporting 126 legitimate `cargo test` checkers as
# vacuous when they were fine, and the fix there was the same one applied
# here -- ask what the command actually RUNS, not what substring it contains.
_CARGO_TEST_RUN_SEGMENT_RE = re.compile(r"\bcargo\s+(?:test|run)\b([^&;|]*)")


def classify_cas_certificate_checker(cmd: str) -> str:
    """Classify a `cas-certificate` fact's `checker_command` by what it
    actually consults (ADR-0601 SS2).

    Returns one of:
      * ``"kernel-reconstructed"`` -- some executed (`cargo test`/`cargo run`)
        segment names the `axeyum-lean-kernel` package (via `-p`,
        `--package`, or `--manifest-path`): an independent, kernel-checked
        re-derivation exists, so this evidence reconstructs through the
        trust anchor rather than terminating in the CAS's own normal form.
      * ``"cas-internal"`` -- every executed segment names only `axeyum-cas`;
        the checker never leaves the CAS's own normal form.
      * ``"unrecognized"`` -- neither package is named by any executed cargo
        segment (a bogus command, or one this classifier cannot identify).
        Flagged, not silently folded into `"cas-internal"`: CLAUDE.md's
        central lesson is that a checker which cannot fail is worse than no
        checker, and binning an unclassifiable command into the "fine"
        bucket would recreate exactly that defect one level up.

    A command consulting BOTH packages (e.g. a bridge checker that runs a
    CAS derivation and then re-checks it through the kernel) classifies as
    `"kernel-reconstructed"`, since that is the stronger, and the accurate,
    claim -- an independent re-derivation exists.
    """
    if not cmd or not cmd.strip():
        return "unrecognized"
    consults_kernel = False
    consults_cas = False
    for match in _CARGO_TEST_RUN_SEGMENT_RE.finditer(cmd):
        segment = match.group(1)
        if "axeyum-lean-kernel" in segment:
            consults_kernel = True
        if "axeyum-cas" in segment:
            consults_cas = True
    if consults_kernel:
        return "kernel-reconstructed"
    if consults_cas:
        return "cas-internal"
    return "unrecognized"


def classify_cas_certificate_fact(fact: dict) -> str:
    """Aggregate a `cas-certificate` fact's classification across its
    evidence rows: `kernel-reconstructed` wins if ANY row reconstructs
    through the kernel (the stronger, accurate claim); otherwise
    `unrecognized` if any row is unclassifiable (`validate_one` already
    rejects a `cas-certificate` fact carrying such a row, so a fact reaching
    this function in a passing ledger should never actually hit this case --
    kept as the safe default rather than silently reading as `cas-internal`
    if that guard is ever weakened); otherwise `cas-internal`.
    """
    classifications = {
        classify_cas_certificate_checker(ev.get("checker_command") or "")
        for ev in fact.get("evidence", [])
    }
    if "kernel-reconstructed" in classifications:
        return "kernel-reconstructed"
    if "unrecognized" in classifications:
        return "unrecognized"
    return "cas-internal"


def validate_one(path: Path, fact: dict, known_ids: set[str]) -> list[str]:
    errors: list[str] = []
    fid = fact.get("id", f"<{path.name}>")

    missing = REQUIRED - set(fact)
    if missing:
        fail(errors, f"{fid}: missing required field(s): {sorted(missing)}")
        return errors

    if not ID_RE.match(fact["id"]):
        fail(errors, f"{fid}: id must match ^F:[a-z0-9-]+$")

    expected_name = fact["id"].replace("F:", "F-") + ".json"
    if path.name != expected_name:
        fail(errors, f"{fid}: lives in {path.name} but its id implies {expected_name}")

    status = fact["epistemic_status"]
    if status not in STATUSES:
        fail(errors, f"{fid}: epistemic_status {status!r} is not one of {sorted(STATUSES)}")

    formal = fact["formal"]
    for key in ("language", "statement", "fragment"):
        if not formal.get(key):
            fail(errors, f"{fid}: formal.{key} is required and must be non-empty")
    if formal.get("language") not in LANGUAGES_ALL:
        fail(errors, f"{fid}: formal.language {formal.get('language')!r} not in "
                     f"{sorted(LANGUAGES_ALL)}")
    # `theorem_of` (scripts/check-fact-depends-derived.py, shared by the chain
    # catalog and the autogenesis snapshot builder) reads this key WHEN PRESENT
    # as the fact's subject theorem, `null` included -- `null` means "explicitly
    # no single kernel theorem" (a package-level fact) and is NOT the same as
    # omitting the key (which asks for extraction from evidence). A malformed
    # string here would be silently treated as a real theorem name by every one
    # of those consumers, so it is validated the same way a theorem name is
    # matched out of a checker_command.
    if "kernel_theorem" in formal and not kernel_theorem_is_valid(formal["kernel_theorem"]):
        fail(errors, f"{fid}: formal.kernel_theorem must be null (explicitly "
                     f"'no single kernel theorem') or a dotted namespaced "
                     f"kernel theorem name such as 'Rat.det2_fib'; got "
                     f"{formal['kernel_theorem']!r}")
    if formal.get("language") == "certificate-spec":
        statement = formal.get("statement", "")
        try:
            certificate_spec = json.loads(statement)
        except json.JSONDecodeError as error:
            fail(errors, f"{fid}: certificate-spec statement is not valid JSON: {error}")
        else:
            if not isinstance(certificate_spec, dict):
                fail(errors, f"{fid}: certificate-spec statement must be a JSON object")
            elif statement != json.dumps(
                certificate_spec, sort_keys=True, separators=(",", ":"), ensure_ascii=False
            ):
                fail(errors, f"{fid}: certificate-spec statement must use canonical JSON")
            elif (
                not isinstance(certificate_spec.get("format"), str)
                or not certificate_spec["format"].strip()
            ):
                fail(errors, f"{fid}: certificate-spec requires a non-empty string format")
            elif not isinstance(certificate_spec.get("version"), int) or isinstance(
                certificate_spec.get("version"), bool
            ) or certificate_spec["version"] <= 0:
                fail(errors, f"{fid}: certificate-spec requires a positive integer version")

    for dep in fact["depends_on"]:
        if not ID_RE.match(dep):
            fail(errors, f"{fid}: depends_on entry {dep!r} is not a fact id")
        elif dep not in known_ids:
            fail(errors, f"{fid}: depends_on {dep} does not exist -- a dependency DAG "
                         f"with dangling edges is not a build order")

    # Read early: the cas-certificate classification guard below (ADR-0601
    # SS2) needs it inside the evidence loop, ahead of the route-membership
    # check further down which reuses this same value.
    route = fact.get("proof_route")

    checked = 0
    for ev in fact["evidence"]:
        for key in ("id", "kind", "supports", "check_status"):
            if key not in ev:
                fail(errors, f"{fid}: evidence row missing {key!r}")
        if ev.get("kind") not in EVIDENCE_KINDS:
            fail(errors, f"{fid}: evidence kind {ev.get('kind')!r} not in {sorted(EVIDENCE_KINDS)}")
        if ev.get("check_status") not in CHECK_STATUSES:
            fail(errors, f"{fid}: evidence check_status {ev.get('check_status')!r} is unknown")
        if ev.get("check_status") == "checked":
            checked += 1
        for c in ev.get("checkers", []):
            if not isinstance(c, str) or not c.strip():
                fail(errors, f"{fid}: evidence.checkers entries must be non-empty names")
        # A checker is only worth its exit status. `smtcomp_cli --evidence` exits
        # 0 on ANY decided verdict -- sat and unsat alike -- so a bare invocation
        # proves the binary ran, not that the recorded verdict still holds. The
        # replay gate ran 16 such commands and reported them as re-derived; a
        # solver flipping `unsat` to `sat` would have passed silently, which is
        # the exact regression the gate exists to catch.
        cmd = ev.get("checker_command") or ""
        # ADR-0601 SS2: a `cas-certificate` fact's evidence must classify as
        # either `kernel-reconstructed` or `cas-internal` -- both are honest
        # positions the summary reports separately -- but never
        # `unrecognized`. An unclassifiable checker_command is exactly the
        # "checker that cannot fail" defect one level up: nothing here would
        # otherwise stop a `cas-certificate` fact from citing a command that
        # consults neither the kernel nor the CAS at all.
        if route == "cas-certificate":
            classification = classify_cas_certificate_checker(cmd)
            if classification == "unrecognized":
                fail(errors, f"{fid}: cas-certificate checker_command {cmd!r} does not "
                             f"consult a recognized checker. "
                             f"classify_cas_certificate_checker found no `cargo test`/"
                             f"`cargo run` segment naming `axeyum-lean-kernel` "
                             f"(kernel-reconstructed) or `axeyum-cas` (cas-internal) -- "
                             f"ADR-0601 SS2 requires every cas-certificate evidence row to "
                             f"be one or the other, not an unclassifiable third case.")
        if "smtcomp_cli" in cmd and not re.search(r"\btest\b|\bgrep\b|\[\[?", cmd):
            fail(errors, f"{fid}: checker_command invokes smtcomp_cli without asserting a "
                         f"verdict. It exits 0 on sat AND unsat, so as written it checks "
                         f"that the binary ran. Wrap it, e.g. "
                         f'test "$(... | tail -1)" = unsat')
        # `grep -q` as a pipeline consumer under `set -o pipefail` is banned
        # (CLAUDE.md, banned-shell-idioms #2): `-q` exits at the FIRST match and
        # SIGPIPEs the producer, so the pipeline's exit status becomes 141 --
        # which `pipefail` turns into "not found". Measured 2026-08-20 in
        # `scripts/check-control-registration.sh`: the SAME unchanged tree
        # reported 7 orphans on one run and 3 on the next, because whether the
        # producer finishes writing before the SIGPIPE arrives depends on
        # buffering -- this is nondeterministic flakiness, not a one-time bug.
        # `grep -c` (or `--count`) consumes all input to EOF and cannot SIGPIPE,
        # so pair it with a count test: `test "$(... | grep -cE '...')" -ge 1`.
        if checker_command_uses_grep_dash_q(cmd):
            fail(errors, f"{fid}: checker_command uses `grep -q` (or `--quiet`) as a "
                         f"pipeline consumer. Under `set -o pipefail` that SIGPIPEs the "
                         f"producer at the first match, turning the pipeline's exit "
                         f"status nondeterministic (141 sometimes, 0 other times, "
                         f"depending on buffering) -- CLAUDE.md's banned-shell-idioms "
                         f"#2, measured to flip 7 vs 3 on an UNCHANGED tree. Replace "
                         f"`grep -q PATTERN` with `grep -c PATTERN` and test the count: "
                         f'test "$(... | grep -cE \'PATTERN\')" -ge 1')
        # `\t` inside a grep -E pattern is NOT a tab in POSIX ERE -- GNU grep
        # drops the backslash and matches a literal 't'. Measured with
        # `/usr/bin/grep` (GNU grep 3.12): `printf 'a\tb\n' | grep -cE 'a\tb'`
        # matches ZERO real tabs and `printf 'atb\n' | grep -cE 'a\tb'`
        # matches ONE literal 't' -- the opposite of what the pattern's
        # author intended. 54 facts / 68 checker_commands carried this before
        # 2026-08-25's rewrite, each silently reporting a PRESENT theorem as
        # ABSENT under any script or CI run (fail-closed, not a wrong sat/unsat,
        # but the evidence did not re-derive anywhere except an interactive
        # shell whose `grep` is a function wrapping `ugrep`, which DOES treat
        # `\t` as a tab and so never saw the bug). Replace a standalone `\t`
        # separator with `[[:space:]]`; inside a bracket expression (`[^\t]`)
        # use `[^[:space:]]`, since backslash is not special there either. If
        # a pattern needs a literal tab specifically (not any whitespace),
        # build one with `$(printf '\t')` outside the single-quoted literal.
        if checker_command_uses_grep_backslash_t(cmd):
            fail(errors, f"{fid}: checker_command passes grep a pattern containing "
                         f"the literal escape `\\t`, which POSIX ERE (and BRE) does "
                         f"NOT interpret as a tab -- GNU grep drops the backslash and "
                         f"matches a literal 't' instead, so a tab-anchored pattern "
                         f"like '^Name\\t' matches NOTHING against real tab-separated "
                         f"output. This reports a PRESENT theorem as ABSENT under any "
                         f"script or CI run (an interactive shell's `grep` may be a "
                         f"function wrapping `ugrep`, which DOES treat \\t as a tab, "
                         f"masking the bug by hand). Replace a standalone `\\t` "
                         f"separator with `[[:space:]]`; inside a bracket expression "
                         f"(`[^\\t]`) use `[^[:space:]]`. For a literal tab "
                         f"specifically, build one with `$(printf '\\t')` outside the "
                         f"single-quoted pattern.")
        # `nat_axiom_inventory --include-constructed`, `prelude_theorem_inventory
        # --include-constructed` and any `theorem_dependency_inventory` build the
        # constructed carriers (CReal/Complex/CPoint) deep enough through
        # `Kernel::add_declaration` to overflow a debug build's default thread
        # stack -- measured exit 134 ("has overflowed its stack") without
        # `--release`, exit 0 with it. 19 committed checker commands carried this
        # before 2026-08-25's fix, silently unrunnable in a debug build.
        if checker_command_needs_release_for_deep_stack(cmd):
            fail(errors, f"{fid}: checker_command runs a kernel-inventory example "
                         f"over the constructed carriers (CReal/Complex/CPoint) "
                         f"without `--release`. That build recurses deep enough to "
                         f"overflow a debug build's default thread stack -- measured "
                         f"exit 134 ('has overflowed its stack') without the flag, "
                         f"exit 0 with it. Add `--release` right after `cargo run -q`.")
        if ev.get("kind") == "claim-ref":
            art = ev.get("artifact")
            if not art:
                fail(errors, f"{fid}: claim-ref evidence must name the claim in `artifact`")
            elif not (ROOT / art).is_file():
                fail(errors, f"{fid}: claim-ref points at {art}, which does not exist")

    # --- the semantic rules ---
    if status in ESTABLISHED and checked == 0:
        fail(errors, f"{fid}: status {status!r} asserts the statement was settled, but no "
                     f"evidence row is `checked`. A status with nothing establishing it is "
                     f"the defect this ledger exists to prevent.")

    if status == "proved" and "axiom_footprint" not in fact:
        fail(errors, f"{fid}: status `proved` requires axiom_footprint. An EMPTY array means "
                     f"axiom-free and is a stronger claim than an absent field, so absence "
                     f"must not read as the strong case.")

    if status == "open" and fact["evidence"]:
        fail(errors, f"{fid}: status `open` must carry an empty evidence array -- an open fact "
                     f"with evidence is a contradiction, and the empty array is a statement.")

    if route is not None and route not in ROUTES:
        fail(errors, f"{fid}: proof_route {route!r} is not one of {sorted(ROUTES)}")
    if status in ESTABLISHED and route is None:
        fail(errors, f"{fid}: status {status!r} requires a proof_route. axiom_footprint is "
                     f"only comparable WITHIN a route, so a settled fact that does not say "
                     f"which machine settled it makes its own footprint unreadable.")
    # The rule this whole field exists for.
    # Scoped to KNOWN routes: an unrecognised route is already reported above, and
    # we cannot say what a route we do not know cannot deliver. Without this guard
    # one bad value produced two errors, which makes a control ambiguous about
    # which rule it exercised.
    if (
        route in ROUTES
        and route not in AXIOM_FREE_CAPABLE
        and fact.get("axiom_footprint") == []
    ):
        fail(errors, f"{fid}: axiom_footprint [] on proof_route {route!r}. An empty footprint "
                     f"asserts axiom-freedom, which only {sorted(AXIOM_FREE_CAPABLE)} can "
                     f"deliver -- there it means a kernel environment admits no Axiom, Opaque "
                     f"or Quotient. On any other route it names semantic assumptions that are "
                     f"real and cannot be empty, so [] would read as the strongest claim the "
                     f"project makes on evidence that cannot support it.")

    # An imported proof term has an author, and it is not us. Requiring the
    # citation structurally is what stops an import from reading as a local
    # result: without it the only thing separating "we proved this" from "Lean
    # proved this and we re-checked the term" is a route string a reader has to
    # already understand.
    if route in IMPORTED_ROUTES and not fact["provenance"].get("prior_art"):
        fail(errors, f"{fid}: proof_route {route!r} means the proof term was authored "
                     f"elsewhere, so provenance.prior_art must name who authored it. "
                     f"An import that reads as a local proof is the failure this route "
                     f"exists to prevent.")

    external = fact.get("external_status")
    if external is not None:
        if external not in EXTERNAL_STATUSES:
            fail(errors, f"{fid}: external_status {external!r} is not one of "
                         f"{sorted(EXTERNAL_STATUSES)}")
        elif (
            external in EXTERNAL_SETTLED
            and status not in OURS_SETTLED
            and not fact["provenance"].get("prior_art")
        ):
            fail(errors, f"{fid}: this fact is {status!r} to us but external_status "
                         f"{external!r}, so the LITERATURE is the only thing holding it up "
                         f"-- provenance.prior_art must name who settled it. (When we have "
                         f"established a fact ourselves, external_status is corroborative "
                         f"and needs no citation; the risk is relying on an unverified "
                         f"claim about the literature, which is how this project came to "
                         f"cite Zenodo self-deposits as refereed results.)")

    return errors


def run_depends_derived_gate(skip: bool) -> int:
    """Fail the ledger validator when `depends_on` drifts from the proof term.

    `check-fact-depends-derived.py` already derives this from the kernel and
    already runs in both `scripts/check.sh` and `just check` -- but both are
    periodic aggregate sweeps, and drift compounded between them: 1054 missing
    edges across 306 facts over 182 fact-touching commits, then 109 more
    within the hour (docs/research/11-design-review/2026-08-29-two-gaps-the-
    gate-sweep-exposed.md). Every one of those repairs was mechanical.

    This validator is the command a lane is actually told to run when it
    touches a fact (CLAUDE.md's Commands section lists it standalone, not only
    as part of the aggregate gate), so wiring the enforcement here catches the
    drift at the point a fact is landed rather than after it has piled up.

    `--skip-depends-derived` exists only for a fast schema-only iteration loop
    while drafting a fact's JSON; it is not a substitute for running this
    (without the flag) before landing one, and CI/the aggregate gates never
    pass it.
    """
    if skip:
        print(
            "validate-facts: SKIPPING depends-derived gate (--skip-depends-derived); "
            "run without this flag before landing a fact"
        )
        return 0
    if not DEPENDS_DERIVED_SCRIPT.is_file():
        print(f"validate-facts: missing {DEPENDS_DERIVED_SCRIPT}", file=sys.stderr)
        return 1
    proc = subprocess.run(
        [sys.executable, str(DEPENDS_DERIVED_SCRIPT), "--quiet"],
        cwd=ROOT,
    )
    return proc.returncode


def main() -> int:
    if not SCHEMA.is_file():
        print(f"validate-facts: missing {SCHEMA}", file=sys.stderr)
        return 2
    if not FACTS.is_dir():
        print("validate-facts: no artifacts/facts/ directory; nothing to check")
        return 0

    paths = sorted(FACTS.glob("*.json"))
    facts: dict[Path, dict] = {}
    errors: list[str] = []

    for p in paths:
        try:
            facts[p] = json.loads(p.read_text())
        except json.JSONDecodeError as exc:
            fail(errors, f"{p.name}: not valid JSON: {exc}")

    ids: dict[str, Path] = {}
    for p, f in facts.items():
        fid = f.get("id")
        if fid in ids:
            fail(errors, f"{fid}: duplicate id, also in {ids[fid].name}")
        elif fid:
            ids[fid] = p

    for p, f in facts.items():
        errors.extend(validate_one(p, f, set(ids)))

    by_status: dict[str, int] = {}
    for f in facts.values():
        by_status[f.get("epistemic_status", "?")] = by_status.get(f.get("epistemic_status", "?"), 0) + 1

    if errors:
        print(f"\nvalidate-facts: {len(facts)} facts, {len(errors)} errors", file=sys.stderr)
        for e in errors:
            print(f"  ERROR {e}", file=sys.stderr)
        return 1

    depends_rc = run_depends_derived_gate("--skip-depends-derived" in sys.argv[1:])
    if depends_rc != 0:
        print(
            "\nvalidate-facts: depends_on drift detected -- see "
            "scripts/check-fact-depends-derived.py output above. Run "
            "`python3 scripts/check-fact-depends-derived.py --fix` to add the "
            "missing edges, review the diff, then re-run this validator.",
            file=sys.stderr,
        )
        return 1

    # Established here, not settled in the literature -- i.e. new. Reported, never
    # failed: this is the output the project exists to produce, and a gate silent
    # about it is measuring the wrong thing.
    novel = sorted(
        f["id"]
        for f in facts.values()
        if f.get("epistemic_status") in OURS_SETTLED
        and f.get("external_status") in {"open", "conjectured"}
    )
    # Known to mathematics, not to us -- the import backlog. Distinct from `open`,
    # and the self-extension loop must not treat these as problems to solve.
    backlog = sum(
        1
        for f in facts.values()
        if f.get("epistemic_status") == "open" and f.get("external_status") == "proved"
    )
    unclassified = sum(1 for f in facts.values() if "external_status" not in f)

    # Route spread, and axiom-freedom reported ONLY where it means something.
    # A single "N axiom-free" number across routes is the exact conflation
    # proof_route exists to prevent, so it is scoped rather than totalled.
    routes: dict[str, int] = {}
    axiom_free = 0
    for f in facts.values():
        r = f.get("proof_route")
        if r:
            routes[r] = routes.get(r, 0) + 1
        if r in AXIOM_FREE_CAPABLE and f.get("axiom_footprint") == []:
            axiom_free += 1
    # ADR-0601 SS2: `cas-certificate` is not one homogeneous class. Split it
    # by what each fact's evidence actually consults -- `kernel-reconstructed`
    # (an independent re-derivation through the trust anchor exists) versus
    # `cas-internal` (the checker never leaves the CAS's own normal form) --
    # so the ledger cannot let the two read identically. `validate_one`
    # rejects a fact reaching `unrecognized` in a passing ledger, so that
    # bucket is expected to be empty here; it is still computed and reported
    # rather than assumed, in case that guard is ever weakened.
    cas_certificate_facts = [f for f in facts.values() if f.get("proof_route") == "cas-certificate"]
    cas_breakdown: dict[str, int] = {}
    for f in cas_certificate_facts:
        c = classify_cas_certificate_fact(f)
        cas_breakdown[c] = cas_breakdown.get(c, 0) + 1
    # Independent re-derivations. Cross-oracle agreement is the strongest signal
    # here, and it was invisible while every row said `checked` and nothing else.
    #
    # THE PRODUCING RUN IS NOT A RE-DERIVATION OF ITSELF, and this counter used
    # to say it was. Measured 2026-08-30 over the whole ledger: of 3,579 rows
    # carrying 2+ checkers, **1,581 name the run that produced the result** --
    # `producing-build (Kernel::add_declaration)` 1,333 times, plus 248 more
    # naming `Kernel::add_declaration` in another phrasing or a
    # `*-producing-solve`. For a kernel-route fact the proof term is built and
    # admitted in one step, so `add_declaration` IS the production; listing it
    # beside `Kernel::axiom_footprint` gives a row with one re-derivation, not
    # two. Only **2,097** rows carry 2+ checks that are not the production.
    #
    # S0's census reported 1,356 of 1,984 facts by matching the literal string
    # `producing`; reproduced here that is 1,359 of 1,989 today (three facts
    # landed since). That measurement was right about what it measured. The
    # broader classifier below is the honest one, because a checker named
    # `Kernel::add_declaration (re-derives the type from the proof term)` is the
    # producing build whether or not the word "producing" appears in it.
    def names_the_producing_run(checker: str) -> bool:
        lowered = checker.lower()
        return "producing" in lowered or "add_declaration" in checker

    multi = 0
    self_rederived = 0
    independent = 0
    for f in facts.values():
        for e in f.get("evidence", []):
            checkers = e.get("checkers", [])
            if len(checkers) < 2:
                continue
            multi += 1
            if any(names_the_producing_run(c) for c in checkers):
                self_rederived += 1
            if sum(1 for c in checkers if not names_the_producing_run(c)) >= 2:
                independent += 1

    # A classifier that matches nothing reports the ledger as fully independent,
    # which is the most flattering possible answer and indistinguishable from a
    # broken pattern. It matched 1,581 rows when written; a zero here means it
    # stopped seeing its subject.
    if multi and self_rederived == 0:
        print(
            f"\nvalidate-facts: the producing-run classifier matched ZERO of {multi} "
            "multi-checker rows. It matched 1,581 when written, so a zero means the "
            "classifier lost its subject rather than the ledger becoming independent "
            "-- an empty result is not a negative result.",
            file=sys.stderr,
        )
        return 1

    spread = " ".join(f"{k}={v}" for k, v in sorted(by_status.items()))
    print(f"{len(facts)} facts checked, 0 errors  ({spread})")
    # ADR-0790: some settled facts state the SAME kernel proposition as a
    # sibling fact (a byte-identical `Kernel::render_lean` canonical type --
    # see scripts/check-proposition-duplication.py). Both stay `proved`, but
    # only one is canonical; the other carries `equivalent_to`. Quoting
    # "N proved" alone double-counts every such pair, which is exactly how
    # this project's headline metric was overstated before this line existed
    # -- so print DISTINCT PROPOSITIONS beside FACTS SETTLED, always together.
    settled_for_count = {"proved", "computed"}
    settled_established = sum(
        1 for f in facts.values() if f.get("epistemic_status") in settled_for_count
    )
    restatements = sum(
        1
        for f in facts.values()
        if f.get("epistemic_status") in settled_for_count and f.get("equivalent_to")
    )
    print(
        f"  {settled_established} facts settled ({sorted(settled_for_count)}), "
        f"{restatements} of those restate a sibling's proposition "
        f"(`equivalent_to`) -- {settled_established - restatements} DISTINCT "
        f"PROPOSITIONS ESTABLISHED"
    )
    if routes:
        route_parts = []
        for k, v in sorted(routes.items()):
            if k == "cas-certificate" and cas_certificate_facts:
                route_parts.append(
                    f"{k}={v}(kernel-reconstructed="
                    f"{cas_breakdown.get('kernel-reconstructed', 0)},cas-internal="
                    f"{cas_breakdown.get('cas-internal', 0)})"
                )
            else:
                route_parts.append(f"{k}={v}")
        print("  routes: " + " ".join(route_parts)
              + f"; {axiom_free} axiom-free on {sorted(AXIOM_FREE_CAPABLE)[0]}"
              + " (not comparable across routes)")
    if cas_certificate_facts:
        kr = cas_breakdown.get("kernel-reconstructed", 0)
        ci = cas_breakdown.get("cas-internal", 0)
        unrec = cas_breakdown.get("unrecognized", 0)
        line = (f"  cas-certificate: {len(cas_certificate_facts)} total -- "
                f"kernel-reconstructed {kr}, cas-internal {ci}")
        if unrec:
            line += (f", unrecognized {unrec} (FLAGGED -- validate_one should have "
                      f"rejected this)")
        print(line)
        # ADR-0622: `kernel-reconstructed` is not one thing. This classifier asks
        # which PACKAGE a checker_command runs and never what the kernel was
        # asked to check, so a reconstruction whose obligation is
        # `poly_expr(X) = 1 * poly_expr(X)` -- true of every polynomial -- moves
        # the counter above by exactly as much as one with real cross-generator
        # cancellation. The sub-line below reads each fact's `cas_substance`
        # block, which scripts/check-cas-substance.py derives from the CAS's own
        # certificate and refuses to let disagree with it. Quote BOTH lines: the
        # first is how many reconstructions exist, the second is what they
        # establish.
        shapes: dict[str, int] = {}
        for f in cas_certificate_facts:
            if classify_cas_certificate_fact(f) != "kernel-reconstructed":
                continue
            substance = f.get("cas_substance")
            shape = substance.get("shape") if isinstance(substance, dict) else None
            shapes[shape or "undeclared"] = shapes.get(shape or "undeclared", 0) + 1
        if shapes:
            nondiscriminating = shapes.get("refl", 0) + shapes.get("empty", 0)
            summary = ", ".join(f"{k} {v}" for k, v in sorted(shapes.items()))
            print(f"    of those {kr} kernel-reconstructed, by what the kernel "
                  f"obligation establishes: {summary}")
            if nondiscriminating:
                print(f"    {nondiscriminating} of the {kr} are NON-DISCRIMINATING "
                      f"(the obligation holds of every polynomial in place of the "
                      f"certificate's) and are disclosed as such -- do not quote "
                      f"{kr} as reconstructions with geometric content")
    # Constructed here vs. checked here but authored elsewhere. Reported apart
    # because the project's headline claim is about the first number, and an
    # ingestion pipeline can move the second one arbitrarily far.
    imported = sum(1 for f in facts.values() if f.get("proof_route") in IMPORTED_ROUTES)
    if imported:
        print(f"  {imported} fact(s) on an IMPORTED route -- proof term checked here, "
              f"authored elsewhere; not evidence of construction")
    print(
        f"  {multi} evidence row(s) checked by 2+ distinct checkers -- "
        f"{self_rederived} of those count the PRODUCING run as one of the two, so "
        f"{independent} carry 2+ checks that are not the production itself"
    )
    print(f"  external: {backlog} settled elsewhere but not here (import backlog), "
          f"{unclassified} unclassified")
    if novel:
        print(f"  NOVEL -- established here, not settled in the literature: {', '.join(novel)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
