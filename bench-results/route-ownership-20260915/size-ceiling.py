#!/usr/bin/env python3
"""ADR-2100 SIZING: how many undecided Tier 1 rows could the ownership rule move?

The question, from the exit criteria: count undecided rows whose trace shows
`decided_by=none` AND where a route BELOW the last-attempted one would own their
constructs. That is the CEILING -- every row the rule could conceivably reach.
It is not a prediction of gains; a route that owns a construct still has to
decide the query.

METHOD, and its two limits, stated up front because a sizing number read as a
forecast is how a lane over-promises:

1. The ladder order and the ownership table are read from the SOURCE
   (`crates/axeyum-solver/src/auto.rs`, `route_ownership::DispatchRoute::owns`),
   parsed out of the `match` rather than retyped here. A test named "every X"
   must derive its X from the authority; so must a sizing script. If the parse
   finds no routes it ABORTS rather than reporting a confident zero.

2. The query's construct set is derived from the ROUTE TRAIL, not from the file
   text. Every rung of the dispatcher gates on a `Features` conjunction, so the
   set of rungs that ran is evidence about the flags -- and it is evidence about
   REACHABILITY, which a text scan is not. ADR-1966 learned this the expensive
   way: 184 of 200 `AUFLIRA` files declare the shape it was aiming at and 186 of
   200 never get past the PARSER, so aiming by text would have produced a
   confident zero and the wrong conclusion.

   The limit of trail-derived features is the other direction: it can only see
   flags a rung that RAN was gated on. A file whose ladder stopped at rung two
   has weak evidence about arrays. Rows where the evidence is too thin to decide
   are counted in their own bucket (`UNDETERMINED`) and never folded into either
   answer.

Usage: size-ceiling.py <auto.rs> <phase1-ceiling.tsv> <trace.tsv>...

The first TSV is lane PLAN-SIZING's inventory
(`bench-results/dispatch-plan-sizing-20260915/phase1-ceiling.tsv`), which fixes
the FRAME: 645 undecided Tier 1 rows, of which **604 are `stopped_by_unknown`**
-- the last recorded attempt's reason is `budget`/`incomplete`/
`verifier-rejected`, an actual `Ok(Unknown)`, so the ladder STOPPED rather than
running out of rungs. Those 604 are the only rows the ownership rule can reach
by construction: on the other 40 the last attempt was an `unsupported` /
`not-applicable` decline, which already let the ladder continue.

That lane could not compute the ceiling itself and said so plainly: *"that
predicate does not exist yet -- building it is Phase 1's own deliverable, so it
cannot be used to size Phase 1 before Phase 1 exists."* This script supplies the
predicate. It does NOT re-run the sweep: the construct evidence comes from this
lane's own `--trace` capture of the same 645 rows, joined to PLAN-SIZING's
inventory by corpus-relative PATH (645 of 645 join, checked, not assumed).
"""

import json
import re
import sys

# The dispatch ladder, in the order `check_auto_dispatch_inner` runs it. Routes
# that are not rungs of THIS ladder (the `fd:` front-door stages and the `q:`
# quantified rungs, which are two other ladders) are excluded by prefix, and the
# sub-route labels a rung records from inside itself are mapped to their rung.
LADDER = [
    "datatype-acyclicity",
    "datatype-elim",
    "datatype-native",
    "dl-online",
    "lira-dpll",
    "uf-nra",
    "nra-real-root",
    "cas-ideal-refuter",
    "nra",
    "uf-arith-overbound-probe",
    "bv2nat-range",
    "bv2nat-blast",
    "int-linear-refuters",
    "uf-routes",
    "abv-online-cdclt",
    "array-fast-path",
    "nia-square",
    "int-blast-ladder",
    "nia-linearize",
    "int-real-relax",
    "qf-bv",
]
# Sub-routes a rung records from inside its own body, mapped to the rung whose
# position in LADDER they occupy.
SUBROUTE_OF_RUNG = {
    "lia-dpll": "int-linear-refuters",
    "lia-simplex": "int-linear-refuters",
    "lia-diophantine": "int-linear-refuters",
    "milp": "int-linear-refuters",
    "euf-online": "uf-routes",
    "euf-offline": "uf-routes",
    "uf-arithmetic": "uf-routes",
    "uf-arith-online": "uf-routes",
    "uf-arith-lazy-overbound": "uf-routes",
    "uf-arith-lazy-overbound-pre-lia": "uf-arith-overbound-probe",
    "ufbv-declared-sort-lazy": "uf-routes",
    "uf-finite-domain-pigeonhole": "uf-routes",
    "nia-bounded-blast": "nia-linearize",
    "nra-even-power": "nra",
    "integer-algebraic-refutation": "int-linear-refuters",
    "coercion-relax": "int-real-relax",
}
POSITION = {name: i for i, name in enumerate(LADDER)}

# Rungs after which NOTHING runs, so "a route below" is empty however the list
# above is ordered.
#
# `dispatch_nonlinear_int_tail` is reached as `return dispatch_nonlinear_int_tail(..)`
# inside `if features.has_int`, so `qf-bv` -- which is textually below it -- is
# unreachable from any integer query. The first run of this script did not model
# that and reported **102 of 116 `QF_NIA` rows** as reachable, every one of them
# with `owner-below=qf-bv`. A ceiling is only an upper bound on the thing it
# actually bounds; a route ordering read off the source text rather than off the
# control flow bounds nothing.
TERMINAL_RUNGS = {"nia-square", "int-blast-ladder", "nia-linearize", "int-real-relax", "qf-bv"}

# The flags a rung's own gate requires to be TRUE before it runs at all.
#
# Owning a construct and being ENTERABLE on a query are different questions, and
# the second one is what decides whether the route below actually gets a turn.
# `array-fast-path` owns `{..., Int, ...}` and runs only `if features.has_array`,
# so on an integer query with no array it owns the constructs and never runs.
# All five rows the un-refined count returned were exactly that shape, confirmed
# against the corpus text: 0 occurrences of `Array` in any of the five.
ENTRY_REQUIRES = {
    "datatype-elim": {"Datatype"},
    "datatype-native": {"Datatype"},
    "lira-dpll": {"Int", "Real"},
    "uf-nra": {"Real", "Function"},
    "nra-real-root": {"Real"},
    "nra": {"Real"},
    "uf-arith-overbound-probe": {"Int", "Function"},
    "bv2nat-blast": {"Int", "BvOrFloat"},
    "int-linear-refuters": {"Int"},
    "abv-online-cdclt": {"Array"},
    "array-fast-path": {"Array"},
    # `uf-routes` gates on `has_function || has_uninterpreted_sort`, a
    # DISJUNCTION, so no single flag is required; it is handled by the empty set
    # rather than by picking one of the two and being wrong half the time.
    "uf-routes": set(),
}

# The flags a rung's gate requires to be CLEAR. The negative half of a gate is
# as load-bearing as the positive half and is easier to forget: `qf-bv` has no
# positive requirement at all, and is still unreachable from any integer query,
# because `if features.has_int { return dispatch_nonlinear_int_tail(..) }` sits
# above it. Leaving this out made all five remaining rows read as enterable via
# `qf-bv` -- the same modelling error as the 102, one rung further down.
ENTRY_FORBIDS = {
    "lira-dpll": set(),
    "uf-nra": {"Int", "Array", "Datatype", "UninterpretedSort"},
    "uf-arith-overbound-probe": {"Real", "Array"},
    "bv2nat-blast": {"Function", "Array", "UninterpretedSort", "Datatype"},
    "abv-online-cdclt": {
        "Function", "Int", "Real", "NonBoolBvArray", "UninterpretedSort", "Datatype",
    },
    "qf-bv": {"Int"},
}

# Which `Features` flag a rung's PRESENCE on the trail is evidence for. Read off
# each rung's gate in `check_auto_dispatch_inner` / the `dispatch_*` helpers.
# `True` means "this flag is set", `False` means "this flag is clear".
EVIDENCE = {
    "datatype-elim": {"Datatype": True},
    "datatype-native": {"Datatype": True},
    "lira-dpll": {"Int": True, "Real": True},
    "uf-nra": {
        "Real": True, "Function": True,
        "Int": False, "Array": False, "Datatype": False, "UninterpretedSort": False,
    },
    "nra-real-root": {"Real": True},
    "nra": {"Real": True},
    "uf-arith-overbound-probe": {
        "Int": True, "Function": True, "Real": False, "Array": False,
    },
    "bv2nat-blast": {
        "Int": True, "BvOrFloat": True,
        "Function": False, "Array": False, "UninterpretedSort": False, "Datatype": False,
    },
    "int-linear-refuters": {"Int": True},
    "uf-routes": {},           # `has_function || has_uninterpreted_sort` -- a disjunction
    "abv-online-cdclt": {
        "Array": True,
        "Function": False, "Int": False, "Real": False,
        "NonBoolBvArray": False, "UninterpretedSort": False, "Datatype": False,
    },
    "array-fast-path": {"Array": True},
    "nia-square": {"Int": True},
    "int-blast-ladder": {"Int": True},
    "nia-linearize": {"Int": True},
    "int-real-relax": {"Int": True},
}


def parse_ownership(auto_rs: str):
    """Reads `DispatchRoute::{label,owns,kind}` out of the source."""
    src = open(auto_rs).read()

    def block(fn_sig):
        """The body of one `match self { ... }`, by brace counting.

        Not by a closing-delimiter literal: an arm whose body is a
        `constructs![...]` list spans lines and a `\\n        }\\n` scan stops
        inside the first one, which is how this script's first run reported a
        variant with no declaration on a tree where it had one.
        """
        i = src.index(fn_sig)
        i = src.index("match self {", i) + len("match self {")
        depth, j = 1, i
        while depth:
            if src[j] == "{":
                depth += 1
            elif src[j] == "}":
                depth -= 1
                if depth == 0:
                    break
            j += 1
        return src[i:j]

    labels, owns, kinds = {}, {}, {}
    for variant, label in re.findall(
        r"Self::(\w+) => \"([a-z0-9-]+)\",", block("pub(crate) const fn label(self)")
    ):
        labels[variant] = label
    owns_src = block("pub(crate) const fn owns(self)")
    # `rustfmt` wraps a long arm body in braces, so the arrow and the macro are
    # not always adjacent. An `=> constructs!` literal missed exactly one
    # variant on this tree and the ABORT below is what said so.
    for variant, body in re.findall(
        r"Self::(\w+) =>\s*\{?\s*constructs!\[([^\]]*)\]", owns_src, re.S
    ):
        owns[variant] = {c.strip() for c in body.split(",") if c.strip()}
    for variant, kind in re.findall(
        r"Self::(\w+) => RouteKind::(\w+),", block("pub(crate) const fn kind(self)")
    ):
        kinds[variant] = kind
    if not labels or not owns or not kinds:
        sys.exit("ABORT: the ownership parse found nothing -- find the match, do not guess")
    missing = set(labels) - set(owns) or set(labels) - set(kinds)
    if missing:
        sys.exit(f"ABORT: parsed a label with no owns/kind: {sorted(missing)}")
    return (
        {labels[v]: owns[v] for v in labels},
        {labels[v]: kinds[v] for v in labels},
    )


def trail_routes(trail_cell: str):
    """The ordered dispatch-ladder routes on this row's trail."""
    marker = "; route-trail "
    if not trail_cell.startswith(marker):
        return None
    try:
        trace = json.loads(trail_cell[len(marker):])
    except json.JSONDecodeError:
        return None
    out = []
    for attempt in trace.get("attempts", []):
        route = attempt.get("route", "")
        route = SUBROUTE_OF_RUNG.get(route, route)
        if route in POSITION:
            out.append(route)
    return out


def constructs_from_trail(routes):
    """Flags the trail is evidence for, and the flags it says nothing about."""
    known = {}
    conflict = False
    for route in routes:
        for flag, value in EVIDENCE.get(route, {}).items():
            if flag in known and known[flag] != value:
                conflict = True
            known[flag] = value
    return known, conflict


def read_frame(path: str):
    """PLAN-SIZING's inventory: `stopped_by_unknown` and `last_route` per row."""
    frame = {}
    for line in open(path):
        cells = line.rstrip("\n").split("\t")
        if cells[0] == "division":
            continue
        # division, path, partial, attempts, last_route, decided_by,
        # decline_reasons, stopped_by_unknown, bound_by, ceiling_hit, capture
        frame[cells[1]] = (cells[7], cells[4])
    if len(frame) < 600:
        sys.exit(f"ABORT: the frame parse found {len(frame)} rows, not a plausible count")
    return frame


def main():
    auto_rs, frame_tsv, *tsvs = sys.argv[1:]
    owns, kinds = parse_ownership(auto_rs)
    frame = read_frame(frame_tsv)
    joined = stopped = 0

    total = reachable = enterable_rows = no_dispatch = undetermined = 0
    per_div = {}
    witnesses = []
    for tsv in tsvs:
        for line in open(tsv):
            cells = line.rstrip("\n").split("\t")
            if len(cells) < 6 or cells[0] == "file":
                continue
            path, verdict, _rc, _ms, route_line, trail_cell = cells[:6]
            if verdict in ("sat", "unsat"):
                continue
            total += 1
            div = path.split("/", 1)[0]
            stopped_by_unknown, _plan_last_route = frame.get(path, ("MISSING", ""))
            if stopped_by_unknown == "MISSING":
                sys.exit(
                    f"ABORT: {path} is in this lane's capture and not in PLAN-SIZING's "
                    "inventory. The two populations must be the same 645 rows or the "
                    "denominators below are describing different things."
                )
            joined += 1
            per_div.setdefault(
                div,
                {"rows": 0, "reachable": 0, "enterable": 0, "no_dispatch": 0, "undet": 0},
            )
            per_div[div]["rows"] += 1
            if "decided_by=none" not in route_line:
                continue
            # THE FRAME. A row whose last attempt was an `unsupported` /
            # `not-applicable` decline already let the ladder continue, so the
            # ownership rule has nothing to change about it. Only a row the
            # ladder STOPPED at can be reached.
            if stopped_by_unknown != "yes":
                continue
            stopped += 1
            routes = trail_routes(trail_cell)
            if not routes:
                no_dispatch += 1
                per_div[div]["no_dispatch"] += 1
                continue
            last = max(routes, key=lambda r: POSITION[r])
            known, conflict = constructs_from_trail(routes)
            if conflict:
                undetermined += 1
                per_div[div]["undet"] += 1
                continue
            present = {flag for flag, value in known.items() if value}
            # A route BELOW the last-attempted one that owns every construct the
            # query is KNOWN to carry, and that is the ladder's decider for it.
            if last in TERMINAL_RUNGS:
                continue
            below = [r for r in LADDER if POSITION[r] > POSITION[last] and r in owns]
            hit = [
                r for r in below
                if kinds[r] == "Decider" and present <= owns[r]
            ]
            absent = {f for f, v in known.items() if not v}
            enterable = [
                r for r in hit
                if ENTRY_REQUIRES.get(r, set()) <= present
                and not (ENTRY_FORBIDS.get(r, set()) & present)
            ]
            del absent
            if hit:
                reachable += 1
                per_div[div]["reachable"] += 1
                if len(witnesses) < 12:
                    witnesses.append((path, last, sorted(present), hit[0], bool(enterable)))
            if enterable:
                enterable_rows += 1
                per_div[div]["enterable"] += 1

    print(f"undecided rows scanned      : {total}")
    print(f"  joined to PLAN-SIZING       : {joined} (must equal the line above)")
    print(f"  stopped_by_unknown (frame)  : {stopped}")
    print(f"  no dispatch-ladder attempt: {no_dispatch}")
    print(f"  UNDETERMINED (conflicting): {undetermined}")
    print(f"  a route below OWNS the constructs           : {reachable}")
    print(f"  CEILING (that route is also ENTERABLE)      : {enterable_rows}")
    print()
    print(
        f"{'division':<12} {'rows':>5} {'owns':>5} {'ceiling':>8} "
        f"{'no-dispatch':>12} {'undet':>6}"
    )
    for div in sorted(per_div):
        d = per_div[div]
        print(
            f"{div:<12} {d['rows']:>5} {d['reachable']:>5} {d['enterable']:>8} "
            f"{d['no_dispatch']:>12} {d['undet']:>6}"
        )
    if witnesses:
        print(
            "\nwitnesses (path, last dispatch rung, known constructs, "
            "first owner below, is it enterable):"
        )
        for w in witnesses:
            print(
                f"  {w[0]}\n      last={w[1]} constructs={w[2]} "
                f"owner-below={w[3]} enterable={w[4]}"
            )


if __name__ == "__main__":
    main()
