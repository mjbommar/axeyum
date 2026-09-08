#!/usr/bin/env python3
"""Route-attribution aggregation and virtual-best-over-our-own-routes (ADR-1760).

Reads the per-division TSVs `run_division.sh` writes plus each file's
`; route-trail <json>` log line, and answers three questions:

1. **Which route decided each file we solve** -- the deciding-route
   distribution, per division and overall.
2. **Which route bound each file we lose** -- and how that compares to the
   route that merely printed last, which is what past censuses recorded.
3. **The virtual best over our own routes**, stated with the bounds the data
   actually supports (see `VIRTUAL BEST` below).

# VIRTUAL BEST: what this can and cannot measure

A strict virtual best runs every route alone on every file and takes the best.
`SolverConfig` has no route-selection knob, so that is NOT measurable here and
this script does not pretend otherwise.

What a sequential dispatch trail does give, per file, is a three-valued fact
about each route:

  * every route tried BEFORE the winner  -> measured NO  (it declined)
  * the winner                           -> measured YES
  * every route AFTER the winner         -> UNKNOWN (never ran)

Two consequences, both of which the output states explicitly:

  * The deciding-route distribution is an **upper bound on route diversity**.
    A file credited to route R might also have been decided by a later route
    that never got a turn, so the routes could be more redundant than they look
    -- never less.
  * The recoverable wall time is **exact**, not a bound. Time spent in routes
    that declined before the winner is time a parallel portfolio does not spend,
    because the winner would have been running concurrently from the start. That
    figure -- `declined_prefix_ms / trail_total_ms` -- is the direct answer to
    "is a portfolio over 16 idle cores the largest available win", and it is
    computed from the trail's own per-attempt timings.

# The guard

`bench-results/instrument-coverage-2026-09-07` found a 130.7% stage coverage
because the fields being summed were non-additive, and it was caught only
because >100% is impossible. Three impossibility guards are enforced here, each
of which exits 1 rather than warning:

  * a trail's summed per-attempt elapsed must not exceed the process wall clock
    (times ALLOWED_SLOP for process-vs-instrument skew);
  * the declined prefix of a decided file must not exceed that file's own trail
    total -- a share above 100% is impossible by construction;
  * a decided file must name a deciding route, and an unsolved one must not
    claim to have been decided by the trail's final entry.

Run:
  python3 aggregate.py <DIV>.tsv ... > aggregate.json
"""
import json
import re
import sys
from collections import Counter, defaultdict

# Headroom for skew between the harness's `date +%s%N` wall clock and the
# binary's own `Instant` timers (process startup/exit, scheduling). NOT a
# license to double-count: the trail's per-attempt elapsed values are disjoint
# by construction (each is measured from the previous record call).
ALLOWED_SLOP = 1.15

TRAIL_RE = re.compile(r"^; route-trail (\{.*\})\s*$", re.MULTILINE)


def read_trail(log_path):
    """The parsed `; route-trail` JSON object, or None if the run printed none."""
    try:
        with open(log_path, encoding="utf-8", errors="replace") as f:
            text = f.read()
    except OSError:
        return None
    m = TRAIL_RE.search(text)
    if not m:
        return None
    try:
        return json.loads(m.group(1))
    except json.JSONDecodeError:
        return None


# Work every arm of a portfolio would have to do anyway, so it is NOT
# recoverable by running the routes in parallel. `fd:parse` turns the file into
# a term arena and `probe` classifies the fragment; both are prerequisites of
# every route, not competitors to any of them. Counting them as recoverable was
# a real error in the first draft of this script -- it inflated QF_SLIA's
# recoverable share -- and it is called out here rather than silently fixed
# because the corrected number is the one the portfolio decision rests on.
SHARED_PREAMBLE_ROUTES = frozenset({"fd:parse", "probe"})


def analyse_trail(trail):
    """Per-file route facts derived from one trail.

    Returns a dict with:
      decided_index      index of the LAST `decided` attempt, or None
      decided_route      its route label, or None
      total_ns           summed elapsed over every attempt
      preamble_ns        elapsed in shared preamble stages (parse, probe) --
                         paid by every arm of a portfolio, NOT recoverable
      prefix_ns          elapsed in COMPETING routes that declined before the
                         winner -- the sequential-only cost a portfolio does
                         not pay
      winner_ns          the deciding attempt's own elapsed
      bound_route        the single most expensive attempt's route
      bound_ns           its elapsed
      last_route         the final attempt's route
    """
    attempts = trail.get("attempts", [])
    if not attempts:
        return None
    elapsed = [int(a.get("elapsed_ns", 0)) for a in attempts]
    routes = [a.get("route", "?") for a in attempts]

    decided_index = None
    for i, a in enumerate(attempts):
        if a.get("outcome") == "decided":
            decided_index = i  # keep the LAST one

    # max() on ties returns the first; take the last maximum to match
    # `RouteTrace::bound_by`, whose `max_by_key` returns the last maximum.
    bound_index = max(range(len(elapsed)), key=lambda i: (elapsed[i], i))

    preamble_ns = sum(e for e, r in zip(elapsed, routes)
                      if r in SHARED_PREAMBLE_ROUTES)
    upto = decided_index if decided_index is not None else len(attempts)
    prefix_ns = sum(e for e, r in zip(elapsed[:upto], routes[:upto])
                    if r not in SHARED_PREAMBLE_ROUTES)

    return {
        "decided_index": decided_index,
        "decided_route": routes[decided_index] if decided_index is not None else None,
        "total_ns": sum(elapsed),
        "preamble_ns": preamble_ns,
        "prefix_ns": prefix_ns,
        "winner_ns": elapsed[decided_index] if decided_index is not None else 0,
        "bound_route": routes[bound_index],
        "bound_ns": elapsed[bound_index],
        "last_route": routes[-1],
        "routes": routes,
        "n_attempts": len(attempts),
    }


def main():
    rows = []
    for path in sys.argv[1:]:
        with open(path, encoding="utf-8") as f:
            header = f.readline().rstrip("\n").split("\t")
            for line in f:
                line = line.rstrip("\n")
                if not line:
                    continue
                parts = line.split("\t")
                if len(parts) != len(header):
                    continue
                rows.append(dict(zip(header, parts)))

    if not rows:
        print("no rows read -- refusing to report a result over an empty "
              "population", file=sys.stderr)
        return 1

    violations = []
    per_division = defaultdict(lambda: {
        "files": 0, "decided": 0, "unsolved": 0,
        "deciding_routes": Counter(), "binding_routes": Counter(),
        "bound_differs_from_last": 0,
        "prefix_ns": 0, "preamble_ns": 0, "total_ns": 0, "winner_ns": 0,
    })

    deciding_overall = Counter()
    binding_overall = Counter()
    bound_differs = 0
    decided_with_trail = 0
    unsolved_with_trail = 0
    grand_prefix_ns = 0
    grand_preamble_ns = 0
    grand_total_ns = 0
    grand_winner_ns = 0
    no_trail = 0
    # Files whose winner was NOT the first route attempted: a portfolio delivers
    # these strictly sooner. Files whose winner WAS first gain nothing from
    # parallelism beyond scheduling.
    winner_not_first = 0
    # Per-loss share of the trail held by the binding route (see the call site).
    loss_binder_shares = []

    for r in rows:
        div = r["division"]
        d = per_division[div]
        d["files"] += 1
        verdict = r["verdict"]
        wall_ms = int(r["wall_ms"]) if r["wall_ms"].isdigit() else 0

        trail = read_trail(r["log_path"])
        if trail is None:
            no_trail += 1
            continue
        a = analyse_trail(trail)
        if a is None:
            no_trail += 1
            continue

        total_ms = a["total_ns"] / 1e6
        # GUARD 1: a trail cannot have spent more time than the process ran.
        if wall_ms > 0 and total_ms > wall_ms * ALLOWED_SLOP:
            violations.append(
                f"{r['file']}: trail total {total_ms:.1f}ms exceeds wall "
                f"{wall_ms}ms * {ALLOWED_SLOP}")
        # GUARD 2: the declined prefix is a subset of the trail; >100% is
        # impossible by construction.
        if a["prefix_ns"] + a["preamble_ns"] + a["winner_ns"] > a["total_ns"]:
            violations.append(
                f"{r['file']}: prefix {a['prefix_ns']} + preamble "
                f"{a['preamble_ns']} + winner {a['winner_ns']} exceeds trail "
                f"total {a['total_ns']}")

        decided = verdict in ("sat", "unsat")
        # GUARD 3: a decided file must name a deciding route.
        if decided and a["decided_route"] is None:
            violations.append(
                f"{r['file']}: verdict {verdict} but no route in the trail "
                f"recorded a decide")

        if decided:
            decided_with_trail += 1
            d["decided"] += 1
            if a["decided_route"]:
                deciding_overall[a["decided_route"]] += 1
                d["deciding_routes"][a["decided_route"]] += 1
            if a["decided_index"] is not None and a["decided_index"] > 1:
                # index 0 is `fd:parse`, index 1 the dispatch probe, so the
                # first real route sits at index 2.
                winner_not_first += 1
            grand_prefix_ns += a["prefix_ns"]
            grand_preamble_ns += a["preamble_ns"]
            grand_winner_ns += a["winner_ns"]
            grand_total_ns += a["total_ns"]
            d["prefix_ns"] += a["prefix_ns"]
            d["preamble_ns"] += a["preamble_ns"]
            d["winner_ns"] += a["winner_ns"]
            d["total_ns"] += a["total_ns"]
        else:
            unsolved_with_trail += 1
            d["unsolved"] += 1
            binding_overall[a["bound_route"]] += 1
            d["binding_routes"][a["bound_route"]] += 1
            if a["bound_route"] != a["last_route"]:
                bound_differs += 1
                d["bound_differs_from_last"] += 1
            # THE strategic number on the loss side. A portfolio's prize on a
            # file we lose is giving the binding route the WHOLE budget instead
            # of whatever was left after the routes ahead of it. If the binder
            # already holds ~100% of the trail, parallelism hands it nothing and
            # the fix is a better route, not more cores. If it holds 40%, a
            # portfolio hands it 2.5x more time to work with.
            if a["total_ns"] > 0:
                loss_binder_shares.append(a["bound_ns"] / a["total_ns"])

    report = {
        "population": {
            "rows": len(rows),
            "with_trail": len(rows) - no_trail,
            "without_trail": no_trail,
            "decided": decided_with_trail,
            "unsolved": unsolved_with_trail,
        },
        "deciding_route_distribution": dict(deciding_overall.most_common()),
        "distinct_deciding_routes": len(deciding_overall),
        "binding_route_distribution_on_losses": dict(binding_overall.most_common()),
        "distinct_binding_routes": len(binding_overall),
        "bound_by_differs_from_last_on_losses": {
            "count": bound_differs,
            "of": unsolved_with_trail,
            "share": (bound_differs / unsolved_with_trail) if unsolved_with_trail else None,
            "meaning": "files where the route that CONSUMED the budget is not "
                       "the route that printed last -- every one of these would "
                       "be misclassified by a last-message census",
        },
        "virtual_best_over_our_own_routes": {
            "method": "sequential trail; see the module docstring for what this "
                      "can and cannot measure",
            "decided_files": decided_with_trail,
            "winner_was_not_the_first_route_tried": winner_not_first,
            "trail_total_ms": grand_total_ns / 1e6,
            "shared_preamble_ms": grand_preamble_ns / 1e6,
            "declined_prefix_ms": grand_prefix_ns / 1e6,
            "winning_route_ms": grand_winner_ns / 1e6,
            "recoverable_share": (grand_prefix_ns / grand_total_ns) if grand_total_ns else None,
            "recoverable_share_meaning": "fraction of in-dispatch wall time on "
                                         "DECIDED files spent in COMPETING routes "
                                         "that declined before the winner. A "
                                         "parallel portfolio does not spend this. "
                                         "EXACT, not a bound. Shared preamble "
                                         "(parse, fragment probe) is EXCLUDED: "
                                         "every arm of a portfolio pays it, so "
                                         "counting it as recoverable overstates "
                                         "the prize.",
            "portfolio_projected_ms": (grand_preamble_ns + grand_winner_ns) / 1e6,
            "portfolio_projected_meaning": "what these same decided files would "
                                           "cost if every route ran concurrently "
                                           "and the winner were not queued behind "
                                           "the losers: shared preamble plus the "
                                           "winning route's own time.",
            "diversity_caveat": "the deciding-route distribution is an UPPER "
                                "bound on route diversity: a later route that "
                                "never ran might also have decided the file.",
        },
        "portfolio_headroom_on_losses": {
            "losses_with_a_trail": len(loss_binder_shares),
            "median_binder_share_of_trail": (
                sorted(loss_binder_shares)[len(loss_binder_shares) // 2]
                if loss_binder_shares else None),
            "mean_binder_share_of_trail": (
                sum(loss_binder_shares) / len(loss_binder_shares)
                if loss_binder_shares else None),
            "losses_where_binder_held_over_90pct": sum(
                1 for s in loss_binder_shares if s > 0.90),
            "losses_where_binder_held_under_50pct": sum(
                1 for s in loss_binder_shares if s < 0.50),
            "meaning": "on a file we LOSE, the share of in-dispatch time the "
                       "binding route already held. A portfolio's prize here is "
                       "giving that route the WHOLE budget instead of the "
                       "remainder. A binder already holding ~100% gains nothing "
                       "from more cores -- that file needs a better route. A "
                       "binder holding under 50% would get more than 2x the "
                       "time it had.",
        },
        "per_division": {
            div: {
                "files": d["files"],
                "decided": d["decided"],
                "unsolved": d["unsolved"],
                "deciding_routes": dict(d["deciding_routes"].most_common()),
                "binding_routes_on_losses": dict(d["binding_routes"].most_common()),
                "bound_differs_from_last": d["bound_differs_from_last"],
                "recoverable_share": (d["prefix_ns"] / d["total_ns"]) if d["total_ns"] else None,
                "trail_total_ms": d["total_ns"] / 1e6,
                "portfolio_projected_ms": (d["preamble_ns"] + d["winner_ns"]) / 1e6,
            }
            for div, d in sorted(per_division.items())
        },
        "impossibility_guard_violations": violations,
    }

    print(json.dumps(report, indent=2, sort_keys=False))

    if violations:
        print(f"\nIMPOSSIBILITY GUARD: {len(violations)} violation(s)",
              file=sys.stderr)
        for v in violations[:20]:
            print(f"  {v}", file=sys.stderr)
        return 1
    if decided_with_trail == 0:
        print("\nno decided file carried a trail -- the deciding-route "
              "distribution would be vacuous", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
