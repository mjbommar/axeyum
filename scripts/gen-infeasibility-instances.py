#!/usr/bin/env python3
"""Generate the committed operations-research infeasibility instances.

WHY A GENERATOR AND A COMMITTED ARTIFACT BOTH EXIST. The `.smt2` files under
`artifacts/instances/infeasibility/` are the evidence: a checker replays them
byte-for-byte, so they must be in the tree and must not be produced on the fly
by a test. But a 100-assertion roster written by hand is unreviewable -- nobody
can confirm that the ONLY contradiction is the one advertised. This script is
the audit trail: the model, the data, and the intended contradiction in one
readable place, emitting exactly what is committed.

Re-run and diff:  python3 scripts/gen-infeasibility-instances.py && git diff

DESIGN RULE FOR EVERY INSTANCE HERE. The contradiction must be buried: the
instance minus its explanation has to be genuinely satisfiable, and the
explanation has to be a small fraction of the rows. An instance whose core is
the whole model demonstrates nothing. The core sizes these are built for are
recorded in each header and MEASURED by
`crates/axeyum-solver/examples/infeasibility_iis.rs`; nothing here asserts
minimality, the example re-solves every leave-one-out subset to establish it.
"""

import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
OUT = os.path.join(ROOT, "artifacts", "instances", "infeasibility")


def emit(name, lines):
    path = os.path.join(OUT, name)
    with open(path, "w") as handle:
        handle.write("\n".join(lines) + "\n")
    n = sum(1 for line in lines if line.startswith("(assert (! "))
    print(f"{name}: {n} named assertions")


# ---------------------------------------------------------------------------
# 1. ICU night roster (QF_LIA).
#
# Six nurses, seven nights, three of them ICU-certified. The ward needs at least
# one certified nurse on every night; nobody works two nights running; nobody
# works more than three nights a week; everybody works at least one.
#
# THE BURIED CONTRADICTION is Thursday night (night 4). Alice is on annual
# leave, Cara is in mandatory recertification training, and Bob is pinned to the
# Wednesday handover -- so the rest rule takes him off Thursday too. Three
# separate, individually reasonable rows plus the rest rule plus the Thursday
# coverage minimum: five rows out of 102, and none of the five mentions the
# other four. Every other night of the week rosters fine.
# ---------------------------------------------------------------------------
def roster():
    nurses = ["alice", "bob", "cara", "dev", "eli", "fern"]
    certified = ["alice", "bob", "cara"]
    nights = range(1, 8)

    lines = [
        "; ICU night roster, one ward, one week -- INFEASIBLE.",
        ";",
        "; 6 nurses (alice bob cara dev eli fern), 7 nights, ICU certification",
        "; held by alice/bob/cara only. Rows: variable domains, nightly certified",
        "; coverage, the consecutive-night rest rule, weekly caps, a minimum-hours",
        "; floor, and five fixed pre-assignments (leave, training, handover duty).",
        ";",
        "; The infeasibility is NOT a global staff-hours shortage -- certified",
        "; capacity is 9 night-shifts against a requirement of 7. It is local to",
        "; night 4 and involves five rows; the other 97 are jointly satisfiable.",
        "",
        "(set-logic QF_LIA)",
        "(set-option :produce-unsat-cores true)",
        "",
    ]
    for nurse in nurses:
        for night in nights:
            lines.append(f"(declare-fun x_{nurse}_{night} () Int)")
    lines.append("")

    lines.append("; -- variable domains: a nurse either works a night or does not")
    for nurse in nurses:
        for night in nights:
            v = f"x_{nurse}_{night}"
            lines.append(
                f"(assert (! (and (>= {v} 0) (<= {v} 1)) :named dom_{nurse}_{night}))"
            )
    lines.append("")

    lines.append("; -- coverage: at least one ICU-certified nurse on every night")
    for night in nights:
        terms = " ".join(f"x_{n}_{night}" for n in certified)
        lines.append(f"(assert (! (>= (+ {terms}) 1) :named cov_night{night}))")
    lines.append("")

    lines.append("; -- rest rule: no nurse works two consecutive nights")
    for nurse in nurses:
        for night in range(1, 7):
            lines.append(
                f"(assert (! (<= (+ x_{nurse}_{night} x_{nurse}_{night + 1}) 1)"
                f" :named rest_{nurse}_n{night}n{night + 1}))"
            )
    lines.append("")

    lines.append("; -- weekly cap: at most three night shifts per nurse")
    for nurse in nurses:
        terms = " ".join(f"x_{nurse}_{j}" for j in nights)
        lines.append(f"(assert (! (<= (+ {terms}) 3) :named cap_{nurse}))")
    lines.append("")

    lines.append("; -- minimum hours floor: every nurse works at least one night")
    for nurse in nurses:
        terms = " ".join(f"x_{nurse}_{j}" for j in nights)
        lines.append(f"(assert (! (>= (+ {terms}) 1) :named minhours_{nurse}))")
    lines.append("")

    lines.append("; -- fixed pre-assignments")
    lines.append(
        "(assert (! (= x_alice_4 0) :named leave_alice_night4))"
        "  ; annual leave, approved"
    )
    lines.append(
        "(assert (! (= x_cara_4 0) :named training_cara_night4))"
        "  ; ICU recertification"
    )
    lines.append(
        "(assert (! (= x_bob_3 1) :named handover_bob_night3))"
        "  ; midweek handover duty"
    )
    lines.append("(assert (! (= x_dev_1 0) :named leave_dev_night1))")
    lines.append("(assert (! (= x_eli_7 0) :named leave_eli_night7))")
    lines.append("")
    lines.append("(check-sat)")
    lines.append("(get-unsat-core)")
    lines.append("(exit)")
    return lines


# ---------------------------------------------------------------------------
# 2. Hazmat load plan (QF_LIA).
#
# Twelve pallets onto five trucks, weight caps, and a dangerous-goods rule:
# class-3 pallets ride only on ADR-certified trucks, and segregation permits at
# most one class-3 pallet per truck.
#
# THE BURIED CONTRADICTION is a pigeonhole: three class-3 pallets, two certified
# trucks, one class-3 pallet allowed per truck. Nothing in the model says
# "three into two" -- it has to be assembled out of three assignment rows, nine
# certification exclusions and two segregation rows. The weight caps are slack
# and appear in no core; the pigeonhole is the only contradiction.
# ---------------------------------------------------------------------------
def loadplan():
    pallets = [f"p{i}" for i in range(1, 13)]
    trucks = [f"t{i}" for i in range(1, 6)]
    weight = {
        "p1": 320, "p2": 410, "p3": 275, "p4": 190, "p5": 350, "p6": 240,
        "p7": 415, "p8": 305, "p9": 180, "p10": 260, "p11": 330, "p12": 225,
    }
    class3 = ["p2", "p5", "p8"]
    adr_certified = ["t1", "t3"]

    lines = [
        "; Outbound load plan, one depot, one dispatch -- INFEASIBLE.",
        ";",
        "; 12 pallets onto 5 trucks. Rows: variable domains, one-truck-per-pallet",
        "; assignment, per-truck weight capacity, ADR certification exclusions for",
        "; the three class-3 dangerous-goods pallets, and the segregation rule",
        "; capping each truck at one class-3 pallet.",
        ";",
        "; Total weight is 3500 kg against 6000 kg of capacity, so nothing is",
        "; short. The contradiction is a pigeonhole hidden in the dangerous-goods",
        "; rules: three class-3 pallets, two certified trucks, one per truck.",
        "",
        "(set-logic QF_LIA)",
        "(set-option :produce-unsat-cores true)",
        "",
    ]
    for pallet in pallets:
        for truck in trucks:
            lines.append(f"(declare-fun y_{pallet}_{truck} () Int)")
    lines.append("")

    lines.append("; -- variable domains")
    for pallet in pallets:
        for truck in trucks:
            v = f"y_{pallet}_{truck}"
            lines.append(
                f"(assert (! (and (>= {v} 0) (<= {v} 1)) :named dom_{pallet}_{truck}))"
            )
    lines.append("")

    lines.append("; -- every pallet rides on exactly one truck")
    for pallet in pallets:
        terms = " ".join(f"y_{pallet}_{t}" for t in trucks)
        lines.append(f"(assert (! (= (+ {terms}) 1) :named assign_{pallet}))")
    lines.append("")

    lines.append("; -- per-truck payload capacity, 1200 kg")
    for truck in trucks:
        terms = " ".join(f"(* {weight[p]} y_{p}_{truck})" for p in pallets)
        lines.append(f"(assert (! (<= (+ {terms}) 1200) :named capacity_{truck}))")
    lines.append("")

    lines.append("; -- ADR: class-3 goods only on certified trucks (t1, t3)")
    for pallet in class3:
        for truck in trucks:
            if truck not in adr_certified:
                lines.append(
                    f"(assert (! (= y_{pallet}_{truck} 0)"
                    f" :named adr_{pallet}_not_{truck}))"
                )
    lines.append("")

    lines.append("; -- segregation: at most one class-3 pallet per truck")
    for truck in adr_certified:
        terms = " ".join(f"y_{p}_{truck}" for p in class3)
        lines.append(f"(assert (! (<= (+ {terms}) 1) :named segregation_{truck}))")
    lines.append("")

    lines.append("; -- customer routing commitments")
    lines.append("(assert (! (= y_p1_t1 1) :named route_p1_t1))")
    lines.append("(assert (! (= y_p12_t5 1) :named route_p12_t5))")
    lines.append("")
    lines.append("(check-sat)")
    lines.append("(get-unsat-core)")
    lines.append("(exit)")
    return lines


# ---------------------------------------------------------------------------
# 3. Project schedule with a delivery deadline (QF_LRA).
#
# Twenty tasks, continuous start times, a precedence DAG, material release dates
# and a contractual 20-day delivery promise.
#
# THE BURIED CONTRADICTION is a critical chain: the long-lead casting for task
# t03 does not land until day 6, and from t03 the chain t03 -> t06 -> t09 -> t12
# is 5 + 6 + 3 = 14 days of work followed by t12's own 4, so delivery cannot be
# before day 24 against a promise of 20. Five rows out of 60, and the chain is
# not the longest path by edge count -- it is one of thirty precedence edges.
#
# This instance is deliberately over the REALS: it is the one whose refutation
# is a textbook Farkas combination with every multiplier 1, which is the form
# the Alethe `la_generic` route and the kernel arithmetic prelude consume.
# ---------------------------------------------------------------------------
def schedule():
    # (task, duration)
    duration = {
        "t01": 4, "t02": 3, "t03": 5, "t04": 2, "t05": 3,
        "t06": 6, "t07": 2, "t08": 4, "t09": 3, "t10": 2,
        "t11": 3, "t12": 4, "t13": 2, "t14": 3, "t15": 2,
        "t16": 4, "t17": 2, "t18": 3, "t19": 2, "t20": 3,
    }
    precedence = [
        ("t01", "t03"), ("t01", "t04"), ("t02", "t05"), ("t02", "t07"),
        ("t03", "t06"), ("t04", "t08"), ("t05", "t08"), ("t06", "t09"),
        ("t07", "t10"), ("t08", "t11"), ("t09", "t12"), ("t10", "t13"),
        ("t11", "t14"), ("t13", "t15"), ("t14", "t16"), ("t15", "t17"),
        ("t16", "t18"), ("t17", "t19"), ("t18", "t20"), ("t19", "t20"),
        ("t04", "t07"), ("t05", "t10"), ("t07", "t11"), ("t10", "t14"),
        ("t13", "t16"), ("t15", "t18"), ("t02", "t04"), ("t01", "t02"),
        ("t11", "t15"), ("t14", "t17"),
    ]
    tasks = sorted(duration)

    lines = [
        "; Project schedule with a contractual delivery date -- INFEASIBLE.",
        ";",
        "; 20 tasks, continuous (Real) start times in days from project start,",
        "; 30 precedence edges, 4 material release dates, 5 crew-availability",
        "; windows, and one delivery deadline on t12.",
        ";",
        "; Nineteen of the twenty tasks can be scheduled inside the window. The",
        "; contradiction is a single critical chain whose head is a long-lead",
        "; material release; it is a five-row explanation in a 60-row model, and",
        "; its Farkas refutation has every multiplier equal to 1.",
        "",
        "(set-logic QF_LRA)",
        "(set-option :produce-unsat-cores true)",
        "",
    ]
    for task in tasks:
        lines.append(f"(declare-fun s_{task} () Real)")
    lines.append("")

    lines.append("; -- no task starts before the project does")
    for task in tasks:
        lines.append(f"(assert (! (>= s_{task} 0.0) :named start_{task}))")
    lines.append("")

    lines.append("; -- precedence: a successor waits for its predecessor to finish")
    for a, b in precedence:
        lines.append(
            f"(assert (! (>= s_{b} (+ s_{a} {duration[a]}.0))"
            f" :named prec_{a}_{b}))"
        )
    lines.append("")

    lines.append("; -- material release dates (long-lead procurement)")
    lines.append("(assert (! (>= s_t03 6.0) :named material_t03))  ; long-lead casting")
    lines.append("(assert (! (>= s_t08 2.0) :named material_t08))")
    lines.append("(assert (! (>= s_t16 3.0) :named material_t16))")
    lines.append("(assert (! (>= s_t20 1.0) :named material_t20))")
    lines.append("")

    lines.append("; -- crew availability windows")
    lines.append("(assert (! (<= s_t02 12.0) :named crew_t02))")
    lines.append("(assert (! (<= s_t05 14.0) :named crew_t05))")
    lines.append("(assert (! (<= s_t07 16.0) :named crew_t07))")
    lines.append("(assert (! (<= s_t10 18.0) :named crew_t10))")
    lines.append("(assert (! (<= s_t13 20.0) :named crew_t13))")
    lines.append("")

    lines.append("; -- contractual delivery: t12 must finish by day 20")
    lines.append(
        "(assert (! (<= (+ s_t12 4.0) 20.0) :named deadline_delivery))"
    )
    lines.append("")
    lines.append("(check-sat)")
    lines.append("(get-unsat-core)")
    lines.append("(exit)")
    return lines


if __name__ == "__main__":
    os.makedirs(OUT, exist_ok=True)
    emit("roster-icu-night.smt2", roster())
    emit("loadplan-hazmat.smt2", loadplan())
    emit("schedule-deadline.smt2", schedule())
