#!/usr/bin/env python3
"""Check every newly decided file against z3, cvc5 and its declared `:status`.

Exits NON-ZERO on any disagreement, so the check cannot pass by being read
charitably. It also prints how much of the agreement is VACUOUS -- a reference
that returned `unknown` agrees with nothing, and a zero-disagreement count over
a population the references mostly could not decide means very little.
"""
import csv
import sys

D = {"sat", "unsat"}
rows = list(csv.DictReader(open(sys.argv[1]), delimiter="\t"))
if not rows:
    print("ABORT: no rows")
    sys.exit(2)
if any(r["lever_refused"] == "yes" for r in rows):
    print("ABORT: a lever refused its value on some row")
    sys.exit(2)
killed = [r for r in rows if r["ax_k"] != "ok"]
if killed:
    print(f"ABORT: {len(killed)} of our own runs were killed rather than answering")
    sys.exit(2)

dec = [r for r in rows if r["axeyum"] in D]
print(f"{len(rows)} newly decided files re-run; we decide {len(dec)} of them here")
bad = [
    r
    for r in dec
    if any(r[k] in D and r[k] != r["axeyum"] for k in ("z3", "cvc5", "status"))
]
for k in ("status", "z3", "cvc5"):
    comparable = [r for r in dec if r[k] in D]
    agree = sum(1 for r in comparable if r[k] == r["axeyum"])
    print(
        f"  vs {k:<7} {agree}/{len(comparable)} agree "
        f"({len(dec) - len(comparable)} of our {len(dec)} not comparable: "
        f"the reference returned no verdict)"
    )
beat = [r for r in dec if r["z3"] not in D and r["cvc5"] not in D]
if beat:
    print(f"\n  we decide {len(beat)} file(s) NEITHER reference does:")
    for r in beat:
        print(
            f"    {r['axeyum']:<6} (:status {r['status']}, z3 {r['z3_k']}, "
            f"cvc5 {r['cvc5_k']})  {r['file']}"
        )
und = [r for r in rows if r["axeyum"] not in D]
if und:
    print(f"\n  {len(und)} still unknown at the SHIPPED setting (the A/B's larger arms")
    print("  reached them; the shipped default deliberately does not):")
    for r in und:
        print(f"    z3 {r['z3']:<7} cvc5 {r['cvc5']:<7} :status {r['status']:<7} {r['file']}")
rc = sum(1 for r in rows if r["cvc5_k"] == "rc134")
if rc:
    print(f"\n  cvc5 hit the protocol's 8 GiB cap on {rc} row(s) (rc134), as on the board.")
print()
if bad:
    print(f"DISAGREEMENTS: {len(bad)}")
    for r in bad:
        print("   ", r)
    sys.exit(1)
print("0 disagreements against :status, z3 and cvc5.")
