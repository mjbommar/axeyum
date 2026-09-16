import csv, sys, os
csv.field_size_limit(sys.maxsize)


def load(p):
    with open(p) as f:
        return list(csv.DictReader(f, delimiter="\t"))


def dec(v):
    return v in ("sat", "unsat")


H2H = {
    "UFLIA": "bench-results/six-divisions-headtohead-20260912/UFLIA.tsv",
    "AUFDTLIRA": "bench-results/dt-divisions-headtohead-20260912/AUFDTLIRA.tsv",
}

for name, p in H2H.items():
    r = load(p)
    br = sum(1 for x in r if dec(x["z3"]) or dec(x["cvc5"]))
    both = sum(1 for x in r if dec(x["z3"]) and dec(x["cvc5"]))
    print(
        f"{name}: rows={len(r)} axeyum={sum(1 for x in r if dec(x['axeyum']))} "
        f"z3={sum(1 for x in r if dec(x['z3']))} cvc5={sum(1 for x in r if dec(x['cvc5']))} "
        f"best-ref(union)={br} both={both}"
    )

for name, p in H2H.items():
    hb = {os.path.basename(x["file"]) for x in load(p)}
    with open(f"bench-results/parity-lists/{name}.txt") as f:
        pb = {os.path.basename(l.strip()) for l in f if l.strip()}
    lb = {
        os.path.basename(x["corpus_path"])
        for x in load(f"bench-results/ledger/t1-{name}-db31113fa.tsv")
    }
    print(
        f"{name}: |h2h|={len(hb)} |parity|={len(pb)} |ledger|={len(lb)} "
        f"h2h==parity:{hb == pb} ledger==parity:{lb == pb}"
    )
