import sys

R = "/home/mjbommar/projects/personal/axeyum/references/"
CLAIMS = [
    ("z3/src/smt/smt_internalizer.cpp", 656, "mk_bool_var(q)"),
    ("z3/src/smt/smt_internalizer.cpp", 664, "set_quantifier_flag"),
    ("z3/src/smt/smt_internalizer.cpp", 665, "m_qmanager->add(q, generation)"),
    ("z3/src/smt/smt_internalizer.cpp", 523, "internalize_quantifier"),
    ("z3/src/smt/smt_internalizer.cpp", 288, "internalize_assertion"),
    ("z3/src/smt/smt_quantifier.cpp", 166, "void add(quantifier * q, unsigned generation)"),
    ("z3/src/smt/smt_quantifier.cpp", 818, "assign_eh(quantifier * q)"),
    ("z3/src/smt/smt_quantifier.cpp", 819, "m_active = true"),
    ("z3/src/smt/smt_quantifier.cpp", 849, "m_mam->add_pattern(q, mp)"),
    ("z3/src/smt/smt_context.cpp", 1473, "is_quantifier()"),
    ("z3/src/smt/smt_context.cpp", 1482, "l_true"),
    ("z3/src/smt/smt_context.cpp", 1485, "assign_quantifier"),
    ("z3/src/smt/smt_context.cpp", 1871, "m_qmanager->assign_eh(q)"),
    ("z3/src/smt/smt_context.cpp", 1687, "relevant_eh"),
    ("z3/src/smt/smt_context.cpp", 307, "is_quantifier"),
    ("z3/src/smt/qi_queue.cpp", 288, "mk_or(m.mk_not(q), s_instance)"),
    ("z3/src/smt/qi_queue.cpp", 336, "internalize_instance(lemma"),
    ("z3/src/smt/smt_context.h", 1784, "internalize_assertion(body"),
    ("cvc5/src/theory/quantifiers/instantiate.cpp", 293, "Kind::IMPLIES"),
    ("cvc5/src/theory/quantifiers/theory_quantifiers.cpp", 83, "preRegisterTerm"),
    ("cvc5/src/theory/quantifiers/theory_quantifiers.cpp", 93, "preRegisterQuantifier"),
    ("cvc5/src/theory/quantifiers/theory_quantifiers.cpp", 173, "preNotifyFact"),
    ("cvc5/src/theory/quantifiers/theory_quantifiers.cpp", 180, "Kind::FORALL"),
    ("cvc5/src/theory/quantifiers/theory_quantifiers.cpp", 182, "assertQuantifier(atom"),
    ("cvc5/src/theory/quantifiers_engine.cpp", 709, "preRegisterQuantifier"),
    ("cvc5/src/theory/quantifiers_engine.cpp", 738, "assertQuantifier"),
    ("cvc5/src/theory/quantifiers_engine.cpp", 766, "assertQuantifier(f)"),
    ("cvc5/src/theory/quantifiers/first_order_model.cpp", 91, "assertQuantifier"),
    ("cvc5/src/theory/quantifiers/first_order_model.cpp", 95, "d_forall_asserts.push_back"),
    ("cvc5/src/theory/quantifiers/quantifiers_registry.cpp", 32, "registerQuantifier"),
    ("cvc5/src/theory/quantifiers/ematching/instantiation_engine.cpp", 162,
     "getNumAssertedQuantifiers"),
    ("cvc5/src/theory/quantifiers/ematching/instantiation_engine.cpp", 165,
     "getAssertedQuantifier"),
    ("cvc5/src/theory/quantifiers/ematching/instantiation_engine.cpp", 166, "isQuantifierActive"),
    ("cvc5/src/theory/quantifiers/first_order_model.cpp", 297, "isQuantifierActive"),
]

bad = 0
for rel, lineno, needle in CLAIMS:
    try:
        with open(R + rel, errors="replace") as f:
            lines = f.readlines()
    except OSError as e:
        print(f"FAIL {rel}: {e}")
        bad += 1
        continue
    if lineno > len(lines):
        print(f"FAIL {rel}:{lineno} -- file has {len(lines)} lines")
        bad += 1
        continue
    line = lines[lineno - 1].rstrip("\n")
    ok = needle in line
    print(f"{'ok  ' if ok else 'FAIL'} {rel}:{lineno}  {line.strip()[:90]}")
    if not ok:
        bad += 1
        for d in range(-6, 7):
            j = lineno - 1 + d
            if 0 <= j < len(lines) and needle in lines[j]:
                print(f"      -> actually at :{j + 1}")
                break
print(f"\nREF CLAIMS={len(CLAIMS)} BAD={bad}")
sys.exit(1 if bad else 0)
