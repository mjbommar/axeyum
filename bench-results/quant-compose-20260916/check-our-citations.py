import sys

CLAIMS = [
    ("crates/axeyum-solver/src/qinst_egraph.rs", 127, "const POSITIVE_PATH_LEVEL"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 361, "const GROUND_SESSION_LEVEL"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 1283, "const GENERATION_LADDER_LEVEL"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 475, "fn positive_path_step"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 483, "BoolAnd | Op::BoolOr"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 485, "BoolNot"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 487, "Ite"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 423, "ground_session_level() >= 1"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 444, "ground_session_level() >= 2"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 1351, "fn generation_ladder_enabled"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 5337, "fn generation_ladder_check"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 5409, "if generation_ladder_enabled()"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 5437, "!generation_ladder_enabled()"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 1952, "let level = positive_path_level();"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 2739, "positive_path_level() >= 1"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 3032, "ground_session_level()"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 1937, "context: (polarity == Some(true))"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 1948, "None, scan)"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 1956, "positive_path_step("),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 2173, "peel_foralls"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 2181, "Some(true),"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 2185, "registration.context.is_none()"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 2186, "MAX_DISCOVERED_REGISTRATIONS"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 7279, "quantifier.context.is_some()"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 7291, "inactive_positive_capped"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 7294, "inactive_dropped"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 5241, "ground_session_abstracts()"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 5249, "ground_session_hosts_arithmetic()"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 4885, "ground_session_hosts_arithmetic()"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 4902, "ground_session_abstracts()"),
    ("crates/axeyum-solver/src/qinst_egraph.rs", 4903, "ground_session_hosts_arithmetic()"),
    ("crates/axeyum-solver/src/quant_macro_inline.rs", 124, "fn macro_inline_enabled"),
    ("crates/axeyum-solver/src/quant_macro_inline.rs", 127, "parse_macro_inline_lever"),
    ("crates/axeyum-solver/src/auto.rs", 13444, "macro_inline_enabled()"),
    ("crates/axeyum-solver/src/config_registry.rs", 7706, "POSITIVE_PATH_LEVEL"),
    ("crates/axeyum-solver/src/config_registry.rs", 7173, "GROUND_SESSION_LEVEL"),
    ("crates/axeyum-solver/src/config_registry.rs", 7125, "GENERATION_LADDER_LEVEL"),
]

bad = 0
for path, lineno, needle in CLAIMS:
    with open(path) as f:
        lines = f.readlines()
    if lineno > len(lines):
        print(f"FAIL {path}:{lineno} -- file has {len(lines)} lines")
        bad += 1
        continue
    line = lines[lineno - 1].rstrip("\n")
    ok = needle in line
    print(f"{'ok  ' if ok else 'FAIL'} {path}:{lineno}  {line.strip()[:100]}")
    if not ok:
        bad += 1
        # show a small window to find the real line
        for d in range(-4, 5):
            j = lineno - 1 + d
            if 0 <= j < len(lines) and needle in lines[j]:
                print(f"      -> actually at :{j + 1}")
print(f"\nCLAIMS={len(CLAIMS)} BAD={bad}")
sys.exit(1 if bad else 0)
