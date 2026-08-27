#!/usr/bin/env python3
"""Test the allowlist fix for logic prelude theorems."""
import re

# NEW REGEX - with all correct namespaces and no Str
NEW_RE = re.compile(
    r"^(?:AxReal|AxNat|Nat|Int|Real|Rat|List|Bool|Prop|Acc|WellFounded|"
    r"And|Decidable|Eq|Iff|Or|"
    r"CReal|Complex|CPoint|axeyum\.string\.[0-9]+)"
    r"(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)

# Logic prelude undotted names - only these are allowed without dots
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

tests = [
    # Should match (dotted namespaced)
    ('Or.resolve_right', True),
    ('Eq.symm', True),
    ('And.left', True),
    ('Decidable.em', True),
    ('Iff.mp', True),

    # Should match (undotted logic prelude)
    ('not_not_imp', True),
    ('not_not_not_intro', True),
    ('demorgan_or_not_and', True),
    ('congrFun\'', True),

    # Should NOT match (Str is gone)
    ('Str.something', False),

    # Should NOT match (non-existent)
    ('Foo.bar', False),
    ('typo_name', False),
]

failed = 0
for name, should_match in tests:
    dotted_match = NEW_RE.match(name) is not None
    undotted_match = name in LOGIC_UNDOTTED
    result = dotted_match or undotted_match
    if result != should_match:
        print(f"FAIL: {name:30} -> {result} (expected {should_match})")
        failed += 1

if failed == 0:
    print("All tests passed")
    exit(0)
else:
    print(f"{failed} tests failed")
    exit(1)
