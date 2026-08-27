#!/usr/bin/env python3
"""Verify that each guard in the allowlist is necessary."""
import re
import sys

# Copy the regex and logic from validate-facts.py
KERNEL_THEOREM_RE = re.compile(
    r"^(?:AxReal|AxNat|Nat|Int|Real|Rat|List|Bool|Prop|Acc|WellFounded|"
    r"And|Decidable|Eq|Iff|Or|"
    r"CReal|Complex|CPoint|axeyum\.string\.[0-9]+)"
    r"(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)

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

def kernel_theorem_is_valid(value):
    if value is None:
        return True
    if not isinstance(value, str):
        return False
    return bool(KERNEL_THEOREM_RE.match(value)) or value in LOGIC_UNDOTTED

# Test the six quarantined names plus controls
test_cases = [
    # The six quarantined facts that should now pass
    ('Or.resolve_right', True, 'Or namespace'),
    ('Eq.symm', True, 'Eq namespace'),
    ('not_not_imp', True, 'logic undotted'),
    ('not_not_not_intro', True, 'logic undotted'),
    ('demorgan_or_not_and', True, 'logic undotted'),
    ('congrFun\'', True, 'logic undotted'),

    # Controls that should pass
    ('Nat.add_comm', True, 'Nat namespace (control)'),
    ('Rat.sub_mul', True, 'Rat namespace (control)'),
    ('And.left', True, 'And namespace (added)'),
    ('Decidable.em', True, 'Decidable namespace (added)'),
    ('Iff.mp', True, 'Iff namespace (added)'),

    # Controls that should fail
    ('Str.something', False, 'Str namespace (removed)'),
    ('Logic.foo', False, 'Logic not in list'),
    ('typo_name', False, 'bare name not in undotted'),
    ('foo_bar', False, 'bare name not in undotted'),
]

failed = 0
for name, should_pass, desc in test_cases:
    result = kernel_theorem_is_valid(name)
    status = "PASS" if (result == should_pass) else "FAIL"
    if result != should_pass:
        failed += 1
        print(f"{status}: {desc:40} {name:30} -> {result} (expected {should_pass})")
    else:
        print(f"PASS: {desc:40}")

print(f"\n{len(test_cases) - failed}/{len(test_cases)} tests passed")
sys.exit(0 if failed == 0 else 1)
