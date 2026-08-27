# Lane 150: Fix allowlist validator for logic prelude

## Status: COMPLETED

### Analysis

All six quarantined facts are real kernel declarations, confirmed from `kernel.environment()`:
1. `Or.resolve_right` - real dotted theorem name (Or namespace)
2. `Eq.symm` - real dotted theorem name (Eq namespace)
3. `not_not_imp` - logic prelude undotted declaration
4. `not_not_not_intro` - logic prelude undotted declaration
5. `demorgan_or_not_and` - logic prelude undotted declaration
6. `congrFun'` - logic prelude undotted declaration

### Fix Implemented

**Updated `KERNEL_THEOREM_RE` regex:**
- Added missing namespaces: And, Decidable, Eq, Iff, Or
- Removed unused: Str (verified to match zero declarations)

**Added `LOGIC_UNDOTTED` allowlist:**
- Explicit set of 16 logic prelude bare names
- Only these accept undotted form (typo guard maintained)

**Updated `kernel_theorem_is_valid()` function:**
- Checks KERNEL_THEOREM_RE for dotted names
- Checks LOGIC_UNDOTTED for bare names
- Returns True for either, False for others

### Trade-off Decision

Accepting bare names ONLY from logic prelude (LOGIC_UNDOTTED):
- **Pros:** Registers all six quarantined facts; maintains typo guard on dotted names
- **Cons:** More complex than fully open bare names; requires updating LOGIC_UNDOTTED if new undotted declarations added
- **Rationale:** The typo guard is critical for soundness—any bare identifier outside this set is still rejected. Only the kernel-admitted logic prelude names are permitted.

### Verification

1. **Functional test:** `scripts/tests/test-allowlist-fix.py` (all pass)
2. **Guard test:** `scripts/tests/mutation-verify-guards.py` (15/15 pass)
3. **Validation:** `python3 scripts/validate-facts.py` → 0 errors on 1809 facts
4. **Coverage:** 
   - kernel_theorems: 1471
   - registered: 1461
   - curated: 474 (unmoved, as required)

### Implementation Details

- Or namespace includes: Or.elim, Or.resolve_left, Or.resolve_right, etc.
- Eq namespace includes: Eq.symm, etc.
- And, Decidable, Iff namespaces similarly included
- Str correctly removed (no declarations match it)

The allowlist is now synchronized with actual kernel.environment() declarations as of 2026-08-27.
