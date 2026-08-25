"""Shared scaffolding for the ``test_prop_*`` property suites.

One idea, and it is the reason this file exists rather than a helper per suite:
**a property that never ran must not look like a property that passed.**

A hypothesis run over a partial function (`factor` declines, `MvPoly.add`
overflows, a random script comes back `unknown`) can spend all 200 examples on
inputs the operation refuses and still report a green test. That is the
inert-gate failure this repository has hit at every layer -- a corpus sweep that
compiled zero tests, a checker whose exit status did not depend on its finding.
:class:`Tally` makes the refusals countable and lets the test assert a floor on
the examples that were *actually checked*, so the suite fails when the
generator stops reaching the operation.

``assume()`` is deliberately not used for this: it silently discards the
example and leaves nothing to assert on afterwards.
"""

from __future__ import annotations

from dataclasses import dataclass, field


@dataclass
class Tally:
    """Counts examples by outcome so a suite can refuse a vacuous pass.

    ``checked`` is incremented when the property was genuinely evaluated;
    ``declined`` when the operation returned ``None`` (outside the fragment or
    an ``i128`` overflow -- a value, never an error) and there was nothing to
    check. ``reasons`` keeps one sample of each decline so a shrinking coverage
    story is visible in the failure message rather than in a debugger.
    """

    name: str
    checked: int = 0
    declined: int = 0
    reasons: dict[str, int] = field(default_factory=dict)

    def check(self) -> None:
        """Records one example on which the property was evaluated."""
        self.checked += 1

    def decline(self, reason: str) -> None:
        """Records one example the operation declined, with a reason."""
        self.declined += 1
        self.reasons[reason] = self.reasons.get(reason, 0) + 1

    def require(self, minimum: int) -> None:
        """Fails unless at least `minimum` examples were actually checked."""
        assert self.checked >= minimum, (
            f"{self.name}: only {self.checked} of {self.checked + self.declined} "
            f"examples were checked (floor {minimum}); declines={self.reasons}. "
            "A property that never ran is not a property that passed."
        )

    def __str__(self) -> str:
        return f"{self.name}: checked={self.checked} declined={self.declined} {self.reasons}"
