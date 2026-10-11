"""Exact 360-period arithmetic using wide fractions and signed CAS powers.

Run with a freshly built axeyum extension. This computes a mathematical example;
the result is independently compared to Python Fraction arithmetic, and every
rewrite is carried by a replayed v2 certificate.
"""
from fractions import Fraction
from axeyum import cas


def payment(principal: int, monthly_rate: Fraction, periods: int) -> Fraction:
    if periods <= 0:
        raise ValueError("periods must be positive")
    if monthly_rate == 0:
        expression = cas.Expr.int(principal) / periods
    else:
        factor = cas.Expr.rat(
            monthly_rate.numerator + monthly_rate.denominator,
            monthly_rate.denominator,
        )
        expression = cas.Expr.int(principal) * monthly_rate / (1 - factor ** -periods)
    produced = cas.normalize_trace(expression, wide=True)
    if produced.status != "produced" or produced.trace is None:
        raise ValueError(f"{produced.status}: {produced.detail}")
    trace = produced.trace
    if cas.replay_trace(trace.to_json(), expression, trace.result).status != "checked":
        raise AssertionError("exported payment trace failed original-statement replay")
    result = trace.result.eval({})
    if result is None:
        raise ValueError("payment expression is undefined")
    reference = (
        Fraction(principal, periods) if monthly_rate == 0
        else principal * monthly_rate / (1 - (1 + monthly_rate) ** -periods)
    )
    if result != reference:
        raise AssertionError("CAS result disagrees with independent Fraction arithmetic")
    return result


if __name__ == "__main__":
    result = payment(300000, Fraction(1, 240), 360)
    print("Exact monthly payment:", result)
    print("Numerator/denominator bits:", result.numerator.bit_length(), result.denominator.bit_length())
    print("Zero-rate control:", payment(300000, Fraction(0), 360))
