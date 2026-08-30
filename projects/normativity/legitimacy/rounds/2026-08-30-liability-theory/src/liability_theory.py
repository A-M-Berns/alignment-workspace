"""Exact finite algebra for the liability-theory round."""

from fractions import Fraction


def dot(xs, ys):
    return sum((x * y for x, y in zip(xs, ys)), Fraction(0))


def total_variation(mu, nu):
    return sum((abs(x - y) for x, y in zip(mu, nu)), Fraction(0)) / 2


def underwriting_bound(theta, upper, deficit=Fraction(0)):
    if theta <= 0:
        raise ValueError("coverage must be positive")
    return (deficit + (1 - theta) * upper) / theta


def switching_debt(previous_mu, current_mu, previous_inventory):
    return max(Fraction(0), -dot(
        [x - y for x, y in zip(current_mu, previous_mu)], previous_inventory
    ))


def controlled_tv_bound(theta, upper, total_tv):
    if total_tv >= theta:
        raise ValueError("the closure requires total variation below coverage")
    return upper * (1 - theta + total_tv) / (theta - total_tv)


def terminal_liability(inventory):
    return max((max(Fraction(0), -x) for x in inventory), default=Fraction(0))


def running_liability(inventories):
    return max((terminal_liability(e) for e in inventories), default=Fraction(0))


def max_trimmed_expectation(values, theta):
    """Max of mu·values over mu_i >= theta, sum mu_i = 1."""
    residual = 1 - len(values) * theta
    if residual < 0:
        raise ValueError("empty trimmed simplex")
    return theta * sum(values, Fraction(0)) + residual * max(values)


def combined_row_deficit(profile_row_values, requirements, row_weights, theta):
    """Dual deficit for a specified convex combination of rows.

    profile_row_values[i][j] is row j's LHS at profile i.
    """
    combined_profiles = [dot(row, row_weights) for row in profile_row_values]
    required = dot(requirements, row_weights)
    return required - max_trimmed_expectation(combined_profiles, theta)
