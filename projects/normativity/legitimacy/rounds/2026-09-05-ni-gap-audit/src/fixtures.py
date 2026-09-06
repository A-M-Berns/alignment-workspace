from fractions import Fraction


def sat(row, point):
    coeffs, bound = row
    return sum((a * x for a, x in zip(coeffs, point)), Fraction(0)) <= bound


def region(rows, point):
    return all(Fraction(0) <= x <= Fraction(1) for x in point) and all(
        sat(row, point) for row in rows
    )


def progress(mu, loss):
    return sum((mu[e] * loss[e] for e in mu), Fraction(0))


def progress_rhs(services, transport, multiplier, defect, error, gamma, diameter):
    transported_error = sum(
        (transport[e, s] * error[e, s] for e, s in transport), Fraction(0)
    )
    mass = sum(transport.values(), Fraction(0))
    weighted_defect = sum(
        (services[s] * defect[s] for s in services), Fraction(0)
    )
    return gamma * weighted_defect + transported_error + diameter * (1 - mass)
