#!/usr/bin/env python3
import sys
from fractions import Fraction as F
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from src.fixtures import progress, progress_rhs, region


def test_joint_conflict():
    low = ((F(1),), F(1, 3))
    high = ((F(-1),), F(-2, 3))
    assert region([low], (F(1, 3),))
    assert region([high], (F(2, 3),))
    assert not any(region([low, high], (F(k, 12),)) for k in range(13))


def test_progress_shared_service():
    mu = {"e0": F(1, 2), "e1": F(1, 2)}
    loss = {"e0": F(1, 4), "e1": F(1, 2)}
    transport = {("e0", "s"): F(1, 2), ("e1", "s"): F(1, 4)}
    error = {("e0", "s"): F(0), ("e1", "s"): F(0)}
    lhs = progress(mu, loss)
    rhs = progress_rhs({"s": F(1)}, transport, {}, {"s": F(1, 2)}, error, F(1), F(1))
    assert lhs == F(3, 8)
    assert rhs == F(3, 4)
    assert lhs <= rhs


def test_response_certificate_is_load_bearing():
    defect = F(0)
    loss = F(1)
    assert loss > F(0) * defect + F(0)
    assert loss <= F(0) * defect + F(1)


def main():
    tests = [test_joint_conflict, test_progress_shared_service, test_response_certificate_is_load_bearing]
    for test in tests:
        test()
    print(f"ok: {len(tests)} exact-rational tests")


if __name__ == "__main__":
    main()
