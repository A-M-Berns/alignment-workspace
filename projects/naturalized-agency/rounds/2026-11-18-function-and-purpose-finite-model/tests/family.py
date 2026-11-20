"""A fixed family of pseudo-random systems, from a linear congruential generator so the
family does not depend on the interpreter's random module."""
from src.system import System


class Lcg:
    def __init__(self, seed):
        self.x = seed

    def below(self, n):
        self.x = (self.x * 6364136223846793005 + 1442695040888963407) % (1 << 64)
        return (self.x >> 33) % n

    def sample(self, xs, k):
        xs = list(xs)
        return [xs.pop(self.below(len(xs))) for _ in range(k)]


def systems(count, seed=1, n=5):
    g = Lcg(seed)
    P = [f"p{i}" for i in range(n)]
    for _ in range(count):
        procs = {}
        for j in range(3 + g.below(4)):
            cond = [g.sample(P + ["g"], 1 + g.below(3)) for _ in range(1 + g.below(2))]
            procs[f"r{j}"] = (cond, g.sample(P, 1 + g.below(2)))
        yield System(P, ["g"], procs), g
