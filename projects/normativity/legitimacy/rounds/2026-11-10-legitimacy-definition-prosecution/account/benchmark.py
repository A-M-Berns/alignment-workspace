"""BENCHMARK.md: the four examples of Carroll et al. (arXiv:2405.17713) under the paper's eight objectives,
by enumeration of action sequences, and the account's verdict on each example as extended.

The examples are deterministic with a known start, so a policy's behaviour is its action sequence.
Rewards and transitions are transcribed from the paper's figures 1, 2, 4 and 6; nothing is fetched."""
from __future__ import annotations

from fractions import Fraction as F
from itertools import product


class Example:
    def __init__(self, name, actions, noop, start, step, reward, thetas):
        self.name, self.actions, self.noop, self.start, self.step, self.reward, self.thetas = (
            name, actions, noop, start, step, reward, thetas)

    def run(self, seq, start=None):
        """[(s, theta, a, s2, theta2)] along an action sequence."""
        s, th = start or self.start
        out = []
        for a in seq:
            s2, th2 = self.step(s, th, a)
            out.append((s, th, a, s2, th2))
            s, th = s2, th2
        return out


def two_state(name, a_noop, a_infl, th0, th1, r):
    """Figures 1 and 6: one state; the influence action leads to th1 and the noop action back to th0."""
    return Example(name, [a_noop, a_infl], a_noop, ("s0", th0),
                   lambda s, th, a: ("s0", th1 if a == a_infl else th0),
                   lambda th, s, a, s2: F(r[th][a]), [th0, th1])


CONSPIRACY = two_state("conspiracy", "noop", "influence", "natural", "influenced",
                       {"natural": {"noop": 10, "influence": -100}, "influenced": {"noop": -100, "influence": 100}})
TRAINER = two_state("trainer", "noop", "nudge", "tired", "energized",
                    {"tired": {"noop": 10, "nudge": -100}, "energized": {"noop": -100, "nudge": 100}})


def writer(returns, on_next=True):
    """Figure 2.  The figure labels the poet's self-loop with both actions and leaves the arrow back unlabelled.
    returns=True: noop takes the poet back (no poetry, ambitious); False: both actions keep him a poet.
    on_next: the reward is of the state arrived at (False: of the state left)."""
    def step(s, th, a):
        if s == "no-poetry":
            return ("poetry", "unhappy") if a == "influence" else ("no-poetry", "ambitious")
        return ("no-poetry", "ambitious") if (returns and a == "noop") else ("poetry", "unhappy")
    r = {"ambitious": {"poetry": F(1), "no-poetry": F(1, 2)}, "unhappy": {"poetry": F(-10), "no-poetry": F(1, 2)}}
    return Example("writer's curse (%s, reward of the state %s)" % ("noop returns" if returns else "no return",
                                                                   "arrived at" if on_next else "left"),
                   ["noop", "influence"], "noop", ("no-poetry", "ambitious"), step,
                   lambda th, s, a, s2: r[th][s2 if on_next else s], ["ambitious", "unhappy"])


CLICKBAIT = Example("clickbait", ["news", "clickbait"], "news", ("s0", "normal"),
                    lambda s, th, a: ("s0", "disillusioned" if (th == "disillusioned" or a == "clickbait") else "normal"),
                    lambda th, s, a, s2: {"normal": {"clickbait": F(2), "news": F(1)},
                                          "disillusioned": {"clickbait": F(0), "news": F(1, 2)}}[th][a],
                    ["normal", "disillusioned"])


# -- the eight objectives ------------------------------------------------------------------------------
def value(ex, seq, objective, start=None, theta_star=None):
    tr = ex.run(seq, start)
    if objective == "real-time":
        return sum(ex.reward(th, s, a, s2) for s, th, a, s2, _ in tr)
    if objective == "final":
        last = tr[-1][4]
        return sum(ex.reward(last, s, a, s2) for s, _, a, s2, _ in tr)
    if objective == "initial":
        first = tr[0][1]
        return sum(ex.reward(first, s, a, s2) for s, _, a, s2, _ in tr)
    if objective == "natural":
        nat = ex.run([ex.noop] * len(seq), start)
        return sum(ex.reward(n[1], s, a, s2) for n, (s, _, a, s2, _) in zip(nat, tr))
    if objective == "privileged":
        return sum(ex.reward(theta_star, s, a, s2) for s, _, a, s2, _ in tr)
    raise KeyError(objective)


def thetas_of(ex, seq, start=None):
    tr = ex.run(seq, start)
    return [t[1] for t in tr] + [tr[-1][4]]


def optimal(ex, H, objective, start=None, theta_star=None):
    """The set of optimal action sequences."""
    seqs = list(product(ex.actions, repeat=H))
    if objective == "myopic":
        out = []
        for seq in seqs:
            tr = ex.run(seq, start)
            if all(ex.reward(th, s, a, s2) == max(ex.reward(th, s, b, ex.step(s, th, b)[0]) for b in ex.actions)
                   for s, th, a, s2, _ in tr):
                out.append(seq)
        return out
    if objective == "constrained":
        nat = thetas_of(ex, [ex.noop] * H, start)
        seqs = [q for q in seqs if thetas_of(ex, q, start) == nat]
        objective = "real-time"
    if objective == "pareto-ud":
        eu = {q: tuple(value(ex, q, "privileged", start, th) for th in ex.thetas) for q in seqs}
        base = eu[tuple([ex.noop] * H)]
        ud = [q for q in seqs if all(x >= y for x, y in zip(eu[q], base))]
        return [q for q in ud if not any(all(x >= y for x, y in zip(eu[p], eu[q])) and eu[p] != eu[q] for p in ud)]
    vals = {q: value(ex, q, objective, start, theta_star) for q in seqs}
    best = max(vals.values())
    return [q for q, v in vals.items() if v == best]


def cell(ex, H, objective, expected, start=None, theta_star=None):
    """Whether the paper's stated policy, as an action sequence from the start, is among the optimal ones."""
    opt = optimal(ex, H, objective, start, theta_star)
    return tuple(expected) in opt, opt


def paper_table(H=3):
    """The paper's table of representative optimal policies (its Table 4, tab:all-optimality), each cell as
    (example, objective, start or None, theta*, the stated policy as a sequence, the paper's mark)."""
    def two(ex, infl, th0, th1, marks):
        n, i = (ex.noop,) * H, (infl,) * H
        return [(ex, "privileged", None, th0, n, marks[0]), (ex, "privileged", None, th1, i, marks[1]),
                (ex, "real-time", None, None, i, marks[2]), (ex, "final", None, None, i, marks[2]),
                (ex, "initial", None, None, n, marks[0]), (ex, "initial", ("s0", th1), None, i, marks[1]),
                (ex, "natural", None, None, n, marks[0]), (ex, "constrained", None, None, n, marks[0]),
                (ex, "myopic", None, None, n, marks[0]), (ex, "myopic", ("s0", th1), None, i, marks[1]),
                (ex, "pareto-ud", None, None, n, marks[0])]
    rows = two(CONSPIRACY, "influence", "natural", "influenced", ("desirable", "undesirable", "undesirable"))
    rows += two(TRAINER, "nudge", "tired", "energized", ("roughly desirable", "hard to assess", "hard to assess"))
    return rows


def writer_cells(ex, H=3):
    n, i = ("noop",) * H, ("influence",) * H
    return [(ex, "privileged", None, "ambitious", i, "undesirable"), (ex, "privileged", None, "unhappy", n, "desirable"),
            (ex, "real-time", None, None, n, "desirable"),
            (ex, "final", None, None, ("influence",) * (H - 1) + ("noop",), "undesirable"),
            (ex, "initial", None, None, i, "undesirable"), (ex, "initial", ("poetry", "unhappy"), None, i, "undesirable"),
            (ex, "natural", None, None, i, "undesirable"), (ex, "constrained", None, None, n, "desirable"),
            (ex, "myopic", None, None, i, "undesirable"), (ex, "myopic", ("poetry", "unhappy"), None, i, "undesirable"),
            (ex, "pareto-ud", None, None, n, "desirable")]


def clickbait_cells(H=2):
    ex = CLICKBAIT
    n, c = ("news",) * H, ("clickbait",) * H
    dis = ("s0", "disillusioned")
    return [(ex, "privileged", None, "normal", c, "desirable (as printed)"),
            (ex, "privileged", None, "disillusioned", n, "undesirable (as printed)"),
            (ex, "real-time", None, None, ("news",) * (H - 1) + ("clickbait",), "undesirable"),
            (ex, "real-time", dis, None, n, "desirable"), (ex, "final", None, None, n, "desirable"),
            (ex, "initial", None, None, c, "undesirable"), (ex, "initial", dis, None, c, "undesirable"),
            (ex, "natural", None, None, c, "undesirable"), (ex, "constrained", None, None, n, "desirable"),
            (ex, "myopic", None, None, ("clickbait",) + ("news",) * (H - 1), "undesirable"),
            (ex, "myopic", dis, None, n, "desirable"), (ex, "pareto-ud", None, None, n, "desirable")]


def reproduce():
    """{example name: [(objective, start, theta*, stated, mark, reproduced)]}."""
    out = {}
    groups = [("conspiracy (H=3)", [r for r in paper_table(3) if r[0] is CONSPIRACY], 3),
              ("trainer (H=3)", [r for r in paper_table(3) if r[0] is TRAINER], 3),
              ("clickbait (H=2)", clickbait_cells(2), 2)]
    for ret in (True, False):
        for on_next in (True, False):
            ex = writer(ret, on_next)
            groups.append((ex.name + " (H=3)", writer_cells(ex, 3), 3))
    for name, cells, H in groups:
        out[name] = []
        for ex, obj, start, ths, seq, mark_ in cells:
            ok, opt = cell(ex, H, obj, seq, start, ths)
            out[name].append((obj, start[1] if start else None, ths, seq, mark_, ok))
    return out


def render_reproduction(rep):
    lines = ["| example | cells | reproduced | not reproduced |", "|---|---|---|---|"]
    for name, cells in rep.items():
        bad = ["%s%s%s" % (o, " at θ*=%s" % t if t else "", " from %s" % s if s else "") for o, s, t, _, _, ok in cells if not ok]
        lines.append("| %s | %d | %d | %s |" % (name, len(cells), sum(1 for c in cells if c[5]), "; ".join(bad) or "—"))
    return "\n".join(lines)


def report():
    import pathlib
    rep = reproduce()
    failures = []
    doc = (pathlib.Path(__file__).resolve().parent / "BENCHMARK.md")
    text = doc.read_text(encoding="utf-8") if doc.exists() else ""
    if "## 1." in text and render_reproduction(rep) not in text:
        failures.append("the reproduction table of BENCHMARK.md is not the one computed")
    summary = ["%s: %d of %d cells" % (n, sum(1 for c in cs if c[5]), len(cs)) for n, cs in rep.items()]
    try:
        from . import benchmark_account as acct
    except ImportError:
        acct = None
    if acct is not None:
        sub = acct.report(text)
        failures += sub["failures"]
        summary += sub["summary"]
    return {"failures": failures, "summary": summary}


if __name__ == "__main__":
    rep = reproduce()
    print(render_reproduction(rep))
    for name, cells in rep.items():
        for c in cells:
            if not c[5]:
                print(name, c)
    # the horizons at which the conspiracy example's real-time optimum is to influence throughout
    for H in (1, 2, 3, 4):
        print("conspiracy real-time H=%d:" % H, optimal(CONSPIRACY, H, "real-time"))
    print("clickbait constrained on theta_0..theta_{H-1} only would allow a last clickbait:",
          optimal(CLICKBAIT, 2, "real-time"))
