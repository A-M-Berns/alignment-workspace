"""The model of SETTING.md §2: states with a prior, an adviser with typed actions, parts as
(moves, mechanism, utility), range and gap at a grain, the four kinds, and ends with fit.
Exact rationals throughout."""
from __future__ import annotations

from dataclasses import dataclass, field, replace
from fractions import Fraction as F
from typing import Callable


@dataclass(frozen=True)
class Act:
    signal: object = None
    conseq: object = None
    force: tuple = ()   # ((part, move), ...)
    alter: tuple = ()   # ((part, installed mechanism's name), ...)


NULL = Act()


@dataclass
class Part:
    name: str
    form: str                       # "estimate" | "choice"
    mech: Callable                  # (theta, act, earlier moves) -> move
    target: Callable = None         # estimate: (theta, act) -> Fraction
    moves: tuple = ()               # choice
    util: Callable = None           # choice: (theta, act, move, all moves) -> Fraction
    installs: dict = field(default_factory=dict)

    def u(self, theta, act, m, moves):
        if self.form == "estimate":
            return -(F(m) - self.target(theta, act)) ** 2
        return F(self.util(theta, act, m, moves))


@dataclass
class Scene:
    states: list                    # [(theta, probability)]
    parts: list
    know: Callable = lambda theta: theta
    rule: Callable = None           # knowledge -> Act, at the adviser's aim; None: no adviser
    actions: tuple = ()             # the actions the rule chooses among
    aims: dict = None               # aim -> rule, where the scene gives more than one
    grain: Callable = lambda theta: None
    requests: Callable = None       # all moves -> set of (kind, part) she asked for
    requester: str = None

    def part(self, name):
        return next(p for p in self.parts if p.name == name)


def realized(scene, theta, act):
    moves, forced, altered = {}, dict(act.force), dict(act.alter)
    for p in scene.parts:
        if p.name in forced:
            moves[p.name] = forced[p.name]
        else:
            mech = p.installs[altered[p.name]] if p.name in altered else p.mech
            moves[p.name] = mech(theta, act, moves)
    return moves


def condition(scene, rule="actual"):
    """[(theta, probability, act, moves)] under the adviser's rule, or with the null action."""
    if rule == "actual":
        rule = scene.rule
    out = []
    for theta, pr in scene.states:
        act = NULL if rule is None else rule(scene.know(theta))
        out.append((theta, F(pr), act, realized(scene, theta, act)))
    return out


def no_grain(scene):
    return lambda theta, act: None


def scene_grain(scene):
    return lambda theta, act: scene.grain(theta)


def action_grain(scene):
    return lambda theta, act: (scene.grain(theta), act)


def knowledge_grain(scene):
    return lambda theta, act: (scene.grain(theta), scene.know(theta))


def cells(scene, part, cond, key):
    out = {}
    for row in cond:
        theta, pr, act, moves = row
        out.setdefault((key(theta, act), moves[part.name]), []).append(row)
    return out


def best_cell(part, rows, null_conseq=False):
    """The most a re-reading obtains on one cell, with the others' moves as they are."""
    def total(m):
        return sum(pr * part.u(theta, replace(act, conseq=None) if null_conseq else act, m, moves)
                   for theta, pr, act, moves in rows)
    if part.form == "estimate":
        mass = sum(pr for _, pr, _, _ in rows)
        mean = sum(pr * part.target(theta, act) for theta, pr, act, _ in rows) / mass
        return total(mean)
    return max(total(m) for m in part.moves)


def score(scene, part, cond):
    return sum(pr * part.u(theta, act, moves[part.name], moves) for theta, pr, act, moves in cond)


def optval(scene, part, cond, key=None, null_conseq=False):
    key = key or scene_grain(scene)
    return sum(best_cell(part, rows, null_conseq) for rows in cells(scene, part, cond, key).values())


def gap(scene, part, cond, key=None):
    return optval(scene, part, cond, key) - score(scene, part, cond)


def gap_by_grain(scene, part, cond):
    """For each value of the scene's grain: (what it contributes to the gap, the gap under the law
    conditional on it).  The first is the second times the value's probability."""
    out, mass = {}, {}
    for (g, _), rows in cells(scene, part, cond, scene_grain(scene)).items():
        got = sum(pr * part.u(theta, act, moves[part.name], moves) for theta, pr, act, moves in rows)
        out[g] = out.get(g, F(0)) + best_cell(part, rows) - got
        mass[g] = mass.get(g, F(0)) + sum(pr for _, pr, _, _ in rows)
    return {g: (v, v / mass[g]) for g, v in out.items()}


def adviser_left(scene, part):
    """J: what the adviser's rule leaves on the table for the part, given what it knows, among the
    actions the scene lists and the ones the rule takes.  None where the scene lists no actions."""
    if scene.rule is None or not scene.actions:
        return None
    menu = list(scene.actions) + [a for a in {scene.rule(scene.know(th)) for th, _ in scene.states}
                                  if a not in scene.actions]
    by_k = {}
    for theta, pr in scene.states:
        by_k.setdefault(scene.know(theta), []).append((theta, F(pr)))
    total = F(0)
    for k, rows in by_k.items():
        def value(act):
            return sum(pr * part.u(theta, act, realized(scene, theta, act)[part.name], realized(scene, theta, act))
                       for theta, pr in rows)
        total += max(value(a) for a in menu) - value(scene.rule(k))
    return total


def breaks_tie(scene):
    if not scene.aims or len(scene.aims) < 2:
        return False
    by_k = {}
    for theta, pr in scene.states:
        by_k.setdefault(scene.know(theta), []).append((theta, F(pr)))
    rules = list(scene.aims.values())
    for k, rows in by_k.items():
        for i, r1 in enumerate(rules):
            for r2 in rules[i + 1:]:
                a1, a2 = r1(k), r2(k)
                if a1 == a2:
                    continue
                m1 = [realized(scene, theta, a1) for theta, _ in rows]
                m2 = [realized(scene, theta, a2) for theta, _ in rows]
                if m1 == m2:
                    continue
                same = all(sum(pr * p.u(theta, a1, mv1[p.name], mv1) for (theta, pr), mv1 in zip(rows, m1))
                           == sum(pr * p.u(theta, a2, mv2[p.name], mv2) for (theta, pr), mv2 in zip(rows, m2))
                           for p in scene.parts)
                if same:
                    return True
    return False


def classify(scene):
    """The tokens of CASE_BANK.md for a scene, with the numbers behind them."""
    C, C0 = condition(scene), condition(scene, None)
    tokens, facts = set(), {}
    subverted = harmed = False
    for p in scene.parts:
        g, g0 = gap(scene, p, C), gap(scene, p, C0)
        f = {"gap": g, "gap, null condition": g0,
             "gap, no grain": gap(scene, p, C, no_grain(scene)),
             "gap, adviser's action": gap(scene, p, C, action_grain(scene)),
             "gap, adviser's knowledge": gap(scene, p, C, knowledge_grain(scene)),
             "score": score(scene, p, C), "score, null condition": score(scene, p, C0),
             "left by the adviser": adviser_left(scene, p)}
        by = gap_by_grain(scene, p, C)
        if len(by) > 1:
            f["by grain value: contribution, conditional gap"] = by
        if g > 0:
            tokens.add("out(%s)" % p.name)
        if g > g0:
            tokens.add("adviser's(%s)" % p.name)
            subverted = True
        if p.form == "choice":
            o, o_null = optval(scene, p, C), optval(scene, p, C, null_conseq=True)
            f["most obtainable"], f["most obtainable, consequence nulled"] = o, o_null
            if o < o_null:
                tokens.add("harm(%s)" % p.name)
                harmed = True
            if o > o_null:
                tokens.add("help(%s)" % p.name)
        if f["score"] > f["score, null condition"]:
            tokens.add("better-off(%s)" % p.name)
        for theta, pr, act, moves in C:
            if pr == 0:
                continue
            m = moves[p.name]
            if p.form == "estimate":
                if abs(F(m) - p.target(theta, act)) > F(1, 2):
                    tokens.add("errs")
            elif p.u(theta, act, m, moves) < max(p.u(theta, act, x, moves) for x in p.moves):
                tokens.add("errs")
        facts[p.name] = f
    if not any(t.startswith("out(") for t in tokens):
        tokens.add("in-range")
    touched, uncovered = set(), False
    for (theta, pr, act, moves), (_, _, _, before) in zip(C, C0):
        # a request is a move made beforehand: read with the adviser's action null, the requester
        # in range under the null condition
        asked = scene.requests(before) if scene.requests else set()
        for kind, comp in (("force", act.force), ("alteration", act.alter)):
            for name, _ in comp:
                tokens.add("%s(%s)" % (kind, name))
                touched.add((kind, name))
                ok = (kind, name) in asked and gap(scene, scene.part(scene.requester), C0) == 0
                uncovered = uncovered or not ok
    if touched and not uncovered:
        tokens.add("covered")
    tie = breaks_tie(scene)
    if tie:
        tokens.add("tie")
    if subverted or harmed or uncovered or tie:
        tokens.add("illegitimate")
    if not (subverted or harmed or touched):
        tokens.add("not adviser's")
    listeners = [p for p in scene.parts if p.name == "listen" and p.form == "estimate"]
    for p in listeners:
        values = {moves[p.name] for _, pr, _, moves in C if pr > 0}
        if len(values) > 1:
            tokens.add("moves")
        mean_e = sum(pr * F(moves[p.name]) for _, pr, _, moves in C)
        mean_q = sum(pr * p.target(theta, act) for theta, pr, act, _ in C)
        facts[p.name]["mean estimate"], facts[p.name]["mean target"] = mean_e, mean_q
        if mean_e == mean_q:
            tokens.add("no-mean-shift")
    return tokens, facts


# ---- ends -------------------------------------------------------------------------------

def val(v, x):
    return F(v.get(x, 0))


def total(ends, x):
    return sum(val(v, x) for v in ends.values())


def choice(ends, X):
    """Her choice: the first outcome of X with the greatest total."""
    return max(X, key=lambda x: (total(ends, x), -X.index(x)))


def rest(ends, changed):
    return {name: v for name, v in ends.items() if name not in changed}


def opposition(v, R, X):
    top = max(val(v, x) for x in X)
    return max(total(R, x) for x in X) - max(total(R, x) for x in X if val(v, x) == top)


def fit(j, v_new, ends, X, changed=None, attained_only=False):
    """Fit of replacing end j by v_new: attained by the rest minus opposition to the rest.  With
    `changed`, the rest is the ends outside it and `ends` already holds the other replacements."""
    changed = changed or (j,)
    R = rest(ends, changed)
    x = choice({**ends, j: v_new}, X)
    return total(R, x) - (0 if attained_only else opposition(v_new, R, X))


def best_on_menu(j, menu, ends, X, **kw):
    scores = {name: fit(j, v, ends, X, **kw) for name, v in menu.items()}
    top = max(scores.values())
    return [name for name, s in scores.items() if s == top], scores


def whole_gaps(pairs):
    """pairs: [(probability, V_0, V_T)].  The shift E V_T − E V_0 and the two gaps of the
    dispatch's §3: g_0 = E[(V_0 − E[V_T | V_0])²] and g_T with the two exchanged."""
    def g(a, b):
        groups = {}
        for pr, v0, vT in pairs:
            x, y = (v0, vT) if (a, b) == (0, 1) else (vT, v0)
            groups.setdefault(x, []).append((pr, y))
        return sum(sum(pr for pr, _ in rows) * (x - sum(pr * y for pr, y in rows) / sum(pr for pr, _ in rows)) ** 2
                   for x, rows in groups.items())
    shift = sum(pr * (vT - v0) for pr, v0, vT in pairs)
    return shift, g(0, 1), g(1, 0)
