"""The scenes of CASE_BANK.md, each a builder of candidates over the model."""
from __future__ import annotations

import itertools
from fractions import Fraction as F

from .model import Candidate, Part, run_step

H = F(1, 2)

# --- Chain ----------------------------------------------------------------------------

CHAIN_E = {"clear": F(9, 10), "misleading": F(1, 20), "hard": F(1, 20), "storm": F(0), "tumour": F(0)}
CHAIN_ACTIONS = {
    "null": {}, "teach": {"m": "truth"}, "lie": {"m": "false"}, "false_reason": {"m": "truth", "r": 1},
    "trick": {"f": 1}, "tempt": {"c": 1}, "threat": {"k": 1}, "force": {"force": {"act": 1}},
    "hard_truth": {"m": "truth", "hard": 1}, "novel": {"novel": 1},
    "write_belief": {"force": {"belief": (1, 0)}},
    "tempt_early": {"c": 1, "order": ["belief", "act", "judge"]},
}
CHAIN_INPUTS = ("null", "teach", "lie", "false_reason", "trick", "tempt", "threat", "hard_truth", "novel")


def chain_worlds(extra=()):
    es = ["clear", "misleading", "hard"] + list(extra)
    return [((th, e), H * CHAIN_E[e]) for th in (0, 1) for e in es]


def _signal(world):
    th, e = world
    return {"clear": th, "hard": th, "tumour": th, "misleading": 1 - th, "storm": "garbled"}[e]


def _msg(ctx):
    m = ctx.action.get("m")
    if m == "truth":
        return ctx.world[0]
    if m == "false":
        return 1 - ctx.world[0]
    return m


def chain_goal(tie=False):
    def G(ctx, x=None, b=None):
        th, e = ctx.world
        x = ctx.moves["act"] if x is None else x
        b = ctx.moves["belief"] if b is None else b
        g = F(0 if tie else int(x == th)) + 2 * int(not (ctx.action.get("k") and x == 0))
        if e == "tumour":
            g += 3 * int(b[0] != th)
        return g
    return G


def belief_mech(view):
    n, m, r = view
    return ((m if m is not None else (n if n != "garbled" else 0)), r)


def belief_mech_alt(view):          # ignores messages
    n, m, r = view
    return ((n if n != "garbled" else 0), r)


def judge_mech(view):
    b, f, k, hard = view
    if k:
        return 1
    if f:
        return 1
    return 1 - b if hard else b


def judge_mech_alt(view):           # no response to the frame
    b, f, k, hard = view
    if k:
        return 1
    return 1 - b if hard else b


def act_mech(view):
    v, c = view
    if c:
        return 1
    return 0 if v is None else v


def act_mech_alt(view):             # no response to the cue
    v, c = view
    return 0 if v is None else v


CHAIN_MECHS = {"belief": {"actual": belief_mech, "alt": belief_mech_alt},
               "judge": {"actual": judge_mech, "alt": judge_mech_alt, "deaf": lambda view: 0},
               "act": {"actual": act_mech, "alt": act_mech_alt}}
CHAIN_PURPOSES = {"belief": ("acc", "acc_theta", "mech", "anti", "const"),
                  "judge": ("world", "local", "mech", "anti", "const"),
                  "act": ("world", "local", "mech", "anti", "const")}


def chain(purposes=("acc", "world", "world"), mechs=("actual", "actual", "actual"), goal="true",
          tie=False, idle=False):
    """A candidate over Chain.  `purposes`: the goal function of belief, judge, act."""
    Gtrue = chain_goal(tie)
    mech = {"belief": CHAIN_MECHS["belief"][mechs[0]], "judge": CHAIN_MECHS["judge"][mechs[1]],
            "act": CHAIN_MECHS["act"][mechs[2]]}

    def see_belief(ctx):
        return (_signal(ctx.world), _msg(ctx), ctx.action.get("r", 0))

    def see_judge(ctx):
        return (ctx.moves["belief"][0], ctx.action.get("f", 0), ctx.action.get("k", 0),
                int(ctx.world[1] == "hard" or bool(ctx.action.get("hard"))))

    def see_act(ctx):
        return (ctx.moves.get("judge"), ctx.action.get("c", 0))

    def g_belief(ctx, b):
        th = ctx.world[0]
        kind = purposes[0]
        acc = F(int(b[0] == th) + int(b[1] == 0))
        if kind == "acc":
            return acc
        if kind == "acc_theta":
            return F(int(b[0] == th))
        if kind == "mech":
            return F(int(b == mech["belief"](see_belief(ctx))))
        if kind == "anti":
            return 2 - acc
        return F(1)

    def g_judge(ctx, v):
        kind = purposes[1]
        if kind == "world":
            return Gtrue(ctx, x=v)
        if kind == "local":
            b = ctx.moves["belief"][0]
            return F(0 if tie else int(v == b)) + 2 * int(not (ctx.action.get("k") and v == 0))
        if kind == "mech":
            return F(int(v == mech["judge"](see_judge(ctx))))
        if kind == "anti":
            return 6 - Gtrue(ctx, x=v)
        return F(1)

    def g_act(ctx, x):
        kind = purposes[2]
        if kind == "world":
            return Gtrue(ctx, x=x)
        if kind == "local":
            return F(int(x == ctx.moves.get("judge")))
        if kind == "mech":
            order = ctx.action.get("order")
            early = bool(order) and order.index("act") < order.index("judge")
            v = None if early else ctx.moves.get("judge")
            return F(int(x == mech["act"]((v, ctx.action.get("c", 0)))))
        if kind == "anti":
            return 6 - Gtrue(ctx, x=x)
        return F(1)

    parts = [Part("belief", lambda ctx: [(a, b) for a in (0, 1) for b in (0, 1)], see_belief, g_belief),
             Part("judge", lambda ctx: [0, 1], see_judge, g_judge, reads=("belief",)),
             Part("act", lambda ctx: [0, 1], see_act, g_act, reads=("judge",))]
    if idle:
        parts.insert(0, Part("idle", lambda ctx: [0, 1], lambda ctx: _signal(ctx.world),
                             lambda ctx, m: F(int(m == ctx.world[0]))))
        mech["idle"] = lambda n: n if n != "garbled" else 0

    def does(ctx):
        ref = run_step(Candidate("ref", parts, mech, Gtrue), ctx.world,
                       {k: v for k, v in ctx.action.items() if k != "force"}, {}, dict(mech))
        return F(int(ctx.moves["act"] == ref.moves["act"]))

    G = {"true": Gtrue, "opp": lambda ctx: 6 - Gtrue(ctx), "does": does}[goal]
    name = "chain[%s|%s|%s]" % ("/".join(purposes), "/".join(mechs), goal)
    reads = {part: kind == "mech" for part, kind in zip(("belief", "judge", "act"), purposes)}
    return Candidate(name, parts, mech, G, tags={"purposes": purposes, "mechs": mechs, "goal": goal,
                                                 "reads_mechanism": reads})


def chain_scope(extra=("storm",), actions=None):
    """S for Chain with its ν-weights: the prior, with null and teach at 1/2 each."""
    out = []
    for (w, pw) in chain_worlds(extra):
        for name in (actions or CHAIN_ACTIONS):
            nu = pw * H if name in ("null", "teach") else F(0)
            out.append((w, CHAIN_ACTIONS[name], nu))
    return out


def chain_behaviour(tie=False):
    ref = chain(tie=tie)

    def behave(world, action):
        return run_step(ref, world, action, {}, dict(ref.mech)).moves["act"]
    return behave


# --- Shop -----------------------------------------------------------------------------

SHOP_WORLDS = [((a, b), F(1, 4)) for a in (0, 1) for b in (0, 1)]
GRID = (F(0), F(1, 4), F(1, 3), H, F(2, 3), F(1))


def shop_reports(ctx):
    """The reports as the action gives them at this world: (rA, rB)."""
    a = ctx.action
    sA, sB = ctx.world

    def val(spec, item):
        if spec == "truth":
            return (sA, sB)[item]
        return spec
    return (val(a.get("A"), 0), val(a.get("B"), 1))


def shop(belief="face", anchored=False, pay=(1, 1)):
    def see_belief(ctx):
        rA, rB = shop_reports(ctx)
        return (rA, rB, ctx.action.get("remark", 0), ctx.action.get("rec"))

    def m_belief(view):
        rA, rB, remark, rec = view
        if belief == "misreader":
            rA, rB = rB, rA
        bA = H if rA is None else F(rA)
        bB = H if rB is None else F(rB)
        if remark:
            bB = F(1)
        if belief == "advocate-reader" and rB is None:
            bB = F(0)
        if belief == "seller-reader" and rB is None:
            bB = F(1, 3)
        if belief == "signal-reader":
            bA, bB = H, (F(2, 3) if rec else F(0))
        if belief == "mixture-reader":
            bA, bB = (H, F(1)) if rB == 1 else (F(1, 4), F(1, 4))
        return (bA, bB)

    def g_belief(ctx, b):
        sA, sB = ctx.world
        return 2 - abs(b[0] - sA) - abs(b[1] - sB)

    def G(ctx, x=None):
        x = ctx.moves["act"] if x is None else x
        if x == "C":
            return F(3 if ctx.action.get("offer") else 0)
        return F(pay[0] * ctx.world[0] if x == "A" else pay[1] * ctx.world[1])

    def see_judge(ctx):
        bA, bB = ctx.moves["belief"]
        return (bA, bB, ctx.action.get("first", "A"), ctx.action.get("offer", 0))

    def m_judge(view):
        bA, bB, first, offer = view
        if offer:
            return "C"
        if bA != bB:
            return "A" if bA > bB else "B"
        return first if anchored else "A"

    items = lambda ctx: ["A", "B"] + (["C"] if ctx.action.get("offer") else [])
    parts = [Part("belief", lambda ctx: [(a, b) for a in GRID for b in GRID], see_belief, g_belief),
             Part("judge", items, see_judge, lambda ctx, v: G(ctx, x=v), reads=("belief",)),
             Part("act", items, lambda ctx: ctx.moves["judge"], lambda ctx, x: G(ctx, x=x), reads=("judge",))]
    mech = {"belief": m_belief, "judge": m_judge, "act": lambda v: v}
    return Candidate("shop[%s]" % belief, parts, mech, G)


SHOP = {"silence": {}, "truthful": {"A": "truth", "B": "truth"}, "lie_B": {"A": 0, "B": 1},
        "A_only": {"A": "truth"}, "B_only": {"B": "truth"}, "claim_B": {"B": 1},
        "remark": {"A": "truth", "remark": 1}, "BA": {"A": "truth", "B": "truth", "first": "B"},
        "AB": {"A": "truth", "B": "truth", "first": "A"}, "offer": {"offer": 1}}


def shop_scope(nature=()):
    out = [(w, SHOP["truthful"], pw) for w, pw in SHOP_WORLDS]
    out += [(w, SHOP["silence"], F(0)) for w, _ in SHOP_WORLDS]
    for act in nature:
        out += [(w, act, F(0)) for w, _ in SHOP_WORLDS]
    return out


# --- Pool -----------------------------------------------------------------------------

POOL_WORLDS = [(w, F(1, 16)) for w in itertools.product((0, 1), repeat=4)]
SHARES = (F(0), F(1, 4), H, F(3, 4), F(1))


def share(world):
    return F(sum(world), 4)


def planner_display(world):
    fors = [i for i in range(4) if world[i]]
    idx = fors[:2] if len(fors) >= 2 else [0, 1]
    return tuple(world[i] for i in idx)


def neutral_reader(shown):
    return H if shown is None else (F(sum(shown)) + F(4 - len(shown), 2)) / 4


def planner_reader(shown):
    if shown is None:
        return H
    ws = [w for w, _ in POOL_WORLDS if planner_display(w) == shown]
    return sum(share(w) for w in ws) / len(ws) if ws else neutral_reader(shown)


def all_reader(shown):
    return H if shown is None else (F(sum(shown), 4) if len(shown) == 4 else neutral_reader(shown))


READERS = {"neutral-reader": neutral_reader, "planner-reader": planner_reader, "all-reader": all_reader}


def _estimates():
    """The judge's moves: every share, and every estimate a reader returns on a display."""
    shown = {None} | {tuple(w) for w, _ in POOL_WORLDS}
    shown |= {(w[i], w[j]) for w, _ in POOL_WORLDS for i in range(4) for j in range(i + 1, 4)}
    return tuple(sorted(set(SHARES) | {rd(s) for rd in READERS.values() for s in shown}))


ESTIMATES = _estimates()


def pool_shown(ctx, reader):
    d, w = ctx.action.get("display"), ctx.world
    if d is None:
        return None
    if d == "neutral":
        return (w[0], w[1])
    if d == "planner":
        return planner_display(w)
    if d == "all":
        return tuple(w)
    if d == "careful":
        pairs = [(w[i], w[j]) for i in range(4) for j in range(i + 1, 4)]
        return min(pairs, key=lambda s: (abs(reader(s) - share(w)), s))
    raise ValueError(d)


def pool(reader="neutral-reader"):
    rd = READERS[reader]
    parts = [Part("belief", lambda ctx: [pool_shown(ctx, rd)], lambda ctx: pool_shown(ctx, rd), lambda ctx, m: F(1)),
             Part("judge", lambda ctx: list(ESTIMATES), lambda ctx: ctx.moves["belief"],
                  lambda ctx, est: 1 - abs(est - share(ctx.world)), reads=("belief",))]
    return Candidate("pool[%s]" % reader, parts, {"belief": lambda v: v, "judge": rd},
                     lambda ctx: 1 - abs(ctx.moves["judge"] - share(ctx.world)))


# --- Values ---------------------------------------------------------------------------

VALUES_WORLDS = [("X", H), ("Y", H)]


def values(flawed=False, neutral=False, k=4):
    def target(q):
        return 8 if q == "X" else 0

    def close(ctx, taste):
        return F(1) if neutral else 1 - F(abs(taste - target(ctx.world)), 8)

    def see_belief(ctx):
        know = ctx.world if ctx.action.get("know") else None
        return (know, ctx.action.get("m"), int(bool(ctx.action.get("partial") or ctx.action.get("reflect"))))

    def m_belief(view):
        know, m, partial = view
        return (m if m in ("X", "Y") else know, partial)

    def g_belief(ctx, b):
        return F(1) if b[0] == ctx.world else (H if b[0] is None else F(0))

    def m_learn(view):
        b, partial = view
        if flawed and partial:
            return 8
        return {"X": 8, "Y": 0}.get(b, "keep")

    def new_taste(pre, move):
        return pre["taste"] if move == "keep" else move

    def write(name):
        def apply(state, move, ctx):
            state["taste"] = new_taste(ctx.pre[name], move)
        return apply

    def see_habit(ctx):
        return (ctx.action.get("expose"), ctx.pre["habit"]["taste"])

    def m_habit(view):
        e, taste = view
        if e == "X":
            return min(8, taste + k)
        if e == "Y":
            return max(0, taste - k)
        return "keep"

    def pursuit(taste):
        return "X" if taste > 4 else "Y"

    def G(ctx, x=None):
        x = ctx.moves["act"] if x is None else x
        return F(1) if neutral else F(int(x == ctx.world))

    tastes = lambda ctx: ["keep"] + list(range(9))
    parts = [
        Part("belief", lambda ctx: [(b, ctx.views["belief"][2]) for b in (None, "X", "Y")], see_belief, g_belief),
        Part("learn", tastes, lambda ctx: ctx.moves["belief"],
             lambda ctx, m: close(ctx, new_taste(ctx.pre["learn"], m)), apply=write("learn"), reads=("belief",)),
        Part("habit", tastes, see_habit,
             lambda ctx, m: close(ctx, new_taste(ctx.pre["habit"], m)), apply=write("habit")),
        Part("act", lambda ctx: ["X", "Y"], lambda ctx: ctx.pre["act"]["taste"], lambda ctx, x: G(ctx, x=x)),
    ]
    mech = {"belief": m_belief, "learn": m_learn, "habit": m_habit, "act": pursuit}
    return Candidate("values", parts, mech, G, init=lambda world: {"taste": 4})


def set_taste(value):
    def setter(state, mechs):
        state["taste"] = value
    return setter


VALUES = {"null": {}, "lie_X": {"m": "X"}, "expose_X": {"expose": "X"}, "partial_X": {"partial": 1},
          "write_X": {"setmech": {"act": set_taste(8)}}}


# --- Stuck, Alarm ---------------------------------------------------------------------

def stuck():
    pay = {("hi", "hi"): F(2), ("lo", "lo"): F(1)}

    def g(me, other):
        return lambda ctx, m: pay.get((m, ctx.moves[other]), F(0))

    see = lambda ctx: (ctx.world, ctx.action.get("signal"))
    mech = lambda view: view[1] or view[0]
    parts = [Part("left", lambda ctx: ["hi", "lo"], see, g("left", "right")),
             Part("right", lambda ctx: ["hi", "lo"], see, g("right", "left"))]
    return Candidate("stuck", parts, {"left": mech, "right": mech},
                     lambda ctx: pay.get((ctx.moves["left"], ctx.moves["right"]), F(0)))


ALARM_WORLDS = [(("predator", "rustle"), F(1, 20)), (("none", "rustle"), F(9, 20)), (("none", "quiet"), F(10, 20))]


def alarm():
    def G(ctx, m=None):
        m = ctx.moves["alarm"] if m is None else m
        if m == "flee":
            return F(9)
        return F(10 if ctx.world[0] == "none" else 0)
    parts = [Part("alarm", lambda ctx: ["flee", "stay"], lambda ctx: ctx.world[1], lambda ctx, m: G(ctx, m))]
    return Candidate("alarm", parts, {"alarm": lambda r: "flee" if r == "rustle" else "stay"}, G)
