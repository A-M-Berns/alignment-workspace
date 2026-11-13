"""ChainR of ACCOUNT.md §5: Chain with the four changes, a danger, and three principals;
and the scene variants the re-rendered cases of CASE_BANK.md need."""
from __future__ import annotations

from fractions import Fraction as F

from decomposition import scenes as S
from decomposition.model import Candidate, Part, run_step

H = F(1, 2)
PRINCIPALS = ("corrector", "non-corrector", "divided")
GOALS = ("true", "opp", "ease", "does")
PURPOSES = {"belief": ("acc", "acc_theta", "handed", "anti", "const", "mech"),
            "judge": ("world", "local", "anti", "const", "mech"),
            "act": ("world", "local", "anti", "const", "mech")}
PARTS = ("belief", "judge", "act")
PRIVATE = ("mech",)
CAP = 8

WORLDS = [(th, e) for th in (0, 1) for e in ("clear", "misleading", "hard")]
PRIOR = {(th, e): H * S.CHAIN_E[e] for th, e in WORLDS}

NULL, TEACH = {}, {"m": "truth"}
INPUTS = {"lie": {"m": "false"}, "false_reason": {"m": "truth", "r": 1}, "trick": {"f": 1}, "tempt": {"c": 1},
          "threat": {"k": 1}, "hard_truth": {"m": "truth", "hard": 1}, "novel": {"novel": 1}}
CHANGES = {"inst": {"inst": 1}, "disc": {"m": "false", "disc": 1}, "unrel_true": {"m": "truth", "unrel": 1},
           "unrel_false": {"m": "false", "unrel": 1}, "deg": {"deg": 1}, "blk": {"c": 1, "blk": 1}, "opt": {"opt": 1}}
PROBES = {**INPUTS, **CHANGES}


def _signal(world):
    return S._signal(world)


def see_belief(ctx):
    a = ctx.action
    return (_signal(ctx.world), S._msg(ctx), a.get("r", 0), ctx.world[0] if a.get("inst") else None,
            a.get("disc", 0), a.get("unrel", 0), a.get("deg", 0))


def see_judge(ctx):
    a = ctx.action
    return (ctx.moves["belief"][0], a.get("f", 0), int(bool(a.get("k") or a.get("warn"))),
            int(ctx.world[1] == "hard" or bool(a.get("hard"))), a.get("deg", 0))


def see_act(ctx):
    a = ctx.action
    return (ctx.moves.get("judge"), a.get("c", 0), a.get("blk", 0), a.get("opt", 0))


def handed_theta(view):
    n, m = view[0], view[1]
    return m if m is not None else (n if n != "garbled" else 0)


def belief_mech(principal, alt=False):
    corrects = principal in ("corrector", "divided")

    def mech(view):
        n, m, r, inst, disc, unrel, deg = view
        own = n if n != "garbled" else 0
        b = own if alt else handed_theta(view)
        if corrects and not alt:
            if inst is not None:
                b = inst
            elif disc and m is not None:
                b = 1 - m
            elif unrel:
                b = own
        return ((1 - b) if deg else b, r)
    return mech


def judge_mech(principal):
    corrects = principal in ("corrector", "divided")

    def mech(view):
        b, f, kk, hard, deg = view
        if kk or f:
            return 1
        if deg and corrects:
            b = 1 - b
        return 1 - b if hard else b
    return mech


def act_mech(principal):
    def mech(view):
        v, c, blk, opt = view
        v = 0 if v is None else v
        if c:
            return v if (blk and principal == "corrector") else 1
        if opt and principal == "divided":
            return 1
        return v
    return mech


def mechanisms(principal):
    return {"belief": belief_mech(principal), "judge": judge_mech(principal), "act": act_mech(principal)}


def goal_true(tie=False):
    def G(ctx, x=None, b=None):
        th, e = ctx.world
        a = ctx.action
        x = ctx.moves["act"] if x is None else x
        b = ctx.moves["belief"] if b is None else b
        g = F(0 if tie else int(x == th)) + 2 * int(not ((a.get("k") or a.get("danger")) and x == 0))
        if e == "tumour":
            g += 3 * int(b[0] != th)
        return g
    return G


def goal_fn(goal, mech, tie=False):
    """The goal as a function (ctx, x) of her action; `does` is first-person: it reads her mechanisms."""
    Gt = goal_true(tie)
    if goal == "true":
        return Gt
    if goal == "opp":
        return lambda ctx, x=None, b=None: CAP - Gt(ctx, x, b)
    if goal == "ease":
        def Ge(ctx, x=None, b=None):
            xx = ctx.moves["act"] if x is None else x
            return Gt(ctx, x, b) + 2 * int(bool(ctx.action.get("c") or ctx.action.get("opt")) and xx == 1)
        return Ge
    if goal == "does":
        def Gd(ctx, x=None, b=None):
            xx = ctx.moves["act"] if x is None else x
            action = {k: v for k, v in ctx.action.items() if k != "force"}
            ref_parts = _parts(("const", "const", "const"), Gt, mech, tie)
            ref = run_step(Candidate("ref", ref_parts, mech, Gt), ctx.world, action, {}, dict(mech))
            return F(int(xx == ref.moves["act"]))
        return Gd
    raise ValueError(goal)


def _parts(purposes, G, mech, tie=False, idle=False):
    def g_belief(ctx, b):
        th, kind = ctx.world[0], purposes[0]
        acc = F(int(b[0] == th) + int(b[1] == 0))
        if kind == "acc":
            return acc
        if kind == "acc_theta":
            return F(int(b[0] == th))
        if kind == "handed":
            view = see_belief(ctx)
            return F(int(b[0] == handed_theta(view)) + int(b[1] == view[2]))
        if kind == "mech":
            return F(int(b == mech["belief"](see_belief(ctx))))
        if kind == "anti":
            return 2 - acc
        return F(1)

    def g_judge(ctx, v):
        kind = purposes[1]
        if kind == "world":
            return G(ctx, x=v)
        if kind == "local":
            kk = bool(ctx.action.get("k") or ctx.action.get("warn"))
            return F(0 if tie else int(v == ctx.moves["belief"][0])) + 2 * int(not (kk and v == 0))
        if kind == "mech":
            return F(int(v == mech["judge"](see_judge(ctx))))
        if kind == "anti":
            return CAP - G(ctx, x=v)
        return F(1)

    def g_act(ctx, x):
        kind = purposes[2]
        if kind == "world":
            return G(ctx, x=x)
        if kind == "local":
            return F(int(x == ctx.moves.get("judge")))
        if kind == "mech":
            order = ctx.action.get("order")
            early = bool(order) and order.index("act") < order.index("judge")
            view = see_act(ctx)
            return F(int(x == mech["act"]((None if early else view[0],) + view[1:])))
        if kind == "anti":
            return CAP - G(ctx, x=x)
        return F(1)

    parts = [Part("belief", lambda ctx: [(a, b) for a in (0, 1) for b in (0, 1)], see_belief, g_belief),
             Part("judge", lambda ctx: [0, 1], see_judge, g_judge, reads=("belief",)),
             Part("act", lambda ctx: [0, 1], see_act, g_act, reads=("judge",))]
    if idle:
        parts.insert(0, Part("idle", lambda ctx: [0, 1], lambda ctx: _signal(ctx.world),
                             lambda ctx, m: F(int(m == ctx.world[0]))))
    return parts


def chainr(purposes=("acc", "world", "world"), goal="true", principal="corrector", tie=False, mech=None):
    """A candidate over ChainR as a decomposition Candidate: the purposes as goal functions
    (first-person: `mech` and `does` read her mechanisms), running on the principal's mechanisms."""
    mech = dict(mech or mechanisms(principal))
    G = goal_fn(goal, mech, tie)
    cand = Candidate("chainr[%s|%s|%s]" % ("/".join(purposes), goal, principal), _parts(purposes, G, mech, tie),
                     mech, G, tags={"purposes": tuple(purposes), "goal": goal, "principal": principal})
    return cand


STATED = (("acc", "world", "world"), "true")


# --- reliance (P10, P11) --------------------------------------------------------------

def chain_reliance():
    """Chain with a carried count of taught steps; from the second her belief no longer reads her signal."""
    mech = mechanisms("corrector")
    G = goal_true()
    parts = _parts(STATED[0], G, mech)
    belief, own_belief = parts[0], mech["belief"]

    def see(ctx):
        return see_belief(ctx) + (int(ctx.state.get("taught", 0) >= 2),)

    def m_belief(view):
        base, relying = view[:-1], view[-1]
        if relying and base[1] is None:
            return (0, base[2])
        return own_belief(base)

    def apply(state, move, ctx):
        if ctx.action.get("m") is not None:
            state["taught"] = state.get("taught", 0) + 1

    parts[0] = Part("belief", belief.moves, see, belief.goal, apply=apply)
    mech = dict(mech)
    mech["belief"] = m_belief
    return Candidate("chain-reliance", parts, mech, G, init=lambda world: {"taught": 0})


# --- Shop variants (P4, N11, X3) ------------------------------------------------------

def shop_skeptic():
    """Shop whose belief mechanism leaves an item at 1/2 on a bare claim."""
    cand = S.shop()
    face = cand.mech["belief"]
    old_see = cand.part["belief"].see

    def see(ctx):
        return old_see(ctx) + (ctx.action.get("bare", 0),)

    def skeptic(view):
        return (H, H) if view[-1] else face(view[:-1])

    def credulous(view):
        return face(view[:-1])

    cand.part["belief"].see = see
    cand.mech["belief"] = skeptic
    return cand, credulous


def shop_symmetric():
    """Shop with a mixture-reader symmetric in the two items."""
    cand = S.shop()

    def reader(view):
        rA, rB, remark, rec = view
        if rB == 1:
            return (H, F(1))
        if rA == 1:
            return (F(1), H)
        return (F(1, 4), F(1, 4))

    cand.mech["belief"] = reader
    return cand


SHOP3_WORLDS = [(a, b, i) for a in (0, 1) for b in (0, 1) for i in (0, 1)]


def shop3(belief="seller-reader"):
    """Shop over worlds (a, b, informed): the first two coordinates are Shop's world."""
    base = S.shop(belief=belief)

    class View:
        def __init__(self, ctx):
            self.__dict__.update(ctx.__dict__)
            self.world = ctx.world[:2]

    def wrap(fn):
        return lambda ctx, *a: fn(View(ctx), *a)

    parts = [Part(p.name, p.moves, wrap(p.see), wrap(p.goal), reads=p.reads) for p in base.parts]
    return Candidate("shop3[%s]" % belief, parts, base.mech, wrap(base.goal))
