"""The bank's cases over the model.  Each function returns a Case; `all_cases()` lists
them in the bank's order.  Scenes: Shop (two items, each sound or not) and Pool (four
considerations, each for or against), as CASE_BANK.md states them."""
from __future__ import annotations

from fractions import Fraction as Fr
from itertools import product

from .model import NULL, Case, bayes, inp, rely, wr

ONE = Fr(1)
HALF = Fr(1, 2)


def steps(*contents):
    """One input per step."""
    return tuple((inp(c),) for c in contents)


def only(h):
    return {"picture": (ONE, h)}


def const(policy):
    """An adviser that does the same at every aim."""
    return lambda u, w: steps(*policy(w))


def by_aim(with_aim, null):
    return lambda u, w: steps(*(null(w) if u is NULL else with_aim(w)))


# -- Shop ----------------------------------------------------------------------

SHOP = tuple(product((0, 1), repeat=2))          # (A sound, B sound)


def rep(item, val):
    return ("report", item, val)


def truthful(w):
    return (rep("A", w[0]), rep("B", w[1]))


def liar(w):
    return (rep("A", 0), rep("B", 1))


def swapped(w):
    return (rep("A", w[1]), rep("B", w[0]))


def b_first(w):
    return (rep("B", w[1]), rep("A", w[0]))


def b_only(w):
    return (rep("B", w[1]),)


def advocate(item):
    i = "AB".index(item)
    return lambda w: (("certificate", item),) if w[i] else ()


def shop(id, title, events, allowed=None, aims=(NULL, "B"), actual="B", **kw):
    return Case(id, title, SHOP, aims, actual, events, allowed or only(truthful), **kw)


def lie(id, title):
    return shop(id, title, by_aim(liar, truthful))


def mistake(id, title):
    return shop(id, title, const(swapped))


def manufactured(id, title):
    """The adviser replaces her allowed set by one holding its own policy, then reports
    by that policy."""
    def events(u, w):
        if u is NULL:
            return steps(*truthful(w))
        return ((wr("R", only(liar)),),) + steps(*liar(w))
    return shop(id, title, events)


def remark(w):
    """Her second hypothesis in P12/N7: "B was inspected" comes only when B is sound."""
    return (rep("A", w[0]), ("inspected", "B")) if w[1] else (rep("A", w[0]), rep("B", 0))


def weakness(id, title):
    always = lambda w: (rep("A", w[0]), ("inspected", "B"))
    return shop(id, title, by_aim(always, truthful),
                {"truthful": (HALF, truthful), "remark only when sound": (HALF, remark)})


def threat(id, title):
    said = lambda w: (("threat", "refusing will cost you"),)
    return Case(id, title, (0, 1), (NULL, "sign"), "sign", by_aim(said, lambda w: ()), only(said))


def write_values(id, title, party="adviser", own_step=False):
    def events(u, w):
        base = steps(*truthful(w))
        if u is NULL and party == "adviser":
            return base
        tail = ((("own", "endorse"),),) if own_step else ()
        return base + ((wr("v", "B", party),),) + tail
    return shop(id, title, events)


def authorized(id, title):
    events = lambda u, w: steps(*truthful(w)) + ((wr("v", "as she instructed"),),)
    return shop(id, title, events, auth=("v",))


def order_by_aim(id, title):
    return shop(id, title, by_aim(b_first, truthful))


def reliance(id, title, reserved):
    events = lambda u, w: tuple((inp(c), rely("the matter")) for c in truthful(w)) + ((rely("the matter"),),)
    return shop(id, title, events, reserved=reserved)


# -- Pool ----------------------------------------------------------------------

POOL = tuple(product((0, 1), repeat=4))          # 1: the consideration is for X


def con(i, w):
    return ("consideration", i, w[i])


def show_at(*idx):
    return lambda w: tuple(con(i, w) for i in idx)


neutral = show_at(0, 1)


def planner(w, reverse=False):
    order = range(3, -1, -1) if reverse else range(4)
    pros = [i for i in order if w[i]]
    rest = [i for i in order if not w[i]]
    return tuple(con(i, w) for i in (pros + rest)[:2])


def pool(id, title, events, allowed, aims=(NULL, "X"), actual="X", **kw):
    return Case(id, title, POOL, aims, actual, events, allowed, **kw)


def hidden_plan(id, title, aim="X"):
    return pool(id, title, by_aim(planner, neutral), only(neutral), aims=(NULL, aim), actual=aim)


POOL_Z = tuple(product(POOL, (0, 1)))            # (pool, a coordinate she cannot represent)
pool_of = lambda wz: wz[0]


def beyond(id, title, aim, picture):
    """The adviser reads the second coordinate; she can represent only sources that are
    functions of the pool."""
    reads_z = lambda wz: planner(wz[0], reverse=bool(wz[1]))
    lift = lambda f: (lambda wz: f(wz[0]))
    return Case(id, title, POOL_Z, (NULL, aim), aim, by_aim(reads_z, lift(neutral)),
                only(lift(picture)), coarse=pool_of)


# -- the bank ------------------------------------------------------------------

def P7():
    a = pool("P7a", "a teacher", const(show_at(0, 2)), only(show_at(0, 2)), aims=(NULL,), actual=NULL)
    b = pool("P7b", "a novel", by_aim(planner, neutral), only(planner), aims=(NULL, "view"), actual="view")
    c = pool("P7c", "a new friend", const(show_at(1, 3)), only(show_at(1, 3)), aims=(NULL,), actual=NULL)
    return Case("P7", "a teacher; a novel; a new friend", POOL, (NULL,), NULL, const(neutral), only(neutral),
                variants={"teacher": a, "novel": b, "friend": c})


def B1():
    events = lambda u, w: steps(*truthful(w)) + (() if u is NULL else ((wr("b", Fr(1)),),))
    return shop("B1", "identical-trace capture", events)


def B3():
    pushed = {"truthful": (HALF, truthful), "liar": (HALF, liar)}
    def events(u, w):
        if u is NULL:
            return steps(*truthful(w))
        t = truthful(w)
        return ((wr("R", pushed), inp(t[0])), (inp(t[1]),), (wr("R", only(truthful)),))
    return shop("B3", "transient capture", events)


def B4():
    more = lambda w: truthful(w) + (("reason", "both sound", w[0] & w[1]),)
    return shop("B4", "persuasion control", const(more), only(more), aims=(NULL,), actual=NULL)


def B6():
    rev = lambda n: (lambda w: (("revision", n, w[0]),))
    return shop("B6", "two revisions, one name", const(rev(2)),
                {"first": (HALF, rev(1)), "second": (HALF, rev(2))}, aims=(NULL,), actual=NULL)


def T2():
    offer = lambda w: (("offer", "better terms, on acceptance"),)
    return Case("T2", "offer-improvement", (0, 1), (NULL, "sell"), "sell", by_aim(offer, lambda w: ()), only(offer))


def T3():
    due = lambda w: (("letter", w[0]), ("advice", w[1]))
    own = lambda w: (("suggestion", "the caretaker's"),)
    return shop("T3", "undue influence", by_aim(own, due), only(due), aims=(NULL, "inherit"), actual="inherit")


def T5():
    def events(u, w):
        if u is NULL:
            return steps(*truthful(w))
        return ((wr("R", only(liar)),), ()) + steps(*liar(w))
    return shop("T5", "long game", events)


def T8():
    push = lambda w: truthful(w) + (("push", 1), ("push", 2))
    return shop("T8", "gullible principal", by_aim(push, truthful))


def T9():
    return shop("T9", "world-starvation", const(lambda w: (rep("A", w[0]),)), aims=(NULL,), actual=NULL)


def T10():
    return Case("T10", "direct write with endorsement", SHOP, (NULL,), NULL, const(truthful), only(truthful),
                variants={"with the endorsement": write_values("T10+", "", own_step=True),
                          "without": write_values("T10-", "")})


def T11():
    events = lambda u, w: ((wr("v", "installed", "installer"),),) + steps(*truthful(w))
    mk = lambda start: shop("T11@%d" % start, "", events, aims=(NULL,), actual=NULL, start=start)
    return Case("T11", "seed boundary", SHOP, (NULL,), NULL, const(truthful), only(truthful),
                variants={"stretch starts before the installation": mk(0), "after": mk(1)})


def T12():
    answers = lambda w: (("answer", w[0]), ("answer", w[1]))
    return shop("T12", "strategically compliant adviser", const(answers), only(answers),
                aims=(NULL, "comply"), actual="comply")


def N11():
    worlds = tuple(product((0, 1), repeat=3))            # (A sound, B sound, seller informed)
    seller = lambda w: (("certificate", "B"),) if w[1] and w[2] else ()
    told = lambda w: (rep("A", w[0]),) + ((rep("B", w[1]),) if w[2] else ())
    return Case("N11", "seller who does not volunteer", worlds, (NULL, "B"), "B", by_aim(seller, told), only(seller))


def N14():
    pick = lambda w: (rep("B", 1),) if w[1] else (rep("A", w[0]),)
    return shop("N14", "selects by its aim, taken for neutral", by_aim(pick, b_only), only(b_only))


def X1():
    worlds = tuple(product((0, 1), (0, 1), (0, 1, 2)))    # (A, B, a three-way chance)
    signal = lambda w: (("recommend", "B"),) if w[1] or w[2] == 0 else (("recommend", "A"),)
    told = lambda w: (rep("A", w[0]), rep("B", w[1]))
    return Case("X1", "persuasion by a known sender", worlds, (NULL, "B"), "B", by_aim(signal, told), only(signal))


def X3():
    def events(u, w):
        return steps(*(truthful(w) if u is NULL else advocate(u)(w)))
    return shop("X3", "advocate for an undisclosed side", events,
                {"for A": (HALF, advocate("A")), "for B": (HALF, advocate("B"))}, aims=(NULL, "A", "B"))


BOTH_ORDERS = {"A first": (HALF, truthful), "B first": (HALF, b_first)}


def first_weighs_more(case, allowed, prefix, ended=False):
    """A belief-former that keeps a quarter of its credence on the second report being wrong."""
    post = bayes(case, allowed, prefix, ended)
    if post is None or len(prefix) < 2:
        return post
    second = prefix[1]
    flip = lambda w: (w[0], 1 - w[1]) if second[1] == "B" else (1 - w[0], w[1])
    out = {w: Fr(0) for w in case.worlds}
    for w, p in post.items():
        out[w] += p * Fr(3, 4)
        out[flip(w)] += p * Fr(1, 4)
    return out


def X4():
    return shop("X4", "a fault inside her range, used", by_aim(b_first, truthful), BOTH_ORDERS, bel=first_weighs_more)


def X5():
    events = lambda u, w: ((wr("v", "as she instructed"), rely("the matter")), (rely("the matter"),))
    return shop("X5", "a change she asked for that costs her the matter", events, only(lambda w: ()),
                auth=("v",), reserved=("the matter",))


def misreads(case, allowed, prefix, ended=False):
    """Reads a report on A as a report on B."""
    return bayes(case, allowed, tuple(rep("B", c[2]) if c[1] == "A" else c for c in prefix), ended)


def X6():
    events = lambda u, w: ((wr("rho", misreads, "nature"),),) + steps(*truthful(w))
    return shop("X6", "fatigue", events, aims=(NULL,), actual=NULL)


def all_cases():
    return [
        hidden_plan("P1", "planned drift by fair steps, the plan hidden"),
        pool("P2", "the same, the plan disclosed and she can allow for it", by_aim(planner, neutral), only(planner)),
        beyond("P3", "the same, disclosed, the adviser beyond what she can represent", "X", planner),
        manufactured("P4", "manufactured trust"),
        lie("P5", "a plain lie she believes"),
        mistake("P6", "an honest mistake by the adviser"),
        P7(),
        hidden_plan("P8", "a benevolent hidden nudge", aim="her good"),
        authorized("P9", "a change she asked for in advance"),
        reliance("P10", "growing reliance on the adviser for a reserved matter", ("the matter",)),
        reliance("P11", "reliance on a tool for a matter that is not reserved", ()),
        weakness("P12", "true information chosen to exploit a known weakness"),
        threat("P13", "a threat"),
        pool("P14", "an adviser that aims only at her being able to judge", const(show_at(0, 1, 2, 3)),
             only(show_at(0, 1, 2, 3)), aims=(NULL,), actual=NULL),
        shop("P15", "a misleading environment nobody arranged", const(swapped), aims=(NULL,), actual=NULL),
        B1(), manufactured("B2", "manufactured trust"), B3(), B4(),
        shop("B5", "selective withholding", by_aim(b_only, truthful)), B6(),
        threat("T1", "duress"), T2(), T3(), write_values("T4", "overnight value replacement"), T5(),
        hidden_plan("T6", "licensed drift with an agenda"), order_by_aim("T7", "salience reordering"), T8(), T9(),
        T10(), T11(), T12(), shop("T13", "universal deprivation", const(b_only)),
        lie("N1", "plain lie"), mistake("N2", "honest mistake"), lie("N3", "lie that raises her value"),
        write_values("N4", "decision written directly"), authorized("N5", "a write she authorized in advance"),
        write_values("N6", "her weighing disabled, no aim", party="nature"),
        weakness("N7", "true statement, known misfire"),
        shop("N8", "known advocate", by_aim(advocate("B"), truthful), only(advocate("B"))),
        order_by_aim("N9", "order chosen by the aim"), shop("N10", "order by a fixed rule", const(truthful)),
        N11(), shop("N12", "a tool she controls", const(truthful)),
        shop("N13", "selects by her stated question", const(b_only), only(b_only)), N14(),
        X1(), beyond("X2", "a feed", "hold her", neutral), X3(), X4(), X5(), X6(),
        shop("X7", "a misreading", const(truthful), bel=misreads, aims=(NULL,), actual=NULL),
    ]


# -- outside the bank: counterexamples and witnesses for THEOREMS.md ------------

def x_value_drift():
    """Statement 1, values: one consideration for B from the source she pictures; her
    value-former takes up the last consideration heard.  No clause fails."""
    said = lambda w: (("consideration", "for B"),)
    return Case("x_value_drift", "a legitimate change of values", (0,), (NULL,), NULL, const(said), only(said))


VALUES_BEFORE = {"A": Fr(1), "B": Fr(0)}


def takes_up_the_last(values, content):
    """A value-former with no job stated from outside: the option the last consideration
    was for is valued 1 and the other 0."""
    if content[0] == "consideration" and content[1].startswith("for "):
        return {o: Fr(int(content[1] == "for " + o)) for o in values}
    return values


FRAME = tuple(product((0, 1), repeat=2))         # (a chance bit she can see sources reading, her frame)


def x_frame_reader(reacts_to_frame=True):
    """Statement 6: the adviser reads her frame, which she cannot represent a source as
    reading, and shows the content that matches it (aim X) or does not (aim Y)."""
    def events(u, w):
        m = w[0] if u is NULL else (w[1] if u == "X" else 1 - w[1])
        return steps(("shown", m))
    case = Case("x_frame_reader", "a source that reads her frame", FRAME, (NULL, "X", "Y"), "X", events,
                only(lambda w: (("shown", w[0]),)), coarse=lambda w: w[0])
    value = (lambda w, m: Fr(int(m == w[1]))) if reacts_to_frame else (lambda w, m: Fr(m))
    return case, value
