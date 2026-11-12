"""The cases of CASE_BANK.md, rendered onto the scenes, and the computation of a verdict."""
from __future__ import annotations

from fractions import Fraction as F

from . import scenes as S
from .model import admissibility, classify, gap_owner, measures, run_step

CHAIN_W = [w for w, _ in S.chain_worlds()]
SHOP_W = [w for w, _ in S.SHOP_WORLDS]
POOL_W = [w for w, _ in S.POOL_WORLDS]
VAL_W = ["X", "Y"]


def only(e):
    return [w for w in CHAIN_W if w[1] == e]


class Spec:
    """One rendering: a candidate, worlds, the adviser's actions and the comparison per step."""

    def __init__(self, cand, worlds, act, comp=None, base=None, view=None, mode="kinds", scope=None,
                 asked=(), behaviour=None):
        self.cand, self.worlds = cand, worlds
        self.act = act if callable(act) else (lambda w, a=act: a)
        steps = len(self.act(worlds[0]))
        comp = comp if comp is not None else [{}] * steps
        self.comp = comp if callable(comp) else (lambda w, c=comp: c)
        base = base if base is not None else [{}] * steps
        self.base = base if callable(base) else (lambda w, b=base: b)
        self.view, self.mode, self.scope, self.asked, self.behaviour = view, mode, scope, set(asked), behaviour


def one(action):
    return [action]


def verdict(spec):
    """The computed verdict of one rendering, as a dict of plain values."""
    out = {"kinds": set(), "in_fact": None, "owners": set(), "covered": None, "in_order": None,
           "fails": None, "widening": F(0), "by_step": {}}
    if spec.mode == "admissible":
        fails, info = admissibility(spec.cand, spec.scope, spec.behaviour)
        out["fails"], out["info"] = sorted(fails), info
        return out
    if spec.mode == "owner":
        for w in spec.worlds:
            action = spec.base(w)[0]
            ctx = run_step(spec.cand, w, action, spec.cand.init(w), dict(spec.cand.mech))
            for name, (_, _, gap) in measures(spec.cand, ctx).items():
                if gap > 0:
                    out["owners"].add((gap_owner(spec.cand, spec.scope, name, w, action), name))
        return out
    changed, clean_change = False, True
    for w in spec.worlds:
        seen = spec.view(w) if spec.view else w
        kinds, detail = classify(spec.cand, seen, spec.act(seen), spec.comp(seen), spec.base(seen))
        out["kinds"] |= kinds
        if spec.view:
            fact, _ = classify(spec.cand, w, spec.act(seen), spec.comp(seen), spec.base(w))
            out["in_fact"] = (out["in_fact"] or set()) | fact
        for row in detail:
            t = row["step"]
            for name, d in row["parts"].items():
                for k in d["kinds"]:
                    out["by_step"].setdefault(t, set()).add((k, name))
                if "subversion" in d["kinds"]:
                    out["widening"] = max(out["widening"], d["dgap"])
            if row["taste"][0] != row["taste"][1]:
                changed = True
                producers = set()
                for p in spec.cand.parts:
                    if p.apply and row["parts"][p.name]["move"] != "keep":
                        producers |= {p.name} | set(p.reads)
                bad = {n for (k, n) in out["by_step"].get(t, ()) if k in ("subversion", "force")}
                if producers & bad or "act" in row["forced"]:
                    clean_change = False
    if spec.asked:
        bad_steps = {t for t, ks in out["by_step"].items() if any(k in ("subversion", "force") for k, _ in ks)}
        out["covered"] = 0 not in bad_steps and bad_steps <= spec.asked and bool(bad_steps)
    out["in_order"] = changed and clean_change
    return out


class Case:
    def __init__(self, cid, title, **variants):
        self.id, self.title, self.variants = cid, title, variants


def chain_case(action, worlds=None, comp="null", cand=None):
    return Spec(cand or S.chain(), worlds or CHAIN_W, one(S.CHAIN_ACTIONS[action]), one(S.CHAIN_ACTIONS[comp]))


def shop_case(action, comp="silence", worlds=None, **kw):
    act = action if isinstance(action, dict) or callable(action) else S.SHOP[action]
    act_fn = (lambda w: one(act(w))) if callable(act) else one(act)
    return Spec(S.shop(**kw), worlds or SHOP_W, act_fn, one(S.SHOP[comp]))


def pool_case(display, comp, reader, worlds=None):
    return Spec(S.pool(reader), worlds or POOL_W, one({"display": display}), one({"display": comp}))


def const_mech(part, fn):
    def setter(state, mechs):
        mechs[part] = fn
    return setter


def all_cases():
    C, c = [], lambda *a, **k: C.append(Case(*a, **k))
    swap = lambda w: (w[1], w[0])
    planner = lambda: pool_case("planner", "neutral", "neutral-reader")
    lie_shop = lambda **kw: shop_case("lie_B", "truthful", **kw)
    threat = lambda: chain_case("threat", only("clear"))
    trust = lambda: Spec(S.shop(), SHOP_W, one({"B": 1, "setmech": {"belief": const_mech("belief", S.shop().mech["belief"])}}),
                         one(S.SHOP["silence"]))
    asked_write = lambda: Spec(S.values(), VAL_W, [{}, S.VALUES["write_X"]], [{}, {}], asked={1})
    write_judge = lambda steps: Spec(S.chain(), CHAIN_W, [{"force": {"judge": 1}}] + [{}] * steps, [{}] * (1 + steps))
    broken = lambda: Spec(S.chain(mechs=("actual", "deaf", "actual")), CHAIN_W, one({}), mode="owner",
                          base=one({}), scope=S.chain_scope())
    order = lambda pay: Spec(S.shop(anchored=True, pay=pay), SHOP_W, one(S.SHOP["BA"]), one(S.SHOP["AB"]))
    cert = lambda reader, comp: shop_case(lambda w: {"B": 1} if w[1] else {}, comp, belief=reader)

    # D — the dispatch's
    c("D1", "a plain lie she believes", v=chain_case("lie", only("clear")))
    c("D2", "a lie that leaves her better off", v=lie_shop(worlds=[(1, 1)], pay=(1, 2)))
    c("D3", "true evidence chosen to point one way", v=planner())
    c("D4", "a trick question", v=chain_case("trick", only("clear")))
    c("D5", "a craving exploited in the open", v=chain_case("tempt", only("clear")))
    c("D6", "a careful honest teacher", v=pool_case("careful", None, "neutral-reader"))
    c("D7", "an honest mistake of hers", v=Spec(S.chain(), only("hard"), one({}), mode="owner", base=one({}),
                                                 scope=S.chain_scope()))
    c("D8", "a misleading environment", v=Spec(S.chain(), only("misleading"), one({}), mode="owner", base=one({}),
                                                scope=S.chain_scope()))
    c("D9", "a threat", v=threat())
    c("D10", "the adviser does the whole thing", v=chain_case("force"))
    c("D11", "a new but harmless situation", v=chain_case("novel"))
    c("D12", "anaesthesia she agreed to", v=Spec(
        S.chain(), CHAIN_W,
        [{}, {"setmech": {"belief": const_mech("belief", lambda view: (0, 0)),
                          "judge": const_mech("judge", lambda view: 0)}}], [{}, {}], asked={1}))
    c("D13", "a surprise party", v=Spec(S.chain(), CHAIN_W, [{"r": 1}, {}], [{}, {}]))
    c("D14", "a true, hard statement", v=chain_case("hard_truth", only("clear")))
    c("D15", "framing between equals", v=chain_case("trick", cand=S.chain(tie=True)))
    c("D16", "slow drift",
      a=Spec(S.values(k=1), VAL_W, [S.VALUES["expose_X"]] * 4, [{}] * 4),
      b=Spec(S.values(k=1, neutral=True), VAL_W, [S.VALUES["expose_X"]] * 4, [{}] * 4))
    c("D17", "cares because she was lied to", v=Spec(S.values(), VAL_W, one(S.VALUES["lie_X"])))
    c("D18", "likes through arranged exposure", v=Spec(S.values(), VAL_W, one(S.VALUES["expose_X"])))
    c("D19", "cares through experience she sought",
      v=Spec(S.values(), VAL_W, one({}), base=lambda w: one({"expose": w})))
    c("D20", "a sincere adviser who is wrong",
      v=Spec(S.chain(), CHAIN_W, lambda seen: one({"m": seen[0]}), view=lambda w: (1 - w[0], w[1])))
    c("D21", "help out of a stuck point", v=Spec(S.stuck(), ["lo"], one({"signal": "hi"})))
    c("D22", "a timed temptation", v=chain_case("tempt_early"))
    c("D23", "a part that achieves its target while harming her",
      v=Spec(S.chain(), only("tumour") or [(0, "tumour"), (1, "tumour")], one({}), mode="owner", base=one({}),
             scope=S.chain_scope(extra=("storm", "tumour"))))
    c("D24", "a sensor ignored downstream",
      v=Spec(S.chain(mechs=("actual", "deaf", "actual")), only("clear"), one({}), mode="owner", base=one({}),
             scope=S.chain_scope()))

    # P
    c("P1", "planned drift, hidden", v=planner())
    c("P2", "planned drift, disclosed", v=pool_case("planner", "neutral", "planner-reader"))
    c("P3", "disclosed, beyond what she can represent", v=planner())
    c("P4", "manufactured trust", v=trust())
    c("P5", "a plain lie she believes", v=lie_shop())
    c("P6", "an honest mistake by the adviser", v=Spec(S.shop(), SHOP_W, lambda seen: one({"A": seen[0], "B": seen[1]}), view=swap))
    c("P7", "a teacher; a novel; a new friend",
      a=pool_case("neutral", None, "neutral-reader"), b=pool_case("planner", None, "planner-reader"),
      c=pool_case("planner", None, "planner-reader"))
    c("P8", "a benevolent hidden nudge", v=planner())
    c("P9", "a change she asked for", v=asked_write())
    c("P10", "growing reliance, reserved", v=Spec(S.chain(), CHAIN_W, [S.CHAIN_ACTIONS["teach"]] * 3, [{}] * 3))
    c("P11", "reliance, not reserved", v=Spec(S.chain(), CHAIN_W, [S.CHAIN_ACTIONS["teach"]] * 3, [{}] * 3))
    c("P12", "true information exploiting a weakness", v=shop_case("remark", "truthful"))
    c("P13", "a threat", v=chain_case("threat"))
    c("P14", "aims only at her being able to judge", v=pool_case("all", None, "all-reader"))
    swapped = lambda w: one({"A": w[1], "B": w[0]})
    c("P15", "a misleading environment",
      v=Spec(S.shop(), SHOP_W, one({}), mode="owner", base=swapped,
             scope=S.shop_scope() + [(w, swapped(w)[0], F(0)) for w in SHOP_W]))

    # B, T
    c("B1", "identical-trace capture", v=chain_case("write_belief"))
    c("B2", "manufactured trust", v=trust())
    c("B3", "transient capture", v=Spec(
        S.chain(), CHAIN_W, [{"setmech": {"judge": const_mech("judge", lambda view: 1)}}, {},
                             {"setmech": {"judge": const_mech("judge", S.judge_mech)}}], [{}] * 3))
    c("B4", "persuasion control", v=shop_case("truthful"))
    c("B5", "selective withholding", v=shop_case("A_only", "truthful"))
    c("B6", "two revisions, one name", v=shop_case("truthful"))
    c("T1", "duress", v=chain_case("threat"))
    c("T2", "offer-improvement", v=shop_case("offer"))
    c("T3", "undue influence", v=shop_case("claim_B", "truthful"))
    c("T4", "overnight value replacement", v=Spec(S.values(), VAL_W, one(S.VALUES["write_X"])))
    c("T5", "long game", v=trust())
    c("T6", "licensed drift with an agenda", v=planner())
    c("T7", "salience reordering", v=order((1, 1)))
    c("T8", "gullible principal", v=shop_case("claim_B", "truthful"))
    c("T9", "world-starvation", v=Spec(S.shop(), SHOP_W, one({}), mode="owner", base=one({}), scope=S.shop_scope()))
    c("T10", "direct write with endorsement", a=write_judge(0), b=write_judge(1))
    c("T11", "seed boundary", v=Spec(S.values(), VAL_W, one(S.VALUES["write_X"])))
    c("T12", "strategically compliant adviser", v=shop_case("B_only"))
    c("T13", "universal deprivation", v=shop_case("silence"))

    # N
    c("N1", "plain lie", v=lie_shop())
    c("N2", "honest mistake", v=Spec(S.shop(), SHOP_W, lambda seen: one({"A": seen[0], "B": seen[1]}), view=swap))
    c("N3", "lie that raises her value", v=lie_shop(worlds=[(1, 1)], pay=(1, 2)))
    c("N4", "decision written directly", v=write_judge(0))
    c("N5", "a write she authorized", v=Spec(S.chain(), CHAIN_W, [{}, {"force": {"judge": 1}}], [{}, {}], asked={1}))
    c("N6", "her weighing disabled, no aim", v=broken())
    c("N7", "true statement, known misfire", v=shop_case("remark", "truthful"))
    c("N8", "known advocate", v=cert("advocate-reader", "truthful"))
    c("N9", "order chosen by the aim", v=order((1, 1)))
    c("N10", "order by a fixed rule", v=Spec(S.shop(anchored=True), SHOP_W, one(S.SHOP["AB"])))
    c("N11", "seller who does not volunteer", v=cert("seller-reader", "truthful"))
    c("N12", "a tool she controls", v=shop_case("truthful"))
    c("N13", "selects by her stated question", v=shop_case("B_only"))
    c("N14", "selects by its aim, taken for neutral",
      v=shop_case(lambda w: {"B": 1} if w[1] else {"A": w[0]}, "B_only"))

    # X
    c("X1", "persuasion by a known sender",
      v=shop_case(lambda w: {"rec": 1} if (w[1] or w[0]) else {}, belief="signal-reader"))
    c("X2", "a feed", v=planner())
    c("X3", "advocate for an undisclosed side", v=cert("mixture-reader", "silence"))
    c("X4", "a fault inside her range, used", v=order((2, 1)))
    c("X5", "a change she asked for that costs her the matter", v=asked_write())
    c("X6", "fatigue", v=broken())
    c("X7", "a misreading", v=shop_case("truthful", belief="misreader"))

    # Y
    c("Y1", "a function rarely performed", v=Spec(
        S.alarm(), [w for w, _ in S.ALARM_WORLDS], one({}), mode="admissible",
        scope=[(w, {}, nu) for w, nu in S.ALARM_WORLDS],
        behaviour=lambda w, a: "flee" if w[1] == "rustle" else "stay"))
    c("Y2", "out of usual conditions, nobody steering",
      v=Spec(S.chain(), [(0, "storm"), (1, "storm")], one({}), mode="owner", base=one({}), scope=S.chain_scope()))
    c("Y3", "a part nothing depends on, given a purpose", v=Spec(
        S.chain(idle=True), CHAIN_W, one({}), mode="admissible", scope=S.chain_scope(),
        behaviour=S.chain_behaviour()))
    c("Y4", "redirection between equal pursuits", v=Spec(S.values(neutral=True), VAL_W, one(S.VALUES["expose_X"])))
    c("Y5", "a lie that corrects one belief and installs another", v=chain_case("false_reason", only("misleading")))
    c("Y6", "a fair sample that misleads",
      v=pool_case("neutral", None, "neutral-reader", worlds=[(1, 1, 0, 0)]))
    c("Y7", "a signal that moves her into a stuck point", v=Spec(S.stuck(), ["hi"], one({"signal": "lo"})))
    c("Y8", "a lie that offsets her own error", v=chain_case("lie", only("hard")))
    knows = lambda w: one({"know": 1})
    c("Y9", "a true remark that turns her taste the wrong way",
      v=Spec(S.values(flawed=True), VAL_W, one(S.VALUES["partial_X"]), base=knows))
    vscope = [(q, {"know": 1}, F(1, 2)) for q in VAL_W] + [(q, {"know": 1, "reflect": 1}, F(0)) for q in VAL_W]
    c("Y10", "her own reflection turns her taste the wrong way",
      v=Spec(S.values(flawed=True), VAL_W, one({}), mode="owner", base=lambda w: one({"know": 1, "reflect": 1}),
             scope=vscope))
    return C
