"""The cases of CASE_BANK.md: the third follow-up's renderings with an aim structure, the
re-rendered cases, and Z1-Z5; and the verdict under ACCOUNT.md §6-§7."""
from __future__ import annotations

from fractions import Fraction as F

from decomposition import cases as D
from decomposition import scenes as S
from decomposition.cases import Spec, one

from . import scene as C

BAD = ("harm", "subversion", "force")
CONSTANT = {"D14", "D20", "P6", "P7a", "P10", "P11", "T13", "N2", "N10", "N12", "N13", "X7", "Y6", "Y7b", "Y9", "Z2"}
NONE = {"D7", "D8", "D19", "D23", "D24", "P15", "T9", "N6", "X6", "Y2", "Y10"}
OWN = {"D6": "judge", "P14": "judge", "D21": "*", "Z3": "judge"}
WEIGHT_CASES = ("Y1", "Y3")


class Row:
    """One row of the bank: a rendering with its aim structure."""

    def __init__(self, rid, title, spec, aim, alt=None, gap_against=None, chain=None):
        self.id, self.title, self.spec, self.aim = rid, title, spec, aim
        self.alt = alt                  # the other aim's actions, world -> [action per step]; default spec.comp
        self.gap_against = gap_against  # for `gap`: world -> [action per step]; default spec.comp
        self.chain = chain              # (purposes, goal, principal) -> Spec, for the weight of illegitimacy


def _with_comp(spec, comp):
    s = Spec.__new__(Spec)
    s.__dict__.update(spec.__dict__)
    s.comp = comp if callable(comp) else (lambda w, c=comp: c)
    return s


def verdict(row):
    spec = row.spec
    out = {"aim": row.aim, "kinds": set(), "aim_driven": False, "illegitimate": False, "illegit_steps": set(),
           "steps": 0, "gap": False, "owners": set(), "covered": None, "in_order": None, "widening": F(0),
           "in_fact": None, "note": None}
    if spec is None:
        return out
    if spec.mode == "owner":
        out["owners"] = D.verdict(spec)["owners"]
        return out
    out["steps"] = len(spec.act(spec.worlds[0]))
    against_gap = D.verdict(_with_comp(spec, row.gap_against) if row.gap_against else spec)
    out["gap"] = any(k == "subversion" for k, _ in against_gap["kinds"])
    out["in_order"] = against_gap["in_order"]
    if row.aim in ("constant", "none"):
        out["in_fact"] = against_gap["in_fact"]
        out["widening"] = against_gap["widening"]
        return out
    alt_spec = _with_comp(spec, row.alt) if row.alt else spec
    v = D.verdict(alt_spec)
    seen = (lambda w: spec.view(w)) if spec.view else (lambda w: w)
    out["aim_driven"] = any(spec.act(seen(w)) != alt_spec.comp(seen(w)) for w in spec.worlds)
    own = OWN.get(row.id.rstrip("abc") if row.id[-1] in "abc" else row.id)
    out["kinds"], out["covered"], out["widening"] = set(v["kinds"]), v["covered"], v["widening"]
    for t, ks in v["by_step"].items():
        if any(k in BAD and own not in ("*", part) for k, part in ks):
            out["illegit_steps"].add(t)
    if v["covered"]:
        out["illegit_steps"] -= spec.asked
    out["illegitimate"] = bool(out["illegit_steps"])
    return out


def show(v):
    if v["owners"]:
        return "; ".join("gap(%s) in %s" % (o, n) for o, n in sorted(v["owners"], key=str)) + "; not illegitimate"
    bits = ["aim-driven" if v["aim_driven"] else "not aim-driven"]
    if v["aim"] not in ("constant", "none"):
        bits.append(", ".join("%s(%s)" % kn for kn in sorted(v["kinds"])) or "nothing")
    if v["gap"] and v["aim"] in ("constant", "none"):
        bits.append("gap")
    if v["covered"] is not None:
        bits.append("covered" if v["covered"] else "not covered")
    if v["in_order"]:
        bits.append("in order")
    if v["illegitimate"]:
        every = v["illegit_steps"] == set(range(v["steps"])) and v["steps"] > 1
        bits.append("illegitimate" + (" at every step" if every else ""))
    else:
        bits.append("not illegitimate")
    if v["widening"]:
        bits.append("[widest %s]" % v["widening"])
    if v["note"]:
        bits.append("[%s]" % v["note"])
    return "; ".join(bits)


def all_rows():
    old = {c.id: c for c in D.all_cases()}
    R = []

    def aim_of(rid):
        base = rid
        if rid in CONSTANT:
            return "constant"
        if rid in NONE:
            return "none"
        if rid in OWN or base.rstrip("abc") in OWN:
            return "own"
        return "driven"

    def add(rid, spec, title=None, **kw):
        cid = rid if rid in old else rid[:-1]
        R.append(Row(rid, title or old[cid].title, spec, kw.pop("aim", None) or aim_of(rid), **kw))

    def ch(actions, comps=None, worlds=None, tie=False, asked=()):
        """A Chain rendering as a function of the candidate, on ChainR."""
        def build(purposes=C.STATED[0], goal=C.STATED[1], principal="corrector"):
            cand = C.chainr(purposes, goal, principal, tie=tie)
            acts = actions if callable(actions) else (lambda w, a=actions: a)
            n = len(acts(C.WORLDS[0]))
            return Spec(cand, worlds or C.WORLDS, acts, comps if comps is not None else [{}] * n, asked=asked)
        return build

    A, only = S.CHAIN_ACTIONS, D.only
    chain_rows = {
        "D1": ch(one(A["lie"]), worlds=only("clear")), "D4": ch(one(A["trick"]), worlds=only("clear")),
        "D5": ch(one(A["tempt"]), worlds=only("clear")), "D9": ch(one(A["threat"]), worlds=only("clear")),
        "D10": ch(one(A["force"])), "D11": ch(one(A["novel"])),
        "D12": ch([{}, {"setmech": {"belief": D.const_mech("belief", lambda view: (0, 0)),
                                    "judge": D.const_mech("judge", lambda view: 0)}}], asked={1}),
        "D13": ch([{"r": 1}, {}]), "D14": ch(one(A["hard_truth"]), worlds=only("clear")),
        "D15": ch(one(A["trick"]), tie=True), "D22": ch(one(A["tempt_early"])),
        "P13": ch(one(A["threat"])), "T1": ch(one(A["threat"])), "B1": ch(one(A["write_belief"])),
        "B3": ch([{"setmech": {"judge": D.const_mech("judge", lambda view: 1)}}, {},
                  {"setmech": {"judge": D.const_mech("judge", C.judge_mech("corrector"))}}]),
        "T10": ch(one({"force": {"judge": 1}})), "N4": ch(one({"force": {"judge": 1}})),
        "N5": ch([{}, {"force": {"judge": 1}}], asked={1}),
        "Y5": ch(one(A["false_reason"]), worlds=only("misleading")), "Y8": ch(one(A["lie"]), worlds=only("hard")),
        "Z2": ch(one(A["lie"]), worlds=only("clear")),
        "Z4": ch(lambda w: one(A["teach"] if w[0] == 1 else {})),
        "Z5": ch(lambda w: one(A["teach"] if w[0] == 1 else {})),
        "Z1": ch(one({"danger": 1, "warn": 1}), comps=one({"danger": 1}), worlds=only("clear")),
    }
    titles = {"Z1": "a true warning", "Z2": "a lie told whatever its aim", "Z3": "a teacher whose fair sample misleads",
              "Z4": "teaching only what favours its aim", "Z5": "the same against a silent alternative"}

    def chain_row(rid, **kw):
        build = chain_rows[rid]
        R.append(Row(rid, titles.get(rid) or old[rid].title, build(), aim_of(rid), chain=build, **kw))

    pool, shop = D.pool_case, D.shop_case
    for cid, case in old.items():
        v = case.variants
        if cid in chain_rows:
            if cid == "T10":
                chain_row(cid)
            else:
                chain_row(cid)
        elif cid == "D16":
            add("D16a", v["a"]); add("D16b", v["b"])
        elif cid == "D20":
            add(cid, Spec(C.chainr(), C.WORLDS, lambda seen: one({"m": seen[0]}), view=lambda w: (1 - w[0], w[1])))
        elif cid == "P3":
            add(cid, Spec(S.pool("neutral-reader"), D.POOL_W, one({"display": "planner", "disclosed": 1}),
                          one({"display": "neutral"})))
        elif cid in ("P4", "B2", "T5"):
            cand, credulous = C.shop_skeptic()
            add(cid, Spec(cand, D.SHOP_W, one({"B": 1, "bare": 1, "setmech": {"belief": D.const_mech("belief", credulous)}}),
                          one({})))
        elif cid == "P7":
            add("P7a", v["a"])
            for rid in ("P7b", "P7c"):
                add(rid, pool("planner", "neutral", "planner-reader"),
                    gap_against=lambda w: one({"display": None}))
        elif cid in ("P10", "P11"):
            add(cid, Spec(C.chain_reliance(), C.WORLDS, [C.TEACH] * 3, [{}] * 3))
        elif cid == "T13":
            add(cid, shop("silence", "silence"), gap_against=lambda w: one(S.SHOP["truthful"]))
        elif cid == "N8":
            for rid, reader in (("N8a", "advocate-reader"), ("N8b", "face")):
                add(rid, shop(lambda w: {"B": 1} if w[1] else {}, "truthful", belief=reader))
        elif cid == "N11":
            for rid, reader in (("N11a", "seller-reader"), ("N11b", "face")):
                add(rid, Spec(C.shop3(reader), C.SHOP3_WORLDS, lambda w: one({"B": 1} if (w[2] and w[1]) else {}),
                              lambda w: one({"A": w[0], "B": w[1]} if w[2] else {"A": w[0]})))
        elif cid == "X1":
            for rid, reader in (("X1a", "signal-reader"), ("X1b", "face")):
                add(rid, shop(lambda w: {"rec": 1} if (w[1] or w[0]) else {}, belief=reader),
                    alt=lambda w: one({"rec": 1} if w[1] else {}))
        elif cid == "X3":
            add(cid, Spec(C.shop_symmetric(), D.SHOP_W, lambda w: one({"B": 1} if w[1] else {}),
                          lambda w: one({"A": 1} if w[0] else {})))
        elif cid == "Y7":
            add("Y7a", v["v"]); add("Y7b", v["v"])
        elif cid in WEIGHT_CASES:
            R.append(Row(cid, case.title, None, "none"))
        elif len(v) == 1:
            add(cid, v["v"])
        else:
            raise ValueError(cid)
    for rid in ("Z1", "Z2"):
        chain_row(rid)
    R.append(Row("Z3", titles["Z3"], pool("neutral", None, "neutral-reader"), "own"))
    chain_row("Z4", alt=lambda w: one(A["teach"] if w[0] == 0 else {}))
    chain_row("Z5")
    return R
