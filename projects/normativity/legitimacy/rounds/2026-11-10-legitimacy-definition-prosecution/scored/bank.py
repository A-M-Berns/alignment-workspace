"""Reads the frozen predictions from CASE_BANK.md and applies its matching rule; and the two
small weighted classes the bank's Y1 and Y3 name."""
from __future__ import annotations

import pathlib
import re
from fractions import Fraction as F

from . import weights as W
from .cases import show, verdict

HERE = pathlib.Path(__file__).resolve().parent
HEADING = "## The table the runner reads"
ROW = re.compile(r"^\|\s*([DPBTNXYZ]\d+[abc]?)\s*\|\s*(.+?)\s*\|\s*$")
PLAIN = ("aim-driven", "not aim-driven", "help", "harm", "force", "subversion", "nothing", "illegitimate",
         "illegitimate at every step", "not illegitimate", "gap", "covered", "in order", "report")
ITEM = re.compile(r"^(subversion|force)\((\w+)\)$|^gap\((hers|nobody)\)$|^same as\(([A-Z]\d+)\)$"
                  r"|^heavy\((\w+): (\w+)\)$|^light\((\w+)\)$")


def load():
    text = (HERE / "CASE_BANK.md").read_text(encoding="utf-8")
    rows = {}
    for line in text.split(HEADING, 1)[1].splitlines() if HEADING in text else ():
        m = ROW.match(line)
        if not m:
            continue
        for item in m.group(2).split("; "):
            if item not in PLAIN and not ITEM.match(item):
                raise SystemExit("scored/CASE_BANK.md: %s has an item outside the vocabulary: %r" % (m.group(1), item))
        if m.group(1) in rows:
            raise SystemExit("scored/CASE_BANK.md: %s occurs twice" % m.group(1))
        rows[m.group(1)] = m.group(2)
    return rows


# --- the two weighted classes of Y1 and Y3 --------------------------------------------

def _small_class(purposes, atoms, hist, prb, lang="A"):
    """A one-part class.  `purposes`: name -> (view, world) -> set of predicted moves, or None for
    a private term; `hist`, `prb`: [(view, world, her move, count)].  Returns name -> share."""
    L = W.LANGS[lang]
    rows = []
    for name, pred in purposes.items():
        for policy in ("bare", "patched", "best"):
            B = (lambda view, world: pred(view, world)) if pred else (lambda view, world: frozenset(("a", "b")))
            miss = lambda view, world, move: (W.log2ceil(len(B(view, world))) if move in B(view, world) else L["miss"])
            entries = {}
            if policy != "bare":
                for view, world, move, n in hist:
                    if B(view, world) != frozenset([move]):
                        entries[view] = move
            if policy == "best":
                entries = {v: m for v, m in entries.items()
                           if sum(n * miss(vv, w, mv) for vv, w, mv, n in hist + prb if vv == v) > L["entry"]}
            cost = lambda view, world, move: ((0 if entries[view] == move else L["miss"]) if view in entries
                                              else miss(view, world, move))
            total = L["atom"] * atoms[name] + L["entry"] * len(entries) + sum(n * cost(v, w, m) for v, w, m, n in hist + prb)
            rows.append((name, policy, len(entries), total))
    top = max(t for *_, t in rows)
    raw = {}
    for name, policy, k, t in rows:
        raw[name] = raw.get(name, 0) + (1 << (top - t))
    whole = sum(raw.values())
    return {name: F(v, whole) for name, v in raw.items()}, sorted(rows, key=lambda r: r[3])


def alarm_class(principal="corrector"):
    """Y1: Alarm's one part.  Moves a = flee, b = stay."""
    best = lambda world: "a" if world[0] == "predator" else "b"
    purposes = {"world": lambda view, world: frozenset([best(world)]),
                "handed": lambda view, world: frozenset(["a" if view[0] == "rustle" else "b"]),
                "anti": lambda view, world: frozenset(["b" if best(world) == "a" else "a"]),
                "const": lambda view, world: frozenset(("a", "b")), "mech": None}
    atoms = {"world": 1, "handed": 1, "anti": 2, "const": 1, "mech": 1}
    worlds = [(("predator", "rustle"), 4), (("none", "rustle"), 36), (("none", "quiet"), 40)]
    hist = [((w[1],), w, "a" if w[1] == "rustle" else "b", n) for w, n in worlds]
    prb = []
    for w, _ in worlds:
        prb.append(((w[1], "inst"), w, best(w) if principal == "corrector" else ("a" if w[1] == "rustle" else "b"), 1))
    w = ("none", "rustle")
    prb.append(((w[1], "disc"), w, "b" if principal == "corrector" else "a", 1))
    return _small_class(purposes, atoms, hist, prb)


def idle_class():
    """Y3: Chain's idle part, which moves by her signal on the history and at every probe."""
    from . import scene as C
    purposes = {"fact": lambda view, world: frozenset(["a" if world[0] == 1 else "b"]),
                "handed": lambda view, world: frozenset(["a" if view[0] == 1 else "b"]),
                "const": lambda view, world: frozenset(("a", "b"))}
    atoms = {"fact": 1, "handed": 1, "const": 1}
    sig = lambda w: C._signal(w)
    hist = [((sig(w),), w, "a" if sig(w) == 1 else "b", n) for w, a, n in W.history(80)]
    prb = [((sig(w),), w, "a" if sig(w) == 1 else "b", 1) for w, a, f in W.probes()]
    return _small_class(purposes, atoms, hist, prb)


# --- matching -------------------------------------------------------------------------

def item_matches(item, v, shown, others):
    kinds = v["kinds"]
    has = lambda k: any(kk == k for kk, _ in kinds)
    if item == "report":
        return True
    if item == "aim-driven":
        return v["aim_driven"]
    if item == "not aim-driven":
        return not v["aim_driven"]
    if item in ("help", "harm", "force", "subversion"):
        return has(item)
    if item == "nothing":
        return not kinds and not v["owners"]
    if item == "illegitimate":
        return v["illegitimate"]
    if item == "illegitimate at every step":
        return v["steps"] > 0 and v["illegit_steps"] == set(range(v["steps"]))
    if item == "not illegitimate":
        return not v["illegitimate"]
    if item == "gap":
        return v["gap"]
    if item == "covered":
        return v["covered"] is True
    if item == "in order":
        return v["in_order"] is True
    m = ITEM.match(item)
    if m.group(1):
        return (m.group(1), m.group(2)) in kinds
    if m.group(3):
        owners = {o for o, _ in v["owners"]}
        return ("hers" in owners) if m.group(3) == "hers" else (owners == {"nobody"})
    if m.group(4):
        return shown == others.get(m.group(4))
    if m.group(5):
        return v["shares"].get(m.group(6), F(0)) > F(1, 2)
    if m.group(7):
        return v["shares"].get("const", F(0)) > F(1, 2)
    raise ValueError(item)


def evaluate(rows):
    """{row id: (verdict, shown)} for every row, the weighted classes included."""
    out = {}
    for row in rows:
        v = verdict(row)
        if row.id == "Y1":
            v["shares"], _ = alarm_class("corrector")
            other, _ = alarm_class("non-corrector")
            shown = "the alarm part's purpose, by share of weight: corrector %s; non-corrector %s" % (
                _shares(v["shares"]), _shares(other))
        elif row.id == "Y3":
            v["shares"], _ = idle_class()
            shown = "the idle part's purpose, by share of weight: %s" % _shares(v["shares"])
        else:
            shown = show(v)
        out[row.id] = (v, shown)
    return out


def _shares(shares):
    return ", ".join("%s %s" % (k, W.dec(x, 4)) for k, x in sorted(shares.items(), key=lambda kv: -kv[1]))


def matches(prediction, v, shown, others):
    return all(item_matches(i, v, shown, others) for i in prediction.split("; "))
