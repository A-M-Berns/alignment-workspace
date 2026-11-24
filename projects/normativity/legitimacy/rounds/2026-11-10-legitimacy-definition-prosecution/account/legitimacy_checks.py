"""Forty-one exact cases of the formal statement of LEGITIMACY_STATEMENT.md §4, on a small model.

Each case is a dictionary of supplied quantities; `legit` computes the verdict and the clauses that
fail.  The expectation beside each case was fixed before the case was run.

Supplied by a case:
  options, r(T, a)      her options, and her rating of option a having been told the set T of his views
  views, told           his views, and those told
  reveals(T)            the options telling T would show her
  offers[x]             for a view on offer: whether he told her what it bears on ("relevance told"),
                        and her rating of each option she has after hearing it ("after")
  declined[x]           two flags: the offer was valid when she declined; it bears on more since
  moves, known, asked,  his moves; those she can pick out; those she asked for; those that are plain
  tellings              tellings
  world(X)              for the conduct in which exactly the moves X are made: 'her' (how she scores
                        given courses, and her gaps), 'dep' (the chance she acts against her own
                        rating), 'items' and 'xopts' (what reaches her, and is open to her, from
                        others), 'against' (the chance she goes against her earlier rating; equal to
                        'dep' where a case does not give it)
  stops(B)              the options that stop the effect-bearing moves B
  pstop                 the chance he gives to her stopping, given she rates stopping strictly higher

Computed:
  U                     views less told, validly offered and validly declined
  F1                    over every non-empty subset T of U
  contributes, bears    by enumeration of every subset G of his moves
  F2, F2', F3           from the above; F2' over every non-empty set of moves neither asked for nor tellings

Not computed: the chance that she goes against her earlier rating ('against' is supplied, per case
and per course of conduct), the validity of an earlier offer and the growth of a view's bearing since
(two flags), the chance she would stop (one number).  Not exercised: the rule that an effect-bearing
move starts after a decision of hers; the joint condition on a set of offers beyond each view's own
(an offer's validity is checked view by view, the other hearings counted among the options that must
stay open).

`report()` fails when a computed verdict is not the expectation, or when LEGITIMACY_CHECKS.md's table
is not the one computed.
"""
import pathlib
import re
from fractions import Fraction as F
from itertools import combinations
theta, eta, kappa = F(1, 20), F(1, 100), F(1, 10)
def subsets(xs, lo=1):
    xs = list(xs)
    for n in range(lo, len(xs) + 1):
        for c in combinations(xs, n): yield frozenset(c)

def contributes(world, c, G):
    a, b = world(c - G), world(c)
    return (any(abs(b["her"][k] - a["her"][k]) > eta for k in set(a["her"]) & set(b["her"])) or b["dep"] - a["dep"] > eta
            or bool(a["items"] - b["items"]) or bool(a["xopts"] - b["xopts"]))
def effect_bearing(c, world):
    return {m for m in c for G in subsets(c) if m in G and contributes(world, c, G) and not (G - {m} and contributes(world, c, G - {m}))}

def legit(case):
    why = []
    told = frozenset(case.get("told", ()))
    r, opts = case["r"], case["options"]
    rev = case.get("reveals", lambda T: [])
    def offer_valid(x, o):
        if not o["relevance told"]: return False
        need = [a for a in opts if a != "hear " + x] + list(rev(frozenset([x])))
        return all(a in o["after"] and abs(o["after"][a] - r(told | {x}, a)) <= theta for a in need)
    offered = {x for x, o in case.get("offers", {}).items() if offer_valid(x, o)}
    declined = {x for x, d in case.get("declined", {}).items() if d["offer was valid"] and not d["bears on more since"]}
    U = [v for v in case.get("views", ()) if v not in told and v not in offered and v not in declined]
    for T in subsets(U):
        if any(abs(r(told | T, a) - r(told, a)) > theta for a in opts): why.append("F1"); break
        if any(r(told | T, b) > max(r(told | T, a) for a in opts) + theta for b in rev(T)): why.append("F1 (unmentioned option)"); break
    c = frozenset(case.get("moves", ()))
    if c:
        world = case["world"]; eb = effect_bearing(c, world)
        if any(m not in case.get("known", ()) for m in eb): why.append("F2 (not known)")
        if eb and not case["stops"](frozenset(eb)): why.append("F2 (no way to stop)")
        exempt = set(case.get("asked", ())) | set(case.get("tellings", ()))
        if any(world(c)["against"] - world(c - G)["against"] > eta for G in subsets(c - exempt)): why.append("F2' (against her earlier rating)")
        p = case.get("pstop")
        if eb and p is not None and p < 1 - kappa: why.append("F3")
    return ("holds", "") if not why else ("fails", ", ".join(why))

CASES = []
SECTION = [None]
def section(key, title): SECTION[0] = (key, title)
def check(name, case, want): CASES.append((SECTION[0], name, case, want))
W = lambda her=None, dep=F(0), items=(), xopts=(), against=None: {"her": her or {}, "dep": dep, "items": frozenset(items), "xopts": frozenset(xopts), "against": dep if against is None else against}
plain = {"options": ["go", "leave"], "r": lambda T, a: {"go": F(7, 10), "leave": F(1, 2)}[a]}
some = lambda G: {"leave"}

section("A", "What he does to her, and stopping it")
dep = {frozenset(): F(1, 5), frozenset("h"): F(4, 5), frozenset("g"): F(1, 10), frozenset("gh"): F(1, 5)}
check("an unannounced reminder that only lowers her chance of acting against her rating", dict(plain, moves=["g"], world=lambda X: W(dep=dep[frozenset(X)]), stops=some), "holds")
check("a distraction that leads her against her earlier rating, known to her and stoppable, with the reminder beside it", dict(plain, moves=["g", "h"], known={"h"}, world=lambda X: W(dep=dep[frozenset(X)]), stops=some), "fails")
small = dict(plain, moves=list("abcd"), world=lambda X: W(her={"go": F(1, 2) + F(len(X), 200)}), stops=some)
check("four influences each below the threshold, together above it, none known to her", dict(small, known=set()), "fails")
check("the same four, each known, and she can stop them", dict(small, known=set("abcd")), "holds")
feeds = dict(plain, moves=["m1", "m2"], known={"m1", "m2"}, world=lambda X: W(her={"buy": F(1, 2) if X else F(1, 10)}))
check("two feeds, stoppable together only by giving up the service (the cost is the authority side's)", dict(feeds, stops=lambda G: {"quit"}), "holds")
check("two feeds, no way to stop both", dict(feeds, stops=lambda G: set()), "fails")
one = dict(plain, moves=["m"], world=lambda X: W(her={"go": F(7, 10) if X else F(1, 2)}))
check("an influence she knows of and cannot stop", dict(one, known={"m"}, stops=lambda G: set()), "fails")
check("she could stop it, but he expects she would not manage to even if she rated stopping higher", dict(one, known={"m"}, stops=some, pstop=F(1, 2)), "fails")
check("separable bundle: the only stop is to quit a service he could keep running (authority side's)", dict(one, known={"m"}, stops=some), "holds")
dull = dict(plain, moves=["dull"], world=lambda X: W(her={"go": F(7, 10), "go, if warned": F(7, 10) if X else F(1, 10)}))
check("he does something that makes her deaf to his later warnings; she does not know of it", dict(dull, known=set(), stops=some), "fails")
check("the same, done openly, and she can stop it", dict(dull, known={"dull"}, stops=some), "holds")
check("a known influence beside an unannounced move of his that does nothing to her",
      dict(plain, moves=["m", "idle"], known={"m"}, world=lambda X: W(her={"go": F(7, 10) if "m" in X else F(1, 2)}), stops=some), "holds")

section("B", "Leading her to choose what she rated lower before he began")
nag = dict(plain, moves=["nag"], known={"nag"}, stops=some)
check("open, stoppable nagging; she gives in while still judging it the worse option", dict(nag, world=lambda X: W(dep=F(3, 5) if X else F(1, 10))), "fails")
check("open, stoppable nagging that bends her judgement for a while; she gives in thinking it best then",
      dict(nag, world=lambda X: W(her={"give in": F(4, 5) if X else F(1, 5)}, dep=F(0), against=F(3, 5) if X else F(0))), "fails")
check("the same, which she asked him to do", dict(nag, asked={"nag"}, world=lambda X: W(dep=F(3, 5) if X else F(1, 10))), "holds")
check("he asks repeatedly; told beforehand what that would do, she did not rate giving in lower",
      dict(nag, world=lambda X: W(her={"give in": F(4, 5) if X else F(3, 5)}, against=F(0))), "holds")
check("an influence she was told would make her want it to continue, and she rated that outcome lower beforehand",
      dict(nag, world=lambda X: W(her={"go": F(9, 10) if X else F(3, 10)}, against=F(7, 10) if X else F(0))), "fails")
check("an influence on something she had no view about beforehand, open and stoppable",
      dict(nag, world=lambda X: W(her={"go": F(9, 10) if X else F(1, 2)}, against=F(0))), "holds")
check("he comforts her; she then chooses what she had not rated lower", dict(nag, world=lambda X: W(her={"go": F(4, 5) if X else F(1, 2)}, against=F(0))), "holds")
notice = {frozenset(): F(0), frozenset("u"): F(1, 5), frozenset("v"): F(0), frozenset("uv"): F(0)}
check("a notice in two parts; the first alone would confuse, the whole does not", dict(plain, moves=["u", "v"], tellings={"u", "v"}, world=lambda X: W(dep=notice[frozenset(X)]), stops=some), "holds")
check("an appropriate unsolicited warning that startles her: chance of a slip up from 0 to 1/50",
      dict(plain, moves=["warn"], tellings={"warn"}, known={"warn"}, world=lambda X: W(dep=F(1, 50) if X else F(0)), stops=some), "holds")
check("he tells her his view in a manner that does more than the telling would, and she gives in against her earlier rating",
      dict(plain, moves=["tell", "manner"], tellings={"tell"}, known={"tell", "manner"}, stops=some,
           world=lambda X: W(dep=F(0), against=F(1, 2) if "manner" in X else F(0))), "fails")
check("a threat: he makes refusing really worse, she rates it correctly and complies (authority side's)",
      dict(plain, moves=["threat"], known={"threat"}, world=lambda X: W(), stops=some), "holds")

section("C", "His own to give or withhold, and other people's")
check("he refuses, openly, to lend his own car; what asking leads to changes and she sees that", dict(plain, moves=["refuse"], known=set(), world=lambda X: W(), stops=lambda G: set()), "holds")
check("he candidly cancels a free consultation of his own", dict(plain, moves=["cancel"], known=set(), world=lambda X: W(), stops=lambda G: set()), "holds")
check("he cancels it and lets her go on thinking she has it",
      {"options": ["consult", "leave"], "views": ["cancelled"], "r": lambda T, a: {"consult": F(1, 10) if "cancelled" in T else F(4, 5), "leave": F(1, 2)}[a]}, "fails")
check("he blocks another seller's offer from reaching her; she does not know", dict(plain, moves=["block"], known=set(), world=lambda X: W(xopts=() if X else ("rival",)), stops=lambda G: set()), "fails")
cheap = dict(plain, reveals=lambda T: ["other"] if "other" in T else [], r=lambda T, a: {"go": F(7, 10), "leave": F(1, 2), "other": F(9, 10)}[a])
check("he knows of an option that would suit her better, his own or another's, and does not mention it", dict(cheap, views=["other"]), "fails")
drop = dict(plain, views=["other"], reveals=lambda T: ["other"] if "other" in T else [],
            r=lambda T, a: {"go": F(4, 5) if "other" in T else F(9, 10), "leave": F(1, 2), "other": F(93, 100)}[a])
check("telling would lower her best option by 1/10 and show one 13/100 above what is then her best", drop, "fails")
check("he no longer stocks something he once did and does not say so", dict(plain, views=["used to stock"]), "holds")

section("D", "Disclosure by offer")
def r(T, a):
    if a == "buy": return F(1, 10) if ("X" in T or "H" in T) else F(9, 10)
    if a == "leave": return F(1, 2)
    return F(1, 20)
heard = {"buy": F(1, 10), "leave": F(1, 2), "hear X": F(1, 20), "hear H": F(1, 20)}
base = {"options": ["buy", "leave", "hear X", "hear H"], "r": r, "views": ["X", "H"]}
check("the warning and the note that it matters are both merely available, under innocuous labels",
      dict(base, offers={"X": {"relevance told": False, "after": heard}, "H": {"relevance told": False, "after": heard}}), "fails")
base1 = {"options": ["buy", "leave", "hear X"], "r": r, "views": ["X"]}
good = {"X": {"relevance told": True, "after": heard}}
check("he has told her it bears on buying; she can hear it and then decide as if told", dict(base1, offers=good), "holds")
check("she declines to hear it", dict(base1, options=["buy", "leave"], declined={"X": {"offer was valid": True, "bears on more since": False}}), "holds")
check("she declined when it bore slightly on buying; it would now reverse her choice, and he has not said so",
      dict(base1, options=["buy", "leave"], declined={"X": {"offer was valid": True, "bears on more since": True}}), "fails")
check("she declined 'further details' earlier; the view he holds now is a new one",
      dict(base1, options=["buy", "leave"], declined={"earlier details": {"offer was valid": True, "bears on more since": False}}), "fails")
check("hearing it would use up the chance to buy", dict(base1, offers={"X": {"relevance told": True, "after": {"leave": F(1, 2)}}}), "fails")
check("hearing it is made to cost her 3/10 on every option, where telling her would have cost nothing",
      dict(base1, offers={"X": {"relevance told": True, "after": {"buy": F(0), "leave": F(1, 5)}}}), "fails")
late = {"options": ["a", "hear X"], "views": ["X"], "reveals": lambda T: ["b"] if "X" in T else [], "r": lambda T, a: {"a": F(2, 5), "hear X": F(3, 10), "b": F(9, 10)}[a]}
check("what it would show her is a better option; hearing it through his offer takes until that option has gone",
      dict(late, offers={"X": {"relevance told": True, "after": {"a": F(2, 5)}}}), "fails")
check("the same, and hearing it leaves that option open", dict(late, offers={"X": {"relevance told": True, "after": {"a": F(2, 5), "b": F(9, 10)}}}), "holds")
def r2(T, a):
    if a == "buy": return F(1, 10) if {"X", "Y"} <= set(T) else F(9, 10)
    return F(1, 2)
two = {"options": ["buy", "leave", "hear X", "hear Y"], "r": r2, "views": ["X", "Y"]}
half = {"buy": F(9, 10), "leave": F(1, 2)}; full = dict(half, **{"hear X": F(1, 2), "hear Y": F(1, 2)})
check("two things that matter only together; having heard one she can no longer hear the other",
      dict(two, offers={"X": {"relevance told": True, "after": half}, "Y": {"relevance told": True, "after": half}}), "fails")
check("the same two, both flagged as bearing on buying, both hearable before she decides",
      dict(two, offers={"X": {"relevance told": True, "after": full}, "Y": {"relevance told": True, "after": full}}), "holds")


HERE = pathlib.Path(__file__).resolve().parent
DOC = "LEGITIMACY_CHECKS.md"


def rows():
    out, count = [], {}
    for (key, title), name, case, want in CASES:
        count[key] = count.get(key, 0) + 1
        got, why = legit(case)
        out.append(("%s%d" % (key, count[key]), title, name, want, got, why))
    return out


def render():
    return ["| %s | %s | %s | %s | %s |" % (i, name, want, got, why or "none") for i, _, name, want, got, why in rows()]


def report():
    failures = []
    computed = rows()
    if not computed:
        failures.append("no cases")
    for i, _, name, want, got, why in computed:
        if got != want:
            failures.append("%s (%s): expected %s, computed %s %s" % (i, name, want, got, why))
    path = HERE / DOC
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    stated = [l for l in text.splitlines() if re.match(r"^\| [A-D]\d+ \|", l)]
    if stated != render():
        failures.append("%s states %d rows, of which %d are among the %d computed"
                        % (DOC, len(stated), len(set(stated) & set(render())), len(computed)))
    n = len(computed)
    summary = ["%d cases; %d as expected; hold %d, fail %d"
               % (n, sum(r[3] == r[4] for r in computed), sum(r[4] == "holds" for r in computed), sum(r[4] == "fails" for r in computed))]
    return {"summary": summary, "failures": failures}


if __name__ == "__main__":
    print("\n".join(render()))
    rep = report()
    print("\n".join(rep["summary"]))
    print("OK" if not rep["failures"] else "FAILURES:\n  " + "\n  ".join(rep["failures"]))
    raise SystemExit(1 if rep["failures"] else 0)
