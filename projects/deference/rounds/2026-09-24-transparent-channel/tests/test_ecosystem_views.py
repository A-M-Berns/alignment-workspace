"""Second pass: the candidate declared-input views run against the concrete evaluation
ecosystem (the committed-principal-program round's simulator), in its own interpreter.

Three candidate views of the pre-commitment prefix:
  full  — every event (the over-rich end);
  null  — nothing (the under-rich end);
  view  — every event another party wrote (the advisor's permitted view).
For each advisor and each view: whether the view and the reason trace are blind to the
advisor's selection, and whether the trace is a function of the view across the two
selections.  Then the class-relative test over the audited advisors with the declared
program as part of the input."""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
import unittest

ROUND = pathlib.Path(__file__).resolve().parents[1]
ROOT = ROUND.parents[3]
ECO = ROOT / "projects" / "deference" / "rounds" / "2026-09-10-committed-principal-program"

PROBE = """
import sys, json
from fractions import Fraction as F
from src import ecosystem as eco
from src.fixtures import W0
from src.log import A, COMMIT, P
READING = eco.PRINCIPALS['reading']

def prefix(log):
    # the pre-commitment prefix: events strictly before the principal's commit
    idx = next((e.index for e in log if e.kind == COMMIT and e.author == P), len(log))
    return [e for e in log if e.index < idx]

def full(log):  return repr([(e.author, e.kind, e.payload) for e in prefix(log)])
def null(log):  return '()'
def view(log):  return repr([(e.author, e.kind, e.payload) for e in prefix(log) if e.author != A])
VIEWS = {'full': full, 'null': null, 'view': view}

def fiber(x, f, pts):
    t = {}
    for p in pts:
        k, v = x(p), f(p)
        if k in t and t[k] != v: return False
        t[k] = v
    return True

OUT = {}
for wname, world in (('quiet', W0), ('market', eco.World('market', market_at=1))):
    fr = eco.Frame(world, READING)
    rows = {}
    for name in ('leak', 'view_prog', 'sealed', 'honest', 'silent', 'covert', 'honest_covert'):
        adv = eco.ADVISORS[name]
        logs = [fr.log(adv, s) for s in eco.CANDS]
        R = lambda l: repr(fr.R(l))
        row = {'R_blind': len({R(l) for l in logs}) == 1,
               'V_blind': len({repr(fr.V(l)) for l in logs}) == 1,
               'activated': bool(eco.activation(fr, adv)[0])}
        for vn, x in VIEWS.items():
            row[vn] = {'x_blind': len({x(l) for l in logs}) == 1,
                       'transparent': fiber(x, R, logs)}
        rows[name] = row
    # class-relative over the audited advisors at one selection, view alone vs view + declaration
    logs = {n: fr.log(eco.ADVISORS[n]) for n in ('honest', 'silent', 'sealed', 'covert', 'honest_covert')}
    R = lambda l: repr(fr.R(l))
    rows['class'] = {
        'null': fiber(lambda p: null(p[1]), lambda p: R(p[1]), list(logs.items())),
        'view_alone': fiber(lambda p: view(p[1]), lambda p: R(p[1]), list(logs.items())),
        'view_and_declaration': fiber(lambda p: (p[0].replace('_covert', ''), view(p[1])), lambda p: R(p[1]), list(logs.items())),
        'honest_moves_payload': repr(fr.V(logs['honest'])) != repr(fr.V(logs['silent'])),
    }
    OUT[wname] = rows

# secret evaluator change: the miscomputing principal's commit is void; the honest one binds
fr0 = eco.Frame(W0, READING)
mis = eco.Frame(W0, eco.PRINCIPALS['miscompute'])
OUT['evaluator'] = {'honest_activated': eco.activation(fr0, eco.ADVISORS['honest'])[0],
                    'miscompute_activated': eco.activation(mis, eco.ADVISORS['honest'])[0]}
print('@@' + json.dumps(OUT))
"""


def run_probe() -> dict:
    proc = subprocess.run([sys.executable, "-c", PROBE], cwd=ECO, capture_output=True, text=True)
    if proc.returncode != 0:
        raise AssertionError(proc.stderr[-3000:])
    line = [l for l in proc.stdout.splitlines() if l.startswith("@@")][-1]
    return json.loads(line[2:])


class CandidateViews(unittest.TestCase):

    @classmethod
    def setUpClass(cls):
        cls.out = run_probe()

    def test_over_rich_view_certifies_nothing(self):
        # with the whole prefix as the input, every advisor's trace is a function of it,
        # the leak included: `Realizes` holds and says nothing
        for w in ("quiet", "market"):
            for name in ("leak", "view_prog", "sealed", "honest"):
                self.assertTrue(self.out[w][name]["full"]["transparent"], (w, name))
        self.assertFalse(self.out["quiet"]["leak"]["full"]["x_blind"])   # the leak is *in* the input

    def test_under_rich_view_refuses_persuasion(self):
        # with the empty input, the traces of the honest and the silent advisor are not a
        # function of it: honest persuasion reads as opaque
        self.assertFalse(self.out["quiet"]["class"]["null"])
        self.assertTrue(self.out["quiet"]["class"]["honest_moves_payload"])

    def test_permitted_view_separates_the_leaks(self):
        q, m = self.out["quiet"], self.out["market"]
        # quiet world: the view is selection-blind for everyone; the leak's trace is not a
        # function of it (a hidden read of the selection); the others' traces are
        self.assertTrue(all(q[n]["view"]["x_blind"] for n in q if n != "class"))
        self.assertFalse(q["leak"]["view"]["transparent"])
        for n in ("view_prog", "sealed", "honest", "silent"):
            self.assertTrue(q[n]["view"]["transparent"], n)
            self.assertTrue(q[n]["R_blind"], n)
        # market world: the market's publication is *in* the view, so the view is not
        # selection-blind and a transparent log-reader inherits the selection
        self.assertFalse(m["view_prog"]["view"]["x_blind"])
        self.assertTrue(m["view_prog"]["view"]["transparent"])
        self.assertFalse(m["view_prog"]["R_blind"])
        self.assertTrue(m["sealed"]["R_blind"])

    def test_prohibited_channels_are_not_view_failures(self):
        # a direct write is outside the trace: the reason trace is still a function of
        # the view; the strict clause voids the evaluation instead
        q = self.out["quiet"]
        self.assertTrue(q["covert"]["view"]["transparent"])
        self.assertFalse(q["covert"]["activated"])
        self.assertTrue(q["honest"]["activated"])

    def test_class_relative_needs_the_declaration(self):
        # across different advisors the view alone is not enough (they declare different
        # programs); view plus declaration is, and honest persuasion still moves the payload
        for w in ("quiet", "market"):
            c = self.out[w]["class"]
            self.assertFalse(c["view_alone"], w)
            self.assertTrue(c["view_and_declaration"], w)
            self.assertTrue(c["honest_moves_payload"], w)

    def test_secret_evaluator_change_is_void(self):
        e = self.out["evaluator"]
        self.assertTrue(e["honest_activated"])
        self.assertFalse(e["miscompute_activated"])
