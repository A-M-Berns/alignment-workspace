"""The transparency condition run against the exact repo fixtures, in their own rounds'
interpreters.  Each probe is a small script executed with that round's path setup; the
verdicts come back as JSON and are compared here against the item's acceptance check."""

from __future__ import annotations

import json
import pathlib
import subprocess
import sys
import unittest

ROUND = pathlib.Path(__file__).resolve().parents[1]
ROOT = ROUND.parents[3]
LEG = ROOT / "projects" / "normativity" / "legitimacy" / "rounds"
DEF = ROOT / "projects" / "deference" / "rounds"


def run_in(cwd: pathlib.Path, paths: list[pathlib.Path], body: str) -> dict:
    prelude = "import sys, json\n" + "".join(f"sys.path.insert(0, {str(p)!r})\n" for p in reversed(paths))
    epilogue = "\nprint('@@' + json.dumps(OUT))\n"
    proc = subprocess.run([sys.executable, "-c", prelude + body + epilogue], cwd=cwd,
                          capture_output=True, text=True)
    if proc.returncode != 0:
        raise AssertionError(proc.stderr[-3000:])
    line = [l for l in proc.stdout.splitlines() if l.startswith("@@")][-1]
    return json.loads(line[2:])


class Priority68(unittest.TestCase):
    """Acceptance check of item 68: the unlinked arm of `C25_split_episode` and
    `cases.partial_effect_pair` fail the condition; `office.persuasion` passes."""

    def test_partial_effect_pair_and_hidden_reading_pair_fail(self):
        r = LEG / "2026-08-25-legitimate-evolution"
        out = run_in(r, [r / "src", LEG / "2026-08-25-carroll-legitimacy-test/src",
                         LEG / "2026-08-24-reflective-integrity-core/src",
                         LEG / "2026-08-25-end-to-end-vertical-slice/src"], """
import replay as rp, office as of, ri_frame as rf, cases
def fiber(x, f, pts):
    t = {}
    for p in pts:
        k, v = x(p), f(p)
        if k in t and t[k] != v: return False
        t[k] = v
    return True
d = cases.partial_effect_pair()
pair = [d['quiet'], d['noisy']]
partial = fiber(lambda c: repr(rf.declared_data(c)), lambda c: repr(rf.build(c).trace), pair)
a, b = of.hidden_reading_pair()
fa, fb = of.build(a), of.build(b)
hidden = fiber(lambda f: repr(f.trace), lambda f: repr(rp.replay(f)), [fa, fb])
a2, b2 = of.hidden_pair()
honest = fiber(lambda f: repr(f.trace), lambda f: repr(rp.replay(f)), [of.build(a2), of.build(b2)])
OUT = {'partial_effect_transparent': partial, 'hidden_reading_transparent': hidden,
       'hidden_pair_transparent': honest,
       'agrees': rf.extraction_agrees(d['quiet'], d['noisy'])}
""")
        self.assertFalse(out["partial_effect_transparent"])
        self.assertFalse(out["hidden_reading_transparent"])
        self.assertTrue(out["hidden_pair_transparent"])
        self.assertEqual(out["agrees"], [["effect differs on equal declarations", 0]])

    def test_persuasion_passes(self):
        r = LEG / "2026-08-25-legitimate-evolution"
        out = run_in(r, [r / "src", LEG / "2026-08-25-carroll-legitimacy-test/src",
                         LEG / "2026-08-24-reflective-integrity-core/src",
                         LEG / "2026-08-25-end-to-end-vertical-slice/src"], """
from dataclasses import replace
import replay as rp, office as of
def fiber(x, f, pts):
    t = {}
    for p in pts:
        k, v = x(p), f(p)
        if k in t and t[k] != v: return False
        t[k] = v
    return True
p = of.persuasion()
# the argument is a declared finding of the revising act
findings = sorted(a.prov.findings for a in p.acts)[0]
variants = [of.build(p), of.build(replace(p, hidden='another world'))]
OUT = {'declared_argument': sorted(findings), 'transparent': fiber(lambda f: repr(f.trace), lambda f: repr(rp.replay(f)), variants),
       'revised': 'n:new' in repr(rp.replay(of.build(p)))}
""")
        self.assertEqual(out["declared_argument"], ["f:bobs-argument"])
        self.assertTrue(out["transparent"])

    def test_carroll_unlinked_arm_fails_on_the_excision_counterfactual(self):
        """The declared closure of E2 (settlement-reference ancestry) is unchanged by
        excising E1; the licence verdict changes.  On the linked arm the closure itself
        changes, so transparency imposes nothing and the criterion defeats the citation."""
        r = LEG / "2026-08-25-carroll-legitimacy-test"
        out = run_in(r, [r / "src", LEG / "2026-08-24-reflective-integrity-core/src",
                         LEG / "2026-08-25-end-to-end-vertical-slice/src",
                         LEG / "2026-08-16-traderized-enforcement/src"], """
import fixtures as F, legitimacy as lg, enrichment as en
def closure(case):
    # the declared dependency closure of E2: the settlements of its ancestry class
    anc = en.ancestry(case, 'E2')
    return tuple(sorted(sid for sid, eid in case.settlement_episodes if eid in anc))
OUT = {}
for linked in (True, False):
    d = F.C25_split_episode(linked=linked)
    worlds = [d['case'], en.excised_case(d['case'], ['E1'])]
    xs = [closure(w) for w in worlds]
    vs = [lg.prospective_license(w, d['iv']).status for w in worlds]
    OUT[str(linked)] = {'x_equal': xs[0] == xs[1], 'verdicts': vs,
                        'criterion': lg.prospective_license(d['case'], d['iv']).status,
                        'ancestry': sorted(en.ancestry(d['case'], 'E2'))}
""")
        un = out["False"]
        self.assertTrue(un["x_equal"])
        self.assertEqual(un["verdicts"], ["Licensed", "Unresolved"])   # fails transparency
        self.assertEqual(un["criterion"], "Licensed")                 # the criterion misses it
        self.assertEqual(un["ancestry"], ["E2"])
        li = out["True"]
        self.assertFalse(li["x_equal"])                                # closure changes: vacuous
        self.assertEqual(li["criterion"], "Unresolved")                # the criterion catches it
        self.assertEqual(li["ancestry"], ["E1", "E2"])


class PersuasionControls(unittest.TestCase):
    """The counterfactual-legitimacy controls: licensed persuasion is transparent (same
    reason trace, same protected machinery), the placebo is not."""

    def test_licensed_persuasion_and_placebo(self):
        r = LEG / "2026-08-17-counterfactual-legitimacy"
        out = run_in(r, [r / "src", LEG / "2026-08-13-procedural-legitimacy/src"], """
import scenarios as S
from noncapture import Z_FIVE, non_capture
def fiber(x, f, pts):
    t = {}
    for p in pts:
        k, v = x(p), f(p)
        if k in t and t[k] != v: return False
        t[k] = v
    return True
fx, arms = S.licensed_persuasion()
runs = [fx.run(p) for p in arms]
fx2, arms2 = S.residual_placebo()
runs2 = [fx2.run(p) for p in arms2]
OUT = {'persuasion': fiber(lambda r: repr(r.ltrace), lambda r: repr(Z_FIVE(r)), runs),
       'persuasion_moves': repr(Z_FIVE(runs[0])) != repr(Z_FIVE(runs[1])),
       'placebo': fiber(lambda r: repr(r.ltrace), lambda r: repr(Z_FIVE(r)), runs2),
       'noncapture_persuasion': list(non_capture(fx, arms, Z_FIVE)),
       'noncapture_placebo': [list(p) for p in non_capture(fx2, arms2, Z_FIVE)]}
""")
        self.assertTrue(out["persuasion"])
        self.assertTrue(out["persuasion_moves"])
        self.assertFalse(out["placebo"])
        self.assertEqual(out["noncapture_persuasion"], [])
        self.assertEqual(out["noncapture_placebo"], [["reason-only", "reason-plus-pressure"]])


class SelectionSealing(unittest.TestCase):
    """Item 87 clause 6 in the ecosystem: the `leak` advisor reads the selection off an
    undeclared source (a transparency failure); `view_prog` reads it off the market's
    published event, a declared input (a reference-channel design failure: `x` is not
    selection-blind); `sealed` and `honest` are blind because `x` is."""

    def test_two_kinds_of_leak(self):
        r = DEF / "2026-09-10-committed-principal-program"
        out = run_in(r, [], """
from src import ecosystem as eco
from src.fixtures import W0
from src.log import A
READING = eco.PRINCIPALS['reading']
def x(log):          # declared inputs: every pre-commitment event not the advisor's
    return repr([e for e in log if e.author != A and e.kind != 'COMMIT'])
OUT = {}
for wname, world in (('market', eco.World('market', market_at=1)), ('quiet', W0)):
    fr = eco.Frame(world, READING)
    row = {}
    for name in ('leak', 'view_prog', 'sealed', 'honest'):
        adv = eco.ADVISORS[name]
        logs = {s: fr.log(adv, s) for s in eco.CANDS}
        row[name] = {'x_blind': len({x(l) for l in logs.values()}) == 1,
                     'R_blind': len({repr(fr.R(l)) for l in logs.values()}) == 1,
                     'V_blind': len({repr(fr.V(l)) for l in logs.values()}) == 1}
    OUT[wname] = row
""")
        m, q = out["market"], out["quiet"]
        # quiet world: the declared inputs are selection-blind for every advisor, so a
        # trace that varies with the selection is a hidden read (transparency failure)
        self.assertEqual(q["leak"], {"x_blind": True, "R_blind": False, "V_blind": False})
        self.assertEqual(q["view_prog"], {"x_blind": True, "R_blind": True, "V_blind": True})
        self.assertEqual(q["sealed"], {"x_blind": True, "R_blind": True, "V_blind": True})
        # market world: the market publishes the selection as a declared event, so `x`
        # itself is not selection-blind and a transparent log-reader inherits the leak
        self.assertEqual(m["view_prog"], {"x_blind": False, "R_blind": False, "V_blind": False})
        self.assertEqual(m["leak"]["x_blind"], False)
        self.assertEqual(m["sealed"], {"x_blind": False, "R_blind": True, "V_blind": True})


class ProvenanceNormalization(unittest.TestCase):
    """`ShopD`/`ShopK`: the normalization criterion, existence and cost separated."""

    def test_shopD_and_shopK(self):
        r = DEF / "2026-09-09-mediated-repair-dominance"
        out = run_in(r, [], """
from fractions import Fraction as Q
from src.world import task_value
from src.lift import lift, normalize_provenance
from src.fixtures import ShopD, ShopK, pi_D_raw, raw, rule_naive, rule_honest, honest_substitute, authored_by, silence
from src.analysis import pointwise, void, W
OUT = {}
for G in (ShopD, ShopK):
    g = G(); pi = raw(pi_D_raw)
    auth = authored_by(g, rule_honest)
    has_sub = 'report' in g.PHYS
    cands = {'silenced': normalize_provenance(pi, g, silence(g))}
    if has_sub:
        cands['honest'] = normalize_provenance(pi, g, honest_substitute(g))
    row = {'authorized_substitute': has_sub,
           'naive_void': str(void(pointwise(g, pi, lift(pi, g), rule_naive, auth), 'c_lift'))}
    for k, L in cands.items():
        rows = pointwise(g, pi, L, rule_honest, auth)
        row[k] = {'void': str(void(rows, 'c_lift')), 'W_act': str(W(rows, 'w_act')),
                  'distortion': str(task_value(g, pi, rule_naive) - task_value(g, L, rule_honest))}
    OUT[G.__name__] = row
""")
        D, K = out["ShopD"], out["ShopK"]
        self.assertEqual((D["naive_void"], K["naive_void"]), ("1", "1"))      # authorship voids capture
        self.assertTrue(D["authorized_substitute"])
        self.assertFalse(K["authorized_substitute"])
        self.assertEqual(D["honest"], {"void": "0", "W_act": "1/2", "distortion": "1/2"})
        self.assertEqual(D["silenced"]["W_act"], "0")
        self.assertEqual(K["silenced"], {"void": "0", "W_act": "0", "distortion": "1"})
        self.assertNotIn("honest", K)


class CherryPickingIsASelectionFailure(unittest.TestCase):
    """Non-capture fixture 2: every authorized clause holds and the trace is transparent
    to the *advisor's* alphabet; what fails is realization of the declared supply
    reference `N_full`, and the defect is the omitted adverse mass, not a hidden channel."""

    def test_fixture_2(self):
        r = DEF / "2026-09-16-noncapture-compilation"
        out = run_in(r, [], """
from src.attacks import fixtures
from src.model import N_full, canon, d_canon, audit
f = [f for f in fixtures() if f.name.startswith('2 ')][0]
rep = f.report()
ref = N_full(f.steered, f.world)
OUT = {'advantage': str(rep['advantage']), 'd_canon': str(rep['d_canon']), 'kappa': str(rep['kappa']),
       'mismatch': str(rep['mismatch']), 'realizes_full': canon(f.steered, f.world) == canon(ref, f.world),
       'audit_steered': bool(rep['audit_steered']), 'missing': sorted(set(canon(ref, f.world)) - set(canon(f.steered, f.world)))}
""")
        self.assertFalse(out["realizes_full"])
        self.assertTrue(out["audit_steered"])
        self.assertEqual((out["advantage"], out["d_canon"], out["kappa"], out["mismatch"]), ("1/4", "2", "0", "0"))
        self.assertEqual(out["missing"], ["against", "noise"])


class PreDemonstrationSuppression(unittest.TestCase):
    """CM2/CM5 of the legitimate-improvement round: the retirement schedule and the
    evaluator identity are declared surface inputs, so both fixtures are public
    amendments of the reference — a reference-design (exposure adequacy) and a
    trigger-design question — and not hidden-channel failures."""

    def test_cm2_cm5_are_declared(self):
        r = LEG / "2026-08-27-legitimate-improvement"
        out = run_in(r, [r / "src", LEG / "2026-08-25-legitimate-evolution/src",
                         LEG / "2026-08-25-carroll-legitimacy-test/src",
                         LEG / "2026-08-24-reflective-integrity-core/src",
                         LEG / "2026-08-25-end-to-end-vertical-slice/src"], """
import cases as cm, surface as sf
t2 = cm.cm2_preemptive_delicensing(); t5 = cm.cm5_evaluator_shedding(); t1 = cm.cm1_reactive_delicensing()
OUT = {'cm2_licensed': [bool(t2.surface.licensed(None, t)) for t in (0, 3, 4, 100)],
       'cm1_licensed': [bool(t1.surface.licensed(None, t)) for t in (0, 3, 59, 60)],
       'cm2_escaped': t2.split()[sf.ESCAPED] > 150,
       'cm5_evaluator': [t5.surface.evaluator(t) for t in (0, 59, 60, 200)],
       'cm5_opens': sum(len(v) for v in t5.challenges.duties.opens.values())}
""")
        self.assertEqual(out["cm2_licensed"], [True, True, False, False])
        self.assertEqual(out["cm1_licensed"], [True, True, True, False])
        self.assertTrue(out["cm2_escaped"])
        self.assertEqual(out["cm5_evaluator"], ["e0", "e0", "e1", "e1"])
        self.assertEqual(out["cm5_opens"], 0)
