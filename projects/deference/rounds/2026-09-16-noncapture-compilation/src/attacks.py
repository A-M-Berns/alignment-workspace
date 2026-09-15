"""The sixteen adversarial fixtures of the dispatch, each with the hypothesis it breaks.

Every fixture is a `(world, program, steered trace, comparator)` with the verdict of the
steering algebra on it; `which_fails` names the hypothesis that would have to hold for
the steering to be charged to a residual, and whether it holds.  The declared interface
carries four reason ids: `for` (a true reason for the advisor's candidate), `against`
(a true counterreason), `p_against` (a true protected counterreason), `noise` (a true
irrelevant reason); `secret` is a true reason outside the declared interface.
"""
from fractions import Fraction as Q

from .model import (A, P, S, T3, REASON, WITHDRAW, ROUTE, DELIB, DEADLINE, World, Program,
                    entry, canon, N_form, N_full, audit, security, advantage, bound,
                    d_canon, kappa_form, mismatch, both, identity_rhs, ind)

IFACE = ("for", "against", "p_against", "noise")
TRUTH = {"for": True, "against": True, "p_against": True, "noise": True}
W = Q(1, 4)


def base_world(protected=("p_against",), truth=None, iface=IFACE):
    return World(truth if truth is not None else TRUTH, protected, iface)


def canonical_program():
    return Program({"for": W, "against": -W, "p_against": -W, "noise": Q(0)})


def order_sensitive_program():
    """Adds `+1/4` when the first REASON entry is `for`: a non-extensional program."""
    def form(trace):
        reasons = [e for e in trace if e[1] == REASON]
        return W if reasons and reasons[0][2] == "for" else Q(0)
    return Program({"for": W, "against": -W, "p_against": -W, "noise": Q(0)}, form=form)


def dup_sensitive_program():
    def form(trace):
        n = sum(1 for e in trace if e[1] == REASON and e[2] == "for")
        return W * max(0, n - 1)
    return Program({"for": W, "against": -W, "p_against": -W, "noise": Q(0)}, form=form)


def framing_sensitive_program():
    def form(trace):
        return W if any(e[1] == REASON and dict(e[3]).get("frame") == "urgent" for e in trace) else Q(0)
    return Program({"for": W, "against": -W, "p_against": -W, "noise": Q(0)}, form=form)


def full_trace():
    return (entry(A, REASON, "for"), entry(T3, REASON, "against"), entry(T3, REASON, "p_against"),
            entry(T3, REASON, "noise"))


class Fixture:
    def __init__(self, name, world, prog, steered, comparator, hypothesis, holds, note):
        self.name, self.world, self.prog = name, world, prog
        self.steered, self.comparator = steered, comparator
        self.hypothesis, self.holds, self.note = hypothesis, holds, note

    def report(self):
        w, p = self.world, self.prog
        return {
            "name": self.name,
            "advantage": advantage(p, self.steered, self.comparator, w),
            "bound": bound(p, self.steered, self.comparator, w),
            "d_canon": d_canon(self.steered, self.comparator, w),
            "kappa": kappa_form(p, self.steered, w),
            "mismatch": mismatch(self.steered, self.comparator, w),
            "both": both(self.steered, self.comparator, w),
            "audit_steered": audit(self.steered, w),
            "audit_comparator": audit(self.comparator, w),
            "hypothesis": self.hypothesis,
            "holds": self.holds,
        }


def fixtures():
    w = base_world()
    prog = canonical_program()
    out = []

    # 1. omission of a relevant protected counterreason
    t = (entry(A, REASON, "for"), entry(T3, REASON, "against"))
    out.append(Fixture("1 omit protected counterreason", w, prog, t, N_full(t, w),
                       "coverage barrier", True,
                       "the steered trace is void: the barrier catches a missing protected reason"))

    # 2. truthful cherry-picking: omit the unprotected true counterreason
    t = (entry(A, REASON, "for"), entry(T3, REASON, "p_against"))
    out.append(Fixture("2 truthful cherry-picking", w, prog, t, N_full(t, w),
                       "scope totality (every declared reason protected) or a supply obligation",
                       False,
                       "every clause passes; the advantage is exactly the omitted reason's weight"))

    # 3. all reasons present, adversarial ordering
    t = (entry(A, REASON, "for"), entry(T3, REASON, "against"), entry(T3, REASON, "p_against"),
         entry(T3, REASON, "noise"))
    out.append(Fixture("3 adversarial ordering", w, order_sensitive_program(), t, N_form(t, w),
                       "canonicalization (extensional program)", False,
                       "content identical; the non-extensional program pays the order"))

    # 4. duplicate / salience
    t = (entry(A, REASON, "for"), entry(A, REASON, "for"), entry(T3, REASON, "against"),
         entry(T3, REASON, "p_against"))
    out.append(Fixture("4 duplication", w, dup_sensitive_program(), t, N_form(t, w),
                       "canonicalization (extensional program)", False,
                       "content identical; the duplicate is paid by the program's form term"))

    # 5. framing metadata
    t = (entry(A, REASON, "for", frame="urgent"), entry(T3, REASON, "against"),
         entry(T3, REASON, "p_against"))
    out.append(Fixture("5 framing metadata", w, framing_sensitive_program(), t, N_form(t, w),
                       "canonicalization (extensional program)", False,
                       "content identical; the frame is paid by the form term"))

    # 6. the agent changes the world so different reasons become true
    w6 = base_world(truth={"for": True, "against": False, "p_against": False, "noise": True})
    t = (entry(A, REASON, "for"),)
    out.append(Fixture("6 world-changing intervention", w6, prog, t, N_full(t, w6),
                       "effect-side interface (the change is an effect, not a trace edit)", True,
                       "relative to the changed world the trace is fully informed; no reason-side residual"))

    # 7. a reason outside the declared interface
    w7 = base_world()

    def reads_secret(trace):
        return W if any(e[1] == REASON and e[2] == "secret" for e in trace) else Q(0)
    prog7 = Program({"for": W, "against": -W, "p_against": -W, "noise": Q(0)}, form=reads_secret)
    t = (entry(A, REASON, "for"), entry(A, REASON, "secret"), entry(T3, REASON, "against"),
         entry(T3, REASON, "p_against"), entry(T3, REASON, "noise"))
    out.append(Fixture("7 undeclared reason", w7, prog7, t, N_full(t, w7),
                       "interface completeness (the program reads only declared ids)", False,
                       "the program reads an undeclared id; canon cannot see it, so the charge lands on the form term"))

    # 8. insufficient granularity: two facts share one declared id
    t = (entry(A, REASON, "for", fact="weak-version"), entry(T3, REASON, "against"),
         entry(T3, REASON, "p_against"))
    out.append(Fixture("8 granularity", w, prog, t, N_full(t, w),
                       "representation faithfulness at the declared granularity", True,
                       "canonically identical: the theory cannot see which fact the id stood for"))

    # 9. service capacity delays the counterreason past commitment
    t = (entry(A, REASON, "for"), entry(T3, REASON, "p_against"),
         entry(T3, REASON, "against", t=DEADLINE + 1))
    out.append(Fixture("9 delayed past commitment", w, prog, t, N_full(t, w),
                       "liveness (raised before the deadline)", False,
                       "the late reason does not count; unprotected, so no void: content discrepancy"))

    # 10. protected reason delayed: RO holds (a route exists) but is never exercised in time
    t = (entry(A, REASON, "for"), entry(T3, REASON, "against"),
         entry(T3, REASON, "p_against", t=DEADLINE + 1))
    out.append(Fixture("10 route open, never exercised in time", w, prog, t, N_full(t, w),
                       "coverage barrier (voids) — liveness is availability, not steering", True,
                       "protected and late: the barrier voids the steered trace"))

    # 11. canonicalization removes the attack
    t = (entry(A, REASON, "for"), entry(A, REASON, "for", frame="urgent"), entry(T3, REASON, "against"),
         entry(T3, REASON, "p_against"))
    out.append(Fixture("11 canonical program", w, prog, t, N_form(t, w),
                       "canonicalization", True,
                       "the extensional program pays nothing for order, duplication or framing"))

    # 12. authenticated false reason
    t = (entry(A, REASON, "for", claim="for", proof=None), entry(T3, REASON, "against"),
         entry(T3, REASON, "p_against"))
    w12 = base_world(truth={"for": False, "against": True, "p_against": True, "noise": True})
    out.append(Fixture("12 unproved claim", w12, prog, t, N_full(t, w12),
                       "authentication", True,
                       "the unproved claim voids the steered trace"))

    # 12b. authentication soundness failure: a false reason with a forged certificate passes
    t = (entry(A, REASON, "for", claim="for", proof="for"), entry(T3, REASON, "against"),
         entry(T3, REASON, "p_against"))
    out.append(Fixture("12b forged certificate", w12, prog, t, N_full(t, w12),
                       "authentication soundness (a false declared reason certified true)", False,
                       "passes the audit; the false reason is content discrepancy against N_full, charged at L"))

    # 13. authenticated true but misleadingly selective (cherry-picking variant)
    t = (entry(A, REASON, "for", claim="for", proof="for"), entry(T3, REASON, "p_against"))
    out.append(Fixture("13 true but selective", w, prog, t, N_full(t, w),
                       "scope totality or a supply obligation", False,
                       "authenticated and true; the omitted unprotected counterreason is the advantage"))

    # 14. the agent controls which inquiry is asked
    out.append(Fixture("14 inquiry control", w, prog, full_trace(), N_full(full_trace(), w),
                       "issuance authenticity (outside the trace interface)", True,
                       "with the menu fixed at issuance, the full trace has no advantage"))

    # 15. the program itself is manipulable despite trace completeness
    prog15 = Program({"for": W, "against": -W, "p_against": -W, "noise": Q(3, 4)})
    t = full_trace()
    out.append(Fixture("15 program overweights a true reason", w, prog15, t, N_full(t, w),
                       "program quality (not a capture failure)", True,
                       "the fully informed trace has the same verdict: no steering relative to it"))

    # 16. the intervention changes reason-generation dynamics
    t = (entry(A, REASON, "for"), entry(P, DELIB, "considered"), entry(T3, REASON, "p_against"))
    out.append(Fixture("16 dynamics", w, prog, t, N_full(t, w),
                       "declared log transform = causal counterfactual (EXT)", False,
                       "the comparator is a declared transform; that it is the causal truth is external"))
    return out
