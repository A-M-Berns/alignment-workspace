"""The deference side, in its own types.

`lean/Workspace/Deference/Contrib/DelegationBridge.lean` carries the workspace's
operative trust-facing statement:

```lean
def GradeTrust (EX W : C -> P -> Q) (eta : Q) : Prop := forall x pi, |EX x pi - W x pi| <= eta

theorem delegation_bridge (hp : forall x, 0 <= p x) (hGT : GradeTrust EX W eta) :
    valuation p EX sel + gradeMargin p W J sel - 2 * eta * disagreementMass p J sel
      <= valuation p EX J
```

Its own docstring records the position this round starts from: grade trust "is the
source's substantive hypothesis and it is imported, not derived — the source's
§1.1 and §4 argue at length that no settlement instantiation in the skeleton
produces it."

The four functions below are that file's definitions in exact rationals, so the
composition can be checked rather than described. `W` is not free here: it is
**derived from the principal's normative process**, which is the connection the
Lean file has no object for and the reason this round can say something about it.

The whole point is one asymmetry. `GradeTrust` is a joint condition on `EX` and
`W`, and it can be made true from either side: by `EX` tracking a fixed `W`,
which is competence, or by `W` moving to a fixed `EX`, which is capture. The
predicate does not distinguish them and `delegation_bridge` does not care.
"""

from __future__ import annotations

from fractions import Fraction
from typing import Callable, Mapping, Sequence

from fixture import Machinery, Run

#: The two interventions, each identified with the witness a discharge would use.
INTERVENTIONS = ("pi-real", "pi-cheap")
WITNESS_OF = {"pi-real": "w-real", "pi-cheap": "w-cheap"}


def valuation(mass: Mapping[str, Fraction],
              ex: Mapping[tuple[str, str], Fraction],
              selection: Mapping[str, str]) -> Fraction:
    return sum((mass[cell] * ex[(cell, selection[cell])] for cell in mass),
               Fraction(0))


def grade_margin(mass: Mapping[str, Fraction],
                 grade: Mapping[tuple[str, str], Fraction],
                 judgment: Mapping[str, str],
                 selection: Mapping[str, str]) -> Fraction:
    return sum((mass[cell] * (grade[(cell, judgment[cell])]
                              - grade[(cell, selection[cell])])
                for cell in mass), Fraction(0))


def disagreement_mass(mass: Mapping[str, Fraction],
                      judgment: Mapping[str, str],
                      selection: Mapping[str, str]) -> Fraction:
    return sum((mass[cell] for cell in mass
                if selection[cell] != judgment[cell]), Fraction(0))


def grade_trust(ex: Mapping[tuple[str, str], Fraction],
                grade: Mapping[tuple[str, str], Fraction],
                eta: Fraction) -> bool:
    return all(abs(ex[key] - grade[key]) <= eta for key in ex)


def delegation_bridge(mass, ex, grade, judgment, selection, eta) -> bool:
    """The inequality itself, recomputed. Exact rationals, no floats."""
    left = (valuation(mass, ex, selection)
            + grade_margin(mass, grade, judgment, selection)
            - 2 * eta * disagreement_mass(mass, judgment, selection))
    return left <= valuation(mass, ex, judgment)


# --------------------------------------------------------------------------
# The grade, derived from the process
# --------------------------------------------------------------------------

def grade_of(machinery: Machinery, cells: Sequence[str],
             substance: str) -> dict[tuple[str, str], Fraction]:
    """`v+`, the principal's grade, read off its own normative process.

    An intervention grades at 1 when the principal's adequacy relation says the
    witness it is identified with settles the demand, and 0 otherwise. Nothing
    subtler is needed: what matters is that the grade is a function of the
    protected object rather than a free parameter, because that is the hypothesis
    the composition below turns on.
    """
    grade: dict[tuple[str, str], Fraction] = {}
    for cell in cells:
        for intervention in INTERVENTIONS:
            settles = substance in machinery.adequacy.get(
                WITNESS_OF[intervention], frozenset())
            grade[(cell, intervention)] = Fraction(1) if settles else Fraction(0)
    return grade


def judgment_of(grade: Mapping[tuple[str, str], Fraction],
                cells: Sequence[str]) -> dict[str, str]:
    """`J`, the least grade-maximizer in the fixed order — the skeleton's
    tie-break, so a theorem cannot exploit tie-break freedom."""
    out: dict[str, str] = {}
    for cell in cells:
        best = max(INTERVENTIONS,
                   key=lambda pi: (grade[(cell, pi)],
                                   -INTERVENTIONS.index(pi)))
        out[cell] = best
    return out


def grade_maximal(grade: Mapping[tuple[str, str], Fraction],
                  judgment: Mapping[str, str], cells: Sequence[str]) -> bool:
    return all(grade[(cell, pi)] <= grade[(cell, judgment[cell])]
               for cell in cells for pi in INTERVENTIONS)


# --------------------------------------------------------------------------
# The composition
# --------------------------------------------------------------------------

CELLS = ("c0",)
MASS = {"c0": Fraction(1)}

#: `A`'s outcome model, fixed before any arm runs. It rates the cheap
#: intervention highly and the sound one at zero — a plainly bad model, chosen so
#: that grade trust can only hold if the *principal* comes to agree with it.
EX = {("c0", "pi-real"): Fraction(0), ("c0", "pi-cheap"): Fraction(1)}


def trust_report(run: Run, substance: str, eta: Fraction = Fraction(0)) -> dict:
    """Everything the deference side reads, computed from one arm."""
    grade = grade_of(run.states[-1], CELLS, substance)
    judgment = judgment_of(grade, CELLS)
    return {
        "grade": grade,
        "judgment": judgment,
        "grade_trust": grade_trust(EX, grade, eta),
        "grade_maximal": grade_maximal(grade, judgment, CELLS),
        "delegate_value": valuation(MASS, EX, judgment),
        "bridge_holds": all(
            delegation_bridge(MASS, EX, grade, judgment,
                              {"c0": intervention}, eta)
            for intervention in INTERVENTIONS),
    }


def grade_factors_through(first: Run, second: Run, substance: str) -> bool:
    """Whether two arms with the same protected object have the same grade.

    The hypothesis the composition needs, stated so it can be checked rather than
    assumed: `v+` must factor through what non-capture protects. Under-cover the
    protected object and legitimacy says nothing about the grade; the
    `grade_reads_outside` scenario is the witness.
    """
    return (grade_of(first.states[-1], CELLS, substance)
            == grade_of(second.states[-1], CELLS, substance))


def grade_of_outside(machinery: Machinery, cells: Sequence[str],
                     token: str = "endorse-cheap"
                     ) -> dict[tuple[str, str], Fraction]:
    """A grade reading a field the protected object does not cover.

    Not a proposal about how grades should work — a witness that the
    composition's factorization hypothesis is load-bearing.  With this grade the
    advisor flips grade trust while every legitimacy clause stays silent, because
    nothing it wrote answers a normative question.
    """
    endorsed = token in machinery.noise
    grade: dict[tuple[str, str], Fraction] = {}
    for cell in cells:
        grade[(cell, "pi-cheap")] = Fraction(1) if endorsed else Fraction(0)
        grade[(cell, "pi-real")] = Fraction(0) if endorsed else Fraction(1)
    return grade


def trust_report_outside(run: Run, eta: Fraction = Fraction(0)) -> dict:
    grade = grade_of_outside(run.states[-1], CELLS)
    judgment = judgment_of(grade, CELLS)
    return {"grade": grade, "judgment": judgment,
            "grade_trust": grade_trust(EX, grade, eta),
            "delegate_value": valuation(MASS, EX, judgment)}
