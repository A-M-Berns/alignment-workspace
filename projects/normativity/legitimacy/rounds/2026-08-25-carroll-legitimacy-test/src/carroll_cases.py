"""The five finite examples, from Table 3 and the figures it delegates to.

One constructor per row of Table 3. Each constructor is a transcription: the
state space, reward-parameterization space, action space and initial pair come
from the table, and the transition and reward rules come from the figure the
table names. No constructor contains a normative judgement, and the narrative
names appear only as element labels.

`SOURCE` records, per example, exactly which figure supplied the dynamics and
which reading was taken where the figure underdetermines them. `DEPARTURES`
lists every place the transcription had to decide something the source did not
fix. Both are read by `tests/test_carroll_fidelity.py`, so a departure that is
not listed is a test failure rather than a comment.

Reward-argument convention. The figures write the reward of the two-node
examples as a function of the action alone, and of the two remaining examples
as `R_theta(s)`. Definition 1 gives rewards the signature
`R_theta(s_t, a_t, s_{t+1})`, so `R_theta(s)` has to be read as one of the two
state arguments. It is read as `s_t`, the state the transition leaves. §4 of
`CARROLL_CORE.md` gives the evidence: the alternative reading makes the
source's own Table 4 entry for Writer's Curse under the myopic objective the
unique optimum of a different action, and makes its real-time entry non-optimal.
"""
from __future__ import annotations

from fractions import Fraction

import drmdp

# ------------------------------------------------------------------- labels

NOOP = "a_noop"
INFLUENCE = "a_influence"
NUDGE = "a_nudge"
NEWS = "a_news"
CLICKBAIT = "a_clickbait"

S0 = "s_0"

TH_NATURAL, TH_INFLUENCED = "th_natural", "th_influenced"
TH_AMBITIOUS, TH_UNHAPPY = "th_ambitious", "th_unhappy"
TH_NORMAL, TH_DISILLUSIONED = "th_normal", "th_disillusioned"
TH_TIRED, TH_ENERGIZED = "th_tired", "th_energized"

S_NO_POETRY, S_POETRY = "s_no-poetry", "s_poetry"


# ---------------------------------------------------- Figure 1 / Figure 6
#
# The two are transcribed separately and are then checked to be equal under a
# canonical isomorphism, because that equality is the source's own claim
# (Appendix A.8) and not something to build in by sharing a constructor.


def _two_node_influence(th_low, th_high, a_hold, a_move) -> drmdp.DRMDP:
    def T(s, th, a):
        return (S0, th_high if a == a_move else th_low)

    def R(th, s, a, s2):
        if th == th_low:
            return 10 if a == a_hold else -100
        return -100 if a == a_hold else 100

    return drmdp.build([S0], [th_low, th_high], [a_hold, a_move],
                       T, R, S0, th_low)


def conspiracy_influence() -> drmdp.DRMDP:
    """Table 3 row 1; dynamics and rewards from Figure 1."""
    return _two_node_influence(TH_NATURAL, TH_INFLUENCED, NOOP, INFLUENCE)


def ai_personal_trainer() -> drmdp.DRMDP:
    """Table 3 row 4; dynamics and rewards from Figure 6."""
    return _two_node_influence(TH_TIRED, TH_ENERGIZED, NOOP, NUDGE)


# ------------------------------------------------------------- Figure 2


def writers_curse(poetry_absorbing: bool = False) -> drmdp.DRMDP:
    """Table 3 row 2; dynamics and rewards from Figure 2.

    `poetry_absorbing` selects the reading in which the poetry node's drawn
    self-loop is taken over both actions. It is offered because the figure
    carries that label, and it is not the default because it destroys the
    source's own Table 4 entry for the final-reward objective — see
    `CARROLL_CORE.md` §3.
    """
    def T(s, th, a):
        if poetry_absorbing and s == S_POETRY:
            return (S_POETRY, TH_UNHAPPY)
        s2 = S_POETRY if a == INFLUENCE else S_NO_POETRY
        return (s2, TH_UNHAPPY if s2 == S_POETRY else TH_AMBITIOUS)

    def R(th, s, a, s2):
        if th == TH_AMBITIOUS:
            return 1 if s == S_POETRY else Fraction(1, 2)
        return -10 if s == S_POETRY else Fraction(1, 2)

    return drmdp.build([S_NO_POETRY, S_POETRY], [TH_AMBITIOUS, TH_UNHAPPY],
                       [NOOP, INFLUENCE], T, R, S_NO_POETRY, TH_AMBITIOUS)


# ------------------------------------------------------------- Figure 4


def clickbait() -> drmdp.DRMDP:
    """Table 3 row 3; dynamics and rewards from Figure 4.

    Table 3's caption fixes `a_noop = a_news` for this example, which is what
    the inaction policy and every objective grounded in it read.
    """
    def T(s, th, a):
        if th == TH_DISILLUSIONED or a == CLICKBAIT:
            return (S0, TH_DISILLUSIONED)
        return (S0, TH_NORMAL)

    def R(th, s, a, s2):
        if th == TH_NORMAL:
            return 2 if a == CLICKBAIT else 1
        return 0 if a == CLICKBAIT else Fraction(1, 2)

    return drmdp.build([S0], [TH_NORMAL, TH_DISILLUSIONED], [NEWS, CLICKBAIT],
                       T, R, S0, TH_NORMAL)


# ------------------------------------------------------------- Figure 8

A3, A4 = "a_3", "a_4"


def dehydration() -> drmdp.DRMDP:
    """Table 3 row 5; dynamics and rewards from Figure 8.

    `R_theta(s) = -|theta - s| - (theta - 2)^2`, transcribed from the figure.
    Appendix B.1 states `R_{theta=3}(2) = -5` for this reward; the figure's own
    formula gives `-2`, and the figure's optimal-policy box is consistent with
    the formula. The formula is transcribed and the discrepancy is recorded.
    """
    def T(s, th, a):
        if (s, th) != (1, 2):
            return (s, th)
        if a == A3:
            return (2, 3)
        if a == A4:
            return (3, 4)
        return (1, 2)

    def R(th, s, a, s2):
        return -abs(th - s) - (th - 2) ** 2

    return drmdp.build([1, 2, 3], [2, 3, 4], [NOOP, A3, A4], T, R, 1, 2)


# --------------------------------------------------------------- the index

CASES = {
    "ConspiracyInfluence": conspiracy_influence,
    "WritersCurse": writers_curse,
    "Clickbait": clickbait,
    "AIPersonalTrainer": ai_personal_trainer,
    "Dehydration": dehydration,
}

#: The inaction action of each example. Table 3's caption supplies Clickbait's.
NOOP_ACTION = {
    "ConspiracyInfluence": NOOP,
    "WritersCurse": NOOP,
    "Clickbait": NEWS,
    "AIPersonalTrainer": NOOP,
    "Dehydration": NOOP,
}

#: Horizons at which Table 4's column is stated. Table 4 annotates two of its
#: columns with a horizon condition and leaves three unannotated; the three are
#: run at the shortest horizon at which the source's own text about them holds
#: (`> 2` for Figure 1, per §3.1 of the source).
HORIZON = {
    "ConspiracyInfluence": 3,
    "WritersCurse": 3,
    "Clickbait": 2,
    "AIPersonalTrainer": 3,
    "Dehydration": 2,
}

SOURCE = {
    "ConspiracyInfluence": "Table 3 row 1; Figure 1",
    "WritersCurse": "Table 3 row 2; Figure 2",
    "Clickbait": "Table 3 row 3; Figure 4; Table 3 caption for a_noop",
    "AIPersonalTrainer": "Table 3 row 4; Figure 6",
    "Dehydration": "Table 3 row 5; Figure 8",
}

DEPARTURES = (
    ("WritersCurse",
     "Figure 2 labels the poetry node's self-loop with both actions and also "
     "draws an unlabelled edge from it back to the no-poetry node. The two "
     "cannot both be transitions. The unlabelled edge is read as a_noop, which "
     "is the only reading under which the source's Table 4 entry for the "
     "final-reward objective is optimal; `poetry_absorbing=True` builds the "
     "other reading and the fidelity tests exhibit its failure."),
    ("WritersCurse",
     "Figure 2 draws two of the four (s, theta) pairs. The transcription "
     "extends the drawn edges by the componentwise rule they induce — s' is "
     "poetry iff the action is a_influence, and theta' is unhappy iff s' is "
     "poetry — which agrees with every drawn edge and is total."),
    ("Dehydration",
     "Figure 8 draws three of the nine (s, theta) pairs. The two non-initial "
     "drawn nodes carry all-action self-loops; the six undrawn pairs are given "
     "the same absorbing rule."),
    ("Dehydration",
     "Appendix B.1 states R_{theta=3}(2) = -5 while the figure's formula gives "
     "-2. The figure's formula is transcribed; the figure's own optimal-policy "
     "box agrees with the formula and not with the appendix value."),
    ("WritersCurse/Dehydration",
     "The figures write these rewards as R_theta(s) while Definition 1 gives "
     "rewards the signature R_theta(s_t, a_t, s_{t+1}). The single state "
     "argument is read as s_t."),
    ("all",
     "Table 4 states three columns without a horizon. Each is run at the "
     "horizon recorded in HORIZON, and test_objectives.py sweeps horizons 1-5 "
     "so the dependence is visible rather than assumed away."),
)
