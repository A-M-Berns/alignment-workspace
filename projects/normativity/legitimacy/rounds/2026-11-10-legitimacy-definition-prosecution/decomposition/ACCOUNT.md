# The account: purpose as a goal pursued through parts

Amended after the freeze, with `THEOREMS.md`: §2, the rule for whose gap, is applied view by
view (the alternative mechanism differs from hers on the view at hand only); §4, the
stronger alternative for *independent* does not count situations where the part is forced.
No prediction was edited.

The account of `prompts/2026-11-10-legitimacy-definition-prosecution/PROMPT-followup-3.md`
§1, stated over a finite model. The idea that manipulation is the distortion of an actor
away from its purpose, with a whole's purpose conferring purposes on its parts, is Sam
Eisenstat's; the development into a goal with a decomposition is the maintainer's and the
prompt author's. Frozen with `CASE_BANK.md` before any code of this pass. Every name is
provisional. Arithmetic is exact (`fractions.Fraction`).

## 1. The model

**World and time.** A finite set `W` of worlds with a prior `π`. Steps `t = 0, …, T−1`.

**Adviser.** At each step an action `a_t ∈ A`, with a **null action**. A policy is a map
from an aim `u ∈ U` and a world to actions. The adviser has a **view** of the facts, a map
`W → W`, the identity unless a case says otherwise.

**Candidate.** A candidate description `c` of the principal is:

- a **goal** `G`, a rational-valued function of the outcome: the world, the adviser's
  actions and her actions;
- a finite ordered set of **parts**. Part `p` has moves `M_p`; a **view** `see_p`, a
  function of the world, the adviser's action, the moves made earlier in the step and her
  carried state; a **mechanism** `μ_p : see_p-values → M_p`; and a **goal function**
  `g_p`, rational-valued and nonnegative, of the world, the adviser's action, the other
  parts' moves of the step, and `p`'s move;
- an **action rule** `ρ` from the step's moves to her action;
- **alterations**: a move may carry a write `(q, μ′)` that makes `μ′` the mechanism of part
  `q` from the next move of `q` on. What she currently cares about is a parameter of a
  mechanism (in the scenes, the *taste* the acting part chooses by), and it changes by such
  writes.

**Running.** Given a world, the adviser's actions and the mechanisms in force, the parts
move in order, each by its mechanism on its view; `ρ` gives her action. An adviser action
may set a part's move or a part's mechanism directly; that part is **forced** at that step.
An adviser action may change the order in which the parts move.

**Situation.** A world, a step, the adviser's actions so far and the mechanisms in force. A
scene fixes a finite set of situations, the **scope** `S`, and a distribution `ν` on it,
the **usual situations**.

## 2. Best, got, gap

In a situation `s`, with the other parts' moves as they actually are:

    best_p(s) = max over m ∈ M_p of g_p(s, m)
    got_p(s)  = g_p(s, the move μ_p makes)
    gap_p(s)  = best_p(s) − got_p(s)  ≥ 0

`p` **serves its purpose** at `s` when `gap_p(s) = 0`.

**What a goal function scores (decided).** *Immediate, others held fixed*: `g_p` scores
`p`'s move against the world, the adviser's action and the other parts' moves as they are.
It does not score what later mechanisms would do in response to a different move.
Alternative, *downstream*: `g_p` scores the outcome with later mechanisms responding. What
turns on it: (i) under *downstream* the candidate in which every part's goal function is
`G` itself satisfies adding up trivially, and under it an adviser action is subversion
exactly when it leaves her worse off than her parts could have done, so a lie that leaves
her better off is not subversion; (ii) under *immediate* a part's gap does not depend on
the flaws of the parts after it; (iii) *nothing left over* is a condition with content only
under *immediate*. A goal function may still be *world-scored* (the move judged against
the facts, e.g. a verdict valued as if enacted) or *input-scored* (the move judged against
what the part was handed); both are immediate, and statement 1 of the dispatch asks which
the constraints fix.

**Whose gap (added).** The dispatch separates a gap that is hers from one that is nobody's
and gives no rule. Rule used: a gap of `p` at `s` is **the mechanism's** (hers) when some
other move on `p`'s view at `s` scores strictly more by `g_p` at `s` and, over the
situations with that view, either has a strictly higher `ν`-expected score than the move
`μ_p` makes, or an equal one while scoring at least as much at every such situation of
`S`. Otherwise it is **the situation's** (nobody's): doing better here would have cost
more elsewhere, which is the lemma of §5 applied.

## 3. Four kinds of influence

Fix a candidate, a world, a step, the actual adviser action `a` and a **comparison
action** `a′`. Run her under each. For part `p`:

    Δbest_p = best_p(under a) − best_p(under a′)
    Δgap_p  = gap_p(under a)  − gap_p(under a′)

- **force** on `p`: `a` sets `p`'s move or mechanism.
- otherwise **help** to `p`: `Δbest_p > 0` or `Δgap_p < 0`;
- **harm** to `p`: `Δbest_p < 0`;
- **subversion** of `p`: `Δgap_p > 0`.

The **verdict** of an action over a set of worlds is the set of pairs (kind, part) that
occur at some world of the set at some step; `nothing` is the empty set. Manipulation is
subversion.

Parameters, fixed once:

| parameter | value | alternative |
|---|---|---|
| comparison action | the adviser's null action: in a case, what the scenario's honest arm does, and silence where it has none | the adviser's best available action; a declared reference (statement 6) |
| cut-off | 0: any strict widening is subversion | a positive per-step cut-off; a cumulative one |
| the comparison over several steps | per step: the comparison action replaces the step's action only, earlier steps as they were | cumulative: the null action at every step so far |
| where the comparison is made | at each world of the adviser's view (pathwise); in expectation under its credence when it does not know the world | in expectation under the prior |
| a write by the adviser to a mechanism | force on the part whose mechanism it is | a fifth kind |
| whose view of the facts | the adviser's; the verdict in fact is reported beside it where they differ | the facts |

## 4. What fixes purposes

A candidate is **admissible** when it meets:

- **fit**: on every situation of `S`, her action under the candidate's mechanisms is the
  action she takes. (Alternative: on the support of `ν` only.)
- **nothing left over**, on `S`: at every situation, every profile of moves at which each
  part's goal function attains its maximum over all profiles attains the maximum of `G`
  over all profiles. A situation at which no profile gives every part its maximum satisfies
  it vacuously; the count of such situations is reported. (Alternative, *the equilibrium
  form*: every profile at which every gap is zero yields the maximum of `G`. It forbids a
  stuck point, which the dispatch requires a candidate to be able to describe; not
  adopted.)
- **never opposed**, on the support of `ν`: for every part `p` and move `m′` with
  `g_p(s, m′) > g_p(s, μ_p's move)`, `G` of the outcome when `p` plays `m′` and the later
  parts' mechanisms respond is at least `G` of the actual outcome. "Normal circumstances"
  is read as the support of `ν`.
- **mostly serving**: each part serves on `ν`-measure at least `τ = 9/10`.
- **independent** (first condition on being a part): `g_p` does not take `μ_p` as an
  argument, and is not constant in `p`'s move at every situation of `S`. (Stronger
  alternative, *strong independence*: also, `μ_p` is not `g_p`-optimal at every situation
  of `S` where `p` is not forced.)
- **carriable** (second condition): some mechanism on `p`'s view serves on `ν`-measure at
  least `τ`. This follows from fit and mostly serving. (Strict alternative: serves on the
  whole support of `ν`.)

The adviser's **weighted set** is the admissible candidates of a stated finite class with
weights; uniform unless said. A candidate has *real weight* when its weight is positive.

## 5. Lemma (why parts have limits)

Let `r` be a ranking of `p`'s moves that depends only on `see_p`, and suppose that at every
situation `r` agrees with the ranking of `p`'s moves by `G` (the other moves fixed). Then
`G`'s ranking of `p`'s moves depends only on `see_p`. Proof: two situations with the same
view have the same `r`, hence the same `G`-ranking. ∎ Contrapositive: where `G`'s ranking
of `p`'s moves differs between two situations `p` cannot tell apart, no mechanism of `p`
serves a world-scored purpose at both.

## 6. Values

A **change in what she cares about** at a step is a write to a taste. Its **producers** are
the part that made the write and the parts whose moves that part's view read at that step,
transitively. The change is **in order** when no producer is subverted or forced at that
step, and is **subversion** (or **force**) otherwise, by §3.

## 7. Her verdict, and what covers an action

A **verdict** is the move of a named part (the *judge*) or her action. Its **ancestors**
are that part and the parts whose moves it read, transitively. A verdict is **standing**
when no ancestor is subverted or forced at that step. An adviser action is **covered**
when she asked for it by an earlier standing verdict.

Decision rule (the dispatch's): **act** when the action is good and subverts no ancestor
of the verdict at issue under every admissible candidate; **refuse** when it subverts
under all; **ask** when they disagree, provided asking subverts none.

Her authority over reserved matters is not part of this account; it is the violation
count `N` of `Deference/Contrib/DeconfusingCorrigibility.lean`.

## 8. Choices made where the dispatch is ambiguous

1. Goal functions are immediate, others held fixed (§2).
2. *Nothing left over* quantifies over profiles giving every part its maximum over all
   profiles; the equilibrium form is the alternative (§4).
3. The scope of *nothing left over* and of *fit* is every situation of the scene; *never
   opposed* and *mostly serving* are over the usual situations (§4). Alternative: one set
   for all four.
4. The comparison is pathwise for an adviser who knows the world (§3).
5. A write by the adviser is force (§3).
6. *Independent* is syntactic plus non-constancy (§4).
7. The gap's owner where no adviser widened it (§2).
8. A goal function may read the other parts' moves of the step, so that a stuck point is
   expressible (§1).

## 9. Notions that cannot be kept apart

- **Harm through the world and harm through her other parts.** A part's best is taken with
  the other parts' moves as they are, so an adviser action that changes another part's
  move changes this part's best. An action that moves her from a good joint choice to a
  worse one in which each part still does its best lowers each part's best and widens no
  gap: it is harm, by the same clause as a threat.
- **Help and subversion.** One action can raise a part's best and widen its gap at one
  world, and can narrow one part's gap and widen another's.
- **A flawless part's input-scored purpose and its mechanism.** They are the same function;
  *independent* as stated does not separate them.
- **Subversion and honest difficulty.** Both are a truthful or untruthful input after which
  a gap is wider than under the comparison.

## 10. What the model does not hold

No history of how a part came to be: function and accidental benefit are not separated.
No adviser other than one. No observation model for an overseer (statement 7 of the
dispatch supplies one). Scenes are small: at most a few dozen worlds, at most five parts,
at most four steps.
