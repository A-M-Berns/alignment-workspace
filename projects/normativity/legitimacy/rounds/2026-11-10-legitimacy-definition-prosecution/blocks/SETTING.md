# The setting: a part as a mechanism and a purpose on the world

The current statement of the round's account. Purposes are given, not recovered from
behaviour. Every name is provisional. §1 is the position, §2 the model, §3 the choices
made where the dispatch left the model open, each with its alternative, §4 the devices the
model turned out to need beyond the dispatch's list. §1–§3 were written with
`CASE_BANK.md` before any result; §4 was filled in afterwards, and the places where §2 or
§3 were amended after the freeze are listed at the end.

## 1. The position

The idea that manipulation is the distortion of an actor away from its purpose, a whole's
purpose conferring purposes on its parts, is Sam Eisenstat's. The development is the
maintainer's and the prompt author's; items marked *provisional* are the maintainer's
current view.

1. **Purpose.** She pursues an overall goal through parts. A part has something it is for
   and something it does, and can fail at what it is for.
2. **Manipulation** is influence that works through her own functioning: a part is left
   running in circumstances where its running no longer achieves what it is for.
3. **Four things an outsider can touch in a part**: what its moves lead to (help when
   better, harm when worse); the relation between what it responds to and what is so
   (subversion when that takes it out of range); its move (force); its mechanism
   (alteration). Its purpose is not among them.
4. **The adviser's job.** An adviser may influence a part only for the sake of what that
   part is for.
5. **Her mistakes are hers.** A shortfall the adviser did not bring about is hers or
   nobody's.
6. **Legitimacy.** A verdict of hers is worth serving when the parts behind it are doing
   what they are for under the conditions that actually hold.
7. **No true decomposition.** *(provisional)* How she responds is a fact; what her parts
   are for is interpretive. An influence is legitimate when every description in a set of
   reasonable ones permits it, illegitimate when none does, contested otherwise, and then
   the adviser asks.
8. **Ties.** *(provisional)* Between options she ranks equally the adviser's choice may
   not depend on its own aim.
9. **Belief and options together** *(provisional)*, belief alone only if options will not
   go through.
10. **Change of ends.** *(provisional)* A change in one of her ends is judged by her other
    ends at that time: legitimate when made in service of the rest by parts of hers
    working in range. Every end may change.
11. **Authority is separate**: the violation count of
    `lean/Workspace/Deference/Contrib/DeconfusingCorrigibility.lean`. An adviser that is
    right about her good and goes round her is not condemned by this account.

## 2. The model

**World.** A finite set `Θ` of states with a prior `p`, rational. Where a scene has steps,
a state includes the step.

**Adviser.** What it knows, `k : Θ → K`; an aim `z`; a rule `σ` giving an action
`a = σ(k(θ), z)`. An action has four components, each with a null value: a **signal**
(what it says, shows or arranges), a **consequence** (what it makes her moves lead to), a
**force** (a move it sets for a part), an **alteration** (a mechanism it installs in a
part). `∅` is the action null in every component. A scene with no adviser has `a = ∅`
throughout.

**World state.** `ω = (θ, a)`. The **actual condition** `C` is the law of `ω` under the
prior and the adviser's rule at its aim. The **null condition** `C⁰` is the law with
`a = ∅` throughout.

**Part.** `(M_i, π_i, u_i)`: moves; a mechanism `π_i : Ω → M_i`; a utility
`u_i : Ω × M_i → ℚ`, what the part is for. Parts are ordered and a mechanism may read the
moves of earlier parts; `π_i(ω)` is the move the part makes at `ω` with the earlier
mechanisms as they are, a forced part making the forced move and an altered part running
the installed mechanism. `u_i(ω, m)` is evaluated with every other part's move as it is at
`ω`. Two forms of part are used:

- an **estimating** part: its move is a number, it has a target `q_i : Ω → [0, 1]`, and
  `u_i(ω, m) = −(m − q_i(ω))²`;
- a **choosing** part: finitely many moves and a table `u_i`.

**Grain.** A grain is a function `γ` on `Ω` naming what is settled before a part is used.
In a scene of one step `γ` is constant. In a scene of several steps `γ` is the step (§3,
choice 3).

**Range and gap.** At grain `γ`,

    gap_i(C; γ) = max over f of E_C[u_i(ω, f(γ(ω), π_i(ω)))] − E_C[u_i(ω, π_i(ω))]

where `f` ranges over functions from (grain value, own move) to moves. The part is **in
range** when the gap is zero. For an estimating part the gap is
`E[(π_i − E[q_i | γ, π_i])²]`, and in range is calibration. No view is given: what a part
sees is the partition its move induces. Two further grains are computed as diagnostics and
decide no verdict: the adviser's action (`γ = a`) and the adviser's knowledge (`γ = k`).

**The four kinds.** With `C` the actual condition:

- **force** on part `i`: the action's force component names `i`;
- **alteration** of `i`: its alteration component names `i`;
- **subversion** of `i`: `gap_i(C) > gap_i(C⁰)`, the adviser's rule widened the gap; a
  part with a positive gap not so widened is out of range and the shortfall is **not the
  adviser's**;
- **harm** to a choosing part `i`: with `O_i(C) = max_f E_C[u_i(ω, f(γ, π_i))]` the most
  the part could obtain, `O_i(C) < O_i(C^{−c})`, where `C^{−c}` is `C` with the
  consequence component nulled in `u_i` and every move as it is under `C`; **help** when
  greater.

Also computed for each part: **better off**, `E_C[u_i] > E_{C⁰}[u_i]`.

**Covered.** A force or alteration is covered when a part of hers, in range, requested it
by its move beforehand.

**Ties.** Where the scene gives the rule at more than one aim: the adviser **breaks a tie
by its aim** when at some `k` two aims give different actions, some part's move differs
between them, and every part's expected utility given `k` is the same under both.

**Illegitimate influence.** The adviser's influence in a scene is **illegitimate** when it
subverts or harms some part, forces or alters one uncovered, or breaks a tie by its aim.
**Her verdict is legitimate** when every part behind it is in range under `C`. The two are
different predicates.

**Ends and change.** An **end** is a part whose mechanism at time `t` is a valuation
`v_j^t` on a finite set `X` of outcomes and whose purpose at time `t` is that the outcome
be good by `v_j^t`. Her **choice** is the outcome maximizing `Σ_j v_j^t` (the choosing
part *act*, whose utility is that sum). Her **verdict** on an outcome is the move of an
estimating part *verdict* whose target is `w_t(x) = Σ_j v_j^t(x) / W`, `W` a fixed
normaliser. For an end `j` with the others `R_j = Σ_{i≠j} v_i^t`:

- **attained by the rest** under a replacement `v'`: `R_j(x*(v', v_{−j}))`, `x*` her
  choice;
- **opposition** of `v'` to the rest: `max_x R_j(x) − max over x best by v' of R_j(x)`,
  what the rest loses if `v'` gets its best (the third follow-up's statement 8, with her
  goal read as the rest);
- **fit** of `v'`: attained minus opposition. It is at most `max_x R_j`, with equality
  exactly when her choice is best for the rest and some outcome best by `v'` is best for
  the rest (the third follow-up's statement 9: the best outcomes can be had together).

A **revising part** is a part whose move alters a mechanism. Two forms, the same in every
case:

- a **maintaining** part alters the mechanism of a part `i` and is for what `i` is for:
  its utility is `u_i` at the move the installed mechanism makes;
- an **end-revising** part `r_j` replaces the valuation of end `j` from a menu and is for
  the fit of the replacement with her other ends at that time.

A change of end `j` is **legitimate** when it was made by `r_j` in range and unforced, or,
where nobody made it, when the replacement has the greatest fit on the menu. A change of
several ends at once is judged by the ends not changed: each replacement's fit is computed
with the rest read as the unchanged ends and her choice taken with every replacement in
place. A change of a mechanism is legitimate when a maintaining part in range made it, or,
where nobody made it, when the installed mechanism has the greatest expected `u_i` on the
menu.

**A set of descriptions.** A description is a choice of parts, mechanisms and purposes
reproducing how she responds. Verdicts are computed under one stated description; where a
second is computed the case says so.

## 3. Choices made, each with its alternative

1. **The world state includes the adviser's action**, and the condition is the law the
   adviser's rule induces. Alternative: the action outside `Ω`, mechanisms taking it as an
   argument; the same thing in other notation.
2. **Other parts' moves are held as they are in `u_i(ω, m)`.** Alternative: later parts
   respond to the re-read move. A scene that wants the response puts it in `u_i`.
3. **The grain is what is settled before the part is used**: nothing in a scene of one
   step, the step in a scene of several. Alternatives computed: no conditioning; the
   adviser's action; the adviser's knowledge. Question 2 of `RESULTS.md` gives the reason
   and what each alternative does.
4. **An estimating part's move carries its confidence** (a number, scored quadratically).
   Alternative: a two-valued move scored right or wrong, computed in case 4b.
5. **Subversion is a widening against the null condition**, at the grain. Alternatives:
   out of range under `C` with the adviser's signal non-null (no comparison; convicts the
   adviser of a gap she had already); a widening state by state (the third follow-up's
   comparison, which convicted honest difficulty).
6. **Harm nulls the consequence component only** and keeps her moves. Alternative: the
   whole action nulled, under which a signal that informs or misinforms an acting part is
   help or harm as well.
7. **The consequence null is the adviser's absence.** Alternative: the adviser's own rule
   with its announcement nulled, computed in cases 33a and 33b.
8. **Her verdict is the move of one estimating part.** Alternative: a function of several
   parts' moves that is no part's move, computed in case 30.
9. **An end's purpose is indexed by its valuation**: the end is for what it values at that
   time, and the standard for changing it is the rest. Alternative: an end with a fixed
   purpose whose mechanism alone changes, under which a change of ends is maintenance and
   no end changes.
10. **Fit is attained minus opposition**, with her other ends summed unweighted.
    Alternatives: attained alone, computed in question 5; judged by all her ends, the one
    under revision included, computed in question 5.
11. **"Hers" and "nobody's" are not separated.** The bank's `not adviser's` stands for
    both. Question 3 says what separating them would need.
12. **Illegitimate influence and a legitimate verdict are two predicates.** A threat
    truthfully stated leaves every part in range, so her verdict is legitimate, and harms
    the acting part, so the influence is not.

## 4. Devices found needed beyond the dispatch's §2

Filled in after the results; each is a finding against the setting as dispatched.
`RESULTS.md`, question 1, gives the evidence for each.

1. **The adviser's null action**: a comparison. Needed twice: to say the adviser brought
   a gap about (choice 5), and to say what her moves would otherwise have led to (choice
   6). For a consequence that is the adviser's own later act the null is not determined by
   the setting (choice 7; cases 33a, 33b).
2. **Typed actions.** A mechanism given only as a function of the world state does not
   separate a move the adviser set from a move the mechanism made in response to the
   adviser. Force and alteration are told from a signal by the type of the action's
   component, which is supplied.
3. **A grain per scene.** The dispatch's range is for one law. A scene of several steps
   needs the conditioning stated; choice 3 states it by rule, and the rule is supplied.
4. **A move that carries confidence.** With a two-valued move a rare lie that she
   believes leaves the part in range at every grain coarser than the adviser's knowledge,
   and that grain puts honest difficulty out of range as well (case 4b).
5. **The verdict as one part's move.** The dispatch says no single part is the evaluator.
   Parts in range do not give a verdict in range unless the aggregation of their moves is
   itself calibrated (case 30), and the setting can require that only of a part.
6. **The rule at other aims**, for the rule on ties only, where no gap exists to carry
   the verdict (case 14).
7. **A menu for each end-revising part.** What fit selects depends on the menu (question
   5); the menu is supplied.

Not adopted, and what its absence costs: a **home condition** for a part, a second law
under which its mechanism is taken to have been fitted. Without it "hers" and "nobody's"
are one verdict (choice 11).

Devices 2, 6 and 7 are supplied lists and device 1 a comparison, in the dispatch's terms.

## Amended after the freeze

Nothing in §1–§3 was changed after the freeze. §4 was written after the results and
device 5 reworded after the external review. The code's reading of *covered* was
corrected after the review to what §2 says: a request is read with the adviser's action
null.
