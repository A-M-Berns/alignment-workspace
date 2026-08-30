# Progress as the consumer of Normative Continuity

Status: research specification; unregistered; not frozen or settled. Definitions,
assumptions, derived results, and realization choices are marked separately.

## 1. The inherited interface

Progress does not own a lifecycle. For a Continuity matter `m`, it inherits exactly

\[
\Live_n(m),\quad \Reach_n(m),\quad \Work_n(m),\quad o_n(m),\quad
a_n(m),\quad A_N(m)=\sum_{n<N}a_n(m),
\]

together with issue occurrences, anchored protocols, accepted resolutions, explicit
fresh successors, and matter ancestry. Under Continuity's no-permanent-wait and
non-starvation hypotheses,

\[
m\text{ live eventually forever}\quad\Longrightarrow\quad A_N(m)\to\infty.
\tag{C-service}
\]

This is the sole liveness premise below. There is no Progress queue, pending set,
successor relation, or attention variable. The upstream source is revision 2 of
Normative Continuity at commit `bb741d4`; the checkpoint at `dbd5e9d` remains its
provenance source. No defect in that specification was found in this pass.

## 2. Decision-local objects

Fix a matter `m`. Objects below exist at each position where service can be assigned.

### Definitions

1. `X_n(m)` is a nonempty finite set of service-move labels available at strict prefix
   `H_n`. A label can denote investigation, incorporating a repair, pursuing a route,
   recording a defeater, resolving a ready issue, proposing a successor, or explicitly
   acknowledging a conflict. These are service responses, not necessarily world acts.

2. `p_n^m in Delta(X_n(m))` is the response distribution used on the serviced fraction
   of the occasion.

3. `K_n(m)` is a nonempty subset of `[0,1]^{X_n(m)}`. Its elements are admissible
   valuations of this decision's labels. The schematic needs only nonemptiness; compact
   sets are preferable because they make robust minima and nearest points attain.
   `K_n(m)` is **decision-local**, with provenance pointing to its matter and anchored
   issue episode. It is not one eternal utility function for the matter.

4. A repair identity `rho` is a fixed causal program. At `H_n` it emits a feasible map

   \[
   \Phi_n^\rho:\Delta(X_n(m))\to\Delta(X_n(m)).
   \]

   The program identity persists while its date-specific map may change with the menu
   and prefix. Unavailability is totalized by the identity map. The abstract layer does
   not require affinity; the regret realization will.

5. Its robust advantage is

   \[
   g_n(m,\rho)=\inf_{v\in K_n(m)}
   \langle\Phi_n^\rho(p_n^m)-p_n^m,v\rangle.
   \tag{Gain}
   \]

   Thus `g_n>0` is a strict unanimity claim over the currently admissible valuations.
   It represents a robust reason for changing this service response, not every ordinary
   pro tanto reason.

6. `c_n(m,rho) in [0,1]` is predictable applicability/confidence, defined before
   `p_n^m`. Set

   \[
   w_n=a_n(m)c_n(m,\rho),\qquad W_N=\sum_{n<N}w_n.
   \]

   `c_n` is a counterfactual scoring gate, not physical attention. If the whole repair
   family can be evaluated from one full valuation vector, all repairs share the same
   service choice and no repair scheduler is needed.

7. A repair-specific defect is any `d_n(m,rho) in [0,1]`. Its weighted mass is

   \[
   D_N(m,\rho)=\sum_{n<N}w_n d_n(m,\rho).
   \]

### Typing choices that survived prosecution

- `K_n` belongs to the service decision, not globally to `m`. Episode provenance is
  nevertheless mandatory so changing standards cannot silently rewrite an earlier
  score.
- A stable repair is a stable **program**, not a fixed function between varying sets.
  A realization may instead embed all `X_n` in a fixed finite label alphabet.
- General distribution maps are the thinnest semantic type. Deterministic action maps
  `f:X->X`, lifted linearly to distributions, or stochastic kernels are the realizable
  subclass for ordinary Phi-regret.
- Predictability means `X_n`, `K_n`, `c_n`, and the entire function `Phi_n^rho` are
  functions of `H_n` (and the candidate input action where appropriate), never of the
  realized current response, current event, or future record. Applying an already-fixed
  function to `p_n` is not hindsight choice.

## 3. Uptake

### Abstract assumption

For each registered repair program `rho`,

\[
W_N\to\infty\quad\Longrightarrow\quad
\limsup_{N\to\infty}\frac{\sum_{n<N}w_ng_n}{W_N}\le 0.
\tag{Uptake}
\]

The sign is correct: positive `g_n` is foregone value from failing to transform the
played response, so an uptake guarantee upper-bounds its cumulative average. Uptake is
an abstract responsiveness condition. It mentions neither markets nor regret.

### Why signed rather than positive-part Uptake

The stronger candidate

\[
\frac{\sum w_n[g_n]_+}{W_N}\to0
\tag{Positive Uptake}
\]

prevents a repair from banking negative credit and later ignoring positive gains. It
is attractive but is not delivered by ordinary external, internal, or Phi-regret:
those control the signed comparator advantage. Sleeping weights do not solve this if
sleep/wake status is chosen after seeing the current response or gain.

Signed Uptake is sufficient for the primary theorem because Sensitivity makes the
witness eventually nonnegative. Positive Uptake or interval/strongly-adaptive regret
is needed only for a stronger theory that must respond to arbitrary recurring positive
episodes separated by genuine negative ones.

### Sensitivity assumption

For a witness repair, there are `gamma>0` and `n_0` such that whenever `n>=n_0`
and `w_n>0`,

\[
g_n(m,\rho)\ge\gamma d_n(m,\rho).
\tag{Sensitivity}
\]

This is not a definition of defect. It is the substantive adapter saying that this
measured defect exposes a uniformly valuable feasible repair on the occasions counted.
In particular, it eliminates negative comparator credit on the relevant tail.

### Theorem: defect elimination

**Theorem (schematic Progress).** Uptake and eventual Sensitivity imply

\[
W_N(m,\rho)\to\infty
\quad\Longrightarrow\quad
\frac{D_N(m,\rho)}{W_N(m,\rho)}\to0.
\tag{DE}
\]

**Proof.** The prefix before `n_0` has finite weighted mass. On the tail,
`0 <= gamma sum w_n d_n <= sum w_n g_n`. Divide by divergent `W_N`. The right
side has limsup at most zero by Uptake and is eventually nonnegative up to the
vanishing finite prefix. Therefore both normalized sums converge to zero. QED.

This is the preferred basic Progress conclusion. Eventual issue closure is stronger
than the mathematics supports and is unnecessary: inquiry, a defeater, an explicit
reframing, or vanishing defective response can answer a reason without terminal closure.

## 4. What counts as an answer

Progress reuses Continuity's recorded events:

- an accepted terminal resolution is an answer;
- an accepted resolution into fresh successors is an explicit answer/revision, with
  the successor's evaluator anchored prospectively;
- a recorded legitimate defeater can support such a resolution or remove the operative
  reason from the next decision-local `K`;
- continued inquiry can be progress when it changes the measured defect or creates a
  recorded route, result, defeater, or successor; merely consuming attention is not;
- acknowledgement of an unresolved conflict can be a service move, but repeating it
  forever with a stable positive defect is not uptake.

The phrase **genuine stagnation** is therefore deliberately not a new issue status. It
is a semantic predicate on a tail saying that after some point there are no accepted
answer/revision events relevant to the reason and a substantive defect persists.

## 5. Candidate Stagnation Witness conditions

The bridge from genuine stagnation to a repair witness is the Progress analogue of
Persistent-Wait. Unlike Persistent-Wait, it is not currently derivable from structural
bookkeeping.

### SW-strong (the prompt's candidate)

Eventual genuine stagnation implies one `rho`, `gamma,delta>0`, and `n_0` such that
`W_N->infinity`, eventual Sensitivity holds, and

\[
\liminf_N D_N/W_N\ge\delta.
\]

This is sufficient but stronger than the contradiction needs.

### SW-density (recommended weakest theorem interface)

Eventual genuine stagnation implies one historically registered predictable repair
program `rho`, one `gamma>0`, and a defect `d` such that

\[
W_N\to\infty,\qquad g_n\ge\gamma d_n\text{ eventually on }w_n>0,
\qquad \limsup_N D_N/W_N>0.
\tag{SW-density}
\]

The limsup is enough because (DE) gives a limit of zero. Requiring a positive liminf
should be reserved for a definition of persistent positive-density stagnation.

### SW-pointwise (clean sufficient form)

After a hypothetical last legitimate progress event, one stable repair has
`c_n>=c_*>0` on a service-weighted set of infinite mass and
`d_n>=delta>0`, `g_n>=gamma d_n` on that tail. Together with `A_N->infinity`
when applicability covers every later service occasion, this implies SW-strong.

### SW-churning (rejected as a basic axiom)

“At every stagnant date some positive-gap repair exists” is too weak. The witness can
change every date, no comparator need accumulate gain, and a varying menu can make the
class unbounded. Repair churn requires a finite-class pigeonhole argument with
nonnegative gains, dynamic/interval regret, or an additional compactness/completeness
theorem. None belongs in basic Progress.

### No-persistent-unanswered-reason theorem

Assume Continuity (hence unbounded service for an eventually live matter), Uptake, and
SW-density. If a represented, answerable reason were eventually genuinely stagnant,
SW-density would provide a repair to which defect elimination applies and would also
say its normalized defect has positive limsup, a contradiction. Therefore no such
stagnant tail exists.

This is a clean compression, but **SW-density remains an assumption**, not a theorem
of Continuity or the current reason representation.

## 6. Why the stagnant tail matters

Suppose `q_0 -> q_1 -> ...` contains infinitely many accepted prospective revisions.
Basic Progress may count each as an explicit answer, so there is no last stagnant tail
and no need to compare all eras with one switching comparator. This does not certify
that the revisions are good. A stronger diachronic theory may later rule out revision
spam or evaluator laundering.

If legitimate progress events are finite, choose a point after the last one. Continuity
then prevents silent issue disappearance and retroactive evaluator change. A stable
episode-local repair witness can be demanded only on this tail. Any negative comparator
credit before the tail is finite and vanishes after normalization. This observation is
enough to avoid dynamic regret for the **basic** theorem, conditional on SW-density.

## 7. Strict-prefix timing

The clean order is

\[
H_n\to(\Work_n,X_n,K_n,c_n,\Phi_n)
\to a_n\to p_n\to e_n.
\]

`a_n` must be known to the confidence-rated learner before it chooses `p_n`; writing
them in one display stage is harmless only if this internal order is respected. After
`p_n`, the full valuation/loss vector may be revealed and the learner updated. Events
in `e_n` can resolve issues, open successors, revise standards prospectively, or change
the next position's reason state. No event in `e_n` rescoring the choice at `n` is
allowed.

## 8. Open design choices

1. The semantic definition of genuine stagnation and which recorded inquiry events
   count as substantive progress.
2. SW-density/normative witness completeness: why an unanswered reason entails a stable
   robust dominance claim rather than conflict, incomparability, or open uncertainty.
3. Whether the first implementation uses a fixed episode-local alphabet or a proved
   encode/decode bridge for changing menus.
4. Whether a stronger future theory should judge infinite explicit revision. That
   requires a diachronic standard and probably dynamic regret; basic Progress does not.
5. Whether ordinary reasons should use local faces or conditional regions of `K_n`.
   Whole-region infima intentionally capture only unanimity reasons; weakening that
   reading requires naming whose disagreement may be ignored.

