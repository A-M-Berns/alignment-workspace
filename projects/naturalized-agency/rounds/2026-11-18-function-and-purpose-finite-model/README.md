# Function and purpose in a finite model

**Verdict.** MODEL-BUILT-NOTHING-REGISTERED — a finite model of self-maintaining wholes, the functions of their parts and the aims of regulators. Proved on paper for any discrete-time process: a part that seldom outlasts its dead whole cannot outlive it by more than a constant, and when the whole in turn seldom outlasts a step unserved, the expected number of steps at which the part is alive and the whole unserved is at most a constant. In worked systems, computed exactly: the ascription of functions changes with the choice of parts, an aim is relative to a class of admissible targets, a part lives longer by serving exactly when its independence is below a closed-form threshold, and a part able to build durable support lives longer by building it and then defecting. Every component is open.

Nothing here is registered; the support of each statement is named beside it.

Rerun: `python3 tests/run.py` from this directory (47 tests, about ten seconds,
standard library, exact rationals throughout).

All names in this document are **provisional**.

## 1. Systems and self-maintenance (`src/system.py`)

A *system* is a finite set `P` of parts, a set `F` of givens, and finitely many
processes. A process has a condition, a monotone boolean function of which parts and
givens are present, and a set of parts it maintains. For `X ⊆ P`,

    Φ(X) = the union of the outputs of the processes whose condition holds on X ∪ F.

`Φ` is monotone. `X` is *self-maintaining* when `X ⊆ Φ(X)`. `G(X)` is the result of
iterating `X ↦ X ∩ Φ(X)` to a fixed point.

**1.1** Self-maintaining sets are closed under union, and `G(X)` is the greatest
self-maintaining subset of `X`. *Proof.* If `X ⊆ Φ(X)` and `Y ⊆ Φ(Y)` then
`X ∪ Y ⊆ Φ(X) ∪ Φ(Y) ⊆ Φ(X ∪ Y)`. A self-maintaining `Y ⊆ X` has
`Y ⊆ Φ(Y) ⊆ Φ(X)`, so it survives each step of the iteration; the limit is
self-maintaining. ∎ Checked on 200 systems, `test_closure.py`. They are not closed
under intersection: the organism of §3 has two minimal ones whose intersection is not
self-maintaining.

Write `S = G(P)`.

- *Necessity.* `q` is necessary for `p` when `p ∉ G(S ∖ {q})`.
- *Relevance.* `q` is relevant to `p` when for some `T ⊆ S ∖ {q}`, `p ∈ G(S ∖ T)` and
  `p ∉ G(S ∖ T ∖ {q})`.
- *Influence.* Let each part `x` fail independently with probability `r(x)`, `T` the
  set of failed parts. `I(q → p) = P(p ∈ G(S ∖ T) | q ∉ T) − P(p ∈ G(S ∖ T) | q ∈ T)`.
  This is the Birnbaum measure of reliability importance of the component `q`, for the
  binary monotone system that works when `p` survives, with independent components:
  Huseby and Dahl, *Risk- and Reliability Analysis with Applications* (University of
  Oslo, 2024), Definition 5.2.1 and equation (5.2), who attribute it to Birnbaum (1969).

**1.2** Necessity is transitive. *Proof.* If `p ∉ G(S ∖ {q})` then `G(S ∖ {q})` is a
self-maintaining subset of `S ∖ {p}`, hence inside `G(S ∖ {p})`; anything missing from
the latter is missing from the former. ∎ Relevance is not transitive: a witness family
is in `test_closure.py`.

Two parts are *interchangeable* when swapping them leaves every process unchanged; a
*kind* is a class under the transitive closure. A part is *ascribed a function* when it
lies in a class of mutually relevant parts, is relevant to another member, has a member
relevant to it, is not producible from the givens alone, and the class holds at least
two kinds of such parts. This follows the three conditions of Mossio, Saborido and
Moreno, "An organizational account of biological functions", *BJPS* 60 (2009), §5:
contribution to the maintenance of the organisation, production under its constraints,
and organisational differentiation.
Montévil and Mossio, "Biological organisation as closure of constraints", *J. Theor.
Biol.* (2015), doi:10.1016/j.jtbi.2015.02.029, Definition 4, require of a closed set that
each constraint depend directly on another member and have another member depend on
it, which a single self-sustaining pattern cannot meet; the two-kinds condition here
plays that role.

## 2. Re-carving (`split`, `merge`)

**Splitting theorem.** Replace a part `q` by `q₁, q₂`: each condition clause containing
`q` now contains both, and each process maintaining `q` maintains both. Give them
failure rates with `(1 − r₁)(1 − r₂) = 1 − r(q)` and leave the other rates alone. Then
for parts `a, b` other than `q`:

1. `I′(a → b) = I(a → b)`;
2. `I′(q₁ → b) = (1 − r₂) · I(q → b)`;
3. `|I′(a → q₁) − I(a → q)| ≤ (1 − r₁) · r₂`.

*Proof.* Let `π` send a set `X′` of new parts to the old set that agrees with it off
`q` and contains `q` exactly when `X′ ⊇ {q₁, q₂}`, and let `ι` replace `q` by both
halves. A new clause `ι(c)` lies in `X′ ∪ F` exactly when `c` lies in `π(X′) ∪ F`, so
`Φ′(X′) = ι(Φ(π(X′)))`. Then `π(X′ ∩ Φ′(X′)) = π(X′) ∩ Φ(π(X′))`: off `q` both sides
agree termwise, and `q` is in the left side exactly when both halves are in `X′` and
`q ∈ Φ(π(X′))`. So `π` commutes with each step of the iteration,
`π(G′(X′)) = G(π(X′))`, and `G′(X′)` and `G(π(X′))` agree off `q`. The image under `π`
of the new failure set is distributed as the old failure set, and the event that `a`
has failed is the same event in both, which gives (1). For (2), conditional on `q₁`
alive, `q` has failed with probability `r₂`, and conditional on `q₁` failed it has
failed, so `I′(q₁ → b) = (1 − r₂)P(b | q alive) + r₂P(b | q failed) − P(b | q failed)`.
For (3), `q₁` survives when `q` does if `q₂` is alive; the two differ only on the event
that `q₁` is alive and `q₂` has failed, of probability `(1 − r₁)r₂`, on which the
difference of conditional probabilities lies in `[−1, 1]`. ∎

By Huseby and Dahl's Theorem 5.2.2 the measure is the derivative of the system's
reliability in the component's, so for two components in series forming a module,
(2) is the chain rule; (3) concerns the module as the thing that survives. The proof is on paper and not machine-checked. `test_splitting.py` checks (1) and (2)
with exact equality and (3) with the bound attained, on the systems of a fixed
pseudo-random family whose greatest self-maintaining set has at least three parts.

Ascription by relevance is not preserved by this split: `cases.split_witness` has
functions `{p0, p1, p2}` before `p3` is split and those together with both halves
after. It is preserved on a family of 150 systems when the split is into redundant
copies (either serves wherever `q` did); that is an observation, with no proof.
Merging every part of the organism into one removes every function.

## 3. Worked systems (`src/cases.py`, `tests/test_cases.py`)

| system | result |
|---|---|
| vortex, air a given | one produced part; no function |
| vortex with circulating parcels as parts | every part ascribed a function |
| `n` interchangeable parcels sustaining one another | one kind; no function; influence of one parcel on another at rate 1/10 is 9/1000 at `n = 4` and decreases through `n = 8` |
| self-copying catalyst with a membrane | all three parts |
| organism (five organs, four resources, two kidneys) | all nine parts; the heart is necessary for the other eight, a kidney for none; at rate 1/10, `I(Heart → Lungs) = 52612659/10⁸`, `I(Kidney1 → Lungs) = 4782969/10⁸` |
| household, thermostat maintained by the person | the thermostat is ascribed a function |
| household, thermostat supplied as a given's product | the thermostat is relevant to others and is ascribed none |
| lab: staff train a model, the model earns, earnings fund staff and compute | all four parts; with staff removed nothing survives |
| the same lab with a process by which the model maintains itself | with staff removed `{Model, Compute, Revenue}` survives; staff are ascribed no function |

The second row lists the vortex and the parcels as separate parts although neither can
be removed while the other stays. The third row is the same physical case with parts
that can be removed independently.

## 4. Aims (`src/aims.py`, `tests/test_aims.py`)

A *regulator* is a policy from disturbances to actions; disturbance and action
determine an outcome. For a set `T` of outcomes and a distribution on disturbances,

    gain(π, T) = P(outcome ∈ T | π) − max over fixed actions a of P(outcome ∈ T | a).

Relative to a class of admissible targets, the *aim* of `π` is a target of greatest
gain and that gain is its *strength*. A fixed action has strength 0 for every class.

Disturbances and actions in `{−1, 0, 1}`, uniform disturbances, outcome their sum:

- with every proper nonempty set of outcomes admissible, 22 of the 27 policies have
  positive strength; the policy `a = d` has strength 1/3 with target the even outcomes;
- with intervals admissible, 13 have positive strength, the policy `a = d` has none,
  and `a = −d` has strength 2/3 with target `{0}`.

**4.1** If the set `V` on which a whole persists is admissible, strength is at least
`gain(π, V)`. Immediate from the definition. The converse fails: four of the 27
policies have positive strength and hit `{0}` less often than the idle policy.

**4.2** If two distributions on disturbances are at total-variation distance `δ`, the
two strengths of a policy differ by at most `2δ`, and a target that leads every other
gain by more than `4δ` under one is a target of greatest gain under the other.
*Proof.* Each of `P(T | π)` and `P(T | a)` moves by at most `δ`, so each gain moves by
at most `2δ`. ∎ Checked on 1500 pairs with the factor 2 attained.

## 5. A self-maintaining part inside a self-maintaining whole (`src/nested.py`)

The system is described at the head of `src/nested.py`: an inner loop of two parts fed
by the whole or, with probability `ρ` per step, from outside; an outer part that
persists when the inner loop delivered its service on the previous step or, with
probability `h`, from a reserve; a policy by which the inner loop steers the outcome to
the whole's target (*serve*) or to one that lowers its own failure rate from `ε` to
`ε′` (*defect*). Expected lifetimes are computed exactly from the Markov chain on its
32 states.

**5.1** Let `u = (1 − ε)²` and `v = (1 − ε′)²`. If `u > vh`, put

    ρ* = (1 − v(1 − h)(1 − u) / (u − vh)) / v.

The part's expected lifetime is longer under serve than under defect exactly when
`ρ < ρ*`, and the two are equal at `ρ*`. *Proof.* Under serve the service arrives every
step, the whole persists, and the part survives each step with probability `u`: its
expected lifetime is `1/(1 − u)`. Under defect the first step is taken at the
unlowered rate with the whole still supplied, so the part survives it with probability
`u` and the whole survives it surely. From then on, with the whole alive the part
survives a step with probability `v` and the whole with probability `h`; with the whole
gone the part survives a step with probability `ρv`. The expected lifetimes `A` and `B`
from those two states satisfy `B = 1 + ρvB` and `A = 1 + v(hA + (1 − h)B)`, so
`A = (1 + v(1 − h)/(1 − ρv)) / (1 − vh)`, increasing in `ρ`. The part's expected
lifetime under defect is `1 + uA`, and `1 + uA < 1/(1 − u)` exactly when
`A < 1/(1 − u)`, which rearranges to `ρ < ρ*`. ∎

`test_nested.py` checks the equality at `ρ*` exactly and the two strict inequalities at
`ρ* ± 1/1000` for `(ε, ε′, h) = (1/10, 1/40, 1/2), (1/5, 1/20, 1/4), (1/10, 1/20, 3/4)`,
and that at `(1/4, 1/100, 1/2)`, where `ρ* < 0`, defect is longer at `ρ = 0`.

**5.2 (dependence bounds defection).** Take any process in discrete time with two
absorbing deaths, a whole's and a part's, and write `L_W` and `L_w` for the expected
numbers of steps each is alive. Suppose that whenever the whole is dead at a step, the
part is alive at the next with conditional probability at most `ρ < 1`, whatever the
history. Then

    L_w ≤ L_W + 1/(1 − ρ).

*Proof.* The steps at which the part is alive are those at which the whole is also
alive, at most `L_W` in expectation, and those from the whole's death on. At the step
of the whole's death the part is alive with probability at most 1, and `k` steps later
with probability at most `ρᵏ`. ∎

The statement uses nothing about policies, parts or processes beyond the hypothesis.
Two consequences. If a behaviour gives the part an expected lifetime at least that of a
reference behaviour `σ`, it gives the whole at least `L_w(σ) − 1/(1 − ρ)`. And for a
part inside a whole inside a larger whole, with independences `ρ₁` and `ρ₂`, the
part's expected lifetime is at most the largest whole's plus
`1/(1 − ρ₁) + 1/(1 − ρ₂)`. In the system of this section the hypothesis holds with the
`ρ` of the outside source. `test_dependence.py` checks the inequality and the first
consequence over all 125 policies at `ρ = 0, 1/2, 9/10`; at `ρ = 1` the hypothesis
fails and defect gives the part more than 17 against the whole's 3; at `ρ = 0` defect
gives the part more than the whole and less than the whole plus one.

**5.3 (closure bounds shirking).** Take a process as in 5.2 with a third indicator, that
the whole is *served* at a step. Suppose the hypothesis of 5.2, and suppose that
whenever the whole is alive and unserved at a step it is alive at the next with
conditional probability at most `h < 1`, whatever the history. Then the expected
number of steps at which the part is alive and the whole is unserved is at most

    1/(1 − h) + 1/(1 − ρ).

*Proof.* Such steps with the whole dead number at most `1/(1 − ρ)` in expectation, as
in 5.2. For those with the whole alive, let `N` count the steps at which the whole is
alive and unserved; each is survived by the whole with probability at most `h`, so
`P(N ≥ k) ≤ hᵏ⁻¹` and `E N ≤ 1/(1 − h)`. ∎

The two hypotheses are quantitative forms of conditions C2 and C1 of the
organisational account as §1 cites it: the part is maintained by the whole, and the
whole is maintained through what the part does. The conclusion holds for every
behaviour of the part. A part whose expected lifetime is `L` has therefore served at
all but `1/(1 − h) + 1/(1 − ρ)` of its steps in expectation. In the system of this
section, with *served* read as `Service` present, both hypotheses hold.
`test_closure_bounds_shirking.py` checks the bound over all 125 policies at
`h = 1/4, 1/2` and `ρ = 0, 1/2, 9/10`, with some policy above half the bound; at
`ρ = 1`, and separately at `h = 1`, a hypothesis fails and defect leaves the whole
unserved for more than 16 of the part's steps.

**5.4 (the tail).** Under the hypotheses of 5.3, with `θ = max(h, ρ)`, the probability
that the part is alive with the whole unserved at `m` or more steps is at most
`(m + 1) θ^(m − 2)`. *Proof.* Let `N₁` count such steps with the whole alive and `N₂`
those with it dead; the former precede the latter. Conditioning step by step,
`P(N₁ ≥ j, N₂ ≥ k) ≤ h^(j−1) ρ^(k−1)` with an exponent read as 0 when negative, and
`N₁ + N₂ ≥ m` forces `N₁ ≥ j` and `N₂ ≥ m − j` for one of the `m + 1` values of `j`. ∎
`test_tail_and_long_run.py` checks it for three policies, three settings of `(h, ρ)`
and `m = 2, …, 8`, and that the exact tail sums to the expectation of 5.3.

5.2–5.4 use no distribution on failures or disturbances: `ρ` and `h` are bounds on two
conditional probabilities, required to hold after every history, and the conclusions
hold conditionally on any history as well.

**5.5 (who is left).** In the system of this section, the probability that the part is
alive at step `t` is `uᵗ` under serve, and under defect it is, for `t ≥ 2`,

    u · ( (vh)^(t−1) + Σ_{k=0}^{t−2} (vh)^k · v(1 − h) · (ρv)^(t−2−k) ),

which decays at rate `v · max(h, ρ)`. So for large `t` the part is likelier to be alive
under serve exactly when `u > v · max(h, ρ)`, and a part drawn to serve or to defect
with any fixed positive probabilities is, given that it is alive at `t`, a server with
probability tending to 1 in that case and to 0 when the inequality is reversed.
*Proof.* Under serve the whole persists and the part survives each step with
probability `u`. Under defect the first step is survived with probability `u` and the
whole survives it; thereafter each step with the whole alive is survived by both with
probability `vh` and by the part alone with probability `v(1 − h)`, and each step with
the whole dead is survived with probability `ρv`. ∎

The condition is symmetric in the two independences and differs from 5.1: at
`(ε, ε′, h, ρ) = (1/10, 1/40, 1/2, 4/5)` defect gives the longer expected lifetime and
serve the higher probability of being alive at step 400. `test_tail_and_long_run.py`
checks the sign of the comparison at step 400 against the inequality at four settings.

At `(1/10, 1/40, 1/2)` and `ρ = 1/2` the whole's expected lifetime is `157/19` with the
part serving, `3` with it defecting and `3` with it absent. Of the 125 policies with
actions in `{−2, …, 2}`, compared with the idle policy on both lifetimes:

| `ρ` | longer for both | longer for the whole only | longer for the part only |
|---|---|---|---|
| 1/2 | 16 | 0 | 1 |
| 9/10 | 7 | 9 | 10 |

## 6. Independence the part builds (`src/acquired.py`, `tests/test_acquired.py`)

The outside source is replaced by a store `X` that feeds the inner loop when the whole
does not. The intact inner loop steers each step to one of three targets: *serve*,
*boost* (the lowered failure rate) or *build* (`X` present on the next step). `X` lapses
each step with probability `δ` unless rebuilt. A policy names a target for each of `X`
absent and `X` present, nine policies in all. At `(ε, ε′, h) = (1/10, 1/40, 1/2)`:

- at `δ = 1/4` no policy gives the part a longer expected lifetime than serving in both
  cases, `100/19`;
- at `δ = 1/10` the policy *build while `X` is absent, boost while it is present* gives
  the part `5500218221251/817862668900`, longer than every other policy, and gives the
  whole expected lifetime `3`, its lifetime with the part absent; at `δ = 0` the part's
  is `4771/316`;
- that policy overtakes serving between `δ = 2/11` and `δ = 1/6`.

## What is not shown

- That the model's form (monotone conditions, presence or absence, one step of
  maintenance, independent failures) is the right one. Inhibition and competition for
  a resource cannot be expressed in §1.
- Any derivation of parts or processes from a dynamics. Every system here is written
  by hand, and §3 shows the ascription changing with the choice of parts.
- That the function definition of §1 is stable under any re-carving. The theorem is
  about influence; "function strength" as a single number is not defined.
- That the admissible targets of §4 can be chosen without reference to an observer.
- More than a few lines of argument in 5.2–5.4: each conclusion is close to its
  hypotheses, and what they add is the form of the hypotheses and the constants.
- Any statement about nested systems other than the two of §§5 and 6. §6 is computed at
  one setting of `(ε, ε′, h)`, and its nine policies cannot condition on the whole's state.
- Anything comparing two descriptions arrived at separately, beyond 4.2.

## Sources read for this round

Eisenstat, "Condensation: a theory of concepts" (2025 draft,
https://www.sameisenstat.net/doc/condensation-25-07.pdf); Garrabrant, Herrmann and
Lopez-Wild, "Cartesian Frames", arXiv:2109.10996, and the sequence posts "Introduction
to Cartesian Frames", "Controllables and Observables, Revisited" and "Time in Cartesian
Frames"; Mindermann and Armstrong, "Occam's razor is insufficient to infer the
preferences of irrational agents", NeurIPS 2018; Dennett, "Real Patterns", *J. Phil.*
88 (1991), and "True Believers" (1981); Mossio, Saborido and Moreno (2009), cited
above; Dittrich and Speroni di Fenizio, "Chemical organization theory",
arXiv:q-bio/0501016; Hordijk, Steel and Kauffman, "The Structure of Autocatalytic
Sets", arXiv:1205.0584; Beer, "The Cognitive Domain of a Glider in the Game of Life",
*Artificial Life* 20 (2014); Krakauer et al., "The Information Theory of
Individuality", arXiv:1412.2447 (abstract and measures); Kenton et al., "Discovering
Agents", arXiv:2208.08345 (introduction and assumptions). Huseby and Dahl (2024), cited in §1
(Chapter 5, sections 5.1–5.2, and the definition of a module in section 3.3). Montévil and
Mossio (2015), cited in §1 (Definitions 1–4 and section 6.1). Di Paolo, "Autopoiesis,
adaptivity, teleology, agency", *Phenomenology and the Cognitive Sciences* 4 (2005)
(the definition of adaptivity and the argument around it). Millikan, "In Defense of
Proper Functions", *Philosophy of Science* 56 (1989). The closure-under-union and
lattice structure of §1 follows Dittrich and Speroni di Fenizio; the target-relative
gain of §4 takes its baseline from Dennett's lectern in "True Believers".
