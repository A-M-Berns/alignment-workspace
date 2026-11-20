# Function and purpose in a finite model

**Verdict.** MODEL-BUILT-NOTHING-REGISTERED — a finite model of self-maintaining wholes, the functions of their parts and the aims of regulators, with a theorem on splitting a part proved on paper and exact computations on worked systems; the ascription of functions changes with the choice of parts, an aim is relative to a class of admissible targets, in a nested system a part lives longer by serving its whole exactly when its independence is below a closed-form threshold, and a part able to build its own support lives longer by building it and then defecting once that support is durable enough. Every component is open.

Nothing here is registered; the support of each statement is named beside it.

Rerun: `python3 tests/run.py` from this directory (32 tests, about four seconds,
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

The proof is on paper and not machine-checked. `test_splitting.py` checks (1) and (2)
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
Agents", arXiv:2208.08345 (introduction and assumptions). The closure-under-union and
lattice structure of §1 follows Dittrich and Speroni di Fenizio; the target-relative
gain of §4 takes its baseline from Dennett's lectern in "True Believers".
