# Lateral / Creative Findings — Deference & Trust Lab

*Covers the agenda's less-LI-central items and hunts for non-obvious cross-connections. Other
agents own the Eisenstat merge (Q4/Q5), the weak-endorsement⇒weak-deference impossibility (Q10),
legitimacy/corrigibility (Q11), updateless deference (Q8), and the Cole-Wyeth thread (Q9), plus the
Lean audit. This file deliberately does **not** re-derive those; it stays in the corners they leave
open and bridges between threads.*

Every claim is flagged **PROVED** / **SKETCHED** (LI-paper-level rigor) / **CONJECTURE** /
**INTERPRETATION**, matching v2's discipline. Citations into v2 are by section; into the LI paper by
theorem number; into the UDT dir by filename.

Companion Lean candidate: `lean/lateral-dtype.lean` (**UNCHECKED — for the Lean-verify agent**),
discussed in §1.5.

---

## Part 1 — "What is a decision problem?" The dependent type, and systematized winning

### 1.0 The principal's complaint, made precise

The principal typed a decision procedure as `(S, A) → A` and flagged that "the two `A`s are not
really the same; the first is a *set* of actions, the second an *element* of that set" — it wants a
dependent type. The fix is standard, but stating it cleanly turns out to *relate the optimality
notion to deference* in a way that is not obvious from the prose, so it is worth doing carefully.

### 1.1 The clean dependently-typed formalization (INTERPRETATION; the type theory is PROVED-trivial)

Let `State` be a type of *decision situations*. A situation `s : State` carries:
- a type of available actions `Act s : Type` (this is the dependency the principal wants — the
  action menu is *indexed by* the situation),
- and, to even talk about optimality, a payoff. Keep it abstract: a value type `V` with a preorder
  `≤`, and `pay : (s : State) → Act s → V`. (For decision theory `V = ℝ` or a `[0,1]`-LUV.)

Then a **decision procedure** is a *dependent function*

```
D : (s : State) → Act s
```

— a section of the family `Act`. This is the honest type: `D s : Act s`, so the output lives in
*the menu of the situation it was handed*. The non-dependent `(S, A) → A` collapses the family to a
single `A` and is exactly what loses the information that the chosen action must come from *this*
situation's menu. In dependent-type vocabulary: a decision procedure is an element of the
**Π-type** `Π (s : State), Act s`, the type of *choice functions*. (When `Act` is constant the
Π-type degenerates to `State → A`, recovering the principal's `(S,A)→A` — so the dependent version
strictly generalizes, with no loss.)

> **Remark (this is literally the UDT policy type).** `formal-single-agent.md`'s "unified decision
> procedure `D : S → A`" and `agency-as-condensation.md`'s "policy `Π` with `H(A_i | Π, O_i)=0`" are
> the *non-dependent* shadow of `Π (s : State), Act s`. The dependent typing is what lets different
> situations carry *different* menus — exactly the heterogeneous-decision-point /
> mismatched-ontology setting that `superconditioning-mismatched-ontologies.md` reaches for. So
> "give a dependent type for a decision procedure" and "let UDT span decision points with different
> action sets" are *the same refactor*. **INTERPRETATION.**

### 1.2 Optimality without "rich by whose measure?": the why-ain'cha-rich notion as a *fixed point*, not an external yardstick

The principal's stated goal (from "Coherent Care") is to make "systematized winning / why ain'cha
rich" arguments crisp, dodging the objection *"rich by whose measure? — the optimality standard is
itself part of what decision theories dispute."* The dependent-type framing suggests a way to phrase
optimality that is **internal**, so the objection has no purchase.

**The move.** Don't grade `D` against an externally chosen utility scale. Grade it against the
*counterfactual menu of procedures*, using only the structure already in the problem. Concretely,
suppose the environment is **decision-determined** in the `udt-representation-theorem` sense (the
world responds to the *policy* `D`, not to the mechanism computing it; `formal-single-agent.md`
§"Decision-Determination"). Then each policy `D` induces a distribution `P_D` over worlds, and a
*global* payoff `EU(D) := E_{P_D}[pay]`. Say:

> **Def (Systematized Winning / WAR-optimal).** `D⋆` is *systematized-winning* iff
> `EU(D⋆) ≥ EU(D)` for every policy `D` in the comparison class.

This looks circular ("optimal = maximizes EU") but the anti-circularity content is in **what the
comparison class is and that the yardstick `EU` is the agent's own**: we are *not* importing CDT's
or EDT's counterfactuals. We are asking whether `D⋆` is a **fixed point** of "would I, reasoning
from my own `P_D⋆`, want to deviate at any situation `s`?" That is the **endorsement** reading:

> **Claim (the bridge — INTERPRETATION, well-argued).** `D⋆` is systematized-winning **iff** `D⋆` is
> *control-endorsed by its own induced prior* `P_{D⋆}` in the sense of
> `agency-via-endorsement.md` §"Control Endorsement": for every situation `s`,
> `D⋆(s) ∈ argmax_{a : Act s} E_{P_{D⋆}}[U | action at s is a]`.

*Why this dissolves "rich by whose measure?"* The measure is **the agent's own induced beliefs**,
and the optimum is a **self-consistency / fixed-point** condition, not a comparison to a rival
theory's preferred counterfactual. "Why ain'cha rich?" stops being "you failed *my* yardstick" and
becomes "*by your own lights, evaluated at the prior your policy induces*, you would deviate" — which
even a CDT-er must grant is a defect, because it is internal incoherence, not a foreign standard.
This is exactly the `daniel-h-challenge.md` "broadest fairness that admits a good DT" point,
re-cast: the WAR argument has bite precisely when the loser is *not* a fixed point of its own
endorsement. **INTERPRETATION.**

### 1.3 The tiling connection: WAR-optimal = a one-step tiling condition

A reflectively-consistent / **tiling** agent is one that, given the option to self-modify, leaves
itself unchanged — it *endorses its own continuation*. Compare:

- **Tiling (one step):** at every situation `s`, the agent would not replace `D(s)` with anything
  else if offered the choice (it *chooses itself instrumentally*).
- **WAR-optimal / control-endorsed (§1.2):** at every `s`, `D(s)` is `argmax` under the agent's own
  induced prior.

These are the **same fixed-point condition** at one level of recursion. **INTERPRETATION.** The
slogan: *systematized winning is the value-of-information shadow of tiling, and control-endorsement
is their common fixed point.* This is why the v2 deference theorem keeps landing in "the
tiling/Vingean-reflection register" (v2 §10.4): **Value (LI form)** —
`𝔼_n(Ŝ_n) ≳ₙ 𝔼_n(O^i_n)` — *is the WAR/tiling fixed-point condition for the present-self ↦
future-self handoff*. "I'd rather let my future self pick the bet" is literally "I endorse my own
continuation as a decision procedure," i.e. a tiling step for the trivial self-modification
`D ↦ (defer to f(n)-self)`.

### 1.4 Where CDT vs EDT enters (and a caveat)

The principal asked to relate this to the CDT/EDT debate. The dependent-type framing is *neutral*
between them — the difference is entirely in how `P_D` is computed from `D`:

- **EDT/split:** `P_D(·) = P(· | "I take action D(s) at s")`, conditioned situation-by-situation
  (`formal-single-agent.md` §"Conditioning Interpretation"). The Π-type is evaluated pointwise.
- **UDT/unified:** `P_D(·) = P(· | "my policy is D")`, conditioned on the *whole* section of the
  Π-type at once.

**CONJECTURE (lateral).** The dependent type makes a *third* option visible that neither the
principal's prose nor `formal-single-agent.md` names: condition on the *germ* of `D` at `s` —
`D` restricted to situations the environment can causally/acausally couple to `s`. This is the
type-theoretic analogue of a **sheaf/locality** structure on `State`: situations carry a topology
("which decision points are entangled"), and the right conditioning is on the stalk. UDT1.1 = global
sections (the whole Π-type); UDT1.0/EDT = points; "germ-UDT" = a middle the agenda's open-minded
updatelessness thread might want. *I flag this as speculative but precise enough to chase: it is the
locality structure the Coordinated-Buttons / Stag-Hunt failures of `examples-revisited.md` are
implicitly about.*

### 1.5 A tiny checkable algebraic kernel (UNCHECKED Lean — `lean/lateral-dtype.lean`)

The fully type-theoretic content of §1.1 is too soft to be a satisfying Lean target on its own (a
Π-type existing is trivially true). But §1.2–1.3 have a **non-trivial algebraic shadow** that ties
directly to the v2 `decomposition` identity and is plausibly Lean-checkable. Statement in plain
English first:

> *On a finite state space, a recommended strategy's realized (diagonal) return equals the
> novice-expected return of the **best fixed action** exactly when the conditional-martingale
> defect vanishes; and when it vanishes, the strategy is WAR-optimal (no fixed action beats it).*

This is the "systematized winning" face of v2's `value_of_CM`. The candidate Lean file proves the
*clean direction*: **if** the per-option conditional-martingale defects are zero **and** the softmax
slack is zero (hard argmax), **then** the diagonal return `≥` every fixed option's return — i.e. WAR
holds. It is a small specialization/re-skinning of the existing `Deference.value_of_CM` backbone,
re-stated in "no fixed action beats the policy" language so the *optimality/WAR* reading is explicit
rather than buried. See the file for the faithfulness analysis (§"Fidelity"). **The Lean is
UNCHECKED**; I reason there about whether it actually says WAR-optimality and where it could be
vacuous.

---

## Part 2 — Vingean agency & abstraction, via Blackwell/Geanakoplos

### 2.0 The target

The principal: *"we can't predict the chess master's moves but can predict they'll win."* Goal:
characterize **Vingean agency** by a theory of **abstraction**, and (my added mandate) connect it to
the **Blackwell/Geanakoplos "trust on general principles"** already loaded in v2 §1.1.

### 2.1 The two things Vingean agency must do at once

From `meaning-and-agency-reference.md` (Eliezer's airport example) and
`communication-trust-translated.md` (Yudkowsky's tiling/Vingean principle: *"the offspring's
actions should only appear inside quantifiers"*), Vingean agency is a **joint** epistemic state:

1. **Unpredictability of moves:** I have high entropy over the master's next action
   `H(Act) ≫ 0` — I cannot compute it (it is more skilled than me; computing it would *be* being
   that skilled).
2. **Predictability of outcome:** I have low entropy over the *outcome* `H(Win) ≈ 0` — I am nearly
   certain they win.

The puzzle is that these coexist *because of*, not in spite of, the skill gap. A theory of
abstraction must explain why the **coarse variable** `Win` is predictable while the **fine variable**
`Act` is not, and why this licenses *trust*.

### 2.2 The abstraction = a Blackwell garbling that the outcome survives (SKETCHED)

Here is the bridge to Blackwell/Geanakoplos that v2 §1.1 sets up but does not spend on Vingean
agency. Model the master as an information-processing experiment `E_master : W → 2^W` (what the
master "knows"/computes), and the observer as a coarser experiment `E_obs` with
`E_obs(w) ⊇ E_master(w)` — i.e. **`E_master` is a Blackwell refinement of `E_obs`** (v2 §1.1
"refinement"). Now introduce the **abstraction map** `α : Act → Out` collapsing fine moves to the
outcome (`α(move) = `does-this-line-win). Vingean agency is the conjunction:

> **(V1) The observer cannot invert `E_master`** (cannot simulate the master): `E_master` is
> *strictly* finer, so predicting `Act` requires information the observer lacks.
>
> **(V2) The abstraction `α` is measurable w.r.t. the observer's *own* coarse experiment** *after
> conditioning on agency*: the observer can compute the distribution of `α(Act)=Win` from `E_obs`
> **given** the premise "this is a master," even though it cannot compute `Act`.

The **Blackwell/Geanakoplos content** is what makes (V2) a *justified* prediction rather than a
hope. By Geanakoplos (v2 §1.1: reflexive+transitive+nested ⇒ value of information ≥ 0), a
better-informed agent following a *recommended* strategy obtains **outcome** value at least that of
any fixed strategy. The observer does not need to predict *which* recommended move the master plays;
**Blackwell guarantees the outcome dominates regardless of which one it is** — precisely
*"prediction inside the quantifier."* So:

> **Claim (Vingean agency = quantified Blackwell dominance — SKETCHED at the §1.1 level).** The
> observer is in a *Vingean* epistemic state toward the master iff (i) `E_master` is a refinement of
> `E_obs` it cannot in:vert (V1), and (ii) the outcome abstraction `α` is one along which
> Blackwell–Geanakoplos monotonicity gives `∀` recommended strategies `s`,
> `E_obs[α ∘ s] ≥ E_obs[α ∘ (fixed)]`. The observer predicts `α(Act)` (the win) *universally over*
> the master's unknown move, which is exactly "the offspring's actions appear only inside
> quantifiers."

This **is** the v2 §1.1 picture read backwards: v2 uses Blackwell to show *the present self should
defer to its future self*; the very same theorem, read as the *observer's* warrant, says *the
observer can predict the better-informed agent's outcome without predicting its move.* **Deference
and the intentional stance are the same Blackwell inequality, viewed from the two endpoints of the
refinement.** INTERPRETATION/SKETCHED.

### 2.3 Why this needs *abstraction* and not just refinement (the load-bearing subtlety)

Refinement alone (V1) does **not** give predictability of outcome — a strictly more-informed agent
can do *anything* you can't predict, at the move level *and* the outcome level, unless you also have
a coarse variable on which its competence is **monotone**. That coarse variable is the abstraction
`α`. The precise demand is:

> **(A) Monotone-under-refinement abstraction.** `α : Act → Out` such that on the menu in play,
> `Out`-value is *Blackwell-monotone*: more information never lowers the `E[α]` of the recommended
> strategy. (This is exactly Geanakoplos's "value of information ≥ 0" *restricted to the abstracted
> payoff* `α`.)

When `α` is the identity (no abstraction), monotonicity can fail (the master might make moves whose
*fine* consequences you cannot bound — Weatherson's Coin, v2 §6, is the unbounded case where even
the outcome value misbehaves). **Abstraction is the operation that throws away exactly the
move-level detail on which competence is *non*-monotone, retaining a coarse `Out` on which it *is*
monotone.** That is the theory-of-abstraction characterization the principal wanted:

> **Thesis (Vingean abstraction — INTERPRETATION).** *A phenomenon is rationally regarded as
> Vingean-agentic at abstraction level `α` iff `α` is the coarsest abstraction on which the
> phenomenon's behavior is Blackwell-monotone (value-of-information ≥ 0) relative to the observer's
> own experiment.* Predict the outcome, not the move; trust on the general principle that
> information has nonnegative value *for the coarse variable*.

### 2.4 Connection to condensation (and a counterexample to a too-strong version)

`agency-as-condensation.md` defines agency as a latent `Π` with `H(A_i | Π, O_i)=0`. Vingean
agency *weakens* this: the observer does **not** have `Π` (cannot resolve the policy — that is (V1)),
but has a *coarsening* of `Π`'s effects, namely `α∘behavior`. So:

> **CONJECTURE.** Vingean agency = possession of a **condensation of the agent's outcome variable
> `α(A)` but not of its policy latent `Π`**. Formally: `H(α(A) | E_obs)` small while
> `H(A | E_obs)` large, with the gap explained by a latent `Π` the observer has only at the `α`
> resolution. This is "condensation at the outcome abstraction, not the action abstraction." It
> predicts the intentional stance is *graded by how coarse an `α` you need*: the airport friend
> needs only `α = arrived?`; a grandmaster studied move-by-move would need finer `α`.

**Counterexample / failure mode (important).** This can be *spuriously* satisfied by a
**non-agent**: a thermostat makes `α = room-temperature-stays-≈20°C` predictable while
`α = exact-duty-cycle-waveform` is not. So coarse-predictable + fine-unpredictable is **necessary
but not sufficient** for agency. The missing ingredient is the **Blackwell-monotonicity across a
*family of menus*** (V2/A): a thermostat's "competence" does not survive changing the menu (put it
in a room with a window it cannot model and the outcome abstraction stops being predictable), whereas
a chess master's does. **Vingean agency is robustness of outcome-predictability under menu variation
— the universal quantifier over decision problems is doing the work, just as in DDB's `∀`-menu
Value.** This matches `daniel-h-challenge.md`'s "fairness = depends only on what the agent *does*,
across problems." SKETCHED.

---

## Part 3 — The "size problem": asymmetric modeling, recursion, and whether LI fixes it

### 3.0 The two distinct problems hiding in the principal's worry

The principal flags that DDB/Managing-Misalignment model principal and agent **asymmetrically** (the
principal's beliefs are *given*; the agent's are *uncertain over a finite set*), and worries about
(a) recursive modeling of *each other*, and (b) recursive modeling of *themselves*
(self-referential `G = "P_A(G) < ½"`). These are **two different size problems** and LI treats them
very differently. Separating them is the contribution.

### 3.1 Problem (b), self-reference: LI genuinely fixes it; this is already v2's spine

v2 §5.2 / §0.3 is exactly the resolution of (b): the random-variable trick (beliefs-about-beliefs as
events) is *consistent with perfect self-knowledge*, which Gödel's diagonal lemma forbids under
modest conditions; LI's **soft** Self-Trust (Thm 4.12.4) is the surviving weakening, and the **hard**
version is *permanently false* (the liar `χ`). So for (b) the answer is: **the finite frame's
implicit perfect-self-knowledge is the size problem, and LI dissolves it by ranging over a continuum
of consistent completions with a never-closing soft/hard gap.** This is well-covered by v2 and by the
impossibility-thread agent; I only note the *typing* point that makes it lateral-relevant:

> **Observation (INTERPRETATION).** The asymmetry "principal given, agent uncertain" is the
> *non-dependent* `(S,A)→A` typing again (Part 1): it fixes one belief object and quantifies over a
> *flat finite set* of the other. A self-referential `G` requires the action/belief menu to **depend
> on the belief state itself** — a fixed point in the family `Act`, i.e. a dependent type whose index
> appears in its own fiber. *The size problem and the dependent-type problem are the same problem.*
> Perfect self-knowledge = assuming the Π-type has no nontrivial fixed points; diagonalization
> exhibits one. **This is the §1↔§3 internal bridge.**

### 3.2 Problem (a), mutual recursion: LI does NOT obviously fix it — and here is the breakage

This is the genuinely open corner, and the place to be careful. The principal asks: what breaks when
principal and agent *recursively model each other*? The asymmetric DDB model has the novice `π` model
the expert `P`, but `P` does **not** model `π` back. Make it symmetric and you get a **regress**:
`π` models `P` modeling `π` modeling `P`…. In finite frames this is the classic **common-knowledge /
Aumann** regress that Dorst flags (AGENDA: "impacting the theory of common knowledge, Aumann's
agreement theorem").

**What breaks (SKETCHED, with a concrete failure):**

> **The two-inductor reflexivity gap.** Suppose novice `N` and expert `M` are *both* logical
> inductors, and we want `N` to LUV-Total-Trust `M` *and* `M` to LUV-Total-Trust `N` (mutual
> deference). v2 §10.4 already says cross-agent LUV-Total-Trust is **not free** (unlike the
> self-directed case, which is `thm:ccee`). I claim mutual trust is *strictly harder than the sum of
> two one-way trusts*, because of a **diagonalization against the pair**: let `M`'s estimate query
> `N`'s future price of `χ_M = "𝔼^N_{later}(χ_M) < ½"` and vice versa. Each one-way soft Self-Trust
> survives (v2 §5.2), but the *joint* hard system `{N trusts M, M trusts N}` instantiated on the
> mutually-referential pair `(χ_M, χ_N)` is a **2×2 liar** with no consistent hard fixed point. The
> soft versions each hold individually; whether they hold *simultaneously with the same `δ_n→0`
> schedule* is **open** and is, I conjecture, the real content of "the size problem."

> **CONJECTURE (size problem = no joint immodesty, restated).** On any *finite* frame, mutual
> soft-conditional-martingale between two experts forces *both* immodest (by applying v2 §5.2 /
> `CM_implies_immodest` in each direction), hence a *common partition* (S5 on both), hence — by a
> two-sided version of the §5.2 collapse — **the two agents share a single information partition**:
> they have *merged into one agent*. So in finite frames "two agents recursively modeling each other
> with clean mutual trust" **collapses the agent count from 2 to 1**. That collapse *is* the size
> problem: the finite model cannot host two genuinely distinct mutually-trusting modest reasoners.
> LI evades the collapse the same way it evades §5.2 — by living on an infinite self-referential
> frame — **but** whether two *distinct* inductors can mutually-trust without merging is exactly the
> Eisenstat-merge question (Q4/Q5) seen from the other side: *the merge succeeds precisely when the
> collapse is benign (B_t is a new inductor) rather than paradoxical.*

This reframes the merge thread: **the Eisenstat construction is the controlled, asymmetric (one-way,
fast/slow) version of a mutual recursion that, if made symmetric, would either collapse (finite) or
diagonalize (hard LI).** The asymmetry `f(t)` (ask AI about the *future* human) is not a convenience
— it is what *breaks the symmetry of the regress* and lets `B_t` exist. **SKETCHED / CONJECTURE.**
This is a non-obvious gift to the merge agent: it explains *why the deferral function must point
one way*.

### 3.3 What LI does and does not buy for (a)

- **Buys:** no perfect self-knowledge ⇒ no immediate Gödel collapse for *one* agent modeling the
  other (Part 3.1). Observability (market-generability) is the LI stand-in for "can model."
- **Does not buy:** symmetric mutual trust is not free and may be unsatisfiable in the *hard* joint
  form; the *soft* joint form's consistency is open (§3.2). So the asymmetric DDB modeling is **not**
  an artifact to be casually symmetrized — the asymmetry is load-bearing, and LI inherits that.

---

## Part 4 — Wildcard cross-connections (≥3, chosen to be non-obvious)

Each connects **two** agenda threads the per-thread agents are unlikely to put together.

### W1. Legitimacy = the Blackwell-monotone abstraction `α` of Part 2 (connects *Agency&Abstraction* ↔ *Legitimacy/Corrigibility*)

**The link.** `meaning-and-agency-reference.md`: *legitimacy is to endorsement as good is to
utility*; a process is legitimate if it is *truth-tracking*. Part 2: Vingean agency is competence
that is **Blackwell-monotone on the abstraction `α`** (more information never hurts the coarse
outcome). Put them together:

> **CONJECTURE (legitimacy = monotone abstraction).** A belief-formation process `Π` is
> *legitimate-to-`H`* iff there is an abstraction `α` (e.g. `α = `gets-the-answer-right) on which `H`
> sees `Π` as Blackwell-monotone — i.e. running `Π` *longer / with more information* never lowers
> `H`'s expected `α`-value. **Wireheading is illegitimate precisely because it is
> Blackwell-NON-monotone:** more "information" (more reward signal) *lowers* the truth-tracking
> abstraction `α = accuracy-about-the-world`, even as it raises a different abstraction
> `α' = reported-reward`. Legitimacy is endorsement *of the right `α`*; reward-hacking is endorsement
> of `α'` over `α`.

This gives the legitimacy/corrigibility agent a **formal handle**: the drug-avoidance analogy ("don't
endorse a future addicted self") is exactly "the addiction process is Blackwell-monotone for
`α' = pleasure` but anti-monotone for `α = accurate-values`, and `H` endorses `α` not `α'`." The
*choice of `α`* is where human values enter — connecting to the principal's Geometric-UDT conjecture
(updateful about values/`α`, updateless about the rest). **CONJECTURE.** Genuinely lateral because
the legitimacy agent works in endorsement language and the abstraction agent in Blackwell language;
they don't obviously meet.

### W2. The deferral function `f` is the *temperature* of a Vingean trust thermometer (connects *Fast-Student/Slow-Teacher* ↔ *Agency&Abstraction* ↔ the softmax in v2 §3)

**The link.** v2 §3 softens argmax with temperature `δ_n → 0` (softmax selection `α^j_n`). Separately,
the deferral function `f(n) > n` controls *how much more thought* the trusted self has. Both are
"how far ahead do I trust." Wildcard observation:

> **INTERPRETATION.** There are **two independent knobs of Vingean trust** in the v2 proof, and they
> trade off: (i) the *temperature* `δ_n` (how sharply I commit to the future self's argmax) and (ii)
> the *deferral horizon* `f(n)` (how much more competent the future self is). The proof needs
> `δ_n log k → 0` (commit sharply) *and* `f(n) > n` (genuinely more informed). **Conjecture: there is
> a joint schedule `(δ_n, f(n))` for which Value holds at an explicit finite-horizon rate**, and the
> rate degrades gracefully as either knob is loosened — a *quantitative* Vingean trust bound. This is
> the §8 "quantitative version" open problem, but the lateral content is *which two quantities trade
> off*: **sharpness of deference vs. competence gap.** In the Eisenstat merge, `f(t)` is the
> competence gap (slow human's future) and the implicit temperature is how literally `B_t` takes the
> AI's report — so the merge has the *same two knobs*, and "f grows fast enough" (Sam's condition) is
> the `f`-knob while "good feedback" is the `δ`-knob (sharpness of `A`'s commitment to `H`'s
> verdict). **This re-reads Sam's two hypotheses as the two trust knobs of the deference proof.**
> CONJECTURE/INTERPRETATION.

### W3. Improbable actions (Cole Wyeth) ↔ the soft/hard split (v2 §5.2): the chicken rule is a *temperature floor* (connects *Unbounded Embedded Agency* ↔ *LI Self-Trust*)

**The link.** AGENDA "Improbable Actions": an agent confident of its source code must assign tiny
probability to un-taken actions, and reasoning about them needs "contrived worlds"; the **chicken
rule** ("if you prove you won't do `a`, do `a`") forces action probabilities positive. v2 §5.2: the
**hard** conditional martingale is false (liar), only the **soft** (`Ind_δ`, `δ > 0`) version holds;
the gap "never closes."

> **INTERPRETATION (non-obvious).** The chicken rule and the LI softening `δ_n > 0` are the **same
> device**: both forbid the agent from being *hard*-certain about its own future/own action, by
> keeping a positive floor (`δ` of probability, or the chicken-rule's forced positive action
> probability) under the self-referential event. "Improbable actions need contrived worlds" is
> exactly "*hard* conditioning on a measure-zero self-prediction is paradox-prone (Bentham's null
> tail, v2 §6 / the liar)." So **Cole's improbable-action problem is the reflective-oracle
> instantiation of the false-hard/true-soft split**, and the fix is structurally identical: never
> hard-condition on your own self-model; keep `δ > 0` / keep the chicken-rule floor. **The deferral
> function `f` is even the analogue of "the future self is genuinely larger" — the very property that
> Cole's `(1−δ)`-self-knowledge assumption *destroys* (AGENDA: it rules out self-modification).**

> **CONJECTURE (sharp prediction for the Cole agent).** A reflective-oracle agent that conditions on
> its own future actions *hardly* (probability-0 actions truly excluded) will exhibit Troll-Bridge /
> spurious-proof pathologies; an agent that conditions *softly* (every action floored at `δ_t > 0`,
> `δ_t → 0`) will satisfy an LI-style soft Self-Trust and *avoid* them — and the cost is exactly v2's
> cost: it can never be *certain* of its own decision procedure, which is **precisely the
> self-knowledge the principal flags as the bad assumption**. So *fixing Cole's self-knowledge
> problem and adopting LI's soft conditioning are the same move.* This hands the Cole-thread agent a
> concrete bridge: replace "`(1−δ)`-believes its source code" with "soft-conditions on its future
> behavior at floor `δ`," and the optimality result becomes a Vingean/tiling statement rather than a
> self-knowledge statement — sidestepping the AGENDA's complaint that self-knowledge rules out
> self-modification. CONJECTURE.

### W4 (bonus). The intentional stance is a *coarse* logical inductor (connects *Agency&Abstraction* ↔ *the size problem* ↔ *merging inductors*)

**The link.** Part 2: the observer predicts `α(Act)` not `Act`. Part 3: an observer cannot host a
full model of a more-competent agent (size problem). LI: a market-generable coarsening of prices is
itself a price stream.

> **CONJECTURE.** When observer `N` (an inductor) regards `M` as agentic at abstraction `α`, the
> sequence `B^α_t(φ) := 𝔼^N_t(⌜α(M's verdict on φ)⌝)` — `N`'s estimate of `M`'s *coarse* output — is
> itself (a fragment of) a logical inductor *on the `α`-coarsened sublanguage*, even though `N`
> cannot host `M`'s full price stream. **This is the Eisenstat `B_t` construction with `α` in place
> of `f`:** instead of asking the AI about the *future* human (temporal coarsening), ask the observer
> about the *outcome abstraction* of the agent (semantic coarsening). Both produce a trustworthy
> derived inductor by *throwing away resolution the truster cannot or need not host*. **The
> intentional stance, the merge construction, and the size-problem evasion are one operation:
> coarsen-then-trust.** This is the deepest cross-connection I found, and it suggests the
> Eisenstat-merge agent and a future agency-as-abstraction model are studying *the same theorem at
> different coarsenings* (temporal `f` vs. semantic `α`). CONJECTURE — and a candidate unifying frame
> for the whole lab.

---

## Summary of statuses and the single most checkable thing

| # | Claim | Status |
|---|---|---|
| 1.1 | Decision procedure = `Π (s:State), Act s` (dependent/Π-type); generalizes `(S,A)→A` | PROVED-trivial (type theory) / INTERPRETATION for the DT reading |
| 1.2 | WAR-optimal ⇔ control-endorsed by own induced prior (dissolves "rich by whose measure?") | INTERPRETATION (well-argued) |
| 1.3 | Systematized winning = one-step tiling = control-endorsement fixed point | INTERPRETATION |
| 1.4 | "germ-UDT": condition on the stalk; sheaf/locality on `State` | CONJECTURE |
| 1.5 | Algebraic shadow: CM-defect=0 ⇒ WAR (diagonal ≥ every fixed option) | candidate Lean, UNCHECKED |
| 2.2 | Vingean agency = quantified Blackwell dominance on an abstraction `α` | SKETCHED |
| 2.3 | Agency at `α` = `α` is coarsest Blackwell-monotone abstraction | INTERPRETATION |
| 2.4 | Vingean = condensation of `α(A)` not of `Π`; thermostat counterexample ⇒ need menu-robustness | CONJECTURE + counterexample |
| 3.1 | Size problem (self) = dependent-type fixed point = perfect self-knowledge failure | INTERPRETATION |
| 3.2 | Mutual hard trust = 2×2 liar; finite mutual soft-CM ⇒ both immodest ⇒ agents merge | SKETCHED + CONJECTURE |
| 3.3 | Asymmetry of `f` is load-bearing; symmetrizing breaks | SKETCHED |
| W1 | Legitimacy = Blackwell-monotone abstraction; wireheading = anti-monotone | CONJECTURE |
| W2 | Two trust knobs (temperature `δ`, horizon `f`); Sam's two hypotheses are these knobs | INTERPRETATION/CONJECTURE |
| W3 | Chicken rule = LI soft floor; Cole's self-knowledge problem = false-hard/true-soft | CONJECTURE |
| W4 | Intentional stance = coarse inductor; merge & stance & size-evasion = "coarsen-then-trust" | CONJECTURE |

**Most checkable:** the §1.5 algebraic kernel (it sits on the confirmed `Deference.value_of_CM`
backbone). Everything in Parts 2–4 is a *modeling/bridge* contribution, not yet a Lean target; the
Blackwell-monotonicity content of Part 2 (a finite value-of-information ≥ 0 lemma) is the
**second**-most plausible Lean target and is flagged for a future modeling agent — it would also
discharge orientation Q6.

**Single biggest red-flag to hand the verifier:** my §1.5 Lean must NOT smuggle WAR-optimality into
its hypotheses. The danger is stating "no fixed option beats the policy" as both hypothesis and
conclusion. The file is written so the hypothesis is *only* `CM-defect = 0` (a martingale condition,
provably the LI content) plus hard argmax, and the conclusion is the *inequality* `diagonal ≥
fixed-option`. I argue in the file this is non-vacuous (it fails when CM-defect ≠ 0, exactly DDB
Fig. 2 / v2 §1.3 anti-expert), so it is not a disguised `True`.
