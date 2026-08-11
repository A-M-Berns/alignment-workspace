# Updatelessness & Deference — Ideation

*Thread: "Updatelessness & deference" (AGENDA "Deference Done Better, Done Better →
Updatelessness"; orientation Q8). Goal: find an **endorsement-LIKE** concept that characterizes
"the updates a UDT-like agent will happily defer to". Every claim flagged
**PROVED / SKETCHED / CONJECTURE / INTERPRETATION**, matching v2 discipline. Cross-connected to v2
§10 modularization and to `udt-representation-theorem/` (control-endorsement, superconditioning).*

---

## 0. The problem, stated sharply

Updateful endorsement⇔deference (DDB Thm 2.2; ported to LI in v2) rests on a hidden assumption:
that "what `A` would believe if it learned `R`" is the **Bayesian update** `P_A(·∣R)`
(AGENDA/Reflection gloss; v2 §0.4). The updateless agent breaks this assumption at the root: it
does **not** treat its observation as a *fact about the world to condition on*; it conditions on
**"my policy maps this observation to this action"** (`when-udt-edt-diverge.md`;
`formal-single-agent.md`). So a "more-knowledgeable future self" that has Bayes-updated is **not**
automatically someone the prior should hand the wheel to: it may two-box a transparent Newcomb,
refuse a counterfactual mugging, defect a Twin PD — all cases where the updated posterior is
*epistemically* better (more accurate about the realized branch) yet *instrumentally* worse from
the prior's seat (`when-udt-edt-diverge.md` §"Cross-Situation Dependence").

So endorsement is **neither necessary nor sufficient** for updateless deference:

- **Not sufficient.** `A`'s prior can endorse (in the van-Fraassen sense) the posterior `P_A(·∣R)`
  — the posterior *is* truth-tracking on branch `R` — and yet refuse to defer, because deferring to
  the *posterior's* choice loses the acausal payoff. (Counterfactual mugging: the heads-self's
  posterior is perfectly accurate; UDT still won't defer to it.)
- **Not necessary.** UDT happily accepts genuine *improvements* (better empirical estimates, fixed
  logical facts) that are not its exact prior — so "defers only to its own prior" is false too
  (AGENDA: "there are real improvements which UDT will accept").

We want the in-between object. **Working name: `endorsement⊕` ("policy-respecting endorsement").**
The candidate unifying slogan, which the ideas below try to make precise from several angles:

> **`A` defers to an update `u` iff `u` is endorsed by `A`'s prior *as a refinement of the global
> policy's information*, not as a fact to act on at the node.** Equivalently: the prior would have
> *pre-committed* to letting the `u`-informed self choose, evaluated updatelessly.

---

## 1. Idea A — **Policy-respecting endorsement** = control-endorsement of the updated self

**CONJECTURE (central; the "endorsement-like concept").**
Let a prior `P` define a UDT agent over situations `S` (observations), action set `A`, utility
`U : Ω × policies → ℝ`. An *update* is a map `u` sending each situation `s` to a refined credence
`P^u_s` (radical-probabilist: `u` need not be Bayesian conditioning, no evidence index — cf.
`radical-probabilist-udt.md`). Say **`P` policy-endorses `u`** iff the policy

  `π_u(s) := argmax_a E_{P^u_s}[ U ∣ "policy maps s to a" ]`     (UDT formula *with the updated
  belief plugged into the global expectation*)

is **control-endorsed by `P`** in the sense of `agency-via-endorsement.md`:
`π_u = argmax_{π} E_P[ U(π, B, Ξ) ]`. That is, the updated agent's *whole policy* is one the prior
would itself have chosen updatelessly.

**Claim:** *UDT defers to `u` iff `P` policy-endorses `u`.* Endorsement-of-beliefs (van Fraassen) is
the **special case** where the situations are decoupled (no cross-situation dependence): there the
local-posterior-argmax already lands on the global optimum (this is exactly the
`when-udt-edt-diverge.md` "no cross-situation dependence ⇒ EDT = UDT" theorem). So `endorsement⊕`
*restricts to* ordinary endorsement on the value-only / decoupled coordinate, and *diverges* from it
precisely on the acausally-coupled coordinate — which is the structure we wanted.

**Why it bears on human-trustable AI.** This is the precise statement of *when a principal can let a
more-informed AI act on freshly-acquired information*: not "whenever the principal would believe what
the AI believes" (that licenses the AI to blow acausal/commitment situations), but "whenever the
information leaves the principal's *pre-committed global policy* a best response." It tells you which
new knowledge an AI may safely use *updatefully* (the principal control-endorses the resulting
policy) versus which it must handle *updatelessly* (honor the prior commitment despite knowing more).

**Cleanest formal setting.** The `udt-representation-theorem/` condensation model
(`agency-via-endorsement.md` Full Control Endorsement, eq. line 217) already has the exact operator.
The work is: define `π_u` and prove the biconditional. The forward direction (defer ⇒ control-
endorsed) is near-definitional given the representation theorem (UDT policy = control-endorsed
policy, already Lean-verified in `udt-representation-theorem/lean/`). The reverse needs that
control-endorsement of `π_u` implies node-by-node the agent is content to act on `u`.

**Hardness.** Medium. The hard part is honestly stating "defers to `u`" *independently* of the
endorsement object (else circular, the exact trap flagged in `formal-single-agent.md` "What's
Non-Trivial"). Proposed independent definition of "defers": `A` is *willing to be replaced by* the
`u`-informed self in every menu, i.e. a **Value-style** inequality `E_P(diagonal of π_u) ≥ E_P(O)`
for every option `O` — this is literally DDB Value with the "expert" = the updated self. That makes
the biconditional a genuine **updateless Total-Trust ⇔ Value** statement, paralleling v2.

---

## 2. Idea B — **Calibrated anticipation = the no-evidence-index bridge** (superconditioning)

This is the idea the task explicitly gestures at ("superconditioning may bridge endorsement (no
evidence index) to updates"). It is the most *ready-to-formalize* and I think the **most promising**.

**Setting (TRUSTED machinery).** `superconditioning-mismatched-ontologies.md` §3 gives, with full
proofs, an **anticipation structure** `(Ā, κ)` on a prior `P`: a sub-algebra `Ā ⊆ P̄` of
"distinguishable future belief states" plus an *intended kernel* `κ_ā` = "the beliefs I expect to
hold in anticipation-state `ā`." Crucially **there is no evidence index** — anticipation states are
not events-conditioned-on, they are *self-predicted future credences*. Two graded conditions:

- **Reflection (Def 3.7):** prior-predictive `= prior`, `∑_ā κ_ā · P(ā) = P`. (van-Fraassen
  reflection in radical-probabilist dress.)
- **Calibration (Def 3.5):** `P(· ∣ ā) = κ_ā` for every atom `ā`. **Strictly stronger** than
  reflection (Prop 3.8, with explicit 4-atom counterexample, PROVED there).

**CANDIDATE DEFINITION (`endorsement⊕` via anticipation).**

> An update `u` (taking `P` to `P^u`) is **`A`-deferrable** iff `P^u = κ_{ā₀}` for some atom `ā₀` of
> a **calibrated** anticipation structure on `P` — i.e. `u` lands `A` in a future credence `A`
> *already anticipated, and anticipated correctly*. (This is exactly Def 12.1
> "epistemically coherent pair" in the heterogeneous-UDT section, PROVED to be a calibrated
> refinement model.)

**SKETCHED PROPOSITION (the bridge theorem).** *Endorsement is calibration-of-a-degenerate-
anticipation; deferrable-updates are calibration-of-a-genuine-anticipation.* Precisely: when the
anticipation sub-algebra `Ā` is the **full** algebra `P̄` (the agent anticipates every world as its
own belief state — maximal self-knowledge), calibration `P(·∣ā)=κ_ā` collapses to van-Fraassen
endorsement / the S5 partition (each `ā` a singleton, `κ_ā = δ`). When `Ā` is **coarse** (the agent
anticipates only *bands* of future belief — modesty), calibration permits a *family* of admissible
updates none of which is the exact prior, yet all reflection-coherent. **This is the generalization
of endorsement we sought**, with a **dial** (`Ā`'s granularity) interpolating from "defers only to
self" (full `Ā`) to a permissive class.

**Cross-connect to v2 §5.2 (PROVED).** This dovetails *exactly* with finite collapse. v2 §5.2:
soft-conditional-martingale on a **finite gapped** frame ⇒ immodesty ⇒ the S5 partition. Here:
calibration on a **full** `Ā` ⇒ the same S5 partition / endorsement. So the granularity of `Ā` is
the *updateless analog* of the soft/hard split: a **coarse** `Ā` (modesty about your own future
verdicts) is what makes room for non-trivial deferrable updates, mirroring how the permanent
soft/hard gap is "the home of modesty." **This is a genuine cross-thread unification** of the
updateless picture with the LI finite-collapse picture, and I'd build it out first.

**Why it bears on trust.** Gives an operational test a principal can apply *before* deployment: an
AI's proposed belief-update is trustworthy iff it lands in a state the principal's prior already
anticipated as a calibrated future of itself. Wireheading / manipulation updates fail this — they
are *not* in any calibrated anticipation of the original values (connects to the legitimacy thread,
Q11): the addiction-posterior is a future belief the prior anticipates but does **not** calibrate
to (it does not endorse `κ` = "I'll value the drug"). So calibration cleanly separates *legitimate
learning* (deferrable) from *value-corruption* (not), which is the AGENDA's stated payoff for
legitimacy.

**Hardness.** Low-to-medium and **Lean-adjacent**: the same-ontology calibration/reflection facts
(Prop 3.8, 4.2) are small finite measure-theory and could be Lean'd; the *bridge* (full-`Ā`
calibration = endorsement = S5) is an elementary atom-counting argument. Most promising because the
scaffolding is already TRUSTED and the dial is conceptually exactly "more updateful about X, more
updateless about Y."

---

## 3. Idea C — **Geometric-UDT split as a utility-coordinate decomposition** (LEAN-candidate)

**Setting.** Formalize the principal's Geometric-UDT conjecture ("more updateful about moral
uncertainty / values, more updateless about other matters") as a **separability** statement on the
utility, reusing the v2 §3 `decomposition` algebra.

**CANDIDATE (PROVED, modulo Lean-verify — see `lean/UpdatelessDeference.lean`).** Decompose the
agent's uncertainty into coordinates. A coordinate is a **values coordinate** iff utility there is
*separable across situations* — `U(s,a)` with no dependence on actions at other situations (learning
a value fact re-weights outcomes but does not couple your copies' choices). On such a coordinate,
the global (updateless/UDT) optimum **equals** the situation-by-situation (updateful/EDT) optimum:

  `max_π ∑_s p(s) U(s, π(s)) = ∑_s p(s) max_a U(s,a)`.

(This is the `when-udt-edt-diverge.md` "no cross-situation dependence ⇒ EDT=UDT" theorem; the Lean
file proves the load-bearing half: split optimum dominates every policy AND is achieved.) **Reading:
on the values coordinate, updateful and updateless reasoning coincide, so the agent can safely be
fully updateful about values** — which is precisely the Geometric-UDT recommendation. Cross-situation
coupling (hence the endorsement⇔deference gap) lives *entirely* in the complementary, non-values
coordinate.

**INTERPRETATION (the conjecture proper).** Geometric UDT = choose the updateful/updateless split to
**match the separable/coupled decomposition of `U`**. Be updateful exactly on the separable
("values") sub-`σ`-algebra and updateless on its coupled complement. The above makes this a
*consistent* prescription (no Dutch book / no regret from being updateful on the separable part).

**Why it bears on trust.** This is the formal skeleton of "an aligned AI should be (almost) fully
updateful about human values": value-learning is the coordinate where there is no acausal trap, so
deferring to a more-value-informed AI is safe *for the same reason ordinary endorsement works there*.
It carves out the safe region for updateful deference.

**Hardness.** The decomposition direction is **easy and Lean-stated now** (file written). The
converse (coupling ⇒ genuine divergence, non-vacuity) is a small witness (Newcomb). The
*interpretation* (that human-values uncertainty really is separable) is a substantive modeling
CONJECTURE — likely false in full generality (values can couple across copies via e.g.
population-ethics aggregation), and that failure is itself worth surfacing as the boundary of the
"fully updateful about values" slogan.

**Lean candidate:** `lean/UpdatelessDeference.lean` — `split_eq_global` (split optimum dominates
every policy; needs `p ≥ 0`) and `split_achieved` (the bound is hit by a local-argmax policy).
UNCHECKED; faithful-hypothesis analysis in the file header. *Caveat:* it proves only the **decoupled
boundary fact**, which is the trivial-but-correct half; the open content is the coupled case.

---

## 4. Idea D — **UDT1.0-believes-it's-UDT1.1 as updateless self-trust** (Cole thread cross-link)

**Setting.** AGENDA "Updatelessness"/Unbounded Embedded Agency (orientation Q9): *if a UDT1.0 agent
`(1−δ)`-believes its policy is UDT1.1, it is `ε(δ)`-optimal.* UDT1.0 picks single actions; UDT1.1
picks the whole policy and is optimal by construction. Belief-that-you're-UDT1.1 is exactly the
self-model that lets local (updateful-ish) action choices inherit global optimality — replacing
Cole's hand-built reflective oracle.

**CONJECTURE (the cross-link to this thread).** Belief-that-you're-UDT1.1 **is the self-directed
instance of `endorsement⊕`**: it is precisely "the prior policy-endorses (Idea A) its own future
node-decisions." Concretely: UDT1.0's per-node argmax is control-endorsed by the prior **iff** the
prior assigns high credence that the node-decisions assemble into the UDT1.1 (globally optimal)
policy. So Cole's optimality hypothesis and the updateless-deference object are the *same condition*
viewed from two ends — self-trust (defer to your own future node-self) is `endorsement⊕` with
expert = future self, just as v2's LI self-trust is DDB Total-Trust with expert = future self.

**Why it bears on trust.** Makes "tiling" / reflective-consistency a *special case* of the human-AI
deference question: the agent trusts its own future updateful self exactly under the updateless-
deference condition. If true, the single object `endorsement⊕` governs both self-trust (Q9) and
cross-agent trust (Q4/Q5), unifying the agenda's two registers.

**Hardness.** Medium-high; lives in the reflective-oracle apparatus
(`internal-fixpoint/reflective-oracles-project/`), and the AGENDA flags the self-knowledge
assumption as suspect (rules out self-modification). Pin first: separate self-knowledge from
environmental modification (orientation Q9). Not Lean-ready. Valuable as a *unification claim*, not a
near-term proof.

---

## 5. Idea E — **The acausal-failure menu as a non-Euclidean modal gap** (red-team / structural)

**CANDIDATE (INTERPRETATION → theorem).** Reuse v2's modal picture (§5.3: S5 immodest vs. S4
modest). The updateful endorsement⇔deference equivalence is the **S5/partition** case. The acausal
counterexamples (counterfactual mugging, transparent Newcomb) are exactly the configurations where
the *information partition is not common knowledge in the right way* — the agent's
"learning `R`" event is **not biconvex** / not a partition cell from the prior's decision-relevant
standpoint, because the prior's payoff depends on the counterfactual branch the posterior has
discarded. Conjecture: **endorsement⇔deference holds updatelessly iff the update `u` refines the
prior by a partition that is "decision-flat"** (the v2 biconvex/`Ā`-compatible condition of §4.6 in
superconditioning), and the acausal failures are precisely the non-decision-flat refinements.

**Why it bears on trust.** Pinpoints the *geometric* signature of "an update an AI may act on
updatefully": decision-flat refinements (those whose cells don't cross a payoff-relevant
counterfactual boundary). It would give a checkable property of an update, not just of a belief.

**Hardness.** Medium; it's a re-import of DDB's biconvex/Geanakoplos machinery (v2 §1.1) into the
update-space. Risk (flag): "decision-flat" may turn out to *be* policy-endorsement (Idea A) in
disguise — if so, that's a welcome collapse (one concept, two descriptions), but it must be checked,
not assumed.

---

## 6. Idea F — **Deferrable-update characterization for LI's own future self** (ties to v2 §10)

**Setting.** Make the whole thread *concrete and computable* by instantiating in LI, leveraging
v2 §10. v2 §10.1–10.2 already isolates **the one expert-specific premise**: LUV-Total-Trust toward
the expert, `E_n(⌜X·w⌝) ≂_n E_n(⌜E_exp(X)·w⌝)`. For the **future self**, this is *free* (Thm 4.12.3
`ccee`). The updateless question becomes: **which "updates" (future estimates `E_{f(n)}`) does the
present self defer to?** In LI, deferral to the future self is automatic *because* `ccee` holds —
but `ccee` is a martingale, which is the LI shadow of **calibration/reflection** (Idea B)!

**CONJECTURE (the LI ⇄ updateless dictionary).**

> LI's conditional martingale `ccee` (the engine of v2's Value proof) **is** the
> logical-induction realization of "the future self is a calibrated anticipation of the present
> self." Hence in LI, the deferrable updates are *exactly* the future-self estimates, and the
> reason there is no acausal-mugging failure is that LI's `E_n` already **bundles** the selection
> weight `w` with the bet (the diagonal↔row-wise bridge, orientation §1) — i.e. LI deference is
> *natively policy-respecting* (Idea A), not node-local. LI dodges the endorsement⇔deference
> updateless gap **for free**, the same way it dodges the finite-collapse gap.

So §10's "LUV-Total-Trust toward an external expert" is the **updateless** generalization: trusting a
*different* inductor's update is the open characterization (v2 §10.4 = orientation Q5), and Idea B's
calibrated-anticipation condition is a candidate answer — *`N` deferrable-trusts `M`'s updates iff
`M`'s estimates are an `N`-calibrated anticipation* (market-generable `Ā` + reflection-coherence on
every generable weight). This **directly proposes a definition for the v2 §10.4 / Q5 open problem.**

**Why it bears on trust.** Connects the updateless characterization to the constructive LI agenda
(Eisenstat merge, Q4): the merged inductor `B_t` is deferrable-trusted by `H_t` iff it is an
`H`-calibrated anticipation, which is checkable via market-generability + a martingale condition.

**Hardness.** Medium; conceptual unification is SKETCHED-plausible, but the precise LI statement of
"calibrated anticipation" needs the soft-`Ind_δ` machinery (v2 §0.3) and is genuinely open. Best
pursued *after* Idea B fixes the radical-probabilist definition, then ported via the §10 dictionary.

---

## 7. Ranking and top pick

| Idea | object | formalizability | payoff | status |
|---|---|---|---|---|
| **B (calibrated anticipation)** | `endorsement⊕` via calibrated `Ā`-kernel | **high** (TRUSTED scaffolding, Lean-adjacent) | high (the dial; legitimacy split) | SKETCHED bridge thm |
| A (policy-endorsement) | control-endorse the updated policy | medium | high (the clean biconditional) | CONJECTURE |
| C (values-coordinate split) | separable ⇒ updateful=updateless | **highest** (Lean written) | medium (carves safe region) | PROVED boundary half (UNCHECKED Lean) |
| F (LI dictionary) | `ccee` = calibration; §10.4 answer | medium | high (ties to Q4/Q5) | CONJECTURE |
| D (UDT1.0⊨UDT1.1) | self-trust = `endorsement⊕`(self) | medium-high | high (unifies Q9) | CONJECTURE |
| E (decision-flat refinements) | biconvex update geometry | medium | medium (checkable property) | INTERPRETATION |

**TOP PICK: Idea B — `endorsement⊕` as calibrated anticipation.** It is the literal cash-out of the
task's "superconditioning bridges endorsement (no evidence index) to updates": the anticipation
structure carries **no evidence index** (atoms are self-predicted credences, not conditioned
events), calibration *is* the reflection/endorsement condition in that index-free language, and the
**granularity of the anticipation sub-algebra `Ā` is an explicit dial** interpolating from "defers
only to its exact self" (full `Ā` = S5 = van-Fraassen endorsement) to a permissive deferrable class
(coarse `Ā` = modesty). That dial is *exactly* the Geometric-UDT intuition ("more updateful about
some coordinates, more updateless about others") made into a tunable mathematical object, and it
**cross-connects cleanly to v2 §5.2** (full-`Ā` calibration reproduces the S5/immodesty collapse,
so `Ā`-coarseness is the updateless twin of the soft/hard modesty gap) and to the legitimacy thread
(wireheading updates fail calibration). The scaffolding (`superconditioning-mismatched-ontologies.md`
§§3–4, 12) is already **TRUSTED with proofs**, the bridge theorem is elementary atom-counting, and
the same-ontology calibration facts are small enough to attempt in Lean. Develop B first, use it to
*define* the open object in A and F, then test the Geometric-UDT split (C) and the LI port (F).

**Most important caveat to flag:** the independent definition of "defers to `u`" must not be the
endorsement object itself (circularity trap, `formal-single-agent.md`). Idea A's proposed fix —
define "defers" as an **updateless Value inequality** (the prior would rather be replaced by the
`u`-informed self in every menu) — is what makes any of these a real **Total-Trust ⇔ Value**
biconditional rather than a definition restated. Pin that *first*.

---

## Cross-references

- v2 **§10** (deferring to non-self experts): supplies the modularization — one cross-agent premise
  (LUV-Total-Trust). Idea F proposes calibrated-anticipation as the answer to §10.4's open
  characterization (= orientation Q5).
- v2 **§5.2** (finite collapse, PROVED): full-`Ā` calibration ↔ S5/immodesty; coarse-`Ā` ↔ the
  modesty-preserving soft/hard gap. Idea B's dial is the updateless mirror of this.
- `udt-representation-theorem/agency-via-endorsement.md`: control-endorsement operator (Idea A);
  `radical-probabilist-udt.md`: no-evidence-index updates (Ideas A, B); `when-udt-edt-diverge.md`,
  `formal-single-agent.md`: the cross-situation-dependence decomposition (Idea C, Lean).
- `superconditioning-mismatched-ontologies.md` §§3–4, 12: TRUSTED calibration/anticipation
  machinery (Idea B), heterogeneous-UDT harmony/Pareto (latent in Idea A's multi-agent extension).
- Orientation **Q8** (this thread), **Q5** (cross-agent trust; Idea F), **Q9** (UDT1.0⊨UDT1.1;
  Idea D), **Q11** (legitimacy; Idea B's wireheading separation).
- Lean candidate: `lean/UpdatelessDeference.lean` (Idea C) — **UNCHECKED, for the Lean-verify
  agent.** Proves only the decoupled-coordinate boundary fact (updateful=updateless when utility is
  separable across situations).
