# Updateless Deference — A Toy Formal Model

*Thread: "Updatelessness & deference" (AGENDA §"Deference Done Better, Done Better →
Updatelessness"; orientation Q8). Develops the top pick of `findings/updateless-deference-ideate.md`
by **fusing Idea A's independent "defers" definition** (the circularity fix) **with Idea B's
calibration intuition**, into a single relation that classifies the canonical examples correctly.
Every claim flagged **PROVED / SKETCHED / CONJECTURE / INTERPRETATION**, matching v2 discipline.
Companion artifacts: `models/updateless_deference_check.py` (RUN, all cases pass),
`lean/updateless-deference.lean` (UNCHECKED candidate, for the Lean-verify agent).*

---

## 0. What we are after (recap, sharp)

The updateful equivalence **endorsement ⇔ deference** (DDB Thm 2.2; ported to LI in v2) rests on
reading "what `A` would believe upon learning `R`" as the Bayesian posterior `P_A(·|R)`. UDT breaks
this: it does not condition on the observation *as a fact to act on at the node*; it conditions on
*"my policy maps this observation to this action"* (`when-udt-edt-diverge.md`). Consequently a
more-knowledgeable, Bayes-updated future self is **not** automatically someone the prior should hand
the wheel to. We want a relation

> **`A` updatelessly-defers to `u`**

that (i) **reduces to ordinary endorsement** in the updateful / no-acausal case, (ii) **does NOT
hold** for the future self that caves to counterfactual mugging or two-boxes transparent Newcomb,
and (iii) **DOES hold** for genuine improvements UDT accepts. The central design hazard, flagged in
the ideation as the top caveat, is **circularity**: "defers" must be defined *independently* of the
endorsement object, or the biconditional is a tautology. We resolve this by taking **DDB Value,
evaluated in the global (updateless) expectation**, as the definition of "defers."

---

## 1. The model

### 1.1 Decision problem (the coupled, general form)

**Definition (multi-situation decision problem).** A tuple `(S, p, A, U)`:

- `S` — a finite set of **situations** (decision nodes the agent might face — times, copies,
  observations, or counterfactual branches; deliberately agnostic, per `formal-single-agent.md`).
- `p : S → ℝ≥0` — the **prior** over situations, `∑_s p(s) = 1`. (In acausal problems `p` ranges
  over branches that include ones the agent never consciously *acts* in — e.g. the tails branch of a
  mugging — but whose payoff is a function of the agent's policy. This is the crucial generality.)
- `A` — a finite **action set** (same at each node, WLOG).
- `U : (S → A) → ℝ` — utility of a **whole policy** `π : S → A`. This is the **general coupled
  form**: `U(π)` may depend on actions at situations other than the one realized — that dependence
  *is* cross-situation coupling (prediction, correlation, commitment, coordination; the four sources
  enumerated in `when-udt-edt-diverge.md`).

**Separable special case.** `U` is **separable** iff `U(π) = ∑_s p(s) · u(s, π(s))` for some
`u : S × A → ℝ` — the utility at `s` depends only on the action *at* `s`. This is exactly "no
cross-situation dependence." It is the updateful / no-acausal regime.

### 1.2 An update and the diagonal assembly

An **update** `u` is whatever causes the agent, at each node `s`, to adopt a refined local
valuation `vₛ : A → ℝ` (radical-probabilist: `u` need not be Bayesian conditioning, carries no
evidence index — cf. `radical-probabilist-udt.md`, and Idea B's anticipation-kernel `κ`). The
**`u`-informed self** then plays, at each node, its **local argmax**:

> `nodeChoice(s) := argmax_{a ∈ A} vₛ(a)`. (EDT-style: condition on being-at-`s`, optimize locally.)

Assembling these node-local picks gives the **diagonal assembly** policy

> `π_u(s) := nodeChoice(s)`   for all `s ∈ S`.

The name "diagonal" matches v2 §1.2: `π_u` is the policy whose action at each world is *the one the
informed self picks at that very world*. **Deference to `u` = letting `π_u` run instead of honoring
the prior's pre-committed policy.**

The decisive modeling point — and the honest subtlety (see §5) — is **what `vₛ` encodes about
coupling**. An update that *keeps* the cross-situation coupling inside `vₛ` (the informed self still
reckons its choice is correlated with the predictor / twin / its other copies) yields a different
`nodeChoice` than one that *discards* it (treats the predictor's box / the twin as a fixed fact to
condition on). The mugging-caver and the transparent-two-boxer are precisely **decoupling updates**.

### 1.3 The deference relation (independent definition — circularity fix)

**Definition (updateless deference; the central object).**
`A` (with prior `p`, utility `U`) **updatelessly-defers to `u`** iff the diagonal assembly `π_u` is a
**global maximizer of the updateless objective**:

> `U(π_u)  ≥  U(π)`  for every policy `π : S → A`. **(UD)**

Equivalently, in DDB's menu form: for the menu of all constant ("fixed-option") policies `O` and the
recommended strategy that delegates to the `u`-informed self, `E_p(diagonal) ≥ E_p(O)` for every
`O` — this is **DDB Value with the expert = the `u`-informed self, evaluated in the global
expectation `U(·)` rather than node-locally.**

**Why this dodges circularity (the top-flagged caveat).** "Defers" is here a *Value inequality*,
phrased purely in terms of `U` and the candidate policy `π_u`. It does **not** mention endorsement,
calibration, or any anticipation kernel. So a theorem of the form "`A` updatelessly-defers to `u` ⇔
[endorsement-like condition on `u`]" is a genuine **Total-Trust ⇔ Value** statement, not a
definitional restatement — exactly the structure of v2 and DDB Thm 2.2. (This is Idea A's proposed
fix, made the load-bearing definition; cf. `formal-single-agent.md` "What's Non-Trivial.")

> **INTERPRETATION.** (UD) says: *the prior would rather be replaced by the `u`-informed self, in
> every menu, than commit to any fixed option* — evaluated from the prior's updateless seat. It is
> the literal "would I pre-commit to letting the `u`-informed self choose?" test.

---

## 2. The reduction theorem (clause (i)) — **PROVED** (Lean candidate written)

**Theorem R (Reduction to ordinary endorsement).** *Suppose `U` is **separable**,
`U(π) = ∑_s p(s) u(s,π(s))`, with `p ≥ 0`. If the `u`-informed self plays a per-node argmax — i.e.
`u(s,a) ≤ u(s, nodeChoice(s))` for all `s,a` — then `A` updatelessly-defers to `u`:*
`U(π_u) ≥ U(π)` *for every policy `π`.*

**Status: PROVED.** Proof (the decomposition identity behind v2 §3 / `when-udt-edt-diverge.md`):
for any `π`,
`U(π) = ∑_s p(s) u(s,π(s)) ≤ ∑_s p(s) u(s, nodeChoice(s)) = U(π_u)`,
term-by-term, using `u(s,π(s)) ≤ u(s,nodeChoice(s))` and `p(s) ≥ 0`. ∎

**Reading.** When the utility carries **no cross-situation coupling**, the local-argmax assembly is
*automatically* a global optimum, so updateless deference **coincides with ordinary (van-Fraassen)
endorsement**: the prior defers to `u` exactly when it would adopt `u`'s node-local verdicts. This is
clause (i). It also reproduces the `when-udt-edt-diverge.md` slogan "no cross-situation dependence ⇒
EDT = UDT," now read as a *deference* statement. **Connection to Idea B's dial:** separability is the
coordinate on which the anticipation sub-algebra is trivially calibrated, so the dial sits at the
"defer to your updated self" end; coupling is where the dial must move toward updatelessness.

**Lean.** `lean/updateless-deference.lean`, theorems `defers_of_local_argmax` and
`endorsement_reduction`. Faithful-hypothesis analysis in the file header. The Lean encodes `U` with
the **decoupled type** `S → A → ℝ` (so separability is structural, not smuggled) and `nodeChoice` as
an *arbitrary* per-node argmax (so global optimality is the conclusion, not an assumption).
**UNCHECKED — for the Lean-verify agent.** It proves only this separable boundary fact (the
trivial-but-correct half); the coupled content is §3.

---

## 3. The discriminating examples — **PROVED (finite witnesses; checked in Python)**

All three run in `models/updateless_deference_check.py` (executed; output reproduced in the table).
For each, `U` is the explicit coupled policy-utility; the `u`-informed self's local valuation `vₛ`
is given; the script computes `π_u`, `U(π_u)`, and `max_π U(π)` by brute force, then tests **(UD)**.

| Example | `π_u` (informed self) | `U(π_u)` | global opt `U` | **(UD)?** | want |
|---|---|---|---|---|---|
| **Counterfactual mugging** | `refuse` | `0` | `4950` (`pay`) | **NO** | NO ✓ |
| **Transparent Newcomb** | `twobox` | `1000` | `1000000` (`onebox`) | **NO** | NO ✓ |
| **Benign empirical update** (separable) | `bet_H, bet_T` | `3.5` | `3.5` | **YES** | YES ✓ |
| Genuine improvement, ≠ prior default | `red` | `7` | `7` | **YES** | YES ✓ |
| Twin PD, update *reveals* mirror | `C` | `3` | `3` | **YES** | (acausal gain kept) ✓ |
| Twin PD, update *decouples* (defects) | `D` | `1` | `3` (`C`) | **NO** | NO ✓ |

**Counterfactual mugging (worked micro-example).** `S = {heads}` (the only node the agent *acts*
at), `A = {pay, refuse}`, fair coin. Whole-policy utility, prior 50/50 over the coin, tails payoff a
function of the heads-counterfactual (this is the coupling):

`U(π) = 0.5·(−100 if π(heads)=pay else 0) + 0.5·(10000 if π(heads)=pay else 0)`.

So `U(pay) = 0.5(−100) + 0.5(10000) = 4950`, `U(refuse) = 0`. The `u`-informed heads-self has
*learned the coin is heads*; its local valuation sees only the heads payoff (the tails branch is
causally/temporally gone): `v_heads(pay) = −100 < 0 = v_heads(refuse)`, so `nodeChoice = refuse`,
`π_u = refuse`, `U(π_u) = 0 < 4950`. **(UD) fails — `A` does NOT updatelessly-defer to the
mugging-caver.** ✓ (clause (ii)). The *reason* it fails is exactly that the heads-update **decoupled**
the tails payoff from the choice — it dropped a cross-situation term the prior cares about.

**Transparent Newcomb.** `S = {see_full}`, `A = {onebox, twobox}`; predictor fills the big box iff
the policy one-boxes. `U(onebox) = 1_000_000`, `U(twobox) = 1000`. The informed self *sees the full
box* and locally reasons "two-boxing nets a free extra $1k": `v(twobox)=1_001_000 > v(onebox)=1_000_000`,
so `π_u = twobox`, `U(π_u) = 1000 < 1_000_000`. **(UD) fails.** ✓ (clause (ii)).

**Benign empirical update.** Two independent situations, separable `U`, the update reveals each
coin's bias. `nodeChoice` = the locally-best bet at each node; by **Theorem R** this assembly is
globally optimal, so **(UD) holds**. ✓ (clause (i)/(iii)).

**Genuine improvement ≠ prior default (clause (iii), the sharp test).** `S = {bet}`, `A = {blue,red}`,
prior tie-broke to `blue` (value 5); the update reveals `red` pays 7 and (being on an orthogonal
coordinate) does not disturb any coupling. `π_u = red ≠ blue`, yet `U(red) = 7 = max`. **(UD) holds.**
This shows the relation is **not** the trivial "defer iff `u` agrees with what you'd have done by
default" — it accepts a real, policy-changing improvement. ✓

**Twin PD contrast (the cleanest illustration of the mechanism).** Same true game (twin mirrors you;
both-C = 3, both-D = 1). If the update *reveals the mirror*, `v(C)=3 > v(D)=1`, `π_u = C`, **(UD)
holds**. If the update *decouples* (treats the twin as a fixed cooperator, so defect dominates
locally), `v(D)=4 > v(C)=3`, `π_u = D`, `U(D)=1 < 3 = U(C)`, **(UD) fails**. The relation defers to
the coupling-preserving update and refuses the coupling-discarding one — **with identical true
payoffs**. This isolates the content: *deferrability is a property of whether `u`'s induced
node-choices preserve the prior's cross-situation couplings, not of the world.*

---

## 4. The UDT1.0 / UDT1.1 deference theorem schema — **CONJECTURE (schema PROVED-shaped, two gaps named)**

This connects the relation to AGENDA §"Updatelessness" / orientation Q9 (the Cole-Wyeth /
UDT1.0⊨UDT1.1 thread), per Idea D. **UDT1.1** chooses the whole policy at once: `π^{1.1} :=
argmax_π U(π)` (globally optimal by construction). **UDT1.0** chooses single actions node-by-node,
under a *self-model* — a belief `β` over "which policy generates my other nodes' actions."

**Definition (UDT1.0 under self-model `β`).** At node `s`, UDT1.0 plays
`a^{1.0}(s) := argmax_a E_β[ U | my-policy-maps-`s`-to-`a` ]`, where the expectation over the
*other* nodes' actions is taken under `β`.

**Theorem Schema (UDT1.0 deference).**
*Let `u` be the update "adopt self-model `β`." Then:*

> **(D0)** *If UDT1.0-under-`β` plays the diagonal assembly `π_u` with `π_u = π^{1.1}` (the global
> optimum), then `A` updatelessly-defers to `u` (by Def UD, trivially: `U(π_u) = max U`).*
>
> **(D1)** *Conversely, `A` updatelessly-defers to the update "be UDT1.0-under-`β`" **iff** `β`'s
> induced node-choices assemble to a global optimum — i.e. iff `β` makes UDT1.0 believe (correctly
> enough) that its own decisions are generated by UDT1.1.*
>
> **(D-approx, the Cole-shaped quantitative form).** *If `β` puts mass `≥ 1−δ` on "my policy is
> `π^{1.1}`," and `U` is bounded with `|U| ≤ M`, then `U(π_β) ≥ max_π U(π) − ε(δ)` with
> `ε(δ) → 0` as `δ → 0` — i.e. `A` **`ε`-updatelessly-defers** to the self-model `β`.*

**Status.** (D0) is **PROVED** (immediate from Def UD). (D1) is **SKETCHED**: forward direction is
Def UD; reverse needs "global-opt diagonal ⇒ `β` is a near-1.1 self-model," which requires a
*selection/identifiability* assumption (distinct policies give distinct diagonals on `β`'s support).
(D-approx) is **CONJECTURE**, the direct analog of Cole Wyeth's `(1−δ)`-self-confidence ⇒
`ε`-optimality theorem; the gap is a **continuity/Lipschitz** estimate of `U(π_β)` in the
self-model mass `δ`, plus the **self-coordination** subtlety Cole's special oracle handles (UDT1.0
can sit in a bad Stag-Hunt equilibrium with itself even believing it's 1.1, if the belief is about
the *wrong* optimum). **Named gaps:** (a) identifiability of policy from diagonal; (b) Lipschitz
bound `ε(δ)`; (c) ruling out self-coordination failure — AGENDA flags this last as exactly what the
"believe you're UDT1.1" hypothesis is meant to buy, replacing Cole's hand-built oracle.

**INTERPRETATION (the unification).** Under this schema, *self-trust (defer to your own future
node-self) is the self-directed instance of updateless deference*, just as v2's LI Self-Trust is DDB
Total-Trust with expert = future self. So a single relation governs both Q9 (self-trust / tiling) and
Q5 (cross-agent trust): `A` deferring to a *different* agent `B` is **(UD)** with `π_u` = "`B`'s
node-choices," and the `ε`-form is the realistic, bounded-confidence version a human principal would
actually have toward an AI.

---

## 5. Failure modes, caveats, and honest gaps (surface, don't hide)

1. **The relation is only as good as `vₛ` (the modeling of the update's local valuation).** The
   classification of mugging/Newcomb as non-deferrable depends on the *informed self decoupling* the
   acausal term (`v_heads` sees only the heads payoff). If one instead modeled an informed self that
   *retains* the coupling, it would cooperate / pay / one-box and **(UD) would hold** — correctly,
   because then it is no longer a "caver." So **(UD) is not a test on the world alone**; it is a test
   on *(update-induced node-valuation, utility)* jointly. This is faithful to UDT (the whole point is
   that the *naive Bayesian* informed self decouples) but must be stated, or one over-claims. The
   Twin-PD pair (Ex 5 vs 5b) is the clean demonstration. **This is the single most important caveat.**

2. **Brute-force, finite, single-node examples.** The Python witnesses are tiny (1–2 nodes). They
   are *proofs* for those instances (exhaustive over policies), but the general coupled
   characterization — *which* updates are deferrable as a function of the coupling structure — is
   **open** (this is the real content, parallel to v2 §10.4 / Q5). Theorem R only covers separable
   `U`.

3. **No biconditional in the coupled case yet.** We have: separable ⇒ (UD)⇔endorsement (Thm R), and
   finite witnesses for non-deference under coupling. We do **not** have a clean
   "(UD) ⇔ [calibration of the anticipation kernel]" in the coupled regime — that is Idea B's
   conjectured bridge and remains **SKETCHED**. The honest status: **(UD)** is a good *definition*
   that classifies the examples; the *endorsement-like characterization* of it under coupling is the
   open prize.

4. **Ties / argmax non-uniqueness.** `nodeChoice` and `π^{1.1}` may be non-unique; Thm R is stated
   for "a per-node argmax" and is robust to the choice, but the UDT1.0⊨1.1 schema's identifiability
   gap (4(a)) is exactly a tie-breaking subtlety (`formal-single-agent.md` Open Q2).

5. **Where calibration/legitimacy re-enters (Idea B cross-link).** A *wireheading* update is one
   whose `vₛ` re-weights toward a corrupted target; `π_u` then maximizes the corrupted `U`, not the
   prior's `U`, so **(UD) fails against the original `U`** — the prior does not updatelessly-defer to
   the addiction-self. This recovers the AGENDA's legitimacy intuition (don't endorse a future
   addiction-opinion) *inside the same relation*, with no extra machinery: legitimacy = (UD) against
   the **un-corrupted** `U`.

---

## 6. Central claim and status

> **CENTRAL CLAIM.** The relation **"`A` updatelessly-defers to `u`" := `U(π_u) ≥ U(π)` for all `π`**
> (DDB Value, expert = the `u`-informed self's diagonal assembly, evaluated in the global/updateless
> expectation) (i) **reduces to ordinary endorsement on separable utilities** (Theorem R, **PROVED**;
> Lean candidate written), (ii) **fails** for the counterfactual-mugging caver and the
> transparent-Newcomb two-boxer (**PROVED** by finite witness), and (iii) **holds** for genuine
> improvements UDT accepts, including ones differing from the prior's default action (**PROVED** by
> finite witness). The independent (Value-style) definition of "defers" **breaks the circularity** the
> ideation flagged as the top hazard, making any future endorsement-characterization a genuine
> Total-Trust⇔Value theorem.

**Overall status: the relation and the three required classifications are PROVED (Theorem R + finite
witnesses, Python-checked). The coupled-case endorsement characterization and the UDT1.0⊨UDT1.1
`ε`-deference schema are SKETCHED/CONJECTURE with named gaps (§4, §5.3).**

---

## Cross-references

- v2 **§1.2** (the diagonal `Ŝ(w)=S_w(w)`): `π_u` is exactly the diagonal; (UD) is `E_p(diagonal) ≥
  E_p(O)`, i.e. Value, lifted to the global expectation.
- v2 **§10** (deferring to non-self experts): (UD) with `π_u` = an external `B`'s node-choices is the
  cross-agent (Q5) instance; the coupled characterization (§5.2 above) is the open §10.4 problem.
- `when-udt-edt-diverge.md` / `formal-single-agent.md`: the separable ⇒ EDT=UDT decomposition is
  Theorem R; the cross-situation-coupling taxonomy is the source of the §3 examples.
- `agency-via-endorsement.md`: (UD) is the control-endorsement of `π_u` by the prior — Idea A,
  with the Value inequality as the independent "defers."
- `superconditioning-mismatched-ontologies.md` §§3–4 (calibration/anticipation): Idea B; the
  conjectured coupled-case characterization of (UD) (open, §5.3).
- AGENDA §Updatelessness (Geometric-UDT split): separability = the "values" coordinate where (UD) =
  endorsement, so "be updateful about values" = "defer freely on the separable coordinate" (Thm R).
- Orientation **Q8** (this thread), **Q5** (cross-agent; §4 interpretation), **Q9** (UDT1.0⊨1.1; §4),
  **Q11** (legitimacy = (UD) against un-corrupted `U`; §5.5).
- Artifacts: `models/updateless_deference_check.py` (RUN, 6/6 cases pass);
  `lean/updateless-deference.lean` (UNCHECKED — Theorem R, for the Lean-verify agent).
