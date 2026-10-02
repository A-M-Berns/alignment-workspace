# Toward a Real Theorem: Fair Environments

> **Corrected 2026-08-05** (see [cleanup-audit-2026-08-05](cleanup-audit-2026-08-05.md)): the original version formatted the project's central open gap (Gap 1) as a completed Definition/Lemma/Theorem/Corollary chain and declared "This IS a condensation-to-UDT theorem!" **Nothing in this file is proven.** Every formal-looking block below is a conjecture sketch; the two known obstructions (minimality, off-support) are now stated as such. `topics/optimal-prediction.md` has the careful treatment with Eisenstat's actual theorems.

## The Key Question

**When does decision-determination hold?**

If we can characterize this in condensation terms, we get a real theorem.

---

## Decision-Determination Revisited

**Decision-determination says:**
The environment responds to your policy π, not to your internal mechanism.

**Formally:**
For any two mechanisms M₁, M₂ that implement the same policy π:
  U(M₁) = U(M₂)

**In other words:**
Utility is a function of the extensional behavior, not the intensional procedure.

---

## When Should This Hold?

### Case 1: No Predictors

If the environment has no way to predict your behavior, it can't respond to your policy at all. But it also can't discriminate based on mechanism.

**Result:** Decision-determination holds trivially (environment doesn't condition on you at all).

**But this means:** No cross-situation dependence. EDT and UDT agree. Boring case.

### Case 2: Perfect Predictors

If the environment perfectly predicts your behavior, it responds to your policy.

**Key question:** Does it respond to ONLY your policy, or also your mechanism?

**"Fair" predictor:** Responds only to input-output behavior (the policy).

**"Unfair" predictor:** Looks inside your implementation.

### Case 3: Imperfect Predictors

Realistic predictors are imperfect. They have some model of you.

**Question:** Under what conditions is this model effectively "just the policy"?

---

## A Condensation Characterization of Fair Environments

### Setup

- Agent has mechanism M that implements policy π = behavior(M)
- Environment has model E of agent
- Environment responds based on E(M)

### The Fairness Condition (attempt 1)

**The environment's model E is "fair" if:**
E(M) depends only on behavior(M), not on M directly.

Formally: behavior(M₁) = behavior(M₂) → E(M₁) = E(M₂)

**This is just decision-determination restated.** Not a new characterization.

### The Fairness Condition (attempt 2)

**Using condensation:** The environment's model E should be a good condensation of the agent's observable behavior.

If E is trying to predict the agent, and the policy π is a good condensation of behavior, then a good E should recover π.

**Claim:** If E is a good predictor (accurate, minimal), and π is a good condensation of agent behavior, then E ≈ π (up to sufficient statistics).

**Proof sketch:**
- E is accurate → E captures predictive information about behavior
- π is a good condensation → π is the minimal predictor of behavior
- Therefore E contains π (or is equivalent to π)

**Consequence:** A good predictor responds to the policy.

---

## The Potential Theorem

**Theorem (sketch):**

Let:
- Agent behavior B be observable
- Policy π be a perfect condensation of B
- Predictor E be optimal (accurate and minimal)

Then:
- E depends only on π (E is a function of π)
- Any response to E is a response to π
- Decision-determination holds

**This would be a real condensation result!**

---

## Checking the Logic

### Premise 1: Policy is a perfect condensation of behavior

This means:
- H(Bᵢ | π, Oᵢ) = 0 (determination)
- H(π | B) ≈ 0 (recoverability)

In other words: π and B are informationally equivalent (given observation distribution).

### Premise 2: Predictor is optimal

This means:
- E has minimal complexity for its predictive accuracy
- E is a sufficient statistic for predicting B

### Conclusion: Predictor depends only on policy

**Argument:**
1. An optimal predictor extracts the minimal sufficient statistic for prediction
2. The policy π is a sufficient statistic for behavior (given observations)
3. Therefore, an optimal predictor E is a function of π (or equivalent)

**The key step:** Why is π THE minimal sufficient statistic?

**⚠ THIS STEP IS A GAP, NOT A PROOF** (flagged 2026-08-05). The argument needs π to be *minimal* among sufficient statistics — minimal sufficient statistics are unique only up to bijection *within* that class. Recoverability (H(π | B) ≈ 0) says only that π is a coarsening of B, not that it is the coarsest sufficient one. The original answer here ("π and B are informationally equivalent given O") makes minimality *vacuous* rather than establishing it — if π carries all of B's information, it is not a reduction at all. What is actually needed: a proof that the minimal sufficient statistic of B for the environment's prediction task coincides with π, which is precisely open Gap 1.

---

## What Would Need to Be Proven (conjecture sketch — NOTHING below is proven)

### Candidate Definition: Predictive Equivalence

Two latents L₁, L₂ are **predictively equivalent** for observables X if:
  I(L₁ ; X) = I(L₂ ; X) and both are sufficient statistics

### Conjecture A: Condensations are Predictively Equivalent

If L₁ and L₂ are both perfect condensations of X, they are predictively equivalent. *(Unproven. Note also that "perfect condensation" here is used loosely — Eisenstat's actual definition is the score equality χ_L(A) = H(X_A), not the determination+recoverability pair; see the audit.)*

### Conjecture B: Optimal Predictors Agree with Condensations

If π is a perfect condensation of behavior B and E is an optimal (minimal sufficient) predictor of B, then E is predictively equivalent to π, and any function of E is a function of π. *(Unproven — and the minimality gap above plus the off-support obstruction below are known obstacles.)*

### Would-be Corollary: Decision-Determination from Optimality

If Conjectures A and B held (with the obstructions resolved), an environment using an optimal predictor would satisfy decision-determination.

---

## What This Would Prove — If the Conjectures Held

Optimal predictors would respond to policies, not mechanisms, because optimal prediction would extract the policy. In environments with optimal predictors, UDT would then be correct. **None of this is currently established.**

---

## Caveats and Limitations

### Caveat 1: Optimal Predictors Are Idealized

Real predictors aren't optimal. They might:
- Use suboptimal features (mechanism-dependent)
- Have limited computation
- Make systematic errors

**Response:** The theorem provides an ideal. Deviations from optimality might break decision-determination.

### Obstruction (promoted from "Caveat 2" 2026-08-05): The Off-Support Problem

Recoverability depends on the observation distribution having sufficient coverage. If you only ever see observation o*, the predictor can only learn π(o*).

**This is not a caveat — it is a counterexample to the conjecture as stated.** An optimal predictor is optimal *with respect to the realized observation distribution*, so it is under no obligation to determine π off-support. But off-support policy values are exactly where UDT's content lives: transparent Newcomb's unrealized branch, the unvisited room in Coordinated Buttons. So the would-be theorem's conclusion fails precisely in the cases that motivate it. "Assume sufficient observation diversity" assumes away the interesting cases. Any real version of Conjecture B must either restrict its UDT-relevance claims to on-support structure or explain where off-support predictive constraints come from (e.g. simplicity priors over predictors).

### Caveat 3: This Doesn't Cover All "Fair" Environments

Some environments might be "fair" for non-condensation reasons:
- Normative constraints (it's wrong to discriminate on mechanism)
- Physical constraints (can't observe mechanism)

**Response:** The theorem covers one important case, not all cases.

---

## Summary: The Shape of the Hoped-For Theorem

**Conjecture (Informal):**
If the policy is a good condensation of behavior, and the environment uses an optimal predictor, then decision-determination holds.

**Structure:**
- Premise 1: Agency condensation conditions
- Premise 2: Environment optimality
- Conclusion: Decision-determination

**Combined with the (verified, easy) DD → UDT chain, this would be a condensation-to-UDT theorem. It is not one yet:** the minimality gap and the off-support obstruction above are both unresolved, and they are the substance of open Gap 1 — see [project-status](project-status.md) and `topics/optimal-prediction.md`.

---

## Open Questions

1. **Formalize "optimal predictor"** in information-theoretic terms
2. **Prove the lemma** about condensations being predictively equivalent
3. **Extend to approximate condensation** for realistic settings
4. **Connect to Diffractor's framework** for computational aspects

---

## What This Means for the Presentation

**Original claim:** "Agency as condensation implies UDT"

**Refined claim:** "Agency condensation + optimal prediction implies UDT"

**The added premise (optimal prediction) is:**
- Plausible for sophisticated predictors
- Connects prediction quality to decision theory correctness
- Provides a criterion for when UDT applies
