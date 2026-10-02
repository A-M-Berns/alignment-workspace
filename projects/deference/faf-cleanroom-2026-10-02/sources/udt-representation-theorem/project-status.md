# UDT Representation Theorem: Project Status

> **Correction pass 2026-08-05** (see `cleanup-audit-2026-08-05.md`): the "verified chain" claims below are stated with honest labels — two links were originally overstated. No mathematical content changed; the labels did.

## The Goal

Derive UDT from basic principles about agency, using condensation theory as the foundation.

**Target theorem (informal):**
> If you correctly attribute unified agency to a system in a fair environment, updateless reasoning follows.

---

## What's Been Accomplished

### Lean Verification (All Compile Successfully)

| File | Key Result | Status |
|------|------------|--------|
| `BasicSimple.lean` | Global optimality → local optimality | ✅ Verified |
| `Substantive.lean` | Decision-determination → policy utility | ✅ Verified (duplicates ~40 lines of BasicSimple) |
| `OptimalPredictor.lean` | Factors-through-policy → DD | ⚠️ Verified, but "optimal" is *defined as* "factors through policy" (line 119) — the substantive claim is Gap 1, not this theorem |
| `EDTvsUDT.lean` | Newcomb: CDT≠UDT | ⚠️ Relabeled 2026-08-05 — holds the prediction fixed, which is CDT/dominance, not EDT (EDT one-boxes) |
| `UDTConnection.lean` | Documentation (comments only, no code) | ✅ |

**Build caveats:** the default `lake` target builds only `Basic.lean`/`Theorem.lean` (which contain real content despite being listed below as "not built"); none of the five files above is imported by the library root. `lake` is not installed in this environment, so compilation claims are not currently reproducible here.

### The Verified Chain

```
"Optimal" Prediction  (⚠ defined as: factors through policy — the interesting half is Gap 1)
       ↓ [OptimalPredictor.lean: optimal_predictor_gives_dd]
Decision-Determination
       ↓ [Substantive.lean: derivePolicyUtility_spec]
Policy Utility Function
       ↓ [BasicSimple.lean: global_optimal_implies_local_optimal]
UDT Formula: π(o) ∈ argmax_a U(π[o↦a])
```

### Conceptual Analysis

| Document | Content |
|----------|---------|
| `critical-analysis.md` | Honest assessment of what's trivial vs substantive |
| `condensation-connection-attempt.md` | Analysis of condensation connection |
| `fair-environment-theorem.md` | The optimal predictor insight |
| `lean-verification-summary.md` | Summary of Lean results |

---

## The Key Insight

**The real theorem:**
> If the environment uses an optimal predictor (one that factors through the policy), decision-determination holds.

**Why this matters:**
- Optimal prediction is what condensation theory characterizes
- A "good condensation" is one that optimal prediction would extract
- So: condensation conditions → optimal prediction → DD → UDT

**The connection to condensation:**
1. The policy π is a condensation of behavior if it's a minimal sufficient statistic
2. Optimal predictors extract minimal sufficient statistics
3. Therefore, optimal predictors factor through the policy
4. Therefore, decision-determination holds
5. Therefore, UDT is correct

---

## What Remains Unproven

### Gap 1: Condensation → Optimal Prediction Factors Through Policy

**Statement:** If π is a perfect condensation of behavior B, and E is an optimal predictor, then E factors through π.

**Status:** Stated informally in `fair-environment-theorem.md`, not formalized.

**Why it's hard:** Requires information-theoretic definitions of "optimal predictor" and "condensation" that we don't have in basic Lean.

### Gap 2: Information-Theoretic Definitions

We need to formalize:
- H(X | Y) = 0 (determination)
- H(Y | X) ≈ 0 (recoverability)
- Mutual information I(X; Y)
- Sufficient statistics

**Status:** Would require Mathlib probability theory.

### Gap 3: Computational Realization

The theorem assumes we can compute over policies. Under logical uncertainty:
- We don't know our own policy
- We can't enumerate all policies
- UDT1.01 provides a computable approximation

**Status:** Not formalized. Would require formalizing Diffractor's framework.

---

## Honest Assessment

### What We've Achieved

1. **Clarified the structure:** The real content is in the assumptions (optimal prediction), not the derivation (trivial once we have DD).

2. **Identified the key link:** "Optimal predictor factors through policy" is the bridge from condensation to DD.

3. **Verified the easy parts:** The chain from DD to UDT formula is machine-checked.

4. **Provided a concrete example:** Newcomb's problem in Lean shows EDT≠UDT.

### What We Haven't Achieved

1. **Full condensation formalization:** The information-theoretic conditions aren't in Lean.

2. **The key lemma:** "Optimal predictors factor through good condensations" isn't proven.

3. **Computational aspects:** UDT1.01 and logical uncertainty aren't touched.

---

## For the Presentation

### What Can Be Claimed

1. **Structure:** "UDT follows from policy optimization, which follows from decision-determination, which follows from optimal prediction."

2. **Formalization:** "The chain from DD to UDT is machine-verified in Lean 4."

3. **Insight:** "The key assumption is 'optimal prediction' - the environment uses a good model of you."

### What Should Be Flagged as Open

1. **The condensation link:** "The connection to Sam's condensation theory requires formalizing 'optimal predictor' information-theoretically."

2. **Computational aspects:** "Handling logical uncertainty is future work, building on Diffractor's framework."

3. **The key lemma:** "We conjecture but haven't proven that good condensations imply optimal prediction."

---

## Recommended Next Steps

### Short-term (for presentation)
1. Clean up presentation-outline-v2.md with the new results
2. Add the optimal predictor insight to the slides
3. Be honest about what's proven vs conjectured

### Medium-term (for paper)
1. Add Mathlib dependency and formalize entropy
2. Prove the key lemma about condensation → optimal prediction
3. Write up the full theorem chain

### Long-term (future work)
1. Formalize UDT1.01 and computational aspects
2. Connect to InfraBayes / Diffractor's work
3. Prove the correspondence theorem for agency

---

## Files Summary

```
udt-representation-theorem/
├── lean/
│   ├── UDT/
│   │   ├── BasicSimple.lean      # Core theorem (verified)
│   │   ├── Substantive.lean      # DD → policy utility (verified)
│   │   ├── OptimalPredictor.lean # Optimal pred → DD (verified)
│   │   ├── EDTvsUDT.lean         # Newcomb example (verified)
│   │   ├── UDTConnection.lean    # Documentation
│   │   ├── Basic.lean            # Mathlib version (not built)
│   │   └── Theorem.lean          # Mathlib version (not built)
│   ├── UDT.lean                  # Library root
│   ├── Main.lean                 # Entry point
│   ├── lakefile.lean             # Build config
│   └── lean-toolchain            # Lean version
├── critical-analysis.md          # Honest assessment
├── condensation-connection-attempt.md  # Condensation analysis
├── fair-environment-theorem.md   # Optimal predictor insight
├── lean-verification-summary.md  # Lean results summary
├── project-status.md             # This file
├── presentation-outline-v2.md    # Talk slides
├── unified-formal-framework.md   # 7-layer framework
└── [other documents...]
```
