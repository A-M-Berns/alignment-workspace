import Cleanroom.Udt.UdtPolicyCalc.LocalGlobal

/-!
# Deterministic "decision-determination" and the optimal-predictor squeeze: T6, T7

Re-founds `Substantive.lean:36–139` and `OptimalPredictor.lean:46–131` with a **mechanism
coordinate** the source lacks: a type `M` of mechanisms with `behaviour : M → Policy S A` and a
world utility `W : M → ℝ`.

* T6 `PolicyDetermined`, `derivedPolicyUtility` with `derivedPolicyUtility_spec` and
  `exists_policyUtility` (Kind L; hypothesis provenance **(c)**: the deterministic, mechanism-only
  caricature of C&T's decision-determination, which `udt-comm-trust` owns).
* T6 witnesses: `W2_policyDetermined` (N+: two mechanisms with equal behaviour, `W`
  policy-determined and non-constant) and `W2bad_not_policyDetermined` (the failure witness,
  [[critical-analysis]] Counterexample 2).
* T7 `policyDetermined_of_factors`: the composition lemma the source names
  `optimal_predictor_gives_dd`, under an honest name (Kind L; the ledger row is `S`, flagged).

Package `udt-policy-calc` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtPolicyCalc

noncomputable section

section Det

variable {M S A : Type}

/-- **T6 (udt-rep-004).** `W` is **policy-determined** (relative to `behaviour`): two mechanisms
with the same behaviour get the same world utility.
Hyps line applies to every theorem stated over this predicate: **(c)** — this is the
deterministic, mechanism-only caricature of C&T's decision-determination (a conditional
independence `E ⊥ D_{I,B} | Π̈`), which `udt-comm-trust` owns; nothing here is claimed for the
C&T notion. The source's `WorldState` has no mechanism field, so the "mechanism-independence"
it verifies is vacuous (finding, local error); the mechanism coordinate `M` is what this
definition adds.
Source: `lean/UDT/Substantive.lean:103` (`satisfiesDecisionDetermination`; udt-rep-004)
Kind: D
Fidelity: variant: adds the mechanism coordinate the source lacks; (c) relative to C&T's DD
Hyps: n/a -/
def PolicyDetermined (behaviour : M → Policy S A) (W : M → ℝ) : Prop :=
  ∀ m₁ m₂, behaviour m₁ = behaviour m₂ → W m₁ = W m₂

/-- The **derived policy utility**: `U π := W (some mechanism with behaviour π)`, via
`Function.surjInv`. Well-defined on policies only under `PolicyDetermined`
(`derivedPolicyUtility_spec`); the source's `Classical.choose (hasConsistent π)` is the same
construction.
Source: `lean/UDT/Substantive.lean:113` (`derivePolicyUtility`; udt-rep-004)
Kind: D
Fidelity: exact
Hyps: n/a -/
def derivedPolicyUtility (behaviour : M → Policy S A) (hsurj : Function.Surjective behaviour)
    (W : M → ℝ) : Policy S A → ℝ :=
  fun π => W (Function.surjInv hsurj π)

/-- **T6, the spec (udt-rep-004).** Under `PolicyDetermined`, the derived policy utility agrees
with `W` on every mechanism: `U (behaviour m) = W m`.
Source: `lean/UDT/Substantive.lean:121` (`derivePolicyUtility_spec`; udt-rep-004)
Kind: L
Fidelity: exact
Hyps: (c) `PolicyDetermined behaviour W` (the deterministic caricature of C&T's DD; see
`PolicyDetermined`); (a) `Function.Surjective behaviour` (the source's `hasConsistent`) -/
theorem derivedPolicyUtility_spec {behaviour : M → Policy S A}
    (hsurj : Function.Surjective behaviour) {W : M → ℝ} (hW : PolicyDetermined behaviour W)
    (m : M) : derivedPolicyUtility behaviour hsurj W (behaviour m) = W m :=
  hW _ _ (Function.surjInv_eq hsurj (behaviour m))

/-- **T6, headline form.** A policy-determined world utility factors through the behaviour map:
there is `U : Policy S A → ℝ` with `W m = U (behaviour m)` for every mechanism.
Source: `lean/UDT/Substantive.lean:113–131` (udt-rep-004)
Kind: L
Fidelity: exact
Hyps: (c) `PolicyDetermined behaviour W`; (a) surjectivity -/
theorem exists_policyUtility {behaviour : M → Policy S A}
    (hsurj : Function.Surjective behaviour) {W : M → ℝ} (hW : PolicyDetermined behaviour W) :
    ∃ U : Policy S A → ℝ, ∀ m, W m = U (behaviour m) :=
  ⟨derivedPolicyUtility behaviour hsurj W, fun m => (derivedPolicyUtility_spec hsurj hW m).symm⟩

/-- Conversely, anything that factors through the behaviour is policy-determined.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem policyDetermined_of_eq_comp {behaviour : M → Policy S A} {W : M → ℝ}
    {U : Policy S A → ℝ} (h : ∀ m, W m = U (behaviour m)) : PolicyDetermined behaviour W :=
  fun m₁ m₂ hb => by rw [h m₁, h m₂, hb]

/-- **T6 as an equivalence.** For a surjective behaviour map, policy-determination is exactly
factoring through the behaviour.
Source: `lean/UDT/Substantive.lean:113–131` (udt-rep-004)
Kind: L
Fidelity: exact
Hyps: (a) surjectivity -/
theorem policyDetermined_iff_factors {behaviour : M → Policy S A}
    (hsurj : Function.Surjective behaviour) {W : M → ℝ} :
    PolicyDetermined behaviour W ↔ ∃ U : Policy S A → ℝ, ∀ m, W m = U (behaviour m) :=
  ⟨exists_policyUtility hsurj, fun ⟨_, h⟩ => policyDetermined_of_eq_comp h⟩

/-- **T7 (udt-rep-005).** The composition lemma of `OptimalPredictor.lean`: if the predictor
`E` factors through the behaviour and the utility `U m p` depends on `m` only through
`behaviour m`, then `m ↦ U m (E m)` is policy-determined. True and content-free (function
composition). The source names this `optimal_predictor_gives_dd` after *defining* "optimal
predictor" as "factors through the policy" (`OptimalPredictor.lean:119`): the theorem assumes
Gap 1. The honest replacement is `udt-condense-dd`'s approximate-factoring lemma.
Source: `lean/UDT/OptimalPredictor.lean:46–131` (udt-rep-005); [[cleanup-audit-2026-08-05]] finding 2(a)
Kind: L
Fidelity: exact (ledger row `optimal_predictor_gives_dd`: Kind S, flagged)
Hyps: (a) both hypotheses are the conclusion's ingredients; the name "optimal" would be a (c) -/
theorem policyDetermined_of_factors {P : Type} (behaviour : M → Policy S A) (E : M → P)
    (hE : ∃ f : Policy S A → P, ∀ m, E m = f (behaviour m)) (U : M → P → ℝ)
    (hU : ∀ m₁ m₂ p, behaviour m₁ = behaviour m₂ → U m₁ p = U m₂ p) :
    PolicyDetermined behaviour (fun m => U m (E m)) := by
  obtain ⟨f, hf⟩ := hE
  intro m₁ m₂ h
  simp only [hf m₁, hf m₂, h]
  exact hU m₁ m₂ _ h

end Det

/-! ### Witnesses -/

/-- Mechanisms for the witnesses: a policy on `Fin 2 → Fin 2` plus an internal bit the
environment may or may not read.
Source: mandate T6 witnesses
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev Mech2 := (Fin 2 → Fin 2) × Bool

/-- The behaviour map forgets the internal bit.
Source: mandate T6 witnesses
Kind: D
Fidelity: n/a
Hyps: n/a -/
def behav2 : Mech2 → Policy (Fin 2) (Fin 2) := Prod.fst

/-- Supporting lemma `behav2_surjective` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem behav2_surjective : Function.Surjective behav2 := fun π => ⟨(π, true), rfl⟩

/-- Coordinated Buttons read through the behaviour map: a policy-determined, non-constant world
utility.
Source: mandate T6 witnesses
Kind: D
Fidelity: n/a
Hyps: n/a -/
def W2 : Mech2 → ℝ := fun m => coordButtons m.1

/-- **T6, N+ witness.** `W2` is policy-determined, non-constant, and two distinct mechanisms share
a behaviour — the hypothesis package of `exists_policyUtility` is inhabited non-degenerately.
Source: mandate T6 witnesses
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem W2_witness :
    PolicyDetermined behav2 W2 ∧ W2 (![0, 0], true) ≠ W2 (![1, 1], true) ∧
      behav2 (![0, 0], true) = behav2 (![0, 0], false) ∧
        ((![0, 0], true) : Mech2) ≠ (![0, 0], false) := by
  refine ⟨fun m₁ m₂ h => ?_, ?_, rfl, by simp⟩
  · simp only [W2, behav2] at *
    rw [h]
  · simp only [W2, coordButtons, tbl_00, tbl_11]
    norm_num

/-- A world utility reading the internal bit: [[critical-analysis]] Counterexample 2 ("if the
environment discriminates based on mechanism (not just policy): decision-determination fails").
Source: [[critical-analysis]] lines 398–404 (Counterexample 2)
Kind: D
Fidelity: exact
Hyps: n/a -/
def W2bad : Mech2 → ℝ := fun m => if m.2 then 1 else 0

/-- **T6, failure witness.** `W2bad` is not policy-determined: same behaviour, different values.
Source: [[critical-analysis]] lines 398–404 (Counterexample 2)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem W2bad_not_policyDetermined : ¬ PolicyDetermined behav2 W2bad := by
  intro h
  have := h (![0, 0], true) (![0, 0], false) rfl
  simp [W2bad] at this

end

end Cleanroom.Udt.UdtPolicyCalc
