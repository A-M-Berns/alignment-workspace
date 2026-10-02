import Cleanroom.Corrigibility.CorrOsgChai.POOSG

/-!
# Redundant observations: Garber's Proposition 4.3 (T8(c))

Package `corr-osg-chai`. **Redundancy** (Def. 4.2, `OA ⊥ S | OH`) in product form: there is a
kernel `K : ΩH → Distr ΩA` with `O(oH, oA | s) = OH(oH | s) · K(oA | oH)` at every state of
positive prior mass — the Markov chain `S → OH → OA` under the joint law `P0 ⊗ O`, with the
kernel fixed also on `OH`-null rows (harmless: null rows carry no mass; no division anywhere).
`P0`-null states are unconstrained, as in the paper's conditional-independence statement
(audit r1 N2; the earlier form quantified over every state). The proof of Prop. 4.3 first
establishes the product form at *every* state by copying a positive-mass state's row onto the
null states (`payoff_withObs_eq_of_eq_on_support`: this changes no payoff), then runs the
paper's argument (`exists_opp_alwaysWait_of_factor`).

**Proposition 4.3** (`exists_opp_alwaysWait_of_redundantA`): if A's observations are redundant,
some OPP has A always waiting. The paper's proof (l. 423): in the game `G'` where A sees exactly
H's observation (`diagH`), A has no private observations, so Prop. A.12 gives an always-wait OPP
of `G'`; `G`'s structure is the independent garbling `δ_{oH} ⊗ K(· | oA')` of `G'`'s, so by
Theorem 4.7 (⇐) `optValue G ≤ optValue G'`; and an always-wait pair pays the same in `G` and
`G'` because it only uses H's marginal, which is unchanged. The H side
(`exists_opp_neverWait_of_redundantH`) is symmetric.

The converse "always-wait is optimal only if A's observations are redundant" is **not** stated:
it is false (in a game with `ua ≡ uo` every pair is optimal); the inventory's "iff" overstates
Prop. 4.3 (finding F-9).

Source: `04-chai/garber-2024-…md` l. 173 (Def. 4.2, Prop. 4.3), l. 423 (proof).
-/

namespace Cleanroom.Corrigibility.CorrOsgChai

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

namespace POOSG

variable {S ΩH ΩA : Type} [Fintype S] [Fintype ΩH] [Fintype ΩA] [DecidableEq ΩH] [DecidableEq ΩA]
variable (G : POOSG S ΩH ΩA)

/-- **A has redundant observations** (Def. 4.2, `OA ⊥ S | OH`), product form: at every state
of positive prior mass the joint kernel factors as `OH(oH | s) · K(oA | oH)` for one kernel `K`
(the Markov chain `S → OH → OA` under the joint law; `K` is fixed also on `OH`-null rows, which
carry no mass; `P0`-null states are unconstrained).
Source: Garber et al. 2024 Def. 4.2 (l. 173)
Kind: D
Fidelity: exact (Markov-chain reading in product form, on the support of `P0`; disclosed) -/
def RedundantA : Prop :=
  ∃ K : ΩH → Distr ΩA, ∀ s, G.P0.mass s ≠ 0 →
    ∀ oH oA, (G.obs s).mass (oH, oA) = G.obsH s oH * (K oH).mass oA

/-- **H has redundant observations** (Def. 4.2, `OH ⊥ S | OA`), product form on the support of
`P0`.
Source: Garber et al. 2024 Def. 4.2 (l. 173)
Kind: D
Fidelity: exact (product form, on the support of `P0`) -/
def RedundantH : Prop :=
  ∃ K : ΩA → Distr ΩH, ∀ s, G.P0.mass s ≠ 0 →
    ∀ oH oA, (G.obs s).mass (oH, oA) = G.obsA s oA * (K oA).mass oH

/-- An always-wait pair's payoff uses only H's marginal.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma payoff_alwaysWait (πH : ΩH → HAct) :
    G.payoff πH (fun _ => .wait) = ∑ s, G.P0.mass s * ∑ oH, G.obsH s oH * G.u s (πH oH) .wait := by
  unfold payoff obsH
  refine sum_congr rfl fun s _ => congrArg _ ?_
  rw [Fintype.sum_prod_type]
  simp only [sum_mul]

/-- The payoff of a non-waiting A-action does not depend on H's action.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma u_eq_of_ne_wait (s : S) (aH aH' : HAct) {aA : AAct} (h : aA ≠ .wait) :
    G.u s aH aA = G.u s aH' aA := by
  cases aA
  · simp [u]
  · exact absurd rfl h
  · simp [u]

/-- A never-wait pair's payoff uses only A's marginal.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma payoff_neverWait (πH : ΩH → HAct) {πA : ΩA → AAct} (hπA : ∀ oA, πA oA ≠ .wait) :
    G.payoff πH πA = ∑ s, G.P0.mass s * ∑ oA, G.obsA s oA * G.u s default (πA oA) := by
  unfold payoff obsA
  refine sum_congr rfl fun s _ => congrArg _ ?_
  rw [Fintype.sum_prod_type, sum_comm]
  simp only [sum_mul]
  exact sum_congr rfl fun oA _ => sum_congr rfl fun oH _ => by
    rw [G.u_eq_of_ne_wait s (πH oH) default (hπA oA)]

/-- **The diagonal copy of H's observation**: the observation structure in which A sees exactly
what H sees (the paper's `G'` with `OA = OH`).
Source: Garber et al. 2024 Prop. 4.3's proof (l. 423)
Kind: D
Fidelity: exact -/
noncomputable def diagH (s : S) : Distr (ΩH × ΩH) where
  mass p := if p.2 = p.1 then G.obsH s p.1 else 0
  nonneg p := by
    split_ifs
    · exact sum_nonneg fun _ _ => (G.obs s).nonneg _
    · exact le_rfl
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [sum_ite_eq', mem_univ, if_true]
    unfold obsH
    rw [← Fintype.sum_prod_type]
    exact (G.obs s).sum_eq_one

/-- **The diagonal copy of A's observation**: H sees exactly what A sees.
Source: Garber et al. 2024 Prop. 4.3's proof (l. 423), mutatis mutandis
Kind: D
Fidelity: exact -/
noncomputable def diagA (s : S) : Distr (ΩA × ΩA) where
  mass p := if p.1 = p.2 then G.obsA s p.2 else 0
  nonneg p := by
    split_ifs
    · exact sum_nonneg fun _ _ => (G.obs s).nonneg _
    · exact le_rfl
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    simp only [sum_ite_eq, mem_univ, if_true]
    unfold obsA
    rw [sum_comm, ← Fintype.sum_prod_type]
    exact (G.obs s).sum_eq_one

/-- H's marginal is unchanged in the diagonal copy. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsH_withObs_diagH (s : S) (oH : ΩH) : (G.withObs G.diagH).obsH s oH = G.obsH s oH := by
  simp only [obsH, withObs, diagH]
  simp [sum_ite_eq']

/-- A's marginal is unchanged in the diagonal copy. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma obsA_withObs_diagA (s : S) (oA : ΩA) : (G.withObs G.diagA).obsA s oA = G.obsA s oA := by
  simp only [obsA, withObs, diagA]
  simp [sum_ite_eq]

/-- **Proposition 4.3, A's side, with the product form at every state** (the paper's argument).
Source: Garber et al. 2024 Prop. 4.3 (l. 173; proof l. 423)
Kind: C (Prop. A.12 in the diagonal copy, Theorem 4.7 (⇐) for the independent garbling
`δ ⊗ K`, and the marginal identity)
Fidelity: exact (given the product form everywhere; the headline reduces to it)
Hyps: (a) `hK` -/
theorem exists_opp_alwaysWait_of_factor (K : ΩH → Distr ΩA)
    (hK : ∀ s oH oA, (G.obs s).mass (oH, oA) = G.obsH s oH * (K oH).mass oA) :
    ∃ πH, G.IsOPP πH (fun _ => .wait) := by
  -- the diagonal game: A sees H's observation, so A has no private observations
  have hnp : (G.withObs G.diagH).NoPrivateA :=
    ⟨id, fun s _ oH oA hne => by
      simp only [withObs, diagH] at hne
      by_contra hcon
      exact hne (if_neg hcon)⟩
  obtain ⟨πH', hopp'⟩ := (G.withObs G.diagH).exists_opp_alwaysWait_of_noPrivateA hnp
  -- `G.obs` is the independent garbling `δ_{oH} ⊗ K(· | oA')` of the diagonal structure
  have hmi : MoreInformative G.diagH G.obs := by
    refine ⟨fun o => prodDistr (Distr.delta o.1) (K o.2),
      Independent.coordinated ⟨fun oH => Distr.delta oH, K, fun _ _ _ _ => rfl⟩, ?_⟩
    rintro s ⟨oH, oA⟩
    rw [hK s oH oA, Fintype.sum_prod_type]
    simp only [diagH, prodDistr_mass, Distr.delta_mass, ite_mul, zero_mul, sum_ite_eq', mem_univ,
      if_true]
    rw [sum_eq_single oH]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hmem; exact absurd (mem_univ _) hmem
  have h2 : G.optValue ≤ (G.withObs G.diagH).optValue :=
    (G.withObs G.diagH).optValue_withObs_le_of_moreInformative G.obs hmi
  have h1 : G.payoff πH' (fun _ => .wait) = (G.withObs G.diagH).payoff πH' (fun _ => .wait) := by
    rw [payoff_alwaysWait, payoff_alwaysWait]
    simp only [obsH_withObs_diagH]
    rfl
  refine ⟨πH', le_antisymm (G.payoff_le_optValue _ _) ?_⟩
  calc G.optValue ≤ (G.withObs G.diagH).optValue := h2
    _ = (G.withObs G.diagH).payoff πH' (fun _ => .wait) := hopp'.symm
    _ = G.payoff πH' (fun _ => .wait) := h1.symm

/-- **Proposition 4.3, A's side.** If A has redundant observations (Def. 4.2, on the support of
`P0`), some OPP has A always waiting. (No converse is claimed: the trivial game `ua ≡ uo` has
every pair optimal.) Proof: copy a positive-mass state's observation row onto the `P0`-null
states — no payoff, optimum or OPP changes (`isOPP_withObs_iff_of_eq_on_support`) and the
product form now holds at every state — then `exists_opp_alwaysWait_of_factor`.
Source: Garber et al. 2024 Prop. 4.3 (l. 173; proof l. 423)
Kind: C (the null-state edit and `exists_opp_alwaysWait_of_factor`)
Fidelity: exact
Hyps: (a) none -/
theorem exists_opp_alwaysWait_of_redundantA (h : G.RedundantA) :
    ∃ πH, G.IsOPP πH (fun _ => .wait) := by
  obtain ⟨K, hK⟩ := h
  obtain ⟨s₀, hs₀⟩ := exists_pos_mass G.P0
  set O : S → Distr (ΩH × ΩA) := fun s => if G.P0.mass s = 0 then G.obs s₀ else G.obs s
    with hOdef
  have hO : ∀ s, G.P0.mass s ≠ 0 → O s = G.obs s := fun s hs => by
    simp only [hOdef, if_neg hs]
  have hK' : ∀ s oH oA, ((G.withObs O).obs s).mass (oH, oA) =
      (G.withObs O).obsH s oH * (K oH).mass oA := by
    intro s oH oA
    by_cases hs : G.P0.mass s = 0
    · simpa only [withObs, obsH, hOdef, if_pos hs] using hK s₀ hs₀ oH oA
    · simpa only [withObs, obsH, hOdef, if_neg hs] using hK s hs oH oA
  obtain ⟨πH, hopp⟩ := (G.withObs O).exists_opp_alwaysWait_of_factor K hK'
  exact ⟨πH, (G.isOPP_withObs_iff_of_eq_on_support O hO πH _).mp hopp⟩

/-- **Proposition 4.3, H's side, with the product form at every state.**
Source: Garber et al. 2024 Prop. 4.3 (l. 173; "mutatis mutandis", l. 423)
Kind: C
Fidelity: exact (given the product form everywhere; the headline reduces to it)
Hyps: (a) `hK` -/
theorem exists_opp_neverWait_of_factor (K : ΩA → Distr ΩH)
    (hK : ∀ s oH oA, (G.obs s).mass (oH, oA) = G.obsA s oA * (K oA).mass oH) :
    ∃ πH πA, G.IsOPP πH πA ∧ ∀ oA, πA oA ≠ .wait := by
  have hnp : (G.withObs G.diagA).NoPrivateH :=
    ⟨id, fun s _ oH oA hne => by
      simp only [withObs, diagA] at hne
      by_contra hcon
      exact hne (if_neg hcon)⟩
  obtain ⟨πH', πA', hopp', hnw⟩ := (G.withObs G.diagA).exists_opp_neverWait_of_noPrivateH hnp
  have hmi : MoreInformative G.diagA G.obs := by
    refine ⟨fun o => prodDistr (K o.1) (Distr.delta o.2),
      Independent.coordinated ⟨K, fun oA => Distr.delta oA, fun _ _ _ _ => rfl⟩, ?_⟩
    rintro s ⟨oH, oA⟩
    rw [hK s oH oA, Fintype.sum_prod_type, sum_comm]
    simp only [diagA, prodDistr_mass, Distr.delta_mass, ite_mul, zero_mul, sum_ite_eq,
      sum_ite_eq', mem_univ, if_true]
    rw [sum_eq_single oA]
    · simp [mul_comm]
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hmem; exact absurd (mem_univ _) hmem
  have h2 : G.optValue ≤ (G.withObs G.diagA).optValue :=
    (G.withObs G.diagA).optValue_withObs_le_of_moreInformative G.obs hmi
  -- A never waits, so H's policy is immaterial: any `πH` transfers
  have h1 : G.payoff (fun _ => default) πA' = (G.withObs G.diagA).payoff πH' πA' := by
    rw [G.payoff_neverWait _ hnw, (G.withObs G.diagA).payoff_neverWait πH' hnw]
    simp only [obsA_withObs_diagA]
    rfl
  refine ⟨fun _ => default, πA', le_antisymm (G.payoff_le_optValue _ _) ?_, hnw⟩
  calc G.optValue ≤ (G.withObs G.diagA).optValue := h2
    _ = (G.withObs G.diagA).payoff πH' πA' := hopp'.symm
    _ = G.payoff (fun _ => default) πA' := h1.symm

/-- **Proposition 4.3, H's side.** If H has redundant observations (Def. 4.2, on the support of
`P0`), some OPP has A never waiting; by the same null-state edit as the A side.
Source: Garber et al. 2024 Prop. 4.3 (l. 173; "mutatis mutandis", l. 423)
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem exists_opp_neverWait_of_redundantH (h : G.RedundantH) :
    ∃ πH πA, G.IsOPP πH πA ∧ ∀ oA, πA oA ≠ .wait := by
  obtain ⟨K, hK⟩ := h
  obtain ⟨s₀, hs₀⟩ := exists_pos_mass G.P0
  set O : S → Distr (ΩH × ΩA) := fun s => if G.P0.mass s = 0 then G.obs s₀ else G.obs s
    with hOdef
  have hO : ∀ s, G.P0.mass s ≠ 0 → O s = G.obs s := fun s hs => by
    simp only [hOdef, if_neg hs]
  have hK' : ∀ s oH oA, ((G.withObs O).obs s).mass (oH, oA) =
      (G.withObs O).obsA s oA * (K oA).mass oH := by
    intro s oH oA
    by_cases hs : G.P0.mass s = 0
    · simpa only [withObs, obsA, hOdef, if_pos hs] using hK s₀ hs₀ oH oA
    · simpa only [withObs, obsA, hOdef, if_neg hs] using hK s hs oH oA
  obtain ⟨πH, πA, hopp, hnw⟩ := (G.withObs O).exists_opp_neverWait_of_factor K hK'
  exact ⟨πH, πA, (G.isOPP_withObs_iff_of_eq_on_support O hO πH πA).mp hopp, hnw⟩

end POOSG

end Cleanroom.Corrigibility.CorrOsgChai
