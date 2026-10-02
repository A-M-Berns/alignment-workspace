import Cleanroom.Bli.UdtBliCore.Good

/-!
# `udt-bli-core` · Bridges: the two-level bridges between the structural predicates (T7)

* `reflective_of_reflectivePolicy` — the policy-level reflection implies the point-level one
  (summing the cell factorization over the policies with the given point value).
* `homeEU_eq_cellEU_of_localUtility` — under `LocalUtility` alone, the updateful value at `T`
  equals the cell value of any positive policy with that point (the averaging step without
  `ReflectivePolicy`).
* `noCrossBranch_of_localUtility_indepGivenState` — `LocalUtility ∧ IndependentPointsGivenState`
  give `NoCrossBranch`: the other branch's expectation given the point at `T` is
  `∑_c μ(pp · T' = c | state = T') · homeEU T' c`, which does not mention the point at `T`.
* `indepGivenState_of_indep_reflectivePolicy` — `IndependentPoints ∧ ReflectivePolicy` give
  `IndependentPointsGivenState`.
* `trivialLayer` and `policyFair_trivialLayer` — on the trivial procedure layer (`Proc = Policy`,
  `eff = id`) Policy Fairness holds for **every** prior: Kind `T`, the squeeze `udt-paper-tiling`
  must not ship as content.

Also here, because it needs `reflective_of_reflectivePolicy`: `priorOptimal_of_oneStepPolicy`,
the corollary of T6 with T5 (the one-step policy is prior-optimal under the point-level
predicates plus `ReflectivePolicy ∧ LocalUtility`).

The gap witnesses (the correlated-points prior, its full-support variant, the
Transparent-Newcomb-shaped prior) are in `WitnessCorr.lean`; faith without `FaithGivenPoints`,
faith without `FaithGivenAct`, the fair and unfair procedure layers and the entanglement instances
are in `WitnessLayers.lean`; the XOR prior, the full-support correlated gap and the ε-instance are
in `WitnessXor.lean`, `WitnessGap.lean`, `WitnessEps.lean`.
-/

namespace Cleanroom.Bli.UdtBliCore

open Cleanroom.Bli.BliFinite Finset

namespace FiniteBLIPrior

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type} [DecidableEq A] [Fintype A]
variable (P : FiniteBLIPrior 𝒮 m 𝒟 A)

/-- `ppMass T a = ∑_π [π T = a] · policyMass π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ppMass_eq_sum_policyMass (T : ↥𝒟) (a : A) :
    P.ppMass T a = ∑ π, if π T = a then P.policyMass π else 0 := by
  unfold ppMass policyMass
  rw [massOf_fiberwise P.μ _ P.pp]
  apply Finset.sum_congr rfl
  intro π _
  by_cases hπ : π T = a
  · rw [if_pos hπ]
    exact massOf_congr _ (fun ω => by
      constructor
      · rintro ⟨_, hp⟩; exact hp
      · intro hp; exact ⟨hp ▸ hπ, hp⟩)
  · rw [if_neg hπ]
    unfold massOf
    apply Finset.sum_eq_zero
    intro ω _
    rw [if_neg]
    rintro ⟨hpa, hp⟩
    exact hπ (hp ▸ hpa)

/-- A cell of a policy has at most the policy's mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellMass_le_policyMass (T : ↥𝒟) (π : Policy 𝒟 A) : P.cellMass T π ≤ P.policyMass π := by
  rw [P.policyMass_eq_sum_cellMass π]
  exact Finset.single_le_sum (fun T' _ => P.cellMass_nonneg T' π) (Finset.mem_univ T)

/-- Under `ReflectivePolicy` every cell factorizes, null policies included.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cellMass_eq_of_reflectivePolicy' (hR : P.ReflectivePolicy) (T : ↥𝒟) (π : Policy 𝒟 A) :
    P.cellMass T π = P.stateMass T * P.policyMass π := by
  by_cases hπ : 0 < P.policyMass π
  · exact P.cellMass_eq_of_reflectivePolicy hR T π hπ
  · have hz : P.policyMass π = 0 := le_antisymm (not_lt.mp hπ) (P.policyMass_nonneg π)
    rw [hz, mul_zero]
    exact le_antisymm (hz ▸ P.cellMass_le_policyMass T π) (P.cellMass_nonneg T π)

/-- **`ReflectivePolicy → Reflective`**: if no whole policy moves the branch probabilities, no
single point does.
Source: mandate §3.5, T7
Kind: C
Fidelity: exact
Hyps: (a) `ReflectivePolicy`; does not use faith -/
theorem reflective_of_reflectivePolicy (hR : P.ReflectivePolicy) : P.Reflective := by
  intro T T' a hpos
  unfold branchProb
  have hj : P.jointMass T T' a = P.stateMass T * P.ppMass T' a := by
    rw [P.jointMass_eq_sum_cellMass T T' a, P.ppMass_eq_sum_policyMass T' a, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro π _
    split_ifs
    · exact P.cellMass_eq_of_reflectivePolicy' hR T π
    · rw [mul_zero]
  rw [hj, mul_div_assoc, div_self (ne_of_gt hpos), mul_one]

/-- **Corollary of T6 with T5**: under `NDHOME`, `NDPOLICY`, `NoCrossBranch` and the policy-level
predicates (`Reflective` follows from `ReflectivePolicy`), the one-step policy is the updateful
policy, hence prior-optimal: deferral to the *one-step* rule also dominates every precommitment.
(Moved here from `Good.lean` in repair round 1 to drop the redundant `Reflective` hypothesis.)
Source: mandate T6 (corollary); [[bli-program]] §3.9 U4
Kind: C
Fidelity: exact
Hyps: (a) `NDHOME`, `NDPOLICY`, `NoCrossBranch`, `ReflectivePolicy`, `LocalUtility`; does not use
faith -/
theorem priorOptimal_of_oneStepPolicy [Nonempty A] (hhome : P.NDHOME) (hpol : P.NDPOLICY)
    (hN : P.NoCrossBranch) (hRp : P.ReflectivePolicy) (hL : P.LocalUtility)
    (π : Policy 𝒟 A) (h1 : P.IsOneStepPolicy π) : P.IsPriorOptimal π :=
  P.priorOptimal_of_updatefulPolicy hpol hRp hL π
    ((P.oneStepPolicy_iff_updatefulPolicy hhome (P.reflective_of_reflectivePolicy hRp) hN π).mp h1)

/-- **The averaging step under `LocalUtility` alone**: the updateful value at `T` for the action
`π T` equals the cell value of `π`, for any positive cell `state = T ∧ pp = π`.
Source: mandate T6(i), T7
Kind: P
Fidelity: exact
Hyps: (a) `LocalUtility`, `0 < cellMass T π`; does not use faith -/
theorem homeEU_eq_cellEU_of_localUtility (hL : P.LocalUtility) (T : ↥𝒟) (π : Policy 𝒟 A)
    (hcell : 0 < P.cellMass T π) : P.homeEU T (π T) = P.cellEU T π := by
  have hhome : 0 < P.jointMass T T (π T) :=
    lt_of_lt_of_le hcell (P.cellMass_le_jointMass T π (π T) rfl)
  unfold homeEU condEU
  apply condExp_eq_of_fibers P.μ P.U P.μ_nonneg _ P.pp (P.cellEU T π) hhome
  intro π' hπ'
  by_cases he : π' T = π T
  · have hcongr : condExp P.μ P.U (fun ω => (P.state ω = T ∧ P.pp ω T = π T) ∧ P.pp ω = π') =
        P.cellEU T π' := by
      apply condExp_congr
      intro ω
      constructor
      · rintro ⟨⟨hs, _⟩, hp⟩; exact ⟨hs, hp⟩
      · rintro ⟨hs, hp⟩; exact ⟨⟨hs, hp ▸ he⟩, hp⟩
    have hmass : P.cellMass T π' = massOf P.μ (fun ω => (P.state ω = T ∧ P.pp ω T = π T) ∧
        P.pp ω = π') := by
      apply massOf_congr
      intro ω
      constructor
      · rintro ⟨hs, hp⟩; exact ⟨⟨hs, hp ▸ he⟩, hp⟩
      · rintro ⟨⟨hs, _⟩, hp⟩; exact ⟨hs, hp⟩
    rw [hcongr]
    exact hL T π' π he (hmass ▸ hπ') hcell
  · exfalso
    have : massOf P.μ (fun ω => (P.state ω = T ∧ P.pp ω T = π T) ∧ P.pp ω = π') = 0 := by
      unfold massOf
      apply Finset.sum_eq_zero
      intro ω _
      rw [if_neg]
      rintro ⟨⟨_, hpa⟩, hp⟩
      exact he (hp ▸ hpa)
    rw [this] at hπ'
    exact lt_irrefl _ hπ'

/-- The mass of the triple cell as a fiber of the joint cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triMass_eq_fiber (S T T' : ↥𝒟) (a c : A) :
    P.triMass S T T' a c =
      massOf P.μ (fun ω => (P.state ω = S ∧ P.pp ω T = a) ∧ P.pp ω T' = c) :=
  massOf_congr _ (fun ω => and_assoc.symm)

/-- **Under `LocalUtility ∧ IndependentPointsGivenState`, the other branch's expectation given the
point at `T` is `∑_c μ(pp · T' = c | state = T') · homeEU T' c`** — a formula that does not
mention the point at `T`.
Source: mandate T7
Kind: C
Fidelity: exact
Hyps: (a) `LocalUtility`, `IndependentPointsGivenState`, `T' ≠ T`, `0 < jointMass T' T a`; does
not use faith -/
theorem condEU_eq_of_localUtility_indepGivenState (hL : P.LocalUtility)
    (hI : P.IndependentPointsGivenState) (T T' : ↥𝒟) (hne : T' ≠ T) (a : A)
    (hpos : 0 < P.jointMass T' T a) :
    P.condEU T' T a = ∑ c, P.jointMass T' T' c / P.stateMass T' * P.homeEU T' c := by
  have hS : 0 < P.stateMass T' := P.stateMass_pos_of_jointMass_pos hpos
  unfold condEU
  rw [condExp_fiberwise P.μ P.U P.μ_nonneg _ (fun ω => P.pp ω T')]
  apply Finset.sum_congr rfl
  intro c _
  have hI' := hI T' T T' a c (fun h => hne h.symm)
  rw [P.triMass_eq_fiber] at hI'
  by_cases hfib : 0 < massOf P.μ (fun ω => (P.state ω = T' ∧ P.pp ω T = a) ∧ P.pp ω T' = c)
  · -- weight
    have hw : massOf P.μ (fun ω => (P.state ω = T' ∧ P.pp ω T = a) ∧ P.pp ω T' = c) /
        massOf P.μ (fun ω => P.state ω = T' ∧ P.pp ω T = a) =
        P.jointMass T' T' c / P.stateMass T' := by
      change _ / P.jointMass T' T a = _
      rw [div_eq_div_iff (ne_of_gt hpos) (ne_of_gt hS)]
      linarith [hI']
    -- value
    have hv : condExp P.μ P.U (fun ω => (P.state ω = T' ∧ P.pp ω T = a) ∧ P.pp ω T' = c) =
        P.homeEU T' c := by
      apply condExp_eq_of_fibers P.μ P.U P.μ_nonneg _ P.pp (P.homeEU T' c) hfib
      intro π hπ
      by_cases hπc : π T = a ∧ π T' = c
      · have hcongr : condExp P.μ P.U
            (fun ω => ((P.state ω = T' ∧ P.pp ω T = a) ∧ P.pp ω T' = c) ∧ P.pp ω = π) =
            P.cellEU T' π := by
          apply condExp_congr
          intro ω
          constructor
          · rintro ⟨⟨⟨hs, _⟩, _⟩, hp⟩; exact ⟨hs, hp⟩
          · rintro ⟨hs, hp⟩; exact ⟨⟨⟨hs, hp ▸ hπc.1⟩, hp ▸ hπc.2⟩, hp⟩
        have hmass : P.cellMass T' π = massOf P.μ
            (fun ω => ((P.state ω = T' ∧ P.pp ω T = a) ∧ P.pp ω T' = c) ∧ P.pp ω = π) := by
          apply massOf_congr
          intro ω
          constructor
          · rintro ⟨hs, hp⟩; exact ⟨⟨⟨hs, hp ▸ hπc.1⟩, hp ▸ hπc.2⟩, hp⟩
          · rintro ⟨⟨⟨hs, _⟩, _⟩, hp⟩; exact ⟨hs, hp⟩
        rw [hcongr, ← hπc.2]
        exact (P.homeEU_eq_cellEU_of_localUtility hL T' π (hmass ▸ hπ)).symm
      · exfalso
        have : massOf P.μ
            (fun ω => ((P.state ω = T' ∧ P.pp ω T = a) ∧ P.pp ω T' = c) ∧ P.pp ω = π) = 0 := by
          unfold massOf
          apply Finset.sum_eq_zero
          intro ω _
          rw [if_neg]
          rintro ⟨⟨⟨_, hpa⟩, hpc⟩, hp⟩
          exact hπc ⟨hp ▸ hpa, hp ▸ hpc⟩
        rw [this] at hπ
        exact lt_irrefl _ hπ
    rw [hw, hv]
  · have hz : massOf P.μ (fun ω => (P.state ω = T' ∧ P.pp ω T = a) ∧ P.pp ω T' = c) = 0 :=
      le_antisymm (not_lt.mp hfib) (massOf_nonneg _ P.μ_nonneg _)
    rw [hz, zero_mul] at hI'
    have hzc : P.jointMass T' T' c = 0 := by
      rcases mul_eq_zero.mp hI'.symm with h | h
      · exact absurd h (ne_of_gt hpos)
      · exact h
    rw [hz, hzc, zero_div, zero_div, zero_mul, zero_mul]

/-- **`LocalUtility ∧ IndependentPointsGivenState → NoCrossBranch`**.
Source: mandate §3.5, T7
Kind: C
Fidelity: exact
Hyps: (a) `LocalUtility`, `IndependentPointsGivenState`; does not use faith -/
theorem noCrossBranch_of_localUtility_indepGivenState (hL : P.LocalUtility)
    (hI : P.IndependentPointsGivenState) : P.NoCrossBranch := by
  intro T T' a b hne hpa hpb
  rw [P.condEU_eq_of_localUtility_indepGivenState hL hI T T' hne a hpa,
    P.condEU_eq_of_localUtility_indepGivenState hL hI T T' hne b hpb]

/-- `pairMass T T' a b = ∑_π [π T = a ∧ π T' = b] · policyMass π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairMass_eq_sum_policyMass (T T' : ↥𝒟) (a b : A) :
    P.pairMass T T' a b = ∑ π, if π T = a ∧ π T' = b then P.policyMass π else 0 := by
  unfold pairMass policyMass
  rw [massOf_fiberwise P.μ _ P.pp]
  apply Finset.sum_congr rfl
  intro π _
  by_cases hπ : π T = a ∧ π T' = b
  · rw [if_pos hπ]
    exact massOf_congr _ (fun ω => by
      constructor
      · rintro ⟨_, hp⟩; exact hp
      · intro hp; exact ⟨⟨hp ▸ hπ.1, hp ▸ hπ.2⟩, hp⟩)
  · rw [if_neg hπ]
    unfold massOf
    apply Finset.sum_eq_zero
    intro ω _
    rw [if_neg]
    rintro ⟨⟨hpa, hpb⟩, hp⟩
    exact hπ ⟨hp ▸ hpa, hp ▸ hpb⟩

/-- `triMass S T T' a b = ∑_π [π T = a ∧ π T' = b] · cellMass S π`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma triMass_eq_sum_cellMass (S T T' : ↥𝒟) (a b : A) :
    P.triMass S T T' a b = ∑ π, if π T = a ∧ π T' = b then P.cellMass S π else 0 := by
  unfold triMass cellMass
  rw [massOf_fiberwise P.μ _ P.pp]
  apply Finset.sum_congr rfl
  intro π _
  by_cases hπ : π T = a ∧ π T' = b
  · rw [if_pos hπ]
    exact massOf_congr _ (fun ω => by
      constructor
      · rintro ⟨⟨hs, _⟩, hp⟩; exact ⟨hs, hp⟩
      · rintro ⟨hs, hp⟩; exact ⟨⟨hs, hp ▸ hπ.1, hp ▸ hπ.2⟩, hp⟩)
  · rw [if_neg hπ]
    unfold massOf
    apply Finset.sum_eq_zero
    intro ω _
    rw [if_neg]
    rintro ⟨⟨_, hpa, hpb⟩, hp⟩
    exact hπ ⟨hp ▸ hpa, hp ▸ hpb⟩

/-- **`IndependentPoints ∧ ReflectivePolicy → IndependentPointsGivenState`**: when no policy moves
the branch probabilities, unconditional independence of the points is independence given the
state.
Source: mandate T7 ("or the exact relation you find")
Kind: C
Fidelity: exact
Hyps: (a) `IndependentPoints`, `ReflectivePolicy`; does not use faith -/
theorem indepGivenState_of_indep_reflectivePolicy (hI : P.IndependentPoints)
    (hR : P.ReflectivePolicy) : P.IndependentPointsGivenState := by
  intro S T T' a b hne
  have htri : P.triMass S T T' a b = P.stateMass S * P.pairMass T T' a b := by
    rw [P.triMass_eq_sum_cellMass, P.pairMass_eq_sum_policyMass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro π _
    split_ifs
    · exact P.cellMass_eq_of_reflectivePolicy' hR S π
    · rw [mul_zero]
  have hj : ∀ (T₀ : ↥𝒟) (c : A), P.jointMass S T₀ c = P.stateMass S * P.ppMass T₀ c := by
    intro T₀ c
    rw [P.jointMass_eq_sum_cellMass S T₀ c, P.ppMass_eq_sum_policyMass T₀ c, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro π _
    split_ifs
    · exact P.cellMass_eq_of_reflectivePolicy' hR S π
    · rw [mul_zero]
  rw [htri, hj, hj, hI T T' a b hne]
  ring

/-! ## The trivial procedure layer -/

/-- **The trivial procedure layer**: procedures are policies, `eff = id`.
Source: mandate §3.6
Kind: D
Fidelity: exact -/
def trivialLayer : ProcLayer P where
  Proc := Policy 𝒟 A
  proc := P.pp
  eff := id
  pp_eff := fun _ => rfl

/-- **Policy Fairness holds on the trivial layer for every prior** — because `eff p = eff q`
means `p = q`. This is the squeeze `udt-paper-tiling` must not ship as content: without a
procedure coordinate distinct from the policy, fairness says nothing.
Source: mandate §3.6 ("Kind T, labelled as such"); bli-paper-047
Kind: T
Fidelity: exact (and vacuous, by design of the layer)
Hyps: (a) none -/
theorem policyFair_trivialLayer : P.PolicyFair (trivialLayer P) := by
  intro p q hpq _ _
  have : p = q := hpq
  rw [this]

end FiniteBLIPrior

end Cleanroom.Bli.UdtBliCore
