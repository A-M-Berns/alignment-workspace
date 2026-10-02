import Cleanroom.Decision.DpFaithfulUdt.BestReply

/-!
# The cluster branch of `Π_A`: UDT1.1 is EDT at the relocated root (T11(d))

T11(d) of [[dp-faithful-udt-mandate]] (`firstperson.md` §6 step 4, FP-10, FP-12′(ii)'s cluster
half). The cluster branch of `Π_A` maximises the prior's value over whole cluster policies:
`π* ∈ Unif argmax_{σ ∈ Π_U : P_{s°}(ρ(σ)) > 0} V_{s°}(ρ(σ))`, `ρ(σ) := ∧_{e ∈ U} ρ_e(σ(e)) = {pol = σ}`
(`polTuple`, the relocated root's action event `actEvR … (.inr ()) σ`). Under masked prior
calibration to `lift U C'` on `Rel_U B` with `U ⊇ queried B`:

* `P_{s°}(pol = σ) = ∏_{e ∈ U} C'(e)(σ e)` (`polTuple_pr`), positive for a full-support self-model,
  so the domain is all of `Π_U` (`clusterDomain_eq_univ`; the strict rule collapses it,
  Remark 3.6);
* `V_{s°}(pol = σ) = V_{Rel}((lift C')[d̂ ↦ σ]) = V_B(σ)` on **every** tree (`polTuple_V_reloc`,
  `polTuple_V`: Definition 11's clause 2 through the full-tuple analogue of `expPayoffPol_eq`
  and `value_deviate_root`, FR-7(a)) — the "FR-6" step of §6 needs no almost-fairness at the
  pure grade;
* hence `clusterBranch s° U = argmax_σ V_B(σ)` (`mem_clusterBranch_iff`), and on almost-fair
  trees every member is a globally optimal procedure (`clusterBranch_isOptimal`): **UDT1.1 = EDT
  at the relocated root attains `T_opt`** (Definition 21's vertex clause supplies the optimum).

Only the masked (strict, full-support) grade is used: at the relocated root `O = ⊤`, so the
masked prior is the observation-calibrated state there (`recordsForAll_root`); the limit grade of
(H′) is `dp-firstperson-sc`'s. The audit and the survivor branch are that package's as well.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpFaithfulUdt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpFairnessReloc
open Cleanroom.Decision.DpLocalOpt

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ### The full-tuple disposition event and its law -/

section tuple

variable (U : Finset ι) (B : Tree Ω ι acts K)

/-- **The joint disposition event** `ρ(σ) := {pol = σ}` on the relocated carrier: the relocated
root's action event at the tuple `σ` (`actEvR … (.inr ()) σ`), i.e. `∧_{e ∈ U} {pol_e = σ(e)}`.
Source: `firstperson.md` §6 step 1 ("`ρ(π) := ∧_{e∈U} ρ_e(π(e))`"); `dp-fairness-reloc` `actEvR`
Kind: D
Fidelity: exact -/
def polTuple (σ : (d : ↥U) → acts d) : Finset (RW Ω acts U) :=
  Finset.univ.filter fun w => w.2 = σ

/-- `polTuple` is the relocated root's action event. Source: none: infrastructure. Kind: L -/
theorem polTuple_eq_actEvR (actEv : (d : ι) → acts d → Finset Ω) (σ : (d : ↥U) → acts d) :
    polTuple U σ = actEvR U actEv (.inr ()) σ := rfl

/-- Membership in the joint disposition event. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_polTuple (σ : (d : ↥U) → acts d) (w : RW Ω acts U) :
    w ∈ polTuple U σ ↔ w.2 = σ := by
  simp [polTuple]

/-- The joint disposition event is the intersection of the point dispositions.
Source: `firstperson.md` §6 step 1
Kind: L -/
theorem polTuple_eq_iInter (σ : (d : ↥U) → acts d) (w : RW Ω acts U) :
    w ∈ polTuple U σ ↔ ∀ d : ↥U, w ∈ polEv U d (σ d) := by
  rw [mem_polTuple]
  constructor
  · intro h d
    rw [polEv_of_mem U d.2]
    simp [h]
  · intro h
    funext d
    have := h d
    rw [polEv_of_mem U d.2] at this
    simpa using this

variable (C'' : Proc (ι ⊕ Unit) (actsR acts U) K)

/-- The resolved branch's law is the same under `lift C'` and its root deviation (the root is
not queried inside a resolved branch).
Source: none: infrastructure (as in `dp-fairness-reloc`'s `expPayoffPol_eq`)
Kind: L -/
theorem leafLaw_resolve_deviate_root (σ τ : (d : ↥U) → acts d) (ℓ' : (resolve U τ B).Leaves) :
    leafLaw (C''.deviatePure (.inr ()) σ) (resolve U τ B) ℓ' =
      leafLaw C'' (resolve U τ B) ℓ' := by
  apply leafLaw_congr_queried
  intro p hp
  cases p with
  | inl d' => exact Proc.deviate_ne C'' _ (by simp)
  | inr u =>
      exfalso
      obtain ⟨ℓ'', hc⟩ := (mem_queried_iff (Sum.inr u) (resolve U τ B)).mp hp
      cases u
      have := (count_resolveW U (fun ω => (ω, τ)) τ B ℓ'').2
      unfold resolve at hc
      rw [this] at hc
      exact lt_irrefl _ hc

/-- **`ν_{Rel, C''}(pol = σ) = C''(d̂)(σ)`** for *any* procedure `C''` on the relocated tree: the joint
disposition's probability is the root law's weight at `σ` (the full-tuple form of `nu_pol_eq`;
the root law need not be a product — FA-15's correlated priors live here).
Source: `fair-repair.md` FR-2 (the root tuple's law), FR-9(iv); `faithful.md` FA-15
Kind: P
Fidelity: exact
Hyps: none -/
theorem nu_polTuple_root (σ : (d : ↥U) → acts d) :
    nu C'' (relocRoot U B) (polTuple U σ) = (C'' (.inr ())).w σ := by
  unfold nu mass worldEv relocRoot
  rw [Finset.sum_filter, sum_leaves_decision]
  have hbranch : ∀ τ : (d : ↥U) → acts d, ∀ ℓ' : (resolve U τ B).Leaves,
      ((resolve U τ B).world ℓ').2 = τ := by
    intro τ ℓ'
    unfold resolve
    rw [world_resolveW]
  rw [Finset.sum_eq_single σ]
  · have this : ∀ ℓ' : (resolve U σ B).Leaves,
        (if (world (Tree.decision (Sum.inr ()) fun τ => resolve U τ B) ⟨σ, ℓ'⟩) ∈ polTuple U σ then
          leafLaw C'' (Tree.decision (Sum.inr ()) fun τ => resolve U τ B) ⟨σ, ℓ'⟩ else 0) =
        (C'' (.inr ())).w σ * leafLaw C'' (resolve U σ B) ℓ' := by
      intro ℓ'
      rw [if_pos (by rw [mem_polTuple]; exact hbranch σ ℓ')]
      rfl
    simp only [this, ← Finset.mul_sum, sum_leafLaw, mul_one]
  · intro τ _ hτ
    apply Finset.sum_eq_zero
    intro ℓ' _
    rw [if_neg]
    rw [mem_polTuple]
    show ((resolve U τ B).world ℓ').2 ≠ σ
    rw [hbranch τ ℓ']; exact hτ
  · intro h; exact absurd (Finset.mem_univ σ) h

/-- **`𝔼_{Rel, C''}[r · 1_{pol = σ}] = C''(d̂)(σ) · V_{Rel}(C''[d̂ ↦ σ])`** for any procedure `C''` on the
relocated tree: the joint disposition's payoff mass is the root weight times the root's act
value at `σ` (the full-tuple form of `expPayoffPol_eq`).
Source: `fair-repair.md` FR-2; `spectrum.md` SP-3 (the root's act values)
Kind: P
Fidelity: exact
Hyps: none -/
theorem paySum_polTuple_root (σ : (d : ↥U) → acts d) :
    paySum C'' (relocRoot U B) (polTuple U σ) =
      (C'' (.inr ())).w σ * value (C''.deviatePure (.inr ()) σ) (relocRoot U B) := by
  unfold paySum worldEv value relocRoot
  rw [Finset.sum_filter, sum_leaves_decision, sum_leaves_decision, Finset.mul_sum]
  have hbranch : ∀ τ : (d : ↥U) → acts d, ∀ ℓ' : (resolve U τ B).Leaves,
      ((resolve U τ B).world ℓ').2 = τ := by
    intro τ ℓ'
    unfold resolve
    rw [world_resolveW]
  have hw : ∀ τ : (d : ↥U) → acts d,
      (C''.deviatePure (Sum.inr ()) σ (Sum.inr ())).w τ = if τ = σ then 1 else 0 := by
    intro τ
    rw [Proc.deviatePure, Proc.deviate_same, FinDistr.pure_w]
  refine Finset.sum_congr rfl fun τ _ => ?_
  by_cases hτ : τ = σ
  · subst hτ
    have hleft : ∀ ℓ' : (resolve U τ B).Leaves,
        (if (world (Tree.decision (Sum.inr ()) fun τ => resolve U τ B) ⟨τ, ℓ'⟩) ∈ polTuple U τ then
          leafLaw C'' (Tree.decision (Sum.inr ()) fun τ => resolve U τ B) ⟨τ, ℓ'⟩ *
            payoff (Tree.decision (Sum.inr ()) fun τ => resolve U τ B) ⟨τ, ℓ'⟩ else 0) =
        (C'' (.inr ())).w τ * leafLaw C'' (resolve U τ B) ℓ' *
          payoff (resolve U τ B) ℓ' := by
      intro ℓ'
      rw [if_pos (by rw [mem_polTuple]; exact hbranch τ ℓ')]
      rfl
    have hright : ∀ ℓ' : (resolve U τ B).Leaves,
        leafLaw (C''.deviatePure (Sum.inr ()) τ)
            (Tree.decision (Sum.inr ()) fun τ => resolve U τ B) ⟨τ, ℓ'⟩ *
          payoff (Tree.decision (Sum.inr ()) fun τ => resolve U τ B) ⟨τ, ℓ'⟩ =
        leafLaw C'' (resolve U τ B) ℓ' * payoff (resolve U τ B) ℓ' := by
      intro ℓ'
      show (C''.deviatePure (Sum.inr ()) τ (Sum.inr ())).w τ *
        leafLaw (C''.deviatePure (Sum.inr ()) τ) (resolve U τ B) ℓ' *
          payoff (resolve U τ B) ℓ' = _
      rw [hw, if_pos rfl, leafLaw_resolve_deviate_root U B C'' τ τ ℓ', one_mul]
    simp only [hleft, hright, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ' _ => ?_
    ring
  · have hleft : ∀ ℓ' : (resolve U τ B).Leaves,
        (if (world (Tree.decision (Sum.inr ()) fun τ => resolve U τ B) ⟨τ, ℓ'⟩) ∈ polTuple U σ then
          leafLaw C'' (Tree.decision (Sum.inr ()) fun τ => resolve U τ B) ⟨τ, ℓ'⟩ *
            payoff (Tree.decision (Sum.inr ()) fun τ => resolve U τ B) ⟨τ, ℓ'⟩ else 0) = 0 := by
      intro ℓ'
      rw [if_neg]
      rw [mem_polTuple]
      show ((resolve U τ B).world ℓ').2 ≠ σ
      rw [hbranch τ ℓ']; exact hτ
    have hright : ∀ ℓ' : (resolve U τ B).Leaves,
        leafLaw (C''.deviatePure (Sum.inr ()) σ)
            (Tree.decision (Sum.inr ()) fun τ => resolve U τ B) ⟨τ, ℓ'⟩ *
          payoff (Tree.decision (Sum.inr ()) fun τ => resolve U τ B) ⟨τ, ℓ'⟩ = 0 := by
      intro ℓ'
      show (C''.deviatePure (Sum.inr ()) σ (Sum.inr ())).w τ *
        leafLaw (C''.deviatePure (Sum.inr ()) σ) (resolve U τ B) ℓ' *
          payoff (resolve U τ B) ℓ' = 0
      rw [hw, if_neg hτ]; ring
    simp only [hleft, hright, Finset.sum_const_zero, mul_zero]

/-- **`ν_{Rel, lift C'}(pol = σ) = ∏_{e ∈ U} C'(e)(σ e)`**: under the lifted self-model the joint
disposition's probability is the product weight.
Source: `fair-repair.md` FR-2; `firstperson.md` §6 step 4
Kind: L -/
theorem nu_polTuple (C' : Proc ι acts K) (σ : (d : ↥U) → acts d) :
    nu (lift U C') (relocRoot U B) (polTuple U σ) = ∏ d : ↥U, (C' d).w (σ d) := by
  rw [nu_polTuple_root, lift_inr, FinDistr.pi_w]

/-- **`𝔼_{Rel, lift C'}[r · 1_{pol = σ}] = (∏_e C'(e)(σ e)) · V_{Rel}((lift C')[d̂ ↦ σ])`** (the
full-tuple form of `expPayoffPol_eq`).
Source: `fair-repair.md` FR-2; `spectrum.md` SP-3
Kind: L -/
theorem paySum_polTuple (C' : Proc ι acts K) (σ : (d : ↥U) → acts d) :
    paySum (lift U C') (relocRoot U B) (polTuple U σ) =
      (∏ d : ↥U, (C' d).w (σ d)) * value ((lift U C').deviatePure (.inr ()) σ) (relocRoot U B) := by
  rw [paySum_polTuple_root, lift_inr, FinDistr.pi_w]

end tuple

/-! ### The cluster branch -/

section cluster

variable (U : Finset ι) (B : Tree Ω ι acts K) (C' : Proc ι acts K) (s₀ : State (RW Ω acts U) K)

/-- `P_{s°}(pol = σ) = ∏_e C'(e)(σ e)` under prior calibration to `lift U C'`.
Source: `firstperson.md` §6 step 4
Kind: L -/
theorem polTuple_pr (hcal : PriorCalibrated (lift U C') (relocRoot U B) s₀)
    (σ : (d : ↥U) → acts d) : s₀.pr (polTuple U σ) = ∏ d : ↥U, (C' d).w (σ d) := by
  rw [hcal.1, nu_polTuple]

/-- **`V_{s°}(pol = σ) = V_{Rel}((lift C')[d̂ ↦ σ])` on every tree** under prior calibration to a
self-model giving `σ` positive weight (Definition 11's clause 2 at the joint disposition).
Source: `firstperson.md` §6 step 4 ("`= EDT` at the relocated root"); `fair-repair.md` FR-8
Kind: P
Fidelity: exact (every tree)
Hyps: (a) `PriorCalibrated (lift U C') (Rel_U B) s°`; (a) `0 < ∏_e C'(e)(σ e)` -/
theorem polTuple_V_reloc (hcal : PriorCalibrated (lift U C') (relocRoot U B) s₀)
    (σ : (d : ↥U) → acts d) (hpos : 0 < ∏ d : ↥U, (C' d).w (σ d)) :
    s₀.V (polTuple U σ) = value ((lift U C').deviatePure (.inr ()) σ) (relocRoot U B) := by
  have h := hcal.2 (polTuple U σ) (by rw [nu_polTuple]; exact hpos)
  rw [nu_polTuple, paySum_polTuple] at h
  rw [mul_comm] at h
  exact mul_left_cancel₀ hpos.ne' h

/-- **`V_{s°}(pol = σ) = V_B(σ)`**: the prior's value of the joint disposition is the input's pure
value at (any extension of) `σ`, on every tree with `U ⊇ queried B` — FR-6/FR-7(a) at the pure
grade, through `value_deviate_root`.
Source: `firstperson.md` §6 step 4 ("FR-6 (almost fair ⇒ `V_{s°}(ρ(π)) = V_B(π)`)"), FP-10
("`Π_A` with masked/limit prior-calibrated `s°` has `V_{s°}(ρ(π)) = V_B(π)`")
Kind: C
Fidelity: stronger (every tree, not only almost-fair: the pure grade of relocation is exact)
Hyps: (a) `queried B ⊆ U`; (a) `PriorCalibrated (lift U C') (Rel_U B) s°`; (a) `0 < ∏_e C'(e)(σ e)` -/
theorem polTuple_V (hU : queried B ⊆ U) (hcal : PriorCalibrated (lift U C') (relocRoot U B) s₀)
    (σ : (d : ↥U) → acts d) (hpos : 0 < ∏ d : ↥U, (C' d).w (σ d)) :
    s₀.V (polTuple U σ) = value (Proc.ofFun (extendTuple U σ)) B := by
  rw [polTuple_V_reloc U B C' s₀ hcal σ hpos, value_deviate_root U B hU]

/-- **The cluster branch's domain** `{σ ∈ Π_U : P_{s°}(pol = σ) > 0}` (Definition 17's domain at
the relocated root).
Source: `firstperson.md` §6 step 4 ("`π* ∈ Unif argmax_{π ∈ Π_U : P_{s°}(ρ(π)) > 0} V_{s°}(ρ(π))`")
Kind: D -/
def clusterDomain : Finset ((d : ↥U) → acts d) :=
  Finset.univ.filter fun σ => 0 < s₀.pr (polTuple U σ)

/-- **The cluster branch of `Π_A`** (UDT1.1 on the cluster): the argmax of `V_{s°}(pol = σ)` over the
domain — EDT at the relocated root, read as a set of joint policies (Definition 17's uniform
tie convention then selects uniformly from it).
Source: `firstperson.md` §6 step 4 ("UDT1.1 on the cluster; `=` EDT at the relocated root"), D9
Kind: D
Fidelity: exact -/
def clusterBranch : Finset ((d : ↥U) → acts d) :=
  (clusterDomain U s₀).filter fun σ =>
    ∀ τ ∈ clusterDomain U s₀, s₀.V (polTuple U τ) ≤ s₀.V (polTuple U σ)

/-- Under masked calibration (full-support self-model) the domain is all of `Π_U`.
Source: `firstperson.md` §6 step 4 ("limit prior calibration makes the domain all of `Π_U`
(strict collapses it, Remark 3.6)")
Kind: L -/
theorem clusterDomain_eq_univ (hfs : C'.FullSupport)
    (hcal : PriorCalibrated (lift U C') (relocRoot U B) s₀) :
    clusterDomain U s₀ = Finset.univ := by
  ext σ
  simp only [clusterDomain, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  rw [polTuple_pr U B C' s₀ hcal]
  exact Finset.prod_pos fun d _ => hfs d (σ d)

/-- **The cluster branch is the argmax of `V_B` over joint policies**: under masked prior
calibration with `U ⊇ queried B`, `σ ∈ clusterBranch ⟺ V_B(τ) ≤ V_B(σ)` for every tuple `τ`.
Source: `firstperson.md` §6 step 4, FP-10 ("UDT1.1 = Remark 6.2's `UDT_B`")
Kind: C
Fidelity: exact
Hyps: (a) `queried B ⊆ U`; (a) `MaskedPriorCalibrated (lift U C') (Rel_U B) s°` -/
theorem mem_clusterBranch_iff (hU : queried B ⊆ U)
    (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀) (σ : (d : ↥U) → acts d) :
    σ ∈ clusterBranch U s₀ ↔
      ∀ τ, value (Proc.ofFun (extendTuple U τ)) B ≤ value (Proc.ofFun (extendTuple U σ)) B := by
  have hfs : C'.FullSupport := fun d a => hcal.1 (.inl d) a
  have hpos : ∀ σ : (d : ↥U) → acts d, 0 < ∏ d : ↥U, (C' d).w (σ d) :=
    fun σ => Finset.prod_pos fun d _ => hfs d (σ d)
  simp only [clusterBranch, Finset.mem_filter, clusterDomain_eq_univ U B C' s₀ hfs hcal.2,
    Finset.mem_univ, true_and, true_implies]
  constructor
  · intro h τ
    have := h τ
    rwa [polTuple_V U B C' s₀ hU hcal.2 τ (hpos τ), polTuple_V U B C' s₀ hU hcal.2 σ (hpos σ)]
      at this
  · intro h τ
    rw [polTuple_V U B C' s₀ hU hcal.2 τ (hpos τ), polTuple_V U B C' s₀ hU hcal.2 σ (hpos σ)]
    exact h τ

/-- The cluster branch is nonempty under masked calibration. Source: none: infrastructure.
Kind: L -/
theorem clusterBranch_nonempty (hU : queried B ⊆ U)
    (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀) :
    (clusterBranch U s₀).Nonempty := by
  obtain ⟨σ, -, hσ⟩ := Finset.exists_max_image Finset.univ
    (fun σ : (d : ↥U) → acts d => value (Proc.ofFun (extendTuple U σ)) B) Finset.univ_nonempty
  exact ⟨σ, (mem_clusterBranch_iff U B C' s₀ hU hcal σ).mpr fun τ => hσ τ (Finset.mem_univ τ)⟩

/-- Every deterministic procedure is the extension of its own tuple on `U ⊇ queried B`, in value.
Source: none: infrastructure
Kind: L -/
theorem value_ofFun_extendTuple (hU : queried B ⊆ U) (π : (d : ι) → acts d) :
    value (Proc.ofFun (extendTuple U fun d => π d)) B = value (Proc.ofFun π) B := by
  apply value_congr_queried
  intro d hd
  simp [Proc.ofFun, extendTuple, hU hd]

/-- **T11(d) — the cluster branch attains `T_opt` on almost-fair trees**: every member of the
cluster branch extends to a globally optimal procedure (`IsOptimal`) — UDT1.1 = EDT at the
relocated root attains the optimum (Definition 21's vertex clause through
`pureOptimal_iff_isOptimal_of_almostFair`).
Scope: almost-fair `B`, `U ⊇ queried B`, masked prior calibration (the strict rule with a
full-support self-model); the limit grade of (H′) is `dp-firstperson-sc`'s.
Source: `firstperson.md` §6 step 4 ("FP-12′ (`T_opt` under (H)+(H′))"), FP-12′(ii) (cluster half),
FP-10 ("UDT1.1 = Remark 6.2's `UDT_B`"); dp-cf-113
Kind: C
Fidelity: variant: the masked grade in place of (H′)'s limit grade (at the root `O = ⊤`,
`recordsForAll_root`), as the mandate sanctions
Hyps: (a) `AlmostFair B`; (a) `queried B ⊆ U`; (a) `MaskedPriorCalibrated (lift U C') (Rel_U B) s°` -/
theorem clusterBranch_isOptimal (hB : AlmostFair B) (hU : queried B ⊆ U)
    (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀) (σ : (d : ↥U) → acts d)
    (hσ : σ ∈ clusterBranch U s₀) : IsOptimal (Proc.ofFun (extendTuple U σ)) B := by
  rw [← pureOptimal_iff_isOptimal_of_almostFair B hB]
  intro π
  rw [← value_ofFun_extendTuple U B hU π]
  exact (mem_clusterBranch_iff U B C' s₀ hU hcal σ).mp hσ _

/-- **The componentwise `UDT_{s°,pol}` and the cluster branch read the same prior state**: the
point disposition `pol_d = a` is the union of the joint dispositions through `a` at `d`, so the
cluster branch consumes `|Π_U|` values where `UDT_{s°,pol}` consumes `1 + ∑_d (|A_d| − 1)`
(`DataCost.lean`, FP-14′); the two procedures differ (`PiB.lean`, the Stag Hunt).
Source: `firstperson.md` FP-10 ("coincide iff `|U| = 1`")
Kind: L -/
theorem polEv_eq_biUnion_polTuple {d : ι} (h : d ∈ U) (a : acts d) :
    polEv (Ω := Ω) U d a = ((Finset.univ : Finset ((d : ↥U) → acts d)).filter fun σ => σ ⟨d, h⟩ = a).biUnion
      (polTuple U) := by
  ext w
  rw [polEv_of_mem U h]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, mem_polTuple]
  constructor
  · intro hw; exact ⟨w.2, hw, rfl⟩
  · rintro ⟨σ, hσ, rfl⟩; exact hσ

end cluster

end Cleanroom.Decision.DpFaithfulUdt
