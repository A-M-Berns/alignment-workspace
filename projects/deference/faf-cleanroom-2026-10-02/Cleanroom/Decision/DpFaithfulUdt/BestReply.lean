import Cleanroom.Decision.DpFaithfulUdt.Faithful
import Cleanroom.Decision.DpFairnessReloc.TopRepair
import Cleanroom.Decision.DpLocalOpt.Coherence
import Cleanroom.Decision.DpLocalOpt.Optima
import Cleanroom.Found.DpCoreTree.Seed

/-!
# FA-10′ — the inclusion criterion as a restatement (T3)

T3 of [[dp-faithful-udt-mandate]]. On almost-fair `B`, with `s°` masked-prior-calibrated under
`lift U C'` and `U ⊇ queried B`, `T_opt(UDT_{s°,pol}, B)` holds iff every profile of componentwise
best replies to `C'` is a joint optimum: `∏_d supp BR_d(C') ⊆ Π*`
(`isOptimal_udtProc_iff_support_subset_optima`). **This is a restatement**, not a criterion: it is
"a product mixture with positive weights is optimal iff its support lies in `Π*`" (the product
mixture is `dp-core-tree`'s `value'_eq_product_mixture` on almost-fair trees,
`value_eq_product_mixture`) with `supp UDT(d) = BR_d(C')` substituted (T2), and it is not a
condition on `(s°, ρ)` checkable without `V_B` (faithful.md Dead 5). The almost-fair scope is
essential: on the AMD the inclusion holds and optimality fails (`amd_inclusion_not_optimal`).

`Π*` is the source's set of optimal *assignments* (`PureOptimal`: best among deterministic
procedures), which on almost-fair trees is the set of globally optimal deterministic procedures
(`pureOptimal_iff_isOptimal_of_almostFair`); the AMD witness needs the pure reading.

Also here: the two mixture lemmas every "support lies in the argmax" argument uses, and the
pure-grade relocation exactness `value (lift U (ofFun π)) (Rel_U B) = value (ofFun π) B` (FR-7(a)),
consumed by the one-point and cUDT files.
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

/-! ### Two mixture lemmas -/

section mixture

variable {α : Type} [Fintype α]

/-- If a convex combination of values `x_i ≤ M` equals `M`, every value of positive weight is `M`.
Source: none: infrastructure
Kind: L -/
theorem eq_of_sum_eq_of_le (w : FinDistr K α) (x : α → K) (M : K) (hle : ∀ i, x i ≤ M)
    (hsum : ∑ i, w.w i * x i = M) : ∀ i, 0 < w.w i → x i = M := by
  intro i hi
  have hz : ∑ j, w.w j * (M - x j) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, w.sum_one, one_mul, hsum,
      sub_self]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun j _ =>
    mul_nonneg (w.nonneg j) (sub_nonneg.mpr (hle j))).mp hz i (Finset.mem_univ i)
  rcases mul_eq_zero.mp hterm with h | h
  · exact absurd h hi.ne'
  · linarith

/-- If every value of positive weight is `M`, the convex combination is `M`.
Source: none: infrastructure
Kind: L -/
theorem sum_eq_of_support (w : FinDistr K α) (x : α → K) (M : K)
    (h : ∀ i, 0 < w.w i → x i = M) : ∑ i, w.w i * x i = M := by
  calc ∑ i, w.w i * x i = ∑ i, w.w i * M := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rcases (w.nonneg i).lt_or_eq with hi | hi
        · rw [h i hi]
        · rw [← hi, zero_mul, zero_mul]
    _ = M := by rw [← Finset.sum_mul, w.sum_one, one_mul]

/-- A distribution has a supported element.
Source: none: infrastructure
Kind: L -/
theorem FinDistr.exists_pos (w : FinDistr K α) : ∃ i, 0 < w.w i := by
  by_contra h
  push Not at h
  have hz : ∑ i, w.w i = 0 :=
    Finset.sum_eq_zero fun i _ => le_antisymm (h i) (w.nonneg i)
  rw [w.sum_one] at hz
  exact one_ne_zero hz

end mixture

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-! ### The product mixture on almost-fair trees and the pure optimum set -/

section expansion

variable (B : Tree Ω ι acts K)

/-- **Definition 21's multiaffinity on almost-fair trees**: `V_B(C) = ∑_π (∏_{d ∈ queried B}
C(d)(π_d)) · V_B(π)` — the shared-seed product mixture (`dp-core-tree`'s
`value'_eq_product_mixture`) with `V_B = V'_B` on almost-fair trees.
Source: [[decision-problems-v2]] §6 Definition 21 (multiaffinity); `seeds.md` SE-1(a), SE-2
Corollary; `faithful.md` FA-10′ ("multiaffinity makes `V_B` of a product mixture the average of
`V_B(π)` over its support")
Kind: C -/
theorem value_eq_product_mixture (hB : AlmostFair B) (C : Proc ι acts K) :
    value C B =
      ∑ π : (d : ↥(queried B)) → acts d,
        (∏ d : ↥(queried B), (C d).w (π d)) * value (Proc.pureOn C (queried B) π) B := by
  rw [AlmostFair.value_eq_value' hB C, value'_eq_product_mixture]

/-- The pure profile `π` played on `queried B` with `C` elsewhere has the value of the
deterministic procedure extending `π`.
Source: none: infrastructure
Kind: L -/
theorem value_pureOn_eq (C : Proc ι acts K) (π : (d : ↥(queried B)) → acts d) :
    value (Proc.pureOn C (queried B) π) B = value (Proc.ofFun (extendTuple (queried B) π)) B := by
  apply value_congr_queried
  intro d hd
  rw [Proc.pureOn_of_mem C (queried B) π hd]
  simp [Proc.ofFun, extendTuple, hd]

/-- **`Π*`: the optimal assignments** — `π` is at least as good as every deterministic procedure.
Source: `faithful.md` FA-10′ (`Π*`), FA-14′ ("`π* ∈ Π*`")
Kind: D -/
def PureOptimal (π : (d : ι) → acts d) : Prop :=
  ∀ π' : (d : ι) → acts d, value (Proc.ofFun π') B ≤ value (Proc.ofFun π) B

/-- On almost-fair trees the optimal assignments are exactly the globally optimal deterministic
procedures (Definition 21's vertex clause, `exists_pure_isOptimal_of_almostFair`).
Source: [[decision-problems-v2]] §6 Definition 21; `dp-local-opt` `exists_pure_isOptimal_of_almostFair`
Kind: C -/
theorem pureOptimal_iff_isOptimal_of_almostFair (hB : AlmostFair B) (π : (d : ι) → acts d) :
    PureOptimal B π ↔ IsOptimal (Proc.ofFun π) B := by
  constructor
  · intro h C
    obtain ⟨σ, hσ⟩ := exists_pure_isOptimal_of_almostFair B hB
    exact (hσ C).trans (h σ)
  · intro h π'
    exact h (Proc.ofFun π')

/-- Deviating at an unqueried point does not change the value.
Source: none: infrastructure
Kind: L -/
theorem value_deviatePure_of_not_queried (C : Proc ι acts K) {d : ι} (hd : d ∉ queried B)
    (a : acts d) : value (C.deviatePure d a) B = value C B := by
  apply value_congr_queried
  intro e he
  have hne : e ≠ d := fun h => hd (h ▸ he)
  simp [Proc.deviatePure, Proc.deviate_ne C _ hne]

/-- At an unqueried point every action is a best reply.
Source: none: infrastructure
Kind: L -/
theorem BR_eq_univ_of_not_queried (C' : Proc ι acts K) {d : ι} (hd : d ∉ queried B) :
    BR C' B d = Finset.univ := by
  ext a
  simp only [mem_BR, Finset.mem_univ, iff_true]
  intro b
  rw [value_deviatePure_of_not_queried B C' hd, value_deviatePure_of_not_queried B C' hd]

end expansion

/-! ### Pure-grade relocation exactness (FR-7(a)) -/

section pureReloc

variable (U : Finset ι) (B : Tree Ω ι acts K)

/-- **FR-7(a) at the value level**: for `U ⊇ queried B`, `V_{Rel_U B}(lift (ofFun π)) = V_B(ofFun π)`
on *every* tree (the deterministic lift resolves every node to `π`; `value_deviate_root`).
Source: `fair-repair.md` FR-7(a) ("relocation is exact at the pure grade"); `dp-fairness-reloc`
`value_deviate_root`, `lift_ofFun`
Kind: C
Fidelity: exact (every tree, nested included) -/
theorem value_lift_ofFun (hU : queried B ⊆ U) (π : (d : ι) → acts d) :
    value (lift U (Proc.ofFun π)) (relocRoot U B) = value (Proc.ofFun π) B := by
  rw [lift_ofFun]
  have h1 : (Proc.ofFun (liftFun U π) : Proc (ι ⊕ Unit) (actsR acts U) K) =
      (Proc.ofFun (liftFun U π)).deviatePure (.inr ()) (fun d => π d) := by
    funext p
    cases p with
    | inl d => simp [Proc.deviatePure, Proc.deviate_ne]
    | inr u => cases u; rfl
  rw [h1, value_deviate_root U B hU]
  apply value_congr_queried
  intro d hd
  simp [Proc.ofFun, extendTuple, hU hd]

end pureReloc

/-! ### T3: the inclusion criterion -/

section inclusion

variable (U : Finset ι) (B : Tree Ω ι acts K) (C' : Proc ι acts K) (s₀ : State (RW Ω acts U) K)

/-- The weight `∏_{d ∈ queried B} UDT(d)(π_d)` is positive iff every coordinate is a best reply.
Source: none: infrastructure
Kind: L -/
theorem udtProc_prod_pos_iff (hB : AlmostFair B) (hU : queried B ⊆ U)
    (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀)
    (π : (d : ↥(queried B)) → acts d) :
    0 < (∏ d : ↥(queried B), (udtProc s₀ (polEv U) d).w (π d)) ↔
      ∀ d : ↥(queried B), π d ∈ BR C' B d := by
  constructor
  · intro hpos d
    rw [← udtProc_polEv_w_pos_iff U B C' s₀ hB hcal (hU d.2)]
    by_contra hle
    push Not at hle
    have h0 : (udtProc s₀ (polEv U) d).w (π d) = 0 :=
      le_antisymm hle ((udtProc s₀ (polEv U) d).nonneg _)
    have := Finset.prod_eq_zero (f := fun d : ↥(queried B) => (udtProc s₀ (polEv U) d).w (π d))
      (Finset.mem_univ d) h0
    rw [this] at hpos
    exact lt_irrefl _ hpos
  · intro h
    exact Finset.prod_pos fun d _ =>
      (udtProc_polEv_w_pos_iff U B C' s₀ hB hcal (hU d.2) (π d)).mpr (h d)

/-- **T3 — FA-10′, the inclusion criterion as a restatement**: on almost-fair `B`, for `U ⊇
queried B` and `s°` masked-prior-calibrated under `lift U C'`,
`T_opt(UDT_{s°,pol}, B) ⟺ ∀ π, (∀ d, π_d ∈ BR_d(C')) → π ∈ Π*` — the output is optimal iff every
profile of componentwise best replies to the self-model is an optimal assignment. **Restatement:**
this is "a product mixture with positive weights is optimal iff its support lies in `Π*`"
(multiaffinity, `value_eq_product_mixture`) with `supp UDT(d) = BR_d(C')` (T2) substituted; it is
not a condition on `(s°, ρ)` checkable without `V_B` (faithful.md Dead 5, §3 disposition), and it
is removed from the answer to open problem 6. Scope: almost-fair trees (the AMD fails it:
`amd_inclusion_not_optimal`), Definition 6, Definition 11 masked.
Source: `faithful.md` FA-10′ ("`T_opt(UDT_{s°,ρ}, B) ⟺ ∏_d supp BR_d(C') ⊆ Π*` … This restates
… it is not a condition on `(s°,ρ)` checkable without `V_B`"); dp-cf-2-007
Kind: C
Fidelity: exact (`Π*` = optimal assignments; on almost-fair trees = optimal deterministic
procedures, `pureOptimal_iff_isOptimal_of_almostFair`)
Hyps: (a) `AlmostFair B`; (a) `queried B ⊆ U`; (a) `MaskedPriorCalibrated (lift U C') (Rel_U B) s°` -/
theorem isOptimal_udtProc_iff_support_subset_optima (hB : AlmostFair B) (hU : queried B ⊆ U)
    (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀) :
    IsOptimal (udtProc s₀ (polEv U)) B ↔
      ∀ π : (d : ι) → acts d, (∀ d, π d ∈ BR C' B d) → PureOptimal B π := by
  set C := udtProc s₀ (polEv U) with hC
  obtain ⟨σ, hσ⟩ := exists_pure_isOptimal_of_almostFair B hB
  set M := value (Proc.ofFun σ) B with hM
  have hle : ∀ C'' : Proc ι acts K, value C'' B ≤ M := hσ
  -- the product mixture, as a distribution on the tuples
  set w : FinDistr K ((d : ↥(queried B)) → acts d) := FinDistr.pi (queried B) fun d => C d with hw
  have hexp : value C B = ∑ π, w.w π * value (Proc.ofFun (extendTuple (queried B) π)) B := by
    rw [value_eq_product_mixture B hB C]
    exact Finset.sum_congr rfl fun π _ => by rw [value_pureOn_eq, FinDistr.pi_w]
  have hwpos : ∀ π, 0 < w.w π ↔ ∀ d : ↥(queried B), π d ∈ BR C' B d := fun π => by
    rw [hw, FinDistr.pi_w]; exact udtProc_prod_pos_iff U B C' s₀ hB hU hcal π
  constructor
  · intro hopt π hπ
    have hval : value C B = M := le_antisymm (hle C) (hopt (Proc.ofFun σ))
    set π₀ : (d : ↥(queried B)) → acts d := fun d => π d with hπ₀
    have hpos : 0 < w.w π₀ := (hwpos π₀).mpr fun d => hπ d
    have hext : value (Proc.ofFun (extendTuple (queried B) π₀)) B = value (Proc.ofFun π) B := by
      apply value_congr_queried
      intro d hd
      simp [Proc.ofFun, extendTuple, hd, hπ₀]
    have := eq_of_sum_eq_of_le w (fun π => value (Proc.ofFun (extendTuple (queried B) π)) B) M
      (fun π => hle _) (by rw [← hexp, hval]) π₀ hpos
    rw [hext] at this
    intro π'
    rw [this]
    exact hle _
  · intro hall
    have hsum : ∑ π, w.w π * value (Proc.ofFun (extendTuple (queried B) π)) B = M := by
      apply sum_eq_of_support
      intro π hπ
      have hBR := (hwpos π).mp hπ
      have hπ' : ∀ d, extendTuple (queried B) π d ∈ BR C' B d := by
        intro d
        by_cases hd : d ∈ queried B
        · have := hBR ⟨d, hd⟩
          simpa [extendTuple, hd] using this
        · rw [BR_eq_univ_of_not_queried B C' hd]; exact Finset.mem_univ _
      exact le_antisymm (hle _) (hall _ hπ' σ)
    intro C''
    rw [hexp, hsum]
    exact hle C''

/-- **Corollary (`L`): the procedure-level identity `UDT_{s°,pol}(d) = π*_d` holds exactly where the
best reply at `d` is unique** — `UDT(d) = δ_{π*_d} ⟺ BR_d(C') = {π*_d}` for `d ∈ U`.
Source: `faithful.md` FA-10′ ("Procedure-level `UDT_{s°,ρ} = EDT(d̂)` … holds when `Π* = {π*}` and
`BR_d(C') = {π*_d}`")
Kind: L -/
theorem udtProc_polEv_eq_pure_iff (hB : AlmostFair B)
    (hcal : MaskedPriorCalibrated (lift U C') (relocRoot U B) s₀) {d : ι} (h : d ∈ U) (a₀ : acts d) :
    udtProc s₀ (polEv U) d = FinDistr.pure a₀ ↔ BR C' B d = {a₀} := by
  constructor
  · intro heq
    ext a
    rw [← udtProc_polEv_w_pos_iff U B C' s₀ hB hcal h, heq, FinDistr.pure_w, Finset.mem_singleton]
    split_ifs with ha <;> simp [ha]
  · intro hBR
    rw [udtProc_polEv_eq_bestReply U B C' s₀ hB hcal h]
    apply FinDistr.ext'
    intro a
    simp [uniformOn_w, hBR, FinDistr.pure_w]

end inclusion

/-! ### The AMD scope witness -/

section amd

open Cleanroom.Found.DpCoreTree.Catalogue

/-- `V_{amd}(δ_a) = 0`, `V_{amd}(δ_b) = 1`.
Source: `dp-core-tree` `amd_value` (`(1 − q)(3q + 1)`)
Kind: L -/
theorem amd_value_pure :
    value (Proc.ofFun fun _ => Act2.a) amd = 0 ∧ value (Proc.ofFun fun _ => Act2.b) amd = 1 := by
  have ha : (Proc.ofFun fun _ => Act2.a : Proc Unit (fun _ => Act2) ℚ) = procQ 1 zero_le_one le_rfl := by
    funext u; cases u; simp [Proc.ofFun, procQ, pure_a_eq_act2]
  have hb : (Proc.ofFun fun _ => Act2.b : Proc Unit (fun _ => Act2) ℚ) = procQ 0 le_rfl zero_le_one := by
    funext u; cases u; simp [Proc.ofFun, procQ, pure_b_eq_act2]
  rw [ha, hb, amd_value, amd_value]
  norm_num

/-- On a one-point tree the pure deviation of any self-model is the deterministic procedure.
Source: none: infrastructure
Kind: L -/
theorem deviatePure_unit_eq_ofFun {acts : Unit → Type} [∀ d, Fintype (acts d)]
    [∀ d, DecidableEq (acts d)] (C' : Proc Unit acts K) (act : acts ()) :
    C'.deviatePure () act = Proc.ofFun fun _ => act := by
  funext u; cases u; simp [Proc.deviatePure, Proc.ofFun]

/-- **The AMD scope witness for T3**: on the (nested) AMD with any full-support self-model `C'`
and `s°` masked-prior-calibrated under `lift C'`, the inclusion holds — the only best reply is
`b` (`V(δ_b) = 1 > 0 = V(δ_a)`) and `δ_b` is the optimal assignment — while `UDT_{s°,pol} = δ_b` is
not optimal (`1 < 4/3 = V(C(a) = ⅓)`): the almost-fair scope of FA-10′ is essential.
Source: `faithful.md` FA-10′ ("the almost-fair scope is essential (AMD: inclusion holds, `T_opt`
fails)"), FA-5 ("AMD: `max_a V(δ_a) = 1 < 4/3`")
Kind: N+
Fidelity: exact
Hyps: (a) `MaskedPriorCalibrated (lift {()} C') (Rel amd) s°` -/
theorem amd_inclusion_not_optimal (C' : Proc Unit (fun _ => Act2) ℚ)
    (s₀ : State (RW AmdW (fun _ => Act2) {()}) ℚ)
    (hcal : MaskedPriorCalibrated (lift {()} C') (relocRoot {()} amd) s₀) :
    (∀ π : Unit → Act2, (∀ d, π d ∈ BR C' amd d) → PureOptimal amd π) ∧
      BR C' amd () = {Act2.b} ∧
      udtProc s₀ (polEv {()}) = Proc.ofFun (fun _ => Act2.b) ∧
      ¬ IsOptimal (udtProc s₀ (polEv {()})) amd := by
  obtain ⟨hva, hvb⟩ := amd_value_pure
  have hdev : ∀ act : Act2,
      C'.deviatePure () act = (Proc.ofFun fun _ => act : Proc Unit (fun _ => Act2) ℚ) :=
    fun act => deviatePure_unit_eq_ofFun C' act
  have hvdev : ∀ act : Act2, value (C'.deviatePure () act) amd = if act = Act2.b then 1 else 0 := by
    intro act; rw [hdev]; cases act
    · rw [hva]; simp
    · rw [hvb]; simp
  have hBR : BR C' amd () = {Act2.b} := by
    ext act
    rw [mem_BR, Finset.mem_singleton]
    simp only [hvdev]
    cases act
    · constructor
      · intro h; have := h Act2.b; simp at this; norm_num at this
      · intro h; cases h
    · refine ⟨fun _ => rfl, fun _ b' => ?_⟩
      cases b' <;> simp
  have hmem : () ∈ ({()} : Finset Unit) := Finset.mem_singleton_self _
  have hU : queried amd ⊆ {()} := by intro p _; simp
  have hv : ∀ act : Act2, s₀.V (polEv {()} () act) = if act = Act2.b then 1 else 0 := by
    intro act
    rw [polEv_V_eq_value_reloc {()} amd C' s₀ hcal.2 hmem act (hcal.1 (.inl ()) act), hdev,
      value_lift_ofFun {()} amd hU]
    cases act
    · rw [hva]; simp
    · rw [hvb]; simp
  have hproc : udtProc s₀ (polEv {()}) = Proc.ofFun (fun _ => Act2.b) := by
    funext u; cases u
    rw [udtProc_eq_uniformArgmax s₀ (polEv {()}) () fun act => by
      rw [polEv_pr {()} amd C' s₀ hcal.2 hmem]; exact hcal.1 (.inl ()) act]
    show uniformArgmax (fun act => s₀.V (polEv {()} () act)) = FinDistr.pure Act2.b
    apply uniformArgmax_eq_pure
    ext act
    rw [mem_argmaxFull, Finset.mem_singleton]
    simp only [hv]
    cases act
    · constructor
      · intro h; have := h Act2.b; simp at this; norm_num at this
      · intro h; cases h
    · refine ⟨fun _ => rfl, fun _ b' => ?_⟩
      cases b' <;> simp
  refine ⟨?_, hBR, hproc, ?_⟩
  · intro π hπ π'
    have hb : π () = Act2.b := by
      have := hπ (); rw [hBR, Finset.mem_singleton] at this; exact this
    have hπb : π = fun _ => Act2.b := by funext u; cases u; exact hb
    rw [hπb, hvb]
    rcases amd_value_ofFun π' with h | h <;> rw [h] <;> norm_num
  · rw [hproc]
    exact amd_no_pure_optimum _

end amd

end Cleanroom.Decision.DpFaithfulUdt
