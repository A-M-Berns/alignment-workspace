import Cleanroom.Uea.UeaColeShadow.Gap
import Cleanroom.Uea.UeaColeShadow.InstanceA

/-!
# The convexified reset map on Instances B and A (target 6c)

The reaudit's convexification of the strict-reset map: at a node some prefix of which has `r < 0` the value is
`{δ_{π⋆}}`; at a node with an equality prefix (`r = 0`) and no strict one it is the hull
`conv({δ_{π⋆}} ∪ Δ(𝒜_h)) = Δ(𝒜_h ∪ {π⋆})`; otherwise `Δ(𝒜_h)`. On Instance B its **unique** fixed point is the full
reset `(1,1)` (with `λ = 1`), which is **not** a plain fixed point — "dishonest about `π_S`"; on Instance A the
partial-reset point `t⋆ = 7/36` (`λ = 7/36`) is a convexified fixed point beside the honest `t ∈ {0,1}`, and not a
plain one.

Source: [[oracle-side-gaps-reaudit]] Q1 ("Convexification"), lines 29, 42. The general closed graph of the
convexified map is `stretch` and not done.
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset

namespace Model

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)

/-- Some prefix of `h` (including `h`) is an equality node. -/
def hasEqPrefix (π : Policy A E) (n : ℕ) (h : Hist A E n) : Prop :=
  ∃ m, ∃ hm : m ≤ n, M.resid π m (prefixH h m hm) = 0

section Pt
variable [DecidableEq A] [DecidableEq E]

/-- Allowed actions of the convexified reset map.
Source: [[oracle-side-gaps-reaudit]] Q1 ("Convexification")
Kind: D
Fidelity: exact
Hyps: n/a -/
def Sconv (x : M.Pt) (p : M.NT) (a : A) : Prop :=
  (M.hasStrictReset (M.ofPoint x) p.depth p.hist ∧ a = M.piStar p.depth p.hist) ∨
  (¬ M.hasStrictReset (M.ofPoint x) p.depth p.hist ∧ M.hasEqPrefix (M.ofPoint x) p.depth p.hist ∧
    (a = M.piStar p.depth p.hist ∨ M.Qxi (M.ofPoint x) p.depth p.hist a = M.Mx (M.ofPoint x) p.depth p.hist)) ∨
  (¬ M.hasStrictReset (M.ofPoint x) p.depth p.hist ∧ ¬ M.hasEqPrefix (M.ofPoint x) p.depth p.hist ∧
    M.Qxi (M.ofPoint x) p.depth p.hist a = M.Mx (M.ofPoint x) p.depth p.hist)

end Pt

end Model

/-! ### Instance B -/

namespace InstB

open Model

theorem hasEqPrefix_of_root (π : Policy (Fin 2) Unit) (hroot : model.resid π 0 root = 0) (n : ℕ)
    (h : Hist (Fin 2) Unit n) : model.hasEqPrefix π n h :=
  ⟨0, Nat.zero_le n, by rw [prefixH_zero h root]; exact hroot⟩

/-- Points with `(j, k, s) = (1, 1, 1)` are the reset point. -/
theorem eq_resetPoint (x : model.Pt) (hx : x ∈ model.dom) (h1 : model.ofPoint x 0 root 1 = 1)
    (h2 : model.ofPoint x 1 n1 1 = 1) (h3 : model.ofPoint x 2 water 0 = 1) : x = resetPoint := by
  funext p
  obtain ⟨⟨⟨m, hm⟩, hist⟩, prf⟩ := p
  have hsum := (model.mem_dom.1 hx ⟨⟨⟨m, hm⟩, hist⟩, prf⟩).2
  rw [Fin.sum_univ_two] at hsum
  funext a
  match m with
  | 0 =>
    have hh : hist = root := eq_root hist
    subst hh
    rw [model.ofPoint_apply x nt_root] at h1
    have h1' : x ⟨⟨⟨0, hm⟩, root⟩, prf⟩ 1 = 1 := h1
    have hR0 : pointB 1 1 1 ⟨⟨⟨0, hm⟩, root⟩, prf⟩ 0 = 0 := by simp [pointB, NT.depth]
    have hR1 : pointB 1 1 1 ⟨⟨⟨0, hm⟩, root⟩, prf⟩ 1 = 1 := by simp [pointB, NT.depth]
    rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with rfl | rfl
    · show x _ 0 = pointB 1 1 1 _ 0
      rw [hR0]; linarith
    · show x _ 1 = pointB 1 1 1 _ 1
      rw [hR1]; exact h1'
  | 1 =>
    have hh : hist = n1 := eq_n1_of_nonterminal hist prf
    subst hh
    rw [model.ofPoint_apply x nt_n1] at h2
    have h2' : x ⟨⟨⟨1, hm⟩, n1⟩, prf⟩ 1 = 1 := h2
    have hR0 : pointB 1 1 1 ⟨⟨⟨1, hm⟩, n1⟩, prf⟩ 0 = 0 := by simp [pointB, NT.depth]
    have hR1 : pointB 1 1 1 ⟨⟨⟨1, hm⟩, n1⟩, prf⟩ 1 = 1 := by simp [pointB, NT.depth]
    rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with rfl | rfl
    · show x _ 0 = pointB 1 1 1 _ 0
      rw [hR0]; linarith
    · show x _ 1 = pointB 1 1 1 _ 1
      rw [hR1]; exact h2'
  | 2 =>
    have hh : hist = water := eq_water_of_nonterminal hist prf
    subst hh
    rw [model.ofPoint_apply x nt_water] at h3
    have h3' : x ⟨⟨⟨2, hm⟩, water⟩, prf⟩ 0 = 1 := h3
    have hR0 : pointB 1 1 1 ⟨⟨⟨2, hm⟩, water⟩, prf⟩ 0 = 1 := by simp [pointB, NT.depth]
    have hR1 : pointB 1 1 1 ⟨⟨⟨2, hm⟩, water⟩, prf⟩ 1 = 0 := by simp [pointB, NT.depth]
    rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with rfl | rfl
    · show x _ 0 = pointB 1 1 1 _ 0
      rw [hR0]; exact h3'
    · show x _ 1 = pointB 1 1 1 _ 1
      rw [hR1]; linarith
  | m + 3 => exact absurd prf (not_nonterminal_ge_three (m + 3) (by omega) hist)

/-- **The reset point is a fixed point of the convexified map**: at `(1,1,swim)` the root is an equality node
(`r = 0`), so every node has an equality prefix and no strict one, and the reset action is allowed everywhere
(`λ = 1`).
Source: [[oracle-side-gaps-reaudit]] line 42 ("unique fixed point `(1,1)` with `λ = 1`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem resetPoint_mem_conv : resetPoint ∈ model.corrOf model.Sconv resetPoint := by
  have hπ := model.ofPoint_isPolicy resetPoint_mem_dom
  have h111 : model.ofPoint resetPoint 0 root 1 = 1 ∧ model.ofPoint resetPoint 1 n1 1 = 1 ∧
      model.ofPoint resetPoint 2 water 0 = 1 := by
    unfold resetPoint
    rw [ofPoint_pointB_root, ofPoint_pointB_n1, ofPoint_pointB_water]
    simp
  have hroot := resid_root_eq_zero _ hπ h111
  refine model.mem_corrOf.2 fun p => ⟨(model.mem_dom.1 resetPoint_mem_dom) p, fun a ha => ?_⟩
  have hne : a ≠ model.piStar p.depth p.hist := by
    intro h
    apply ha
    by_cases hs : model.hasStrictReset (model.ofPoint resetPoint) p.depth p.hist
    · exact Or.inl ⟨hs, h⟩
    · exact Or.inr (Or.inl ⟨hs, hasEqPrefix_of_root _ hroot _ _, Or.inl h⟩)
  rcases piStar_cases p with ⟨hd, hp⟩ | ⟨hd, hp⟩ | ⟨hd, hp⟩
  · rw [hp] at hne
    show pointB 1 1 1 p a = 0
    simp only [pointB, hd]
    rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with rfl | rfl
    · norm_num
    · exact absurd rfl hne
  · rw [hp] at hne
    show pointB 1 1 1 p a = 0
    simp only [pointB, hd]
    rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with rfl | rfl
    · norm_num
    · exact absurd rfl hne
  · rw [hp] at hne
    show pointB 1 1 1 p a = 0
    simp only [pointB, hd]
    rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with rfl | rfl
    · exact absurd rfl hne
    · norm_num

/-- **Uniqueness**: every fixed point of the convexified map on Instance B in the product of simplices is the
reset point. (If the root were a strict-reset node every node would be reset, giving the reset point, at which the
root is an equality node; otherwise `r_root ≤ 0` forces `r_root = 0`, i.e. `(j,k,s) = (1,1,1)`.)
Source: [[oracle-side-gaps-reaudit]] line 42
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem conv_fixed_eq_resetPoint (x : model.Pt) (hx : x ∈ model.dom) (hfix : x ∈ model.corrOf model.Sconv x) :
    x = resetPoint := by
  have hπ := model.ofPoint_isPolicy hx
  by_cases hneg : model.resid (model.ofPoint x) 0 root < 0
  · -- everything is reset: `x` is the reset point
    have hall : ∀ n (h : Hist (Fin 2) Unit n), model.hasStrictReset (model.ofPoint x) n h :=
      hasStrictReset_of_root _ hneg
    have hroot1 : model.ofPoint x 0 root 1 = 1 := by
      have hmem := ((model.mem_corrOf.1 hfix) ⟨⟨⟨0, Nat.lt_succ_of_lt nt_root.1⟩, root⟩, nt_root⟩)
      have hs := hmem.2 0 (fun hS => by
        rcases hS with ⟨_, h0⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
        · have h0' : (0 : Fin 2) = model.piStar 0 root := h0
          rw [piStar_root] at h0'; exact absurd h0' (by decide)
        · exact h0 (hall _ _)
        · exact h0 (hall _ _))
      have hsum := (model.mem_dom.1 hx ⟨⟨⟨0, Nat.lt_succ_of_lt nt_root.1⟩, root⟩, nt_root⟩).2
      rw [Fin.sum_univ_two] at hsum
      rw [model.ofPoint_apply x nt_root]
      linarith
    have hn11 : model.ofPoint x 1 n1 1 = 1 := by
      have hmem := ((model.mem_corrOf.1 hfix) ⟨⟨⟨1, Nat.lt_succ_of_lt nt_n1.1⟩, n1⟩, nt_n1⟩)
      have hs := hmem.2 0 (fun hS => by
        rcases hS with ⟨_, h0⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
        · have h0' : (0 : Fin 2) = model.piStar 1 n1 := h0
          rw [piStar_n1] at h0'; exact absurd h0' (by decide)
        · exact h0 (hall _ _)
        · exact h0 (hall _ _))
      have hsum := (model.mem_dom.1 hx ⟨⟨⟨1, Nat.lt_succ_of_lt nt_n1.1⟩, n1⟩, nt_n1⟩).2
      rw [Fin.sum_univ_two] at hsum
      rw [model.ofPoint_apply x nt_n1]
      linarith
    have hw0 : model.ofPoint x 2 water 0 = 1 := by
      have hmem := ((model.mem_corrOf.1 hfix) ⟨⟨⟨2, Nat.lt_succ_of_lt nt_water.1⟩, water⟩, nt_water⟩)
      have hs := hmem.2 1 (fun hS => by
        rcases hS with ⟨_, h0⟩ | ⟨h0, _⟩ | ⟨h0, _⟩
        · have h0' : (1 : Fin 2) = model.piStar 2 water := h0
          rw [piStar_water] at h0'; exact absurd h0' (by decide)
        · exact h0 (hall _ _)
        · exact h0 (hall _ _))
      have hsum := (model.mem_dom.1 hx ⟨⟨⟨2, Nat.lt_succ_of_lt nt_water.1⟩, water⟩, nt_water⟩).2
      rw [Fin.sum_univ_two] at hsum
      rw [model.ofPoint_apply x nt_water]
      linarith
    exact eq_resetPoint x hx hroot1 hn11 hw0
  · -- `r_root = 0`, so `(j,k,s) = (1,1,1)`
    have hle : model.resid (model.ofPoint x) 0 root ≤ 0 := by
      unfold Model.resid
      rw [wS_root, Vstar_root, model.Mx_fin_two, Qxi_root_0, mul_one, sub_nonpos, max_le_iff]
      exact ⟨by norm_num, Qxi_root_1_le _ hπ⟩
    have h0 : model.resid (model.ofPoint x) 0 root = 0 := le_antisymm hle (not_lt.1 hneg)
    have hQ : model.Qxi (model.ofPoint x) 0 root 1 = 4 / 5 := by
      unfold Model.resid at h0
      rw [wS_root, Vstar_root, model.Mx_fin_two, Qxi_root_0, mul_one, sub_eq_zero] at h0
      have := Qxi_root_1_le _ hπ
      rcases le_or_gt (model.Qxi (model.ofPoint x) 0 root 1) (7 / 10) with h | h
      · rw [max_eq_left h] at h0; norm_num at h0
      · rw [max_eq_right h.le] at h0; exact h0
    obtain ⟨h1, h2, h3⟩ := (Qxi_root_1_eq_iff _ hπ).1 hQ
    exact eq_resetPoint x hx h1 h2 h3

/-- The convexified map's fixed point is **not** a plain fixed point ("dishonest about `π_S`": the oracle's
picture of `π_S` is `(go, jump)` while `π_S`'s computation gives `(go, stay)`).
Source: [[oracle-side-gaps-reaudit]] line 42
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem resetPoint_not_isPlainFP : ¬ model.IsPlainFP (model.ofPoint resetPoint) := by
  intro hfp
  obtain ⟨_, hj, _, _⟩ := (isPlainFP_iff _).1 hfp
  unfold resetPoint at hj
  rw [ofPoint_pointB_root] at hj
  simp at hj

end InstB

/-! ### Instance A -/

namespace InstA

open Model

/-- The point `t = π(a₂|root)` with the optimal depth-1 choices. -/
noncomputable def pointA (t : ℝ) : model.Pt := fun p a =>
  if p.depth = 0 then (if a = 0 then 1 - t else t) else (if a = 0 then 1 else 0)

theorem pointA_mem_dom {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : pointA t ∈ model.dom := by
  refine model.mem_dom.2 fun p => ⟨fun a => ?_, ?_⟩
  · unfold pointA; split_ifs <;> linarith
  · unfold pointA; split_ifs <;> simp [Fin.sum_univ_two]

theorem ofPoint_pointA (t : ℝ) : model.ofPoint (pointA t) = polA t := by
  funext n h a
  match n with
  | 0 =>
    rw [model.ofPoint_apply _ (by rw [eq_root h]; exact nt_root)]
    simp [pointA, polA, NT.depth]
  | 1 =>
    rw [model.ofPoint_apply _ (⟨by simp, rfl⟩ : model.nonterminal 1 h)]
    simp [pointA, polA, NT.depth]
  | n + 2 =>
    simp [Model.ofPoint, polA, not_nt_ge_two (n + 2) (by omega) h]

theorem resid_L_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ model.resid (polA t) 1 L := by
  unfold Model.resid
  rw [Mx_L, Vstar_L]
  have := model.wS_le_one (polA_isPolicy ht0 ht1) nt_L
  nlinarith

theorem resid_R_nonneg (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ model.resid (polA t) 1 R := by
  unfold Model.resid
  rw [Mx_R, Vstar_R]
  have := model.wS_le_one (polA_isPolicy ht0 ht1) nt_R
  linarith

theorem piStar_L : model.piStar 1 L = 0 := by
  refine model.piStar_eq_of_unique nt_L (Fin.forall_fin_two.2 ⟨fun _ => rfl, fun ha => ?_⟩)
  rw [Qstar_L_1, Vstar_L] at ha; norm_num at ha

theorem piStar_R : model.piStar 1 R = 0 := by
  refine model.piStar_eq_of_unique nt_R (Fin.forall_fin_two.2 ⟨fun _ => rfl, fun ha => ?_⟩)
  rw [Qstar_R_1, Vstar_R] at ha; norm_num at ha

/-- **`t⋆ = 7/36` is a fixed point of the convexified map on Instance A** (with reset weight `λ = 7/36`), and not a
plain fixed point (`InstA.tstar`): the root is an equality node where the hull allows any mixture of `a₁` (the
argmax) and `a₂` (`π⋆`); the depth-1 nodes have the root as an equality prefix and play their unique optimum.
Source: [[oracle-side-gaps-reaudit]] line 29
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem tstar_mem_conv : pointA (7 / 36) ∈ model.corrOf model.Sconv (pointA (7 / 36)) ∧
    ¬ model.IsPlainFP (model.ofPoint (pointA (7 / 36))) := by
  have hpol := ofPoint_pointA (7 / 36)
  have ht0 : (0:ℝ) ≤ 7 / 36 := by norm_num
  have ht1 : (7:ℝ) / 36 ≤ 1 := by norm_num
  obtain ⟨h0, h1, hTB, hargmax, hpi, hnot⟩ := tstar
  have hroot : model.resid (polA (7 / 36)) 0 root = 0 := by
    unfold Model.resid; linarith
  refine ⟨model.mem_corrOf.2 fun p => ⟨(model.mem_dom.1 (pointA_mem_dom ht0 ht1)) p, fun a ha => ?_⟩, by rw [hpol]; exact hnot⟩
  unfold Model.Sconv at ha
  rw [hpol] at ha
  obtain ⟨⟨⟨m, hm⟩, hist⟩, prf⟩ := p
  have hEq : ∀ n (h : Hist (Fin 2) Unit n), model.hasEqPrefix (polA (7 / 36)) n h :=
    fun n h => ⟨0, Nat.zero_le n, by rw [prefixH_zero h root]; exact hroot⟩
  match m with
  | 0 =>
    -- at the root every action is allowed: `π⋆ = a₂`, `𝒜 = {a₁}`
    have hh : hist = root := eq_root hist
    subst hh
    exfalso
    apply ha
    have hns : ¬ model.hasStrictReset (polA (7 / 36)) 0 root := by
      rintro ⟨m, hm, hlt⟩
      match m with
      | 0 => rw [prefixH_self] at hlt; linarith
    refine Or.inr (Or.inl ⟨hns, hEq 0 root, ?_⟩)
    rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with rfl | rfl
    · right
      have : (0 : Fin 2) ∈ model.argmaxSet (polA (7 / 36)) 0 root := by rw [hargmax]; simp
      exact (model.mem_argmaxSet).1 this
    · left; exact hpi.symm
  | 1 =>
    -- depth 1: the hull is `{δ_{π⋆}} ∪ Δ(𝒜) = {δ_0}`
    have hL : ∀ (h : Hist (Fin 2) Unit 1) (hnt : model.nonterminal 1 h), model.piStar 1 h = 0 ∧
        model.Mx (polA (7 / 36)) 1 h = model.Qxi (polA (7 / 36)) 1 h 0 ∧
        model.Qxi (polA (7 / 36)) 1 h 1 < model.Qxi (polA (7 / 36)) 1 h 0 ∧ 0 ≤ model.resid (polA (7 / 36)) 1 h := by
      intro h hnt
      rcases eq_L_or_R h with rfl | rfl
      · exact ⟨piStar_L, by rw [Mx_L, Qxi_L_0], by rw [Qxi_L_0, Qxi_L_1]; norm_num, resid_L_nonneg _ ht0 ht1⟩
      · exact ⟨piStar_R, by rw [Mx_R, Qxi_R_0], by rw [Qxi_R_0, Qxi_R_1]; norm_num, resid_R_nonneg _ ht0 ht1⟩
    obtain ⟨hp, hM, hlt, hres⟩ := hL hist prf
    have hns : ¬ model.hasStrictReset (polA (7 / 36)) 1 hist := by
      rintro ⟨m, hm, hlt'⟩
      match m with
      | 0 => rw [prefixH_zero hist root, hroot] at hlt'; exact lt_irrefl _ hlt'
      | 1 => rw [prefixH_self] at hlt'; linarith
    have hne : a ≠ 0 := by
      intro h0'
      apply ha
      exact Or.inr (Or.inl ⟨hns, hEq 1 hist, Or.inl (by rw [h0']; exact hp.symm)⟩)
    have ha1 : a = 1 := by
      rcases Fin.exists_fin_two.1 ⟨a, rfl⟩ with rfl | rfl
      · exact absurd rfl hne
      · rfl
    subst ha1
    show pointA (7 / 36) ⟨⟨⟨1, hm⟩, hist⟩, prf⟩ 1 = 0
    simp [pointA, NT.depth]
  | m + 2 => exact absurd prf (not_nt_ge_two (m + 2) (by omega) hist)

/-! ### Instance A at `t = 0` is a fixed point of the strict-reset map: the N+ witness for `IsStrictResetFP.sound` -/

/-- At `t = 0` the root residual is non-negative: `Q_ξ(root, a₁) = 3441/3800 > 9/10 = w_root V^*`.
Source: [[oracle-side-gaps-reaudit]] line 30; round-1 audit
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem resid_root_zero_nonneg : 0 ≤ model.resid (polA 0) 0 root := by
  unfold Model.resid
  have q00 : model.Qxi (polA 0) 0 root 0 = 3441 / 3800 := by
    rw [Qxi_root_0 _ le_rfl zero_le_one]; norm_num
  rw [wS_root, Vstar_root, model.Mx_fin_two, q00, mul_one]
  have : (9:ℝ) / 10 ≤ max (3441 / 3800) (model.Qxi (polA 0) 0 root 1) :=
    le_trans (by norm_num) (le_max_left _ _)
  linarith

/-- At `t = 0` no decision node of Instance A has a strictly violated prefix.
Source: round-1 audit (probe `StrictResetWitness`)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem not_hasStrictReset_zero {n : ℕ} (h : Hist (Fin 2) Unit n) (hnt : model.nonterminal n h) :
    ¬ model.hasStrictReset (polA 0) n h := by
  rintro ⟨m, hm, hlt⟩
  have hn : n < 2 := hnt.1
  rcases Nat.lt_or_ge n 1 with h0 | h1
  · have hn0 : n = 0 := by omega
    subst hn0
    have hm0 : m = 0 := by omega
    subst hm0
    rw [prefixH_self, eq_root h] at hlt
    linarith [resid_root_zero_nonneg]
  · have hn1 : n = 1 := by omega
    subst hn1
    rcases Nat.lt_or_ge m 1 with hm0 | hm1
    · have : m = 0 := by omega
      subst this
      rw [prefixH_zero h root] at hlt
      linarith [resid_root_zero_nonneg]
    · have : m = 1 := by omega
      subst this
      rw [prefixH_self] at hlt
      rcases eq_L_or_R h with rfl | rfl
      · linarith [resid_L_nonneg 0 le_rfl zero_le_one]
      · linarith [resid_R_nonneg 0 le_rfl zero_le_one]

/-- **N+ witness for `IsStrictResetFP.sound`**: Instance A at `t = 0` (`a₁` surely at the root, the forced
optimal depth-1 choices) is a fixed point of the strict-reset map — a non-degenerate two-step instance with
`0 < w_root = 9/10 < 1` and a residual of positive mass at which no node is strictly violated and the support is
in the argmax. So `sound`'s hypothesis is inhabited (its emptiness on Instance B is the point of Gap 1, not a
vacuity of the theorem). Supplied by the round-1 fidelity audit.
Source: [[oracle-side-gaps-reaudit]] lines 30, Q6; round-1 audit
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem isStrictResetFP_zero : model.IsStrictResetFP (polA 0) := by
  obtain ⟨hfp0, _, _, _⟩ := isPlainFP_zero_one
  exact ⟨hfp0.1, fun n h hnt => ⟨fun hs => absurd hs (not_hasStrictReset_zero h hnt), fun _ => hfp0.2 n h hnt⟩⟩

/-- `sound` applied to the witness: the trust bound holds at every decision node of Instance A under `polA 0`.
Source: round-1 audit
Kind: C
Fidelity: n/a
Hyps: (a) -/
theorem sound_applies_zero : ∀ n (h : Hist (Fin 2) Unit n), model.nonterminal n h → model.TB (polA 0) n h :=
  isStrictResetFP_zero.sound.2.2

end InstA

end Cleanroom.Uea.UeaColeShadow
