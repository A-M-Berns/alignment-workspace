import Cleanroom.Corrigibility.CorrValueChange.TwoStep
import Mathlib.Data.Fintype.Option

/-!
# corr-value-change — facts and configuration; information and payment (T3)

Source: [[value-change-as-epistemic-update]] §1.4 ("Facts and configuration; information and
payment"). Worlds are `F × Option J × A`: a fact `f`, a configuration `c ∈ {K} ∪ {C_j}` (`none` is
`K`, `some j` is `C_j`) and the act coordinate; `U = U(F, c, a)`. The agent's joint is
`P(f, c, a) = q(f, c) · σ(a)` — the acts independent of fact and configuration ("acts likewise"
carry no information) — and the **uninformative-choice assumption** is `P(F = f ∣ C) = P(F = f ∣ K)`
in product form. The informed keep-value `w_j(a) = E[U(F, K, a) ∣ C_j]` is defined, the identity
`∑_j p_j w_j(a^K) = v_K(a^K)` is *derived* from the assumption (the mandate's trap), and
`(B) + (C) = (I) + (Π)` follows.
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {F J A : Type} [Fintype F] [DecidableEq F] [Fintype J] [DecidableEq J] [Fintype A]
  [DecidableEq A]

/-- **The facts/configuration product model**: a joint `q` on fact × configuration, a positive
self-model `σ` on acts (independent of everything), the utility `U(F, c, a)`, and the model's
positivity convention on the configuration marginal (`P(K) > 0`, `P(C_j) > 0`).
Source: [[value-change-as-epistemic-update]] §1.4 ("Split the world into facts `F` … and the
configuration coordinate … so that `U = U(F, c, a)`")
Kind: D
Fidelity: exact (the act coordinate is explicit, the acts independent by construction) -/
structure ProductModel (F J A : Type) [Fintype F] [Fintype J] [Fintype A] where
  /-- joint weight of fact `f` and configuration `c` -/
  q : F → Option J → ℝ
  /-- nonnegative -/
  q_nonneg : ∀ f c, 0 ≤ q f c
  /-- sums to one -/
  q_sum : ∑ f, ∑ c, q f c = 1
  /-- the self-model on acts -/
  σ : A → ℝ
  /-- every act has positive self-model probability -/
  σ_pos : ∀ a, 0 < σ a
  /-- the self-model sums to one -/
  σ_sum : ∑ a, σ a = 1
  /-- `U(F, c, a)` -/
  Uf : F → Option J → A → ℝ
  /-- `P(K) > 0` -/
  qK_pos : 0 < ∑ f, q f none
  /-- `P(C_j) > 0` -/
  qC_pos : ∀ j, 0 < ∑ f, q f (some j)

namespace ProductModel

variable (M : ProductModel F J A)

/-- The world type `F × Option J × A`.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: D
Fidelity: exact -/
abbrev W (F J A : Type) := F × Option J × A

/-- `P(K)` (fact-marginal mass of the keep configuration).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def qK : ℝ := ∑ f, M.q f none

/-- `P(C_j)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def qC (j : J) : ℝ := ∑ f, M.q f (some j)

/-- `P(C) = ∑_j P(C_j)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def qCtot : ℝ := ∑ j, M.qC j

/-- The joint on worlds, `P(f, c, a) = q(f, c) · σ(a)`.
Source: [[value-change-as-epistemic-update]] §1.4, §2.4 (acts independent)
Kind: D
Fidelity: exact -/
def P : Prob (W F J A) where
  p := fun ω => M.q ω.1 ω.2.1 * M.σ ω.2.2
  nonneg := fun ω => mul_nonneg (M.q_nonneg _ _) (M.σ_pos _).le
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_prod_type, ← mul_sum, M.σ_sum, mul_one]
    exact M.q_sum

/-- The utility as a function of worlds.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: D
Fidelity: exact -/
def U (ω : W F J A) : ℝ := M.Uf ω.1 ω.2.1 ω.2.2

/-- The event "the agent does `a`".
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def actE (a : A) : Finset (W F J A) := univ.filter fun ω => ω.2.2 = a

/-- The event "configuration `c`".
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def confE (c : Option J) : Finset (W F J A) := univ.filter fun ω => ω.2.1 = c

/-- A sum over `act a ∧ conf c` is the fact-sum of the slice.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_act_conf (g : W F J A → ℝ) (a : A) (c : Option J) :
    ∑ ω ∈ actE a ∩ confE c, g ω = ∑ f, g (f, c, a) := by
  have h : (actE a ∩ confE c : Finset (W F J A)) =
      univ.filter fun ω => ω.2.2 = a ∧ ω.2.1 = c := by
    ext ω; simp [actE, confE]
  rw [h, sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun f _ => ?_
  rw [Fintype.sum_prod_type]
  simp [ite_and, Finset.sum_ite_eq']

/-- A sum over `conf c` is the fact-and-act sum of the slice.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_conf (g : W F J A → ℝ) (c : Option J) :
    ∑ ω ∈ confE c, g ω = ∑ f, ∑ a, g (f, c, a) := by
  rw [confE, sum_filter, Fintype.sum_prod_type]
  refine sum_congr rfl fun f _ => ?_
  rw [Fintype.sum_prod_type, sum_comm]
  refine sum_congr rfl fun a _ => ?_
  simp only
  rw [Finset.sum_ite_eq']
  simp

/-- The mass of `act a ∧ conf c` is `σ(a) · P(c)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_act_conf (a : A) (c : Option J) :
    M.P.mass (actE a ∩ confE c) = M.σ a * ∑ f, M.q f c := by
  unfold Prob.mass
  rw [sum_act_conf, mul_sum]
  refine sum_congr rfl fun f _ => ?_
  simp [P, mul_comm]

/-- The integral over `act a ∧ conf c` is `σ(a) · ∑_f q(f, c) U(f, c, a)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem integral_act_conf (a : A) (c : Option J) :
    M.P.integral M.U (actE a ∩ confE c) = M.σ a * ∑ f, M.q f c * M.Uf f c a := by
  unfold Prob.integral
  rw [sum_act_conf, mul_sum]
  refine sum_congr rfl fun f _ => ?_
  simp [P, U]; ring

/-- The step-2 decision: the acts.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: D
Fidelity: exact -/
def D : Decision M.P A where
  act := actE
  disjoint := fun a b h => by
    rw [Finset.disjoint_left]
    intro ω ha hb
    simp [actE] at ha hb
    exact h (ha ▸ hb ▸ rfl)
  cover := fun ω => ⟨ω.2.2, by simp [actE]⟩
  pos := fun a => by
    have h : actE a = actE a ∩ (univ : Finset (W F J A)) := by simp
    have h2 : (univ : Finset (W F J A)) = univ.biUnion (fun c => confE c) := by
      ext ω; simp [confE]
    unfold Prob.mass
    rw [h, h2, inter_biUnion, sum_biUnion]
    · apply lt_of_lt_of_le (b := ∑ ω ∈ actE a ∩ confE none, M.P.p ω)
      · have := M.mass_act_conf a none
        unfold Prob.mass at this
        rw [this]; exact mul_pos (M.σ_pos a) M.qK_pos
      · exact single_le_sum (f := fun c => ∑ ω ∈ actE a ∩ confE c, M.P.p ω)
          (fun c _ => sum_nonneg fun ω _ => M.P.nonneg ω) (mem_univ none)
    · intro c _ c' _ hcc'
      rw [Function.onFun, Finset.disjoint_left]
      intro ω h1 h2
      simp [actE, confE] at h1 h2
      exact hcc' (h1.2 ▸ h2.2 ▸ rfl)

/-- The product model as a two-step decision: `K = {c = none}`, `C_j = {c = some j}`.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: D
Fidelity: exact -/
def toTwoStep [Nonempty J] : TwoStep M.P A J where
  D := M.D
  K := confE none
  C := fun j => confE (some j)
  K_disj := fun j => by
    rw [Finset.disjoint_left]; intro ω h1 h2; simp [confE] at h1 h2; rw [h1] at h2; exact Option.some_ne_none j h2.symm
  C_disj := fun i j hij => by
    rw [Finset.disjoint_left]; intro ω h1 h2; simp [confE] at h1 h2
    rw [h1] at h2; exact hij (Option.some_injective J h2)
  cover := fun ω => by
    rcases h : ω.2.1 with _ | j
    · left; simp [confE, h]
    · right; exact ⟨j, by simp [confE, h]⟩
  posK := fun a => by
    show 0 < M.P.mass (actE a ∩ confE none)
    rw [M.mass_act_conf]; exact mul_pos (M.σ_pos a) M.qK_pos
  posC := fun a j => by
    show 0 < M.P.mass (actE a ∩ confE (some j))
    rw [M.mass_act_conf]; exact mul_pos (M.σ_pos a) (M.qC_pos j)

/-! ## The fact-side values and the transfer lemmas -/

/-- `v_K(a) = (∑_f q(f,K) U(f,K,a)) / P(K)` on the fact side.
Source: none: infrastructure (the computed form of §1.3's `v_K`)
Kind: D
Fidelity: n/a -/
def vKf (a : A) : ℝ := (∑ f, M.q f none * M.Uf f none a) / M.qK

/-- `v_j(a) = (∑_f q(f,C_j) U(f,C_j,a)) / P(C_j)` on the fact side.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def vf (j : J) (a : A) : ℝ := (∑ f, M.q f (some j) * M.Uf f (some j) a) / M.qC j

/-- **The informed keep-value** `w_j(a) = E[U(F, K, a) ∣ C_j]`: the value of act `a` to an agent
that keeps its configuration but knows what outcome `j` reveals about the facts.
Source: [[value-change-as-epistemic-update]] §1.4 (the display defining `w_j`)
Kind: D
Fidelity: exact -/
def w (j : J) (a : A) : ℝ := (∑ f, M.q f (some j) * M.Uf f none a) / M.qC j

/-- `v_K` of the two-step model is the fact-side `v_K` (the self-model cancels).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem toTwoStep_vK [Nonempty J] (a : A) : M.toTwoStep.vK M.U a = M.vKf a := by
  unfold TwoStep.vK Decision.v Prob.condExp toTwoStep D vKf qK
  simp only
  rw [M.integral_act_conf, M.mass_act_conf]
  have := M.σ_pos a
  rw [mul_div_mul_left _ _ this.ne']

/-- `v_j` of the two-step model is the fact-side `v_j`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem toTwoStep_v [Nonempty J] (j : J) (a : A) : M.toTwoStep.v M.U j a = M.vf j a := by
  unfold TwoStep.v Decision.v Prob.condExp toTwoStep D vf qC
  simp only
  rw [M.integral_act_conf, M.mass_act_conf]
  have := M.σ_pos a
  rw [mul_div_mul_left _ _ this.ne']

/-- `p_j` of the two-step model is `P(C_j) / P(C)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem toTwoStep_p [Nonempty J] (j : J) : M.toTwoStep.p j = M.qC j / M.qCtot := by
  unfold TwoStep.p
  rw [TwoStep.mass_changeEvent]
  unfold toTwoStep qCtot qC
  simp only
  unfold Prob.mass
  simp_rw [sum_conf]
  have h : ∀ c : Option J, ∑ f, ∑ a, M.P.p (f, c, a) = ∑ f, M.q f c := by
    intro c; refine sum_congr rfl fun f _ => ?_
    simp only [P]; rw [← mul_sum, M.σ_sum, mul_one]
  simp_rw [h]

/-- **The uninformative-choice assumption**: the step-1 choice carries no information about the
facts, `P(F = f ∣ C) = P(F = f ∣ K)` for every `f`, in product form
`P(f ∧ C) · P(K) = P(f ∧ K) · P(C)`. (Acts carry none by the product construction of `P`.)
Source: [[value-change-as-epistemic-update]] §1.4 ("keep the assumption that the step-1 choice
carries no information about `F`")
Kind: D
Fidelity: exact -/
def Uninformative : Prop := ∀ f, (∑ j, M.q f (some j)) * M.qK = M.q f none * M.qCtot

/-- `P(C) > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem qCtot_pos [Nonempty J] : 0 < M.qCtot := by
  unfold qCtot
  obtain ⟨j⟩ := (inferInstance : Nonempty J)
  exact lt_of_lt_of_le (M.qC_pos j) (single_le_sum (fun i _ => (M.qC_pos i).le) (mem_univ j))

/-- **The trap identity, derived**: under uninformative choice, `∑_j p_j w_j(a) = v_K(a)` for every
act `a` (in particular for `a^K`).
Source: [[value-change-as-epistemic-update]] §1.4 ("The identity uses `∑_j p_j w_j(a^K) = v_K(a^K)`,
which is the uninformative-choice assumption")
Kind: P
Fidelity: exact
Hyps: (a) `h : Uninformative` -/
theorem sum_p_w_eq_vKf [Nonempty J] (h : M.Uninformative) (a : A) :
    ∑ j, M.toTwoStep.p j * M.w j a = M.vKf a := by
  simp_rw [M.toTwoStep_p]
  unfold w vKf
  have hC : 0 < M.qCtot := M.qCtot_pos
  have hK : 0 < M.qK := M.qK_pos
  have h1 : ∀ j, M.qC j / M.qCtot * ((∑ f, M.q f (some j) * M.Uf f none a) / M.qC j) =
      (∑ f, M.q f (some j) * M.Uf f none a) / M.qCtot := by
    intro j
    have hj : M.qC j ≠ 0 := (M.qC_pos j).ne'
    field_simp
  simp_rw [h1]
  rw [← sum_div, sum_comm]
  simp_rw [← sum_mul]
  rw [div_eq_div_iff hC.ne' hK.ne']
  unfold qK at hK ⊢
  rw [sum_mul, sum_mul]
  refine sum_congr rfl fun f _ => ?_
  have hf := h f
  unfold qK at hf
  calc (∑ j, M.q f (some j)) * M.Uf f none a * ∑ f, M.q f none
      = ((∑ j, M.q f (some j)) * ∑ f, M.q f none) * M.Uf f none a := by ring
    _ = (M.q f none * M.qCtot) * M.Uf f none a := by rw [hf]
    _ = M.q f none * M.Uf f none a * M.qCtot := by ring

/-- Term **(I) information**: `∑_j p_j [w_j(ã^j) − w_j(a^K)]`.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: D
Fidelity: exact -/
def termI [Nonempty J] (atil : J → A) (aK : A) : ℝ :=
  ∑ j, M.toTwoStep.p j * (M.w j (atil j) - M.w j aK)

/-- Term **(Π) payment**: `∑_j p_j [v_j(â^j) − w_j(ã^j)]`.
Source: [[value-change-as-epistemic-update]] §1.4
Kind: D
Fidelity: exact -/
def termPi [Nonempty J] (ahat atil : J → A) : ℝ :=
  ∑ j, M.toTwoStep.p j * (M.toTwoStep.v M.U j (ahat j) - M.w j (atil j))

/-- **T3(a), the information/payment split**: under the uninformative-choice assumption and
nothing else, `(B) + (C) = (I) + (Π)`, for any `â^j`, `ã^j`, `a^K`.
Source: [[value-change-as-epistemic-update]] §1.4 ("(B) + (C) = (I) + (Π)")
Kind: P
Fidelity: exact
Hyps: (a) `h : Uninformative` -/
theorem info_payment_split [Nonempty J] (h : M.Uninformative) (ahat atil : J → A) (aK : A) :
    (∑ j, M.toTwoStep.p j * (M.toTwoStep.v M.U j (ahat j) - M.toTwoStep.v M.U j aK)) +
      (∑ j, M.toTwoStep.p j * (M.toTwoStep.v M.U j aK - M.toTwoStep.vK M.U aK)) =
    M.termI atil aK + M.termPi ahat atil := by
  set S := M.toTwoStep
  have hT := (S.table M.U).ValC_sub_ValK_eq_termA_add (fun _ => aK) ahat aK
  have hD := (S.table M.U).decomposition (fun _ => aK) ahat aK
  have hw := M.sum_p_w_eq_vKf h aK
  rw [← M.toTwoStep_vK] at hw
  unfold termI termPi
  have e1 : ∑ j, S.p j * (M.w j (atil j) - M.w j aK) + ∑ j, S.p j * (S.v M.U j (ahat j) - M.w j (atil j))
      = (∑ j, S.p j * S.v M.U j (ahat j)) - ∑ j, S.p j * M.w j aK := by
    rw [← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun j _ => ?_; ring
  rw [e1, hw]
  have e2 := (S.table M.U).ValC_sub_ValK (fun _ => aK) aK
  simp only [ValueTable.termA, ValueTable.termB, ValueTable.termC, ValueTable.ValC,
    ValueTable.ValK, TwoStep.table] at hT hD e2
  linarith

/-- **T3(b), (I) ≥ 0**, from `ã^j` maximizing `w_j` (Good's theorem, finite form).
Source: [[value-change-as-epistemic-update]] §1.4 ("Good's theorem makes it nonnegative")
Kind: P
Fidelity: exact
Hyps: (a) `htil : ∀ j a, w_j a ≤ w_j (ã^j)` -/
theorem termI_nonneg [Nonempty J] (atil : J → A) (aK : A)
    (htil : ∀ j a, M.w j a ≤ M.w j (atil j)) : 0 ≤ M.termI atil aK := by
  unfold termI
  apply sum_nonneg; intro j _
  have := htil j aK
  have := M.toTwoStep.p_pos j
  nlinarith

/-- **S4, when (I) is positive**: `(I) > 0` iff some outcome's informed best act beats `a^K` by
`w_j` — iff `a^K` fails to maximize some `w_j`. (The note's "only if `ã^j ≠ a^K` for some `j`" is
the ⇒ direction with ties ignored: `ã^j ≠ a^K` with `w_j(ã^j) = w_j(a^K)` gives (I) = 0.)
Source: [[value-change-as-epistemic-update]] §1.4 ("(I) is positive only if some outcome changes
the informed best act"); mandate S4
Kind: P
Fidelity: exact (sharpened to an iff)
Hyps: (a) `htil` -/
theorem termI_pos_iff [Nonempty J] (atil : J → A) (aK : A)
    (htil : ∀ j a, M.w j a ≤ M.w j (atil j)) :
    0 < M.termI atil aK ↔ ∃ j, ¬ ∀ a, M.w j a ≤ M.w j aK := by
  unfold termI
  have hnn : ∀ j ∈ (univ : Finset J), 0 ≤ M.toTwoStep.p j * (M.w j (atil j) - M.w j aK) := by
    intro j _; have := htil j aK; have := M.toTwoStep.p_pos j; nlinarith
  constructor
  · intro hpos
    by_contra hall
    push_neg at hall
    have : ∑ j, M.toTwoStep.p j * (M.w j (atil j) - M.w j aK) = 0 := by
      apply sum_eq_zero; intro j _
      have h1 := hall j (atil j)
      have h2 := htil j aK
      have : M.w j (atil j) - M.w j aK = 0 := by linarith
      rw [this, mul_zero]
    linarith
  · rintro ⟨j, hj⟩
    push_neg at hj
    obtain ⟨a, ha⟩ := hj
    have h1 : M.w j aK < M.w j (atil j) := lt_of_lt_of_le ha (htil j a)
    have hp := M.toTwoStep.p_pos j
    calc (0 : ℝ) < M.toTwoStep.p j * (M.w j (atil j) - M.w j aK) := by nlinarith
      _ ≤ ∑ j, M.toTwoStep.p j * (M.w j (atil j) - M.w j aK) :=
          single_le_sum hnn (mem_univ j)

/-- **Outcomes revealing nothing**: if `P(F = f ∣ C_j) = P(F = f ∣ K)` for every `j` (product
form), then `w_j = v_K` pointwise, hence (I) = 0 for any `w`-maximizers `ã^j` and any
`v_K`-maximizer `a^K`.
Source: [[value-change-as-epistemic-update]] §1.4 ("Suppose the outcomes reveal nothing about the
facts, so (I) = 0 and `w_j = v_K`")
Kind: P
Fidelity: exact
Hyps: (a) `hrev : ∀ j f, q(f, C_j) · P(K) = q(f, K) · P(C_j)`; `htil`; `hK` -/
theorem w_eq_vKf_of_uninformative_outcomes [Nonempty J]
    (hrev : ∀ j f, M.q f (some j) * M.qK = M.q f none * M.qC j) (j : J) (a : A) :
    M.w j a = M.vKf a := by
  unfold w vKf
  have hK : 0 < M.qK := M.qK_pos
  have hj : 0 < M.qC j := M.qC_pos j
  rw [div_eq_div_iff hj.ne' hK.ne', sum_mul, sum_mul]
  refine sum_congr rfl fun f _ => ?_
  have := hrev j f
  unfold qK qC at this ⊢
  calc M.q f (some j) * M.Uf f none a * ∑ f, M.q f none
      = (M.q f (some j) * ∑ f, M.q f none) * M.Uf f none a := by ring
    _ = (M.q f none * ∑ f, M.q f (some j)) * M.Uf f none a := by rw [this]
    _ = M.q f none * M.Uf f none a * ∑ f, M.q f (some j) := by ring

/-- (I) = 0 when the outcomes reveal nothing about the facts.
Source: [[value-change-as-epistemic-update]] §1.4 (first route)
Kind: P
Fidelity: exact
Hyps: (a) `hrev`, `htil`, `hK` -/
theorem termI_zero_of_uninformative_outcomes [Nonempty J] (atil : J → A) (aK : A)
    (hrev : ∀ j f, M.q f (some j) * M.qK = M.q f none * M.qC j)
    (htil : ∀ j a, M.w j a ≤ M.w j (atil j)) (hK : ∀ a, M.vKf a ≤ M.vKf aK) :
    M.termI atil aK = 0 := by
  unfold termI
  apply sum_eq_zero; intro j _
  have h1 := htil j aK
  have h2 : M.w j (atil j) ≤ M.w j aK := by
    rw [M.w_eq_vKf_of_uninformative_outcomes hrev, M.w_eq_vKf_of_uninformative_outcomes hrev]
    exact hK (atil j)
  have : M.w j (atil j) - M.w j aK = 0 := by linarith
  rw [this, mul_zero]

/-- **T3(c), a single outcome with uninformative choice reveals nothing**: with `J` a singleton,
the uninformative-choice assumption *is* "`C_1` reveals nothing about `F`", so `w = v_K` and
(I) = 0.
Source: [[value-change-as-epistemic-update]] §1.4 ("If there is a single outcome … `w_C = v_K` and
(I) = 0")
Kind: P
Fidelity: exact
Hyps: (a) `h : Uninformative`, `[Unique J]`, `htil`, `hK` -/
theorem termI_zero_single_outcome [Unique J] (atil : J → A) (aK : A) (h : M.Uninformative)
    (htil : ∀ j a, M.w j a ≤ M.w j (atil j)) (hK : ∀ a, M.vKf a ≤ M.vKf aK) :
    M.termI atil aK = 0 := by
  apply M.termI_zero_of_uninformative_outcomes atil aK _ htil hK
  intro j f
  have hf := h f
  have hj : j = default := Subsingleton.elim _ _
  have hs : ∀ g : J → ℝ, ∑ i, g i = g j := by
    intro g; rw [Fintype.sum_unique]; rw [hj]
  rw [hs] at hf
  unfold qC
  have hC : M.qCtot = ∑ f, M.q f (some j) := by
    unfold qCtot qC; rw [hs]
  rw [hC] at hf
  exact hf

end ProductModel

end

end Cleanroom.Corrigibility.CorrValueChange
