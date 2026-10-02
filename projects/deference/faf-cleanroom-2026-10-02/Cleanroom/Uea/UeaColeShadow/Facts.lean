import Cleanroom.Uea.UeaColeShadow.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Facts F1, F2, Lemma A and Lemma A′

Basic properties of the mixture built from a policy (nonnegativity, normalisation of the kernels, the
one-step `ext` identities), the value bounds `[0, 1]` and the comparison `V^σ ≤ V^*`, the mixture
identities `ξ(h) V_ξ(h) = (1-δ) ξ_S(h) V^π(h) + ∑_i w_i ν_i(h) V^{ν_i}(h)` (and its `Q` form, Lemma A
unnormalised) and `ξ_{-S}(h) V^{π̄}(h) = ∑_i w_i ν_i(h) V^{ν_i}(h)` (Lemma A′), then F1 (percepts do not
move the self-posterior), F2 (the product and odds forms of the posterior update), Lemma A in the
note's and the audit's forms with its upper and lower halves, and Lemma A′.

Sources: [[sequential-self-game]] §1; [[audit-revised-theorem-1]] §1.
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset

namespace Model

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] (M : Model A E ι)

/-! ### Kernels and joints: nonnegativity and normalisation -/

theorem νa_nonneg (i : ι) (n : ℕ) (h : Hist A E n) (a : A) : 0 ≤ M.νa i n h a := (M.νa_mem i n h).1 a
theorem νa_sum (i : ι) (n : ℕ) (h : Hist A E n) : ∑ a, M.νa i n h a = 1 := (M.νa_mem i n h).2
theorem νa_le_one (i : ι) (n : ℕ) (h : Hist A E n) (a : A) : M.νa i n h a ≤ 1 :=
  (mem_Icc_of_mem_stdSimplex (M.νa_mem i n h) a).2
theorem νe_nonneg (i : ι) (n : ℕ) (h : Hist A E n) (a : A) (e : E) : 0 ≤ M.νe i n h a e :=
  (M.νe_mem i n h a).1 e
theorem νe_sum (i : ι) (n : ℕ) (h : Hist A E n) (a : A) : ∑ e, M.νe i n h a e = 1 :=
  (M.νe_mem i n h a).2

theorem nuJoint_nonneg (i : ι) : ∀ (n : ℕ) (h : Hist A E n), 0 ≤ M.nuJoint i n h := by
  intro n
  induction n with
  | zero => intro h; simp
  | succ n ih =>
    intro h
    simp only [nuJoint]
    exact mul_nonneg (mul_nonneg (ih _) (M.νa_nonneg _ _ _ _)) (M.νe_nonneg _ _ _ _ _)

theorem xins_nonneg (n : ℕ) (h : Hist A E n) : 0 ≤ M.xins n h :=
  sum_nonneg fun i _ => mul_nonneg (M.w_nonneg i) (M.nuJoint_nonneg i n h)

theorem xinsA_nonneg (n : ℕ) (h : Hist A E n) (a : A) : 0 ≤ M.xinsA n h a :=
  sum_nonneg fun i _ => mul_nonneg (mul_nonneg (M.w_nonneg i) (M.nuJoint_nonneg i n h)) (M.νa_nonneg _ _ _ _)

/-- `ξ_{-S}(h) = ∑_a ξ_{-S}(ha)`. -/
theorem xinsA_sum (n : ℕ) (h : Hist A E n) : ∑ a, M.xinsA n h a = M.xins n h := by
  unfold xinsA xins
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← mul_sum, M.νa_sum, mul_one]

theorem xinsA_le_xins (n : ℕ) (h : Hist A E n) (a : A) : M.xinsA n h a ≤ M.xins n h := by
  rw [← M.xinsA_sum n h]
  exact single_le_sum (fun b _ => M.xinsA_nonneg n h b) (mem_univ a)

/-- `ξ_{-S}(h) = 0` iff every hypothesis's weighted joint vanishes at `h`. -/
theorem xins_eq_zero_iff (n : ℕ) (h : Hist A E n) :
    M.xins n h = 0 ↔ ∀ i, M.w i * M.nuJoint i n h = 0 := by
  unfold xins
  rw [sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (M.w_nonneg i) (M.nuJoint_nonneg i n h)]
  simp

theorem xinsA_eq_zero_iff (n : ℕ) (h : Hist A E n) (a : A) :
    M.xinsA n h a = 0 ↔ ∀ i, M.w i * M.nuJoint i n h * M.νa i n h a = 0 := by
  unfold xinsA
  rw [sum_eq_zero_iff_of_nonneg fun i _ =>
    mul_nonneg (mul_nonneg (M.w_nonneg i) (M.nuJoint_nonneg i n h)) (M.νa_nonneg _ _ _ _)]
  simp

theorem xinsA_eq_zero_of_xins_eq_zero {n : ℕ} {h : Hist A E n} (hx : M.xins n h = 0) (a : A) :
    M.xinsA n h a = 0 :=
  le_antisymm (hx ▸ M.xinsA_le_xins n h a) (M.xinsA_nonneg n h a)

theorem xie_nonneg (n : ℕ) (h : Hist A E n) (a : A) (e : E) : 0 ≤ M.xie n h a e := by
  unfold xie
  split_ifs with hA
  · exact div_nonneg (sum_nonneg fun i _ => mul_nonneg (M.w_nonneg i) (M.νe_nonneg _ _ _ _ _)) M.δ_pos.le
  · exact div_nonneg (sum_nonneg fun i _ => mul_nonneg (mul_nonneg (mul_nonneg (M.w_nonneg i)
      (M.nuJoint_nonneg i n h)) (M.νa_nonneg _ _ _ _)) (M.νe_nonneg _ _ _ _ _)) (M.xinsA_nonneg n h a)

/-- The percept kernel is a probability distribution: `∑_e ξ(e|ha) = 1`.
Source: [[sequential-self-game]] §1
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem xie_sum (n : ℕ) (h : Hist A E n) (a : A) : ∑ e, M.xie n h a e = 1 := by
  by_cases hA : M.xinsA n h a = 0
  · simp only [xie, if_pos hA]
    rw [← sum_div, sum_comm]
    simp_rw [← mul_sum, M.νe_sum, mul_one]
    rw [M.w_sum]
    exact div_self M.δ_pos.ne'
  · simp only [xie, if_neg hA]
    rw [← sum_div, sum_comm]
    simp_rw [← mul_sum, M.νe_sum, mul_one]
    exact div_self hA

theorem xie_mem_stdSimplex (n : ℕ) (h : Hist A E n) (a : A) : M.xie n h a ∈ stdSimplex ℝ E :=
  ⟨M.xie_nonneg n h a, M.xie_sum n h a⟩

theorem xie_le_one (n : ℕ) (h : Hist A E n) (a : A) (e : E) : M.xie n h a e ≤ 1 :=
  (mem_Icc_of_mem_stdSimplex (M.xie_mem_stdSimplex n h a) e).2

/-- The one-step identity for the non-self mixture: `ξ_{-S}(hae) = ξ_{-S}(ha) ξ(e|ha)` (this is the
content of the fallback convention: where `ξ_{-S}(ha) = 0` both sides vanish).
Source: [[sequential-self-game]] §1 (F1's unwinding)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem xins_ext (n : ℕ) (h : Hist A E n) (a : A) (e : E) :
    M.xins (n + 1) (ext h a e) = M.xinsA n h a * M.xie n h a e := by
  by_cases hA : M.xinsA n h a = 0
  · have h0 : ∀ i, M.w i * M.nuJoint i n h * M.νa i n h a = 0 := (M.xinsA_eq_zero_iff n h a).1 hA
    rw [hA, zero_mul]
    unfold xins
    simp only [nuJoint_ext]
    exact sum_eq_zero fun i _ => by rw [← mul_assoc, ← mul_assoc, h0 i, zero_mul]
  · unfold xins xie
    simp only [nuJoint_ext, if_neg hA]
    rw [mul_div_cancel₀ _ hA]
    exact sum_congr rfl fun i _ => by ring

theorem xins_ext_sum (n : ℕ) (h : Hist A E n) (a : A) :
    ∑ e, M.xins (n + 1) (ext h a e) = M.xinsA n h a := by
  simp_rw [xins_ext, ← mul_sum, M.xie_sum, mul_one]

theorem nuJoint_ext_sum (i : ι) (n : ℕ) (h : Hist A E n) (a : A) :
    ∑ e, M.nuJoint i (n + 1) (ext h a e) = M.nuJoint i n h * M.νa i n h a := by
  simp_rw [nuJoint_ext, ← mul_sum, M.νe_sum, mul_one]

/-! ### The self-hypothesis and the mixture -/

variable {π : Policy A E}

theorem IsPolicy.nonneg {M : Model A E ι} (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n}
    (hnt : M.nonterminal n h) (a : A) : 0 ≤ π n h a := (hπ n h hnt).1 a

theorem IsPolicy.sum {M : Model A E ι} (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n}
    (hnt : M.nonterminal n h) : ∑ a, π n h a = 1 := (hπ n h hnt).2

theorem IsPolicy.le_one {M : Model A E ι} (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n}
    (hnt : M.nonterminal n h) (a : A) : π n h a ≤ 1 := (mem_Icc_of_mem_stdSimplex (hπ n h hnt) a).2

theorem xiS_nonneg (hπ : M.IsPolicy π) :
    ∀ (n : ℕ) (h : Hist A E n), M.nonterminal n h → 0 ≤ M.xiS π n h := by
  intro n
  induction n with
  | zero => intro h _; simp
  | succ n ih =>
    intro h hnt
    simp only [xiS]
    have hi := M.nonterminal_init hnt
    exact mul_nonneg (mul_nonneg (ih _ hi) (hπ.nonneg hi _)) (M.xie_nonneg _ _ _ _)

theorem xiS_ext_nonneg (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (a : A)
    (e : E) : 0 ≤ M.xiS π (n + 1) (ext h a e) := by
  rw [xiS_ext]
  exact mul_nonneg (mul_nonneg (M.xiS_nonneg hπ n h hnt) (hπ.nonneg hnt a)) (M.xie_nonneg _ _ _ _)

theorem xiS_ext_sum (n : ℕ) (h : Hist A E n) (a : A) :
    ∑ e, M.xiS π (n + 1) (ext h a e) = M.xiS π n h * π n h a := by
  simp_rw [xiS_ext, ← mul_sum, M.xie_sum, mul_one]

/-- `ξ(ha) = (1-δ) ξ_S(h) π(a|h) + ξ_{-S}(ha)`.
Source: [[sequential-self-game]] §1 (F2 unnormalised)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem xiA_eq (n : ℕ) (h : Hist A E n) (a : A) :
    M.xiA π n h a = (1 - M.δ) * M.xiS π n h * π n h a + M.xinsA n h a := by
  unfold xiA xi
  rw [sum_add_distrib, ← mul_sum, xiS_ext_sum, xins_ext_sum, mul_assoc]

/-- `ξ(hae) = ξ(e|ha) ξ(ha)`. -/
theorem xi_ext (n : ℕ) (h : Hist A E n) (a : A) (e : E) :
    M.xi π (n + 1) (ext h a e) = M.xie n h a e * M.xiA π n h a := by
  rw [xiA_eq]
  unfold xi
  rw [xiS_ext, xins_ext]
  ring

theorem xi_nonneg (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    0 ≤ M.xi π n h :=
  add_nonneg (mul_nonneg (by linarith [M.δ_lt_one]) (M.xiS_nonneg hπ n h hnt)) (M.xins_nonneg n h)

theorem xiA_nonneg (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (a : A) :
    0 ≤ M.xiA π n h a := by
  rw [xiA_eq]
  exact add_nonneg (mul_nonneg (mul_nonneg (by linarith [M.δ_lt_one]) (M.xiS_nonneg hπ n h hnt))
    (hπ.nonneg hnt a)) (M.xinsA_nonneg n h a)

theorem xins_le_xi (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.xins n h ≤ M.xi π n h := by
  unfold xi
  linarith [mul_nonneg (by linarith [M.δ_lt_one] : (0:ℝ) ≤ 1 - M.δ) (M.xiS_nonneg hπ n h hnt)]

theorem xins_eq_zero_of_xi_eq_zero (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hx : M.xi π n h = 0) : M.xins n h = 0 :=
  le_antisymm (hx ▸ M.xins_le_xi hπ hnt) (M.xins_nonneg n h)

theorem xiS_eq_zero_of_xi_eq_zero (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hx : M.xi π n h = 0) : M.xiS π n h = 0 := by
  have h1 := M.xins_eq_zero_of_xi_eq_zero hπ hnt hx
  unfold xi at hx
  have hδ : (0:ℝ) < 1 - M.δ := by linarith [M.δ_lt_one]
  nlinarith [M.xiS_nonneg hπ n h hnt]

/-- `∑_a ξ(ha) = ξ(h)` at a decision node.
Source: [[sequential-self-game]] §1
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem xiA_sum (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    ∑ a, M.xiA π n h a = M.xi π n h := by
  simp_rw [xiA_eq]
  rw [sum_add_distrib, ← mul_sum, hπ.sum hnt, xinsA_sum]
  unfold xi
  ring

theorem xia_nonneg (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (a : A) :
    0 ≤ M.xia π n h a := by
  unfold xia
  split_ifs with hx
  · exact hπ.nonneg hnt a
  · exact div_nonneg (M.xiA_nonneg hπ hnt a) (M.xi_nonneg hπ hnt)

theorem xia_sum (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    ∑ a, M.xia π n h a = 1 := by
  unfold xia
  split_ifs with hx
  · exact hπ.sum hnt
  · rw [← sum_div, M.xiA_sum hπ hnt, div_self hx]

/-- The mixture's action conditional is a policy (under the continuous extension).
Source: [[sequential-self-game]] §1
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem isPolicy_xia (hπ : M.IsPolicy π) : M.IsPolicy (M.xia π) :=
  fun n h hnt => ⟨M.xia_nonneg hπ hnt, M.xia_sum hπ hnt⟩

/-! ### The posterior -/

theorem wS_of_xi_eq_zero {n : ℕ} {h : Hist A E n} (hx : M.xi π n h = 0) : M.wS π n h = 1 := by
  simp [wS, hx]

theorem wS_of_xi_ne_zero {n : ℕ} {h : Hist A E n} (hx : M.xi π n h ≠ 0) :
    M.wS π n h = (1 - M.δ) * M.xiS π n h / M.xi π n h := by
  simp [wS, hx]

theorem wS_nonneg (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    0 ≤ M.wS π n h := by
  unfold wS
  split_ifs
  · exact zero_le_one
  · exact div_nonneg (mul_nonneg (by linarith [M.δ_lt_one]) (M.xiS_nonneg hπ n h hnt)) (M.xi_nonneg hπ hnt)

theorem wS_le_one (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.wS π n h ≤ 1 := by
  unfold wS
  split_ifs with hx
  · exact le_rfl
  · rw [div_le_one (lt_of_le_of_ne (M.xi_nonneg hπ hnt) (Ne.symm hx))]
    unfold xi
    linarith [M.xins_nonneg n h]

/-- `1 - w_h = ξ_{-S}(h) / ξ(h)` when `ξ(h) ≠ 0`. -/
theorem one_sub_wS {n : ℕ} {h : Hist A E n} (hx : M.xi π n h ≠ 0) :
    1 - M.wS π n h = M.xins n h / M.xi π n h := by
  rw [wS_of_xi_ne_zero M hx]
  unfold xi at hx ⊢
  field_simp
  ring

/-- `w_h = 1` iff the non-self mixture has no mass at `h`.
Source: [[sequential-self-game]] §4.1 (Step 0)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem wS_eq_one_iff (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.wS π n h = 1 ↔ M.xins n h = 0 := by
  by_cases hx : M.xi π n h = 0
  · simp [wS_of_xi_eq_zero M hx, M.xins_eq_zero_of_xi_eq_zero hπ hnt hx]
  · have hpos : 0 < M.xi π n h := lt_of_le_of_ne (M.xi_nonneg hπ hnt) (Ne.symm hx)
    have := M.one_sub_wS (π := π) hx
    constructor
    · intro h1
      rw [h1, sub_self] at this
      rcases (div_eq_zero_iff.1 this.symm) with h2 | h2
      · exact h2
      · exact absurd h2 hx
    · intro h2
      rw [h2, zero_div, sub_eq_zero] at this
      exact this.symm

theorem wS_pos_of_xiS_pos {n : ℕ} {h : Hist A E n} (hS : 0 < M.xiS π n h) : 0 < M.wS π n h := by
  have hx : 0 < M.xi π n h := by
    unfold xi
    have : (0:ℝ) < 1 - M.δ := by linarith [M.δ_lt_one]
    nlinarith [M.xins_nonneg n h]
  rw [wS_of_xi_ne_zero M hx.ne']
  exact div_pos (mul_pos (by linarith [M.δ_lt_one]) hS) hx

theorem xiS_pos_of_wS_pos (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hx : M.xi π n h ≠ 0) (hw : 0 < M.wS π n h) : 0 < M.xiS π n h := by
  rw [wS_of_xi_ne_zero M hx] at hw
  have hpos : 0 < M.xi π n h := lt_of_le_of_ne (M.xi_nonneg hπ hnt) (Ne.symm hx)
  have := (div_pos_iff_of_pos_right hpos).1 hw
  have hδ : (0:ℝ) < 1 - M.δ := by linarith [M.δ_lt_one]
  exact pos_of_mul_pos_right this hδ.le

theorem xi_pos_of_xiS_pos {n : ℕ} {h : Hist A E n} (hS : 0 < M.xiS π n h) : 0 < M.xi π n h := by
  unfold xi
  have : (0:ℝ) < 1 - M.δ := by linarith [M.δ_lt_one]
  nlinarith [M.xins_nonneg n h]

/-! ### `π̄` is sub-stochastic -/

theorem pibar_nonneg (n : ℕ) (h : Hist A E n) (a : A) : 0 ≤ M.pibar n h a :=
  div_nonneg (M.xinsA_nonneg n h a) (M.xins_nonneg n h)

theorem pibar_sum_eq_one {n : ℕ} {h : Hist A E n} (hx : M.xins n h ≠ 0) : ∑ a, M.pibar n h a = 1 := by
  unfold pibar
  rw [← sum_div, xinsA_sum, div_self hx]

theorem pibar_of_xins_eq_zero {n : ℕ} {h : Hist A E n} (hx : M.xins n h = 0) (a : A) :
    M.pibar n h a = 0 := by
  simp [pibar, hx]

theorem pibar_sum_le_one (n : ℕ) (h : Hist A E n) : ∑ a, M.pibar n h a ≤ 1 := by
  by_cases hx : M.xins n h = 0
  · simp [M.pibar_of_xins_eq_zero hx]
  · exact (M.pibar_sum_eq_one hx).le

theorem pibar_le_one (n : ℕ) (h : Hist A E n) (a : A) : M.pibar n h a ≤ 1 :=
  le_trans (single_le_sum (fun b _ => M.pibar_nonneg n h b) (mem_univ a)) (M.pibar_sum_le_one n h)

theorem isSubPolicy_pibar : M.IsSubPolicy M.pibar :=
  fun n h _ => ⟨M.pibar_nonneg n h, M.pibar_sum_le_one n h⟩

/-- `p̄_h ≤ 1`. -/
theorem pbar_le_one (n : ℕ) (h : Hist A E n) : M.pbar π n h ≤ 1 :=
  le_trans (sum_le_sum_of_subset_of_nonneg (subset_univ _) fun b _ _ => M.pibar_nonneg n h b)
    (M.pibar_sum_le_one n h)

theorem pbar_nonneg (n : ℕ) (h : Hist A E n) : 0 ≤ M.pbar π n h :=
  sum_nonneg fun b _ => M.pibar_nonneg n h b


/-! ### Value bounds `[0, 1]` and the comparison `V^σ ≤ V^*` -/

/-- An aggregator is admissible if it maps continuation values in `[0, hi]` to a value in `[0, hi]` at
every decision node (averaging under a sub-stochastic kernel; maximum).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def AggOK (agg : Agg A E) : Prop :=
  ∀ n h, M.nonterminal n h → ∀ (q : A → ℝ) (hi : ℝ), (∀ a, 0 ≤ q a ∧ q a ≤ hi) →
    0 ≤ agg n h q ∧ agg n h q ≤ hi

theorem pathReturnOf_nonneg : ∀ (n : ℕ) (h : Hist A E n), 0 ≤ pathReturnOf M.γ M.r n h := by
  intro n
  induction n with
  | zero => intro h; simp
  | succ n ih =>
    intro h
    simp only [pathReturnOf]
    exact add_nonneg (ih _) (mul_nonneg (pow_nonneg M.γ_pos.le n) (M.r_nonneg n h))

/-- The fuel recursion is nonnegative and, together with the return already accumulated, at most `1`.
Source: [[sequential-self-game]] §1 ("every conditional return from any `h` lies in `[0,1]`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem valF_bounds {agg : Agg A E} (hagg : M.AggOK agg) {κ : PerKernel A E}
    (hκ : ∀ n h a, κ n h a ∈ stdSimplex ℝ E) :
    ∀ k n (h : Hist A E n), n + k ≤ M.T →
      0 ≤ M.valF agg κ k n h ∧ pathReturnOf M.γ M.r n h + M.valF agg κ k n h ≤ 1 := by
  intro k
  induction k with
  | zero =>
    intro n h hk
    simp only [valF, add_zero]
    exact ⟨le_rfl, M.norm n (by omega) h⟩
  | succ k ih =>
    intro n h hk
    by_cases hnt : M.nonterminal n h
    · simp only [valF, hnt, if_true]
      have hin : ∀ a, 0 ≤ (∑ e, κ n h a e * (M.γ ^ n * M.r n (ext h a e) + M.valF agg κ k (n + 1) (ext h a e))) ∧
          (∑ e, κ n h a e * (M.γ ^ n * M.r n (ext h a e) + M.valF agg κ k (n + 1) (ext h a e))) ≤
            1 - pathReturnOf M.γ M.r n h := by
        intro a
        have hterm : ∀ e, 0 ≤ M.γ ^ n * M.r n (ext h a e) + M.valF agg κ k (n + 1) (ext h a e) ∧
            M.γ ^ n * M.r n (ext h a e) + M.valF agg κ k (n + 1) (ext h a e) ≤
              1 - pathReturnOf M.γ M.r n h := by
          intro e
          obtain ⟨h0, h1⟩ := ih (n + 1) (ext h a e) (by omega)
          rw [pathReturnOf_ext] at h1
          exact ⟨add_nonneg (mul_nonneg (pow_nonneg M.γ_pos.le n) (M.r_nonneg _ _)) h0, by linarith⟩
        refine ⟨sum_nonneg fun e _ => mul_nonneg ((hκ n h a).1 e) (hterm e).1, ?_⟩
        calc ∑ e, κ n h a e * (M.γ ^ n * M.r n (ext h a e) + M.valF agg κ k (n + 1) (ext h a e))
            ≤ ∑ e, κ n h a e * (1 - pathReturnOf M.γ M.r n h) :=
              sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hterm e).2 ((hκ n h a).1 e)
          _ = 1 - pathReturnOf M.γ M.r n h := by rw [← sum_mul, (hκ n h a).2, one_mul]
      have := hagg n h hnt _ (1 - pathReturnOf M.γ M.r n h) hin
      exact ⟨this.1, by linarith [this.2]⟩
    · simp only [valF, hnt, if_false, add_zero]
      exact ⟨le_rfl, M.norm n (by omega) h⟩

section Values
variable [Nonempty A]

theorem aggOK_aggPol {σ : Policy A E} (hσ : M.IsSubPolicy σ) : M.AggOK (aggPol σ) := by
  intro n h hnt q hi hq
  obtain ⟨hσ0, hσ1⟩ := hσ n h hnt
  have hhi : 0 ≤ hi := le_trans (hq (Classical.arbitrary A)).1 (hq _).2
  refine ⟨sum_nonneg fun a _ => mul_nonneg (hσ0 a) (hq a).1, ?_⟩
  calc ∑ a, σ n h a * q a ≤ ∑ a, σ n h a * hi :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hq a).2 (hσ0 a)
    _ = (∑ a, σ n h a) * hi := by rw [sum_mul]
    _ ≤ 1 * hi := mul_le_mul_of_nonneg_right hσ1 hhi
    _ = hi := one_mul hi

theorem aggOK_aggMax : M.AggOK aggMax := by
  intro n h _ q hi hq
  refine ⟨le_trans (hq (Classical.arbitrary A)).1 (le_sup' q (mem_univ _)), ?_⟩
  exact Finset.sup'_le _ _ fun a _ => (hq a).2

variable {agg : Agg A E} (hagg : M.AggOK agg) {κ : PerKernel A E} (hκ : ∀ n h a, κ n h a ∈ stdSimplex ℝ E)
include hagg hκ

theorem val_nonneg (n : ℕ) (h : Hist A E n) : 0 ≤ M.val agg κ n h := by
  by_cases hn : n ≤ M.T
  · exact (M.valF_bounds hagg hκ (M.T - n) n h (by omega)).1
  · rw [M.val_eq_zero_of_not_nonterminal agg κ (M.not_nonterminal_of_le (by omega) h)]

theorem val_add_pathReturn_le_one {n : ℕ} (hn : n ≤ M.T) (h : Hist A E n) :
    pathReturnOf M.γ M.r n h + M.val agg κ n h ≤ 1 :=
  (M.valF_bounds hagg hκ (M.T - n) n h (by omega)).2

theorem val_le_one (n : ℕ) (h : Hist A E n) : M.val agg κ n h ≤ 1 := by
  by_cases hn : n ≤ M.T
  · linarith [M.val_add_pathReturn_le_one hagg hκ hn h, M.pathReturnOf_nonneg n h]
  · rw [M.val_eq_zero_of_not_nonterminal agg κ (M.not_nonterminal_of_le (by omega) h)]
    exact zero_le_one

theorem qval_nonneg (n : ℕ) (h : Hist A E n) (a : A) : 0 ≤ M.qval agg κ n h a :=
  sum_nonneg fun e _ => mul_nonneg ((hκ n h a).1 e)
    (add_nonneg (mul_nonneg (pow_nonneg M.γ_pos.le n) (M.r_nonneg _ _)) (M.val_nonneg hagg hκ _ _))

theorem qval_le_one_sub {n : ℕ} (hn : n < M.T) (h : Hist A E n) (a : A) :
    M.qval agg κ n h a ≤ 1 - pathReturnOf M.γ M.r n h := by
  unfold qval
  have hterm : ∀ e, M.γ ^ n * M.r n (ext h a e) + M.val agg κ (n + 1) (ext h a e) ≤
      1 - pathReturnOf M.γ M.r n h := by
    intro e
    have := M.val_add_pathReturn_le_one hagg hκ (n := n + 1) (by omega) (ext h a e)
    rw [pathReturnOf_ext] at this
    linarith
  calc ∑ e, κ n h a e * (M.γ ^ n * M.r n (ext h a e) + M.val agg κ (n + 1) (ext h a e))
      ≤ ∑ e, κ n h a e * (1 - pathReturnOf M.γ M.r n h) :=
        sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hterm e) ((hκ n h a).1 e)
    _ = 1 - pathReturnOf M.γ M.r n h := by rw [← sum_mul, (hκ n h a).2, one_mul]

theorem qval_le_one {n : ℕ} (hn : n < M.T) (h : Hist A E n) (a : A) : M.qval agg κ n h a ≤ 1 := by
  linarith [M.qval_le_one_sub hagg hκ hn h a, M.pathReturnOf_nonneg n h]

end Values

section Compare
variable [Nonempty A] {κ : PerKernel A E} (hκ : ∀ n h a, κ n h a ∈ stdSimplex ℝ E)
include hκ

/-- **Comparison**: the value of any sub-stochastic policy against a percept kernel is at most the
optimal value against the same kernel, at every history.
Source: [[sequential-self-game]] §1 (Lemma A′: "which `V^*_ξ` dominates")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem val_aggPol_le_val_aggMax {σ : Policy A E} (hσ : M.IsSubPolicy σ) :
    ∀ n h, M.val (aggPol σ) κ n h ≤ M.val aggMax κ n h := by
  refine M.depth_induction (fun n h => M.val (aggPol σ) κ n h ≤ M.val aggMax κ n h) ?_ ?_
  · intro n h hnt
    rw [M.val_eq_zero_of_not_nonterminal _ _ hnt, M.val_eq_zero_of_not_nonterminal _ _ hnt]
  · intro n h hnt ih
    rw [M.val_eq_of_nonterminal _ _ hnt, M.val_eq_of_nonterminal _ _ hnt]
    have hq : ∀ a, M.qval (aggPol σ) κ n h a ≤ M.qval aggMax κ n h a := by
      intro a
      unfold qval
      exact sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (by linarith [ih a e]) ((hκ n h a).1 e)
    obtain ⟨hσ0, hσ1⟩ := hσ n h hnt
    have hmax0 : 0 ≤ aggMax n h (M.qval aggMax κ n h) :=
      (M.aggOK_aggMax n h hnt _ 1 fun a =>
        ⟨M.qval_nonneg M.aggOK_aggMax hκ n h a, M.qval_le_one M.aggOK_aggMax hκ hnt.1 h a⟩).1
    calc aggPol σ n h (M.qval (aggPol σ) κ n h) = ∑ a, σ n h a * M.qval (aggPol σ) κ n h a := rfl
      _ ≤ ∑ a, σ n h a * M.qval aggMax κ n h a :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hq a) (hσ0 a)
      _ ≤ ∑ a, σ n h a * aggMax n h (M.qval aggMax κ n h) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (le_sup' _ (mem_univ a)) (hσ0 a)
      _ = (∑ a, σ n h a) * aggMax n h (M.qval aggMax κ n h) := by rw [sum_mul]
      _ ≤ 1 * aggMax n h (M.qval aggMax κ n h) := mul_le_mul_of_nonneg_right hσ1 hmax0
      _ = aggMax n h (M.qval aggMax κ n h) := one_mul _

theorem qval_aggPol_le_qval_aggMax {σ : Policy A E} (hσ : M.IsSubPolicy σ) (n : ℕ) (h : Hist A E n)
    (a : A) : M.qval (aggPol σ) κ n h a ≤ M.qval aggMax κ n h a := by
  unfold qval
  exact sum_le_sum fun e _ => mul_le_mul_of_nonneg_left
    (by linarith [M.val_aggPol_le_val_aggMax hκ hσ (n + 1) (ext h a e)]) ((hκ n h a).1 e)

end Compare

/-! ### The named values: unfolding, bounds, comparisons -/

section Named
variable [Nonempty A]

theorem Vpi_eq {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.Vpi π n h = ∑ a, π n h a * M.Qpi π n h a := M.val_eq_of_nonterminal _ _ hnt

theorem Vpi_of_not_nonterminal {n : ℕ} {h : Hist A E n} (hnt : ¬ M.nonterminal n h) : M.Vpi π n h = 0 :=
  M.val_eq_zero_of_not_nonterminal _ _ hnt

theorem Vstar_eq {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.Vstar n h = univ.sup' univ_nonempty (M.Qstar n h) := M.val_eq_of_nonterminal _ _ hnt

theorem Vstar_of_not_nonterminal {n : ℕ} {h : Hist A E n} (hnt : ¬ M.nonterminal n h) : M.Vstar n h = 0 :=
  M.val_eq_zero_of_not_nonterminal _ _ hnt

theorem Vxi_eq {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.Vxi π n h = ∑ a, M.xia π n h a * M.Qxi π n h a := M.val_eq_of_nonterminal _ _ hnt

theorem Vxi_of_not_nonterminal {n : ℕ} {h : Hist A E n} (hnt : ¬ M.nonterminal n h) : M.Vxi π n h = 0 :=
  M.val_eq_zero_of_not_nonterminal _ _ hnt

theorem Vnu_eq (i : ι) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.Vnu i n h = ∑ a, M.νa i n h a * M.Qnu i n h a := M.val_eq_of_nonterminal _ _ hnt

theorem Vnu_of_not_nonterminal (i : ι) {n : ℕ} {h : Hist A E n} (hnt : ¬ M.nonterminal n h) :
    M.Vnu i n h = 0 := M.val_eq_zero_of_not_nonterminal _ _ hnt

theorem Vbar_eq {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.Vbar n h = ∑ a, M.pibar n h a * M.Qbar n h a := M.val_eq_of_nonterminal _ _ hnt

theorem Vbar_of_not_nonterminal {n : ℕ} {h : Hist A E n} (hnt : ¬ M.nonterminal n h) : M.Vbar n h = 0 :=
  M.val_eq_zero_of_not_nonterminal _ _ hnt

theorem Qxi_eq_sum (n : ℕ) (h : Hist A E n) (a : A) : M.Qxi π n h a =
    ∑ e, M.xie n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vxi π (n + 1) (ext h a e)) := rfl
theorem Qpi_eq_sum (n : ℕ) (h : Hist A E n) (a : A) : M.Qpi π n h a =
    ∑ e, M.xie n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vpi π (n + 1) (ext h a e)) := rfl
theorem Qstar_eq_sum (n : ℕ) (h : Hist A E n) (a : A) : M.Qstar n h a =
    ∑ e, M.xie n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vstar (n + 1) (ext h a e)) := rfl
theorem Qnu_eq_sum (i : ι) (n : ℕ) (h : Hist A E n) (a : A) : M.Qnu i n h a =
    ∑ e, M.νe i n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vnu i (n + 1) (ext h a e)) := rfl
theorem Qbar_eq_sum (n : ℕ) (h : Hist A E n) (a : A) : M.Qbar n h a =
    ∑ e, M.xie n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vbar (n + 1) (ext h a e)) := rfl

theorem Qstar_le_Vstar {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (a : A) :
    M.Qstar n h a ≤ M.Vstar n h := by
  rw [M.Vstar_eq hnt]
  exact le_sup' _ (mem_univ a)

theorem Vstar_eq_Qstar_piStar {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.Vstar n h = M.Qstar n h (M.piStar n h) := by
  rw [M.Vstar_eq hnt, M.Qstar_piStar]

/-- At a node with a unique optimal action, `π⋆` is that action.
Source: [[sequential-self-game]] §1
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem piStar_eq_of_unique {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) {a₀ : A}
    (hu : ∀ a, M.Qstar n h a = M.Vstar n h → a = a₀) : M.piStar n h = a₀ :=
  hu _ (M.Vstar_eq_Qstar_piStar hnt).symm

theorem Vstar_nonneg (n : ℕ) (h : Hist A E n) : 0 ≤ M.Vstar n h :=
  M.val_nonneg M.aggOK_aggMax M.xie_mem_stdSimplex n h
theorem Vstar_le_one (n : ℕ) (h : Hist A E n) : M.Vstar n h ≤ 1 :=
  M.val_le_one M.aggOK_aggMax M.xie_mem_stdSimplex n h
theorem Qstar_nonneg (n : ℕ) (h : Hist A E n) (a : A) : 0 ≤ M.Qstar n h a :=
  M.qval_nonneg M.aggOK_aggMax M.xie_mem_stdSimplex n h a
theorem Qstar_le_one {n : ℕ} (hn : n < M.T) (h : Hist A E n) (a : A) : M.Qstar n h a ≤ 1 :=
  M.qval_le_one M.aggOK_aggMax M.xie_mem_stdSimplex hn h a

theorem Vpi_nonneg (hπ : M.IsPolicy π) (n : ℕ) (h : Hist A E n) : 0 ≤ M.Vpi π n h :=
  M.val_nonneg (M.aggOK_aggPol hπ.isSubPolicy) M.xie_mem_stdSimplex n h
theorem Vpi_le_one (hπ : M.IsPolicy π) (n : ℕ) (h : Hist A E n) : M.Vpi π n h ≤ 1 :=
  M.val_le_one (M.aggOK_aggPol hπ.isSubPolicy) M.xie_mem_stdSimplex n h
theorem Qpi_nonneg (hπ : M.IsPolicy π) (n : ℕ) (h : Hist A E n) (a : A) : 0 ≤ M.Qpi π n h a :=
  M.qval_nonneg (M.aggOK_aggPol hπ.isSubPolicy) M.xie_mem_stdSimplex n h a
theorem Qpi_le_one (hπ : M.IsPolicy π) {n : ℕ} (hn : n < M.T) (h : Hist A E n) (a : A) :
    M.Qpi π n h a ≤ 1 :=
  M.qval_le_one (M.aggOK_aggPol hπ.isSubPolicy) M.xie_mem_stdSimplex hn h a

theorem Vxi_nonneg (hπ : M.IsPolicy π) (n : ℕ) (h : Hist A E n) : 0 ≤ M.Vxi π n h :=
  M.val_nonneg (M.aggOK_aggPol (M.isPolicy_xia hπ).isSubPolicy) M.xie_mem_stdSimplex n h
theorem Vxi_le_one (hπ : M.IsPolicy π) (n : ℕ) (h : Hist A E n) : M.Vxi π n h ≤ 1 :=
  M.val_le_one (M.aggOK_aggPol (M.isPolicy_xia hπ).isSubPolicy) M.xie_mem_stdSimplex n h
theorem Qxi_nonneg (hπ : M.IsPolicy π) (n : ℕ) (h : Hist A E n) (a : A) : 0 ≤ M.Qxi π n h a :=
  M.qval_nonneg (M.aggOK_aggPol (M.isPolicy_xia hπ).isSubPolicy) M.xie_mem_stdSimplex n h a
theorem Qxi_le_one (hπ : M.IsPolicy π) {n : ℕ} (hn : n < M.T) (h : Hist A E n) (a : A) :
    M.Qxi π n h a ≤ 1 :=
  M.qval_le_one (M.aggOK_aggPol (M.isPolicy_xia hπ).isSubPolicy) M.xie_mem_stdSimplex hn h a

theorem Vnu_nonneg (i : ι) (n : ℕ) (h : Hist A E n) : 0 ≤ M.Vnu i n h :=
  M.val_nonneg (M.aggOK_aggPol (fun n h _ => ⟨M.νa_nonneg i n h, (M.νa_sum i n h).le⟩)) (M.νe_mem i) n h
theorem Qnu_nonneg (i : ι) (n : ℕ) (h : Hist A E n) (a : A) : 0 ≤ M.Qnu i n h a :=
  M.qval_nonneg (M.aggOK_aggPol (fun n h _ => ⟨M.νa_nonneg i n h, (M.νa_sum i n h).le⟩)) (M.νe_mem i) n h a
theorem Qnu_le_one (i : ι) {n : ℕ} (hn : n < M.T) (h : Hist A E n) (a : A) : M.Qnu i n h a ≤ 1 :=
  M.qval_le_one (M.aggOK_aggPol (fun n h _ => ⟨M.νa_nonneg i n h, (M.νa_sum i n h).le⟩)) (M.νe_mem i) hn h a

theorem Vbar_nonneg (n : ℕ) (h : Hist A E n) : 0 ≤ M.Vbar n h :=
  M.val_nonneg (M.aggOK_aggPol M.isSubPolicy_pibar) M.xie_mem_stdSimplex n h
theorem Qbar_nonneg (n : ℕ) (h : Hist A E n) (a : A) : 0 ≤ M.Qbar n h a :=
  M.qval_nonneg (M.aggOK_aggPol M.isSubPolicy_pibar) M.xie_mem_stdSimplex n h a
theorem Qbar_le_one {n : ℕ} (hn : n < M.T) (h : Hist A E n) (a : A) : M.Qbar n h a ≤ 1 :=
  M.qval_le_one (M.aggOK_aggPol M.isSubPolicy_pibar) M.xie_mem_stdSimplex hn h a

/-- `V^π_ξ ≤ V^*_ξ` everywhere. -/
theorem Vpi_le_Vstar (hπ : M.IsPolicy π) (n : ℕ) (h : Hist A E n) : M.Vpi π n h ≤ M.Vstar n h :=
  M.val_aggPol_le_val_aggMax M.xie_mem_stdSimplex hπ.isSubPolicy n h
theorem Qpi_le_Qstar (hπ : M.IsPolicy π) (n : ℕ) (h : Hist A E n) (a : A) :
    M.Qpi π n h a ≤ M.Qstar n h a :=
  M.qval_aggPol_le_qval_aggMax M.xie_mem_stdSimplex hπ.isSubPolicy n h a
theorem Vxi_le_Vstar (hπ : M.IsPolicy π) (n : ℕ) (h : Hist A E n) : M.Vxi π n h ≤ M.Vstar n h :=
  M.val_aggPol_le_val_aggMax M.xie_mem_stdSimplex (M.isPolicy_xia hπ).isSubPolicy n h
theorem Qxi_le_Qstar (hπ : M.IsPolicy π) (n : ℕ) (h : Hist A E n) (a : A) :
    M.Qxi π n h a ≤ M.Qstar n h a :=
  M.qval_aggPol_le_qval_aggMax M.xie_mem_stdSimplex (M.isPolicy_xia hπ).isSubPolicy n h a

/-- **Lemma A′, comparison half**: `Q^{π̄}_ξ(h,a) ≤ Q^*_ξ(h,a)` (the non-self mixture, viewed as a policy
against the percept kernel `ξ(e|·)`, is dominated by the optimum).
Source: [[sequential-self-game]] §1 (Lemma A′)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Qbar_le_Qstar (n : ℕ) (h : Hist A E n) (a : A) : M.Qbar n h a ≤ M.Qstar n h a :=
  M.qval_aggPol_le_qval_aggMax M.xie_mem_stdSimplex M.isSubPolicy_pibar n h a
theorem Vbar_le_Vstar (n : ℕ) (h : Hist A E n) : M.Vbar n h ≤ M.Vstar n h :=
  M.val_aggPol_le_val_aggMax M.xie_mem_stdSimplex M.isSubPolicy_pibar n h
theorem Qbar_le_Vstar {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (a : A) :
    M.Qbar n h a ≤ M.Vstar n h :=
  le_trans (M.Qbar_le_Qstar n h a) (M.Qstar_le_Vstar hnt a)

theorem Qxi_le_Mx (n : ℕ) (h : Hist A E n) (a : A) : M.Qxi π n h a ≤ M.Mx π n h :=
  le_sup' _ (mem_univ a)

theorem exists_Qxi_eq_Mx (n : ℕ) (h : Hist A E n) : ∃ a, M.Qxi π n h a = M.Mx π n h := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' (univ_nonempty (α := A)) (M.Qxi π n h)
  exact ⟨a, ha.symm⟩

theorem Mx_le_iff {n : ℕ} {h : Hist A E n} {c : ℝ} : M.Mx π n h ≤ c ↔ ∀ a, M.Qxi π n h a ≤ c := by
  unfold Mx
  rw [Finset.sup'_le_iff]
  simp

theorem Mx_nonneg (hπ : M.IsPolicy π) (n : ℕ) (h : Hist A E n) : 0 ≤ M.Mx π n h :=
  le_trans (M.Qxi_nonneg hπ n h (Classical.arbitrary A)) (M.Qxi_le_Mx n h _)

theorem Mx_le_Vstar (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.Mx π n h ≤ M.Vstar n h :=
  M.Mx_le_iff.2 fun a => le_trans (M.Qxi_le_Qstar hπ n h a) (M.Qstar_le_Vstar hnt a)

theorem gap_nonneg (hπ : M.IsPolicy π) (n : ℕ) (h : Hist A E n) : 0 ≤ M.gap π n h :=
  sub_nonneg.2 (M.Vpi_le_Vstar hπ n h)

theorem gap_le_one (hπ : M.IsPolicy π) (n : ℕ) (h : Hist A E n) : M.gap π n h ≤ 1 := by
  unfold gap
  linarith [M.Vstar_le_one n h, M.Vpi_nonneg hπ n h]

theorem mem_argmaxSet {n : ℕ} {h : Hist A E n} {a : A} :
    a ∈ M.argmaxSet π n h ↔ M.Qxi π n h a = M.Mx π n h := by
  simp [argmaxSet]

theorem mem_supp {n : ℕ} {h : Hist A E n} {a : A} : a ∈ supp π n h ↔ 0 < π n h a := by
  simp [supp]

/-- `∑_{a ∈ supp} π(a|h) = 1` and `V^π(h) = ∑_{a ∈ supp} π(a|h) Q^π(h,a)` at a decision node. -/
theorem sum_supp_eq_one (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    ∑ a ∈ supp π n h, π n h a = 1 := by
  rw [← hπ.sum hnt]
  apply sum_subset (subset_univ _)
  intro a _ ha
  rw [mem_supp] at ha
  exact le_antisymm (not_lt.1 ha) (hπ.nonneg hnt a)

theorem Vpi_eq_sum_supp (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.Vpi π n h = ∑ a ∈ supp π n h, π n h a * M.Qpi π n h a := by
  rw [M.Vpi_eq hnt]
  symm
  apply sum_subset (subset_univ _)
  intro a _ ha
  rw [mem_supp] at ha
  rw [le_antisymm (not_lt.1 ha) (hπ.nonneg hnt a), zero_mul]

end Named


/-! ### The mixture identities: Lemma A unnormalised, at every node -/

section Mixture
variable [Nonempty A]

/-- One step of the mixture identity: if `ξ V_ξ = (1-δ) ξ_S V^π + ∑_i w_i ν_i V^{ν_i}` holds at the
children `hae`, then `ξ(ha) Q_ξ(h,a) = (1-δ) ξ_S(h) π(a|h) Q^π(h,a) + ∑_i w_i ν_i(h) ν_i(a|h) Q^{ν_i}(h,a)`.
Source: [[sequential-self-game]] §1 (Lemma A, unnormalised)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem xiA_mul_Qxi_of_children {n : ℕ} (h : Hist A E n) (a : A)
    (ih : ∀ e, M.xi π (n + 1) (ext h a e) * M.Vxi π (n + 1) (ext h a e) =
      (1 - M.δ) * M.xiS π (n + 1) (ext h a e) * M.Vpi π (n + 1) (ext h a e) +
        ∑ i, M.w i * M.nuJoint i (n + 1) (ext h a e) * M.Vnu i (n + 1) (ext h a e)) :
    M.xiA π n h a * M.Qxi π n h a =
      (1 - M.δ) * M.xiS π n h * π n h a * M.Qpi π n h a +
        ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a := by
  have key : ∀ e, M.xiA π n h a * (M.xie n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vxi π (n + 1) (ext h a e))) =
      (1 - M.δ) * M.xiS π n h * π n h a *
          (M.xie n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vpi π (n + 1) (ext h a e))) +
        ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a *
          (M.νe i n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vnu i (n + 1) (ext h a e))) := by
    intro e
    have h1 : M.xiA π n h a * M.xie n h a e = M.xi π (n + 1) (ext h a e) := by rw [xi_ext]; ring
    have hxi : M.xi π (n + 1) (ext h a e) =
        (1 - M.δ) * (M.xiS π n h * π n h a * M.xie n h a e) +
          ∑ i, M.w i * (M.nuJoint i n h * M.νa i n h a * M.νe i n h a e) := by
      simp [xi, xins, xiS_ext, nuJoint_ext]
    have hxiS : M.xiS π (n + 1) (ext h a e) = M.xiS π n h * π n h a * M.xie n h a e := xiS_ext M π h a e
    have hnu : ∀ i, M.nuJoint i (n + 1) (ext h a e) = M.nuJoint i n h * M.νa i n h a * M.νe i n h a e :=
      fun i => nuJoint_ext M i h a e
    have hR : ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a *
          (M.νe i n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vnu i (n + 1) (ext h a e))) =
        (∑ i, M.w i * (M.nuJoint i n h * M.νa i n h a * M.νe i n h a e)) * (M.γ ^ n * M.r n (ext h a e)) +
          ∑ i, M.w i * M.nuJoint i (n + 1) (ext h a e) * M.Vnu i (n + 1) (ext h a e) := by
      rw [sum_mul, ← sum_add_distrib]
      exact sum_congr rfl fun i _ => by rw [hnu i]; ring
    calc M.xiA π n h a * (M.xie n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vxi π (n + 1) (ext h a e)))
        = (M.xiA π n h a * M.xie n h a e) * (M.γ ^ n * M.r n (ext h a e)) +
            (M.xiA π n h a * M.xie n h a e) * M.Vxi π (n + 1) (ext h a e) := by ring
      _ = M.xi π (n + 1) (ext h a e) * (M.γ ^ n * M.r n (ext h a e)) +
            ((1 - M.δ) * M.xiS π (n + 1) (ext h a e) * M.Vpi π (n + 1) (ext h a e) +
              ∑ i, M.w i * M.nuJoint i (n + 1) (ext h a e) * M.Vnu i (n + 1) (ext h a e)) := by
          rw [h1, ih e]
      _ = _ := by rw [hR, hxi, hxiS]; ring
  rw [Qxi_eq_sum, Qpi_eq_sum]
  simp_rw [Qnu_eq_sum]
  rw [mul_sum, mul_sum]
  simp_rw [key]
  rw [sum_add_distrib]
  congr 1
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]

/-- **The mixture identity** at every history: `ξ(h) V_ξ(h) = (1-δ) ξ_S(h) V^π(h) + ∑_i w_i ν_i(h) V^{ν_i}(h)`
(the EDT value is the posterior-weighted average of the hypotheses' own values; both sides vanish
where `ξ(h) = 0`).
Source: [[sequential-self-game]] §1 (Lemma A)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem xi_mul_Vxi (hπ : M.IsPolicy π) : ∀ n h, M.xi π n h * M.Vxi π n h =
    (1 - M.δ) * M.xiS π n h * M.Vpi π n h + ∑ i, M.w i * M.nuJoint i n h * M.Vnu i n h := by
  refine M.depth_induction (fun n h => M.xi π n h * M.Vxi π n h =
    (1 - M.δ) * M.xiS π n h * M.Vpi π n h + ∑ i, M.w i * M.nuJoint i n h * M.Vnu i n h) ?_ ?_
  · intro n h hnt
    rw [M.Vxi_of_not_nonterminal hnt, M.Vpi_of_not_nonterminal hnt]
    simp only [mul_zero, zero_add]
    exact (sum_eq_zero fun i _ => by rw [M.Vnu_of_not_nonterminal i hnt, mul_zero]).symm
  · intro n h hnt ih
    have hQ : ∀ a, M.xiA π n h a * M.Qxi π n h a =
        (1 - M.δ) * M.xiS π n h * π n h a * M.Qpi π n h a +
          ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a :=
      fun a => M.xiA_mul_Qxi_of_children h a (fun e => ih a e)
    by_cases hx : M.xi π n h = 0
    · rw [hx, zero_mul, M.xiS_eq_zero_of_xi_eq_zero hπ hnt hx]
      have h0 := (M.xins_eq_zero_iff n h).1 (M.xins_eq_zero_of_xi_eq_zero hπ hnt hx)
      simp only [mul_zero, zero_mul, zero_add]
      exact (sum_eq_zero fun i _ => by rw [h0 i, zero_mul]).symm
    · rw [M.Vxi_eq hnt, mul_sum]
      have hxa : ∀ a, M.xi π n h * (M.xia π n h a * M.Qxi π n h a) = M.xiA π n h a * M.Qxi π n h a := by
        intro a
        unfold xia
        rw [if_neg hx]
        field_simp
      simp_rw [hxa, hQ]
      rw [sum_add_distrib]
      congr 1
      · rw [M.Vpi_eq hnt, mul_sum]
        exact sum_congr rfl fun a _ => by ring
      · rw [sum_comm]
        refine sum_congr rfl fun i _ => ?_
        rw [M.Vnu_eq i hnt, mul_sum]
        exact sum_congr rfl fun a _ => by ring

/-- **Lemma A, unnormalised** (every `(h,a)`, no positivity needed):
`ξ(ha) Q_ξ(h,a) = (1-δ) ξ_S(h) π(a|h) Q^π(h,a) + ∑_i w_i ν_i(h) ν_i(a|h) Q^{ν_i}(h,a)`.
Source: [[sequential-self-game]] §1 (Lemma A)
Kind: P
Fidelity: stronger: holds at every `(h,a)`, the normalised forms need `ξ(ha) > 0`
Hyps: (a) -/
theorem xiA_mul_Qxi (hπ : M.IsPolicy π) (n : ℕ) (h : Hist A E n) (a : A) :
    M.xiA π n h a * M.Qxi π n h a =
      (1 - M.δ) * M.xiS π n h * π n h a * M.Qpi π n h a +
        ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a :=
  M.xiA_mul_Qxi_of_children h a fun e => M.xi_mul_Vxi hπ _ _

/-- One step of Lemma A′: if `ξ_{-S} V^{π̄} = ∑_i w_i ν_i V^{ν_i}` holds at the children, then
`ξ_{-S}(ha) Q^{π̄}(h,a) = ∑_i w_i ν_i(h) ν_i(a|h) Q^{ν_i}(h,a)`.
Source: [[sequential-self-game]] §1 (Lemma A′)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem xinsA_mul_Qbar_of_children {n : ℕ} (h : Hist A E n) (a : A)
    (ih : ∀ e, M.xins (n + 1) (ext h a e) * M.Vbar (n + 1) (ext h a e) =
      ∑ i, M.w i * M.nuJoint i (n + 1) (ext h a e) * M.Vnu i (n + 1) (ext h a e)) :
    M.xinsA n h a * M.Qbar n h a = ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a := by
  have key : ∀ e, M.xinsA n h a * (M.xie n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vbar (n + 1) (ext h a e))) =
      ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a *
        (M.νe i n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vnu i (n + 1) (ext h a e))) := by
    intro e
    have h1 : M.xinsA n h a * M.xie n h a e = M.xins (n + 1) (ext h a e) := (xins_ext M n h a e).symm
    have hnu : ∀ i, M.nuJoint i (n + 1) (ext h a e) = M.nuJoint i n h * M.νa i n h a * M.νe i n h a e :=
      fun i => nuJoint_ext M i h a e
    calc M.xinsA n h a * (M.xie n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vbar (n + 1) (ext h a e)))
        = (M.xinsA n h a * M.xie n h a e) * (M.γ ^ n * M.r n (ext h a e)) +
            (M.xinsA n h a * M.xie n h a e) * M.Vbar (n + 1) (ext h a e) := by ring
      _ = (∑ i, M.w i * M.nuJoint i (n + 1) (ext h a e)) * (M.γ ^ n * M.r n (ext h a e)) +
            ∑ i, M.w i * M.nuJoint i (n + 1) (ext h a e) * M.Vnu i (n + 1) (ext h a e) := by
          rw [h1, ih e]; rfl
      _ = _ := by
          rw [sum_mul, ← sum_add_distrib]
          exact sum_congr rfl fun i _ => by rw [hnu i]; ring
  rw [Qbar_eq_sum]
  simp_rw [Qnu_eq_sum]
  rw [mul_sum]
  simp_rw [key]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]

/-- **Lemma A′, identity half**: `ξ_{-S}(h) V^{π̄}_ξ(h) = ∑_i w_i ν_i(h) V^{ν_i}(h)` at every history — the
non-self mixture's own expected return is the value of the policy `π̄` against the percept kernel
`ξ(e|·)` (uses only F1: wherever `ξ_{-S} > 0` the residual's percept conditionals are `ξ`'s).
Source: [[sequential-self-game]] §1 (Lemma A′)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem xins_mul_Vbar : ∀ n h, M.xins n h * M.Vbar n h = ∑ i, M.w i * M.nuJoint i n h * M.Vnu i n h := by
  refine M.depth_induction (fun n h => M.xins n h * M.Vbar n h =
    ∑ i, M.w i * M.nuJoint i n h * M.Vnu i n h) ?_ ?_
  · intro n h hnt
    rw [M.Vbar_of_not_nonterminal hnt, mul_zero]
    exact (sum_eq_zero fun i _ => by rw [M.Vnu_of_not_nonterminal i hnt, mul_zero]).symm
  · intro n h hnt ih
    have hQ : ∀ a, M.xinsA n h a * M.Qbar n h a =
        ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a :=
      fun a => M.xinsA_mul_Qbar_of_children h a (fun e => ih a e)
    by_cases hx : M.xins n h = 0
    · rw [hx, zero_mul]
      have h0 := (M.xins_eq_zero_iff n h).1 hx
      exact (sum_eq_zero fun i _ => by rw [h0 i, zero_mul]).symm
    · rw [M.Vbar_eq hnt, mul_sum]
      have hxa : ∀ a, M.xins n h * (M.pibar n h a * M.Qbar n h a) = M.xinsA n h a * M.Qbar n h a := by
        intro a
        unfold pibar
        field_simp
      simp_rw [hxa, hQ]
      rw [sum_comm]
      refine sum_congr rfl fun i _ => ?_
      rw [M.Vnu_eq i hnt, mul_sum]
      exact sum_congr rfl fun a _ => by ring

/-- `ξ_{-S}(ha) Q^{π̄}(h,a) = ∑_i w_i ν_i(h) ν_i(a|h) Q^{ν_i}(h,a)` at every `(h,a)`. -/
theorem xinsA_mul_Qbar (n : ℕ) (h : Hist A E n) (a : A) :
    M.xinsA n h a * M.Qbar n h a = ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a :=
  M.xinsA_mul_Qbar_of_children h a fun e => M.xins_mul_Vbar _ _

theorem sum_nu_Qnu_nonneg (n : ℕ) (h : Hist A E n) (a : A) :
    0 ≤ ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a :=
  sum_nonneg fun i _ => mul_nonneg (mul_nonneg (mul_nonneg (M.w_nonneg i) (M.nuJoint_nonneg i n h))
    (M.νa_nonneg _ _ _ _)) (M.Qnu_nonneg i n h a)

theorem sum_nu_Qnu_le_xinsA {n : ℕ} (hn : n < M.T) (h : Hist A E n) (a : A) :
    ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a ≤ M.xinsA n h a := by
  unfold xinsA
  refine sum_le_sum fun i _ => ?_
  have h0 : 0 ≤ M.w i * M.nuJoint i n h * M.νa i n h a :=
    mul_nonneg (mul_nonneg (M.w_nonneg i) (M.nuJoint_nonneg i n h)) (M.νa_nonneg _ _ _ _)
  calc M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a
      ≤ M.w i * M.nuJoint i n h * M.νa i n h a * 1 := mul_le_mul_of_nonneg_left (M.Qnu_le_one i hn h a) h0
    _ = _ := mul_one _

/-- **Lemma A′, unnormalised**: `∑_i w_i ν_i(h) ν_i(a|h) Q^{ν_i}(h,a) ≤ ξ_{-S}(ha) V^*_ξ(h)` at every
decision node (the form Theorem B's refinement uses; no positivity needed).
Source: [[sequential-self-game]] §1 (Lemma A′), §3 (refinement)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem sum_nu_Qnu_le_xinsA_mul_Vstar {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (a : A) :
    ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a ≤ M.xinsA n h a * M.Vstar n h := by
  rw [← M.xinsA_mul_Qbar]
  exact mul_le_mul_of_nonneg_left (M.Qbar_le_Vstar hnt a) (M.xinsA_nonneg n h a)

/-- **Lemma A′**: `Q̄(h,a) = Q^{π̄}_ξ(h,a)` where `ξ_{-S}(ha) > 0` (and hence `≤ Q^*_ξ(h,a) ≤ V^*_ξ(h)` by
`Qbar_le_Qstar`, `Qbar_le_Vstar`). At `ξ_{-S}(ha) = 0` the left side is junk `0`.
Source: [[sequential-self-game]] §1 (Lemma A′)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Qmix_eq_Qbar {n : ℕ} {h : Hist A E n} {a : A} (hA : M.xinsA n h a ≠ 0) :
    M.Qmix n h a = M.Qbar n h a := by
  unfold Qmix
  rw [← M.xinsA_mul_Qbar]
  field_simp

theorem Qmix_le_Vstar {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (a : A) :
    M.Qmix n h a ≤ M.Vstar n h := by
  by_cases hA : M.xinsA n h a = 0
  · simp [Qmix, hA, M.Vstar_nonneg n h]
  · rw [M.Qmix_eq_Qbar hA]
    exact M.Qbar_le_Vstar hnt a

theorem Qmix_nonneg (n : ℕ) (h : Hist A E n) (a : A) : 0 ≤ M.Qmix n h a :=
  div_nonneg (M.sum_nu_Qnu_nonneg n h a) (M.xinsA_nonneg n h a)

theorem Qmix_le_one {n : ℕ} (hn : n < M.T) (h : Hist A E n) (a : A) : M.Qmix n h a ≤ 1 := by
  by_cases hA : M.xinsA n h a = 0
  · simp [Qmix, hA]
  · unfold Qmix
    rw [div_le_one (lt_of_le_of_ne (M.xinsA_nonneg n h a) (Ne.symm hA))]
    exact M.sum_nu_Qnu_le_xinsA hn h a

end Mixture

/-! ### The `ξ_{-S}`-null subtree: `Q_ξ = Q^π` (continuous extension) -/

section Null
variable [Nonempty A]

theorem xia_eq_of_xins_eq_zero {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (hx : M.xins n h = 0)
    (a : A) : M.xia π n h a = π n h a := by
  unfold xia
  split_ifs with h0
  · rfl
  · rw [xiA_eq, M.xinsA_eq_zero_of_xins_eq_zero hx, add_zero]
    have hS : M.xiS π n h ≠ 0 := by
      intro hS
      apply h0
      unfold xi
      rw [hS, hx]; ring
    unfold xi
    rw [hx, add_zero]
    have hδ : (1 - M.δ) ≠ 0 := by linarith [M.δ_lt_one]
    field_simp

theorem xins_ext_eq_zero {n : ℕ} {h : Hist A E n} (hx : M.xins n h = 0) (a : A) (e : E) :
    M.xins (n + 1) (ext h a e) = 0 := by
  rw [xins_ext, M.xinsA_eq_zero_of_xins_eq_zero hx, zero_mul]

/-- On a `ξ_{-S}`-null subtree the EDT values are the policy values (Step 0 of Theorem C: the whole
subtree has `w ≡ 1` and `Q_ξ = Q^π` under the continuous extension).
Source: [[sequential-self-game]] §4.1 (Step 0), §1 ("Zero-probability actions")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Vxi_eq_Vpi_of_xins_eq_zero : ∀ n h, M.xins n h = 0 → M.Vxi π n h = M.Vpi π n h := by
  refine M.depth_induction (fun n h => M.xins n h = 0 → M.Vxi π n h = M.Vpi π n h) ?_ ?_
  · intro n h hnt _
    rw [M.Vxi_of_not_nonterminal hnt, M.Vpi_of_not_nonterminal hnt]
  · intro n h hnt ih hx
    rw [M.Vxi_eq hnt, M.Vpi_eq hnt]
    refine sum_congr rfl fun a _ => ?_
    rw [M.xia_eq_of_xins_eq_zero hnt hx]
    congr 1
    rw [Qxi_eq_sum, Qpi_eq_sum]
    refine sum_congr rfl fun e _ => ?_
    rw [ih a e (M.xins_ext_eq_zero hx a e)]

theorem Qxi_eq_Qpi_of_xins_eq_zero {n : ℕ} {h : Hist A E n} (hx : M.xins n h = 0) (a : A) :
    M.Qxi π n h a = M.Qpi π n h a := by
  rw [Qxi_eq_sum, Qpi_eq_sum]
  refine sum_congr rfl fun e _ => ?_
  rw [M.Vxi_eq_Vpi_of_xins_eq_zero (π := π) _ _ (M.xins_ext_eq_zero hx a e)]

end Null

/-! ### F1, F2 and Lemma A in the note's and the audit's normalised forms -/

section F12
variable [Nonempty A]

/-- **F1**: percepts do not move the self-posterior, `w_{hae} = w_{ha}`, at every percept of positive
probability `ξ(e|ha) > 0` (at `ξ(e|ha) = 0` the node `hae` is `ξ`-null and the convention gives
`w_{hae} = 1`, so the identity needs this hypothesis — see the findings); when `ξ(ha) = 0` both sides are
`1` (`wS_ext_of_xiA_eq_zero`).
Source: [[audit-revised-theorem-1]] §1 (F1); [[sequential-self-game]] §1
Kind: P
Fidelity: exact (with the positive-percept hypothesis, which the note leaves implicit)
Hyps: (a) -/
theorem wS_ext_of_xie_ne_zero {n : ℕ} (h : Hist A E n) (a : A) {e : E} (he : M.xie n h a e ≠ 0) :
    M.wS π (n + 1) (ext h a e) = M.wA π n h a := by
  by_cases hA : M.xiA π n h a = 0
  · have h0 : M.xi π (n + 1) (ext h a e) = 0 := by rw [xi_ext, hA, mul_zero]
    rw [wS_of_xi_eq_zero M h0]
    simp [wA, hA]
  · have hne : M.xi π (n + 1) (ext h a e) ≠ 0 := by rw [xi_ext]; exact mul_ne_zero he hA
    rw [wS_of_xi_ne_zero M hne]
    simp only [wA, if_neg hA]
    rw [xiS_ext, xi_ext]
    field_simp

theorem wS_ext_of_xiA_eq_zero {n : ℕ} (h : Hist A E n) (a : A) (e : E) (hA : M.xiA π n h a = 0) :
    M.wS π (n + 1) (ext h a e) = 1 ∧ M.wA π n h a = 1 := by
  have h0 : M.xi π (n + 1) (ext h a e) = 0 := by rw [xi_ext, hA, mul_zero]
  exact ⟨wS_of_xi_eq_zero M h0, by simp [wA, hA]⟩

theorem odds_ext_of_xie_ne_zero {n : ℕ} (h : Hist A E n) (a : A) {e : E} (he : M.xie n h a e ≠ 0) :
    M.odds π (n + 1) (ext h a e) = M.oddsA π n h a := by
  unfold odds oddsA
  rw [M.wS_ext_of_xie_ne_zero h a he]

theorem wA_of_xiA_ne_zero {n : ℕ} {h : Hist A E n} {a : A} (hA : M.xiA π n h a ≠ 0) :
    M.wA π n h a = (1 - M.δ) * M.xiS π n h * π n h a / M.xiA π n h a := by
  simp [wA, hA]

theorem one_sub_wA {n : ℕ} {h : Hist A E n} {a : A} (hA : M.xiA π n h a ≠ 0) :
    1 - M.wA π n h a = M.xinsA n h a / M.xiA π n h a := by
  rw [M.wA_of_xiA_ne_zero hA]
  have := M.xiA_eq (π := π) n h a
  field_simp
  linarith

theorem wA_nonneg (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (a : A) :
    0 ≤ M.wA π n h a := by
  unfold wA
  split_ifs
  · exact zero_le_one
  · exact div_nonneg (mul_nonneg (mul_nonneg (by linarith [M.δ_lt_one]) (M.xiS_nonneg hπ n h hnt))
      (hπ.nonneg hnt a)) (M.xiA_nonneg hπ hnt a)

theorem wA_le_one (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (a : A) :
    M.wA π n h a ≤ 1 := by
  by_cases hA : M.xiA π n h a = 0
  · simp [wA, hA]
  · have := M.one_sub_wA (π := π) hA
    have hpos : 0 < M.xiA π n h a := lt_of_le_of_ne (M.xiA_nonneg hπ hnt a) (Ne.symm hA)
    linarith [div_nonneg (M.xinsA_nonneg n h a) hpos.le]

/-- **F2, product form**: at a decision node with `ξ(h) > 0`,
`ξ(a|h) = w_h π(a|h) + (1 - w_h) π̄(a|h)` (no division by `π̄`).
Source: [[sequential-self-game]] §3 ("F2 in unnormalised form"); [[audit-revised-theorem-1]] §1
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem xia_eq_wS (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hx : M.xi π n h ≠ 0) (a : A) :
    M.xia π n h a = M.wS π n h * π n h a + (1 - M.wS π n h) * M.pibar n h a := by
  unfold xia
  rw [if_neg hx, M.one_sub_wS hx, wS_of_xi_ne_zero M hx, xiA_eq]
  unfold pibar
  by_cases hs : M.xins n h = 0
  · rw [hs, M.xinsA_eq_zero_of_xins_eq_zero hs]
    simp only [add_zero, zero_div, mul_zero, div_zero]
    ring
  · field_simp

/-- `ξ_S(ha) = ξ_S(h) π(a|h)`: the self-hypothesis's mass after an action.
Source: [[sequential-self-game]] §1 (F2)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem xiS_ext_sum' (n : ℕ) (h : Hist A E n) (a : A) :
    ∑ e, M.xiS π (n + 1) (ext h a e) = M.xiS π n h * π n h a := xiS_ext_sum M n h a

/-- **F2, odds form**: `O_{ha} = O_h · π̄(a|h) / π(a|h)` (odds *against* the self; equivalently the odds
for the self are multiplied by `π(a|h)/π̄(a|h)`), for `ξ_S(h) > 0` and `π(a|h) > 0`.
Source: [[sequential-self-game]] §1 (F2); [[audit-revised-theorem-1]] §1
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem oddsA_eq (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hS : 0 < M.xiS π n h) {a : A} (ha : 0 < π n h a) :
    M.oddsA π n h a = M.odds π n h * M.pibar n h a / π n h a := by
  have hδ : (0:ℝ) < 1 - M.δ := by linarith [M.δ_lt_one]
  have hA : 0 < M.xiA π n h a := by
    rw [xiA_eq]
    have := M.xinsA_nonneg n h a
    positivity
  have hx : 0 < M.xi π n h := M.xi_pos_of_xiS_pos hS
  unfold oddsA odds pibar
  rw [M.one_sub_wA hA.ne', M.wA_of_xiA_ne_zero hA.ne', M.one_sub_wS hx.ne', wS_of_xi_ne_zero M hx.ne']
  by_cases hs : M.xins n h = 0
  · rw [hs, M.xinsA_eq_zero_of_xins_eq_zero hs]
    simp
  · field_simp

/-- At a node where the agent plays `a` surely, the odds against the self after `a` are the odds before
times `π̄(a|h) ≤ 1`: a sure action never lowers self-trust.
Source: [[sequential-self-game]] §1 (F2 consequence), §4.4
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem oddsA_eq_of_eq_one (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hS : 0 < M.xiS π n h) {a : A} (ha : π n h a = 1) :
    M.oddsA π n h a = M.odds π n h * M.pibar n h a := by
  rw [M.oddsA_eq hπ hnt hS (by rw [ha]; exact one_pos), ha, div_one]

theorem oddsA_le_odds_of_eq_one (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hS : 0 < M.xiS π n h) {a : A} (ha : π n h a = 1) : M.oddsA π n h a ≤ M.odds π n h := by
  rw [M.oddsA_eq_of_eq_one hπ hnt hS ha]
  have h0 : 0 ≤ M.odds π n h := by
    unfold odds
    have hw := M.wS_pos_of_xiS_pos (π := π) hS
    exact div_nonneg (by linarith [M.wS_le_one hπ hnt]) hw.le
  calc M.odds π n h * M.pibar n h a ≤ M.odds π n h * 1 :=
        mul_le_mul_of_nonneg_left (M.pibar_le_one n h a) h0
    _ = M.odds π n h := mul_one _

/-- **Lemma A** (the note's form): at a decision node with `ξ(h) > 0`,
`ξ(a|h) Q_ξ(h,a) = w_h π(a|h) Q^π(h,a) + (1 - w_h) π̄(a|h) Q̄(h,a)`.
Source: [[sequential-self-game]] §1 (Lemma A)
Kind: P
Fidelity: exact (the note asks `ξ(ha) > 0`; `ξ(h) > 0` suffices because the junk values of `π̄`, `Q̄`
at `ξ_{-S}(ha) = 0` are multiplied by vanishing factors)
Hyps: (a) -/
theorem xia_mul_Qxi (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hx : M.xi π n h ≠ 0) (a : A) :
    M.xia π n h a * M.Qxi π n h a =
      M.wS π n h * π n h a * M.Qpi π n h a + (1 - M.wS π n h) * M.pibar n h a * M.Qmix n h a := by
  have hxa : M.xia π n h a * M.Qxi π n h a = (M.xiA π n h a * M.Qxi π n h a) / M.xi π n h := by
    unfold xia
    rw [if_neg hx]
    ring
  rw [hxa, M.xiA_mul_Qxi hπ, M.one_sub_wS hx, wS_of_xi_ne_zero M hx]
  unfold pibar Qmix
  by_cases hs : M.xins n h = 0
  · have h0 := (M.xins_eq_zero_iff n h).1 hs
    have hA := M.xinsA_eq_zero_of_xins_eq_zero hs a
    have hsum : ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a = 0 :=
      sum_eq_zero fun i _ => by rw [h0 i]; ring
    rw [hs, hA, hsum]
    simp only [add_zero, zero_div, mul_zero, div_zero]
    ring
  · by_cases hA : M.xinsA n h a = 0
    · have h0 := (M.xinsA_eq_zero_iff n h a).1 hA
      have hsum : ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a = 0 :=
        sum_eq_zero fun i _ => by rw [h0 i]; ring
      rw [hA, hsum]
      simp only [add_zero, zero_div, mul_zero, div_zero]
      ring
    · field_simp

/-- **Lemma A** (the audit's normalised form): where `ξ(ha) > 0`,
`Q_ξ(h,a) = w_{ha} Q^π(h,a) + (1 - w_{ha}) Q̄(h,a)` — the EDT value is the mixture's conditional
expectation of the return given `ha` (this is the `L` lemma that identifies the recursive definition of
record with the conditional expectation off the `ξ`-null set).
Source: [[audit-revised-theorem-1]] §1; [[sequential-self-game]] §1
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Qxi_eq_wA (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} {a : A} (hA : M.xiA π n h a ≠ 0) :
    M.Qxi π n h a = M.wA π n h a * M.Qpi π n h a + (1 - M.wA π n h a) * M.Qmix n h a := by
  have hq : M.Qxi π n h a = (M.xiA π n h a * M.Qxi π n h a) / M.xiA π n h a := by
    field_simp
  rw [hq, M.xiA_mul_Qxi hπ, M.one_sub_wA hA, M.wA_of_xiA_ne_zero hA]
  unfold Qmix
  by_cases hs : M.xinsA n h a = 0
  · have h0 := (M.xinsA_eq_zero_iff n h a).1 hs
    have hsum : ∑ i, M.w i * M.nuJoint i n h * M.νa i n h a * M.Qnu i n h a = 0 :=
      sum_eq_zero fun i _ => by rw [h0 i]; ring
    rw [hs, hsum]
    simp only [add_zero, zero_div, mul_zero, div_zero]
    ring
  · field_simp

/-- Lemma A, upper half: `Q_ξ(h,a) ≤ w_{ha} Q^π(h,a) + (1 - w_{ha})` (returns `≤ 1`).
Source: [[audit-revised-theorem-1]] §1
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Qxi_le_wA (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) {a : A}
    (hA : M.xiA π n h a ≠ 0) :
    M.Qxi π n h a ≤ M.wA π n h a * M.Qpi π n h a + (1 - M.wA π n h a) := by
  rw [M.Qxi_eq_wA hπ hA]
  have h1 : 0 ≤ 1 - M.wA π n h a := by linarith [M.wA_le_one hπ hnt a]
  have h2 := M.Qmix_le_one hnt.1 h a
  nlinarith

/-- Lemma A, lower half: `w_{ha} Q^π(h,a) ≤ Q_ξ(h,a)` (returns `≥ 0`).
Source: [[audit-revised-theorem-1]] §1
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem wA_mul_Qpi_le_Qxi (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) {a : A}
    (hA : M.xiA π n h a ≠ 0) : M.wA π n h a * M.Qpi π n h a ≤ M.Qxi π n h a := by
  rw [M.Qxi_eq_wA hπ hA]
  have h1 : 0 ≤ 1 - M.wA π n h a := by linarith [M.wA_le_one hπ hnt a]
  have h2 := M.Qmix_nonneg n h a
  nlinarith

end F12

end Model

end Cleanroom.Uea.UeaColeShadow
