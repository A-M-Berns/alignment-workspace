import Cleanroom.Corrigibility.CorrValueChange.Product
import Mathlib.Tactic.NormNum

/-!
# corr-value-change — the causal (Savage) version (T13, Appendix B)

Source: [[value-change-as-epistemic-update]] Appendix B. States `Ω` with an act-independent `P`;
composite acts `(k, a)`, `(c, a)` with consequence utilities `U_{(k,a)}`, `U_{(c,a)} : Ω → ℝ`; an
outcome coordinate `j(ω)` recording which `U'_j` the change would install. The values `v_K`,
`v_j`, `w_j` form a `ValueTable`, so the decomposition is the same theorem as in §1.4 (B.2 "goes
through verbatim"); the identity `∑_j p_j w_j(a) = v_K(a)` is the tower property with no
assumption (B.2); and under the uninformative-choice assumption the evidential product model
*is* the Savage model with the configuration folded into the act (B.5).
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω A J : Type} [Fintype Ω] [DecidableEq Ω] [Fintype A] [Fintype J] [DecidableEq J]

/-- **The Savage model** of Appendix B: an act-independent state distribution, the consequence
utilities of `(k, a)` and `(c, a)`, the outcome coordinate, and the model's positivity convention
`P(j(ω) = j) > 0`.
Source: [[value-change-as-epistemic-update]] B.1–B.2
Kind: D
Fidelity: exact -/
structure Savage (Ω A J : Type) [Fintype Ω] [Fintype A] [Fintype J] [DecidableEq J] where
  /-- the state distribution, which acts cannot influence -/
  P : Prob Ω
  /-- `U_{(k,a)}` -/
  Uk : A → Ω → ℝ
  /-- `U_{(c,a)}` -/
  Uc : A → Ω → ℝ
  /-- the outcome coordinate `j(ω)` -/
  out : Ω → J
  /-- every outcome has positive probability -/
  out_pos : ∀ j, 0 < P.mass (univ.filter fun ω => out ω = j)

namespace Savage

variable (Sv : Savage Ω A J)

/-- The outcome event `{j(ω) = j}`.
Source: [[value-change-as-epistemic-update]] B.2
Kind: D
Fidelity: exact -/
def outE (j : J) : Finset Ω := univ.filter fun ω => Sv.out ω = j

/-- `p_j = P(j(ω) = j)`.
Source: [[value-change-as-epistemic-update]] B.2
Kind: D
Fidelity: exact -/
def p (j : J) : ℝ := Sv.P.mass (Sv.outE j)

/-- `v_K(a) = E_P[U_{(k,a)}]`.
Source: [[value-change-as-epistemic-update]] B.2
Kind: D
Fidelity: exact -/
def vK (a : A) : ℝ := Sv.P.integral (Sv.Uk a) univ

/-- `v_j(a) = E_P[U_{(c,a)} ∣ j]`.
Source: [[value-change-as-epistemic-update]] B.2
Kind: D
Fidelity: exact -/
def v (j : J) (a : A) : ℝ := Sv.P.condExp (Sv.Uc a) (Sv.outE j)

/-- `w_j(a) = E_P[U_{(k,a)} ∣ j]`: "keep, and choose knowing `j`" — an object of the picture with no
added structure.
Source: [[value-change-as-epistemic-update]] B.2
Kind: D
Fidelity: exact -/
def w (j : J) (a : A) : ℝ := Sv.P.condExp (Sv.Uk a) (Sv.outE j)

/-- A sum over the outcome events is the whole sum (they partition the states).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_outE (g : Ω → ℝ) : ∑ j, ∑ ω ∈ Sv.outE j, g ω = ∑ ω, g ω := by
  unfold outE
  exact sum_fiberwise univ Sv.out g

/-- `∑_j p_j = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem p_sum : ∑ j, Sv.p j = 1 := by
  unfold p Prob.mass; rw [Sv.sum_outE]; exact Sv.P.sum_one

/-- The Savage model's value table.
Source: [[value-change-as-epistemic-update]] B.2
Kind: D
Fidelity: exact -/
def table : ValueTable A J where
  p := Sv.p
  p_pos := Sv.out_pos
  p_sum := Sv.p_sum
  vK := Sv.vK
  v := Sv.v

/-- **T13(b), the decomposition in the Savage model**: the same identity, from the same theorem.
Source: [[value-change-as-epistemic-update]] B.2 ("the decomposition of §1.4 into (A), (B) and (C)
goes through verbatim")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem decomposition_savage (aj ahat : J → A) (aK : A) :
    (∑ j, Sv.p j * Sv.v j (aj j)) - Sv.vK aK =
      (∑ j, Sv.p j * (Sv.v j (aj j) - Sv.v j (ahat j))) +
      (∑ j, Sv.p j * (Sv.v j (ahat j) - Sv.v j aK)) +
      (∑ j, Sv.p j * (Sv.v j aK - Sv.vK aK)) :=
  Sv.table.decomposition aj ahat aK

/-- **T13(c), the tower identity with no assumption**: `∑_j p_j w_j(a) = v_K(a)` for every act —
in the causal picture the uninformative-choice assumption is automatic, "since acts do not
condition".
Source: [[value-change-as-epistemic-update]] B.2 ("The identity `∑_j p_j w_j(a^K) = v_K(a^K)` is
the tower property, with no assumption behind it")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem tower_no_assumption (a : A) : ∑ j, Sv.p j * Sv.w j a = Sv.vK a := by
  unfold p w vK
  have h : ∀ j, Sv.P.mass (Sv.outE j) * Sv.P.condExp (Sv.Uk a) (Sv.outE j) =
      Sv.P.integral (Sv.Uk a) (Sv.outE j) := by
    intro j; rw [mul_comm]; exact Sv.P.condExp_mul_mass _ (Sv.out_pos j)
  simp_rw [h]
  unfold Prob.integral
  exact Sv.sum_outE _

/-- The information/payment split holds in the Savage model with no hypothesis.
Source: [[value-change-as-epistemic-update]] B.2 ("The refinement into (I) and (Π) needs no added
structure")
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem info_payment_split_savage (ahat atil : J → A) (aK : A) :
    (∑ j, Sv.p j * (Sv.v j (ahat j) - Sv.v j aK)) + (∑ j, Sv.p j * (Sv.v j aK - Sv.vK aK)) =
      (∑ j, Sv.p j * (Sv.w j (atil j) - Sv.w j aK)) + ∑ j, Sv.p j * (Sv.v j (ahat j) - Sv.w j (atil j)) := by
  have hw := Sv.tower_no_assumption aK
  have hT := Sv.table.ValC_sub_ValK_eq_termA_add (fun _ => aK) ahat aK
  have hD := Sv.table.decomposition (fun _ => aK) ahat aK
  simp only [ValueTable.termA, ValueTable.termB, ValueTable.termC, ValueTable.ValC,
    ValueTable.ValK, table] at hT hD
  have e : ∑ j, Sv.p j * (Sv.w j (atil j) - Sv.w j aK) + ∑ j, Sv.p j * (Sv.v j (ahat j) - Sv.w j (atil j))
      = (∑ j, Sv.p j * Sv.v j (ahat j)) - ∑ j, Sv.p j * Sv.w j aK := by
    rw [← sum_add_distrib, ← sum_sub_distrib]; refine sum_congr rfl fun j _ => ?_; ring
  rw [e, hw]; linarith

/-- **T13(e), acts do not condition** (a documented non-theorem): in the Savage model there is no
event "the agent does `a`" — an act is a function on states, not a subset of them — so the only
sense "conditioning on an act" can be given is conditioning on the sure event, and
`E[U ∣ a ∧ L] = E[U ∣ L]` for every `L`. An act that raises `P(L)` is therefore inexpressible; B.4's
alternative (a consequence-level effect) is a change of `U_{(·,a)}`, not of `P`.
Source: [[value-change-as-epistemic-update]] B.1 ("there is no event 'the agent does `a`' to
condition on"), B.4 (second difference)
Kind: T (a definitional record; the content is the *type* of `Savage`)
Fidelity: n/a -/
theorem acts_do_not_condition (U : Ω → ℝ) (L : Finset Ω) (_a : A) :
    Sv.P.condExp U (univ ∩ L) = Sv.P.condExp U L := by rw [univ_inter]

end Savage

/-! ## B.5: the evidential product model is the Savage model with the configuration in the act -/

namespace ProductModel

variable {F : Type} [Fintype F] [DecidableEq F] [DecidableEq A] [Nonempty J] (M : ProductModel F J A)

/-- **The Savage model of a product model** (B.5): states `(f, j)` — the fact and "what the change
would install" — with `P(f, j) = P(f ∧ C_j)/P(C)` (the facts and outcomes seen from the change
event), `U_{(c,a)}(f, j) = U(f, C_j, a)`, `U_{(k,a)}(f, j) = U(f, K, a)`, outcome coordinate the second
component. The EDT world must carry a fact coordinate and a configuration coordinate for the
map to be defined; the act coordinate is dropped (acts become functions).
Source: [[value-change-as-epistemic-update]] B.5 ("Define `U_{(c,a)}(f, j) := U(f, C_j, a)` and
`U_{(k,a)}(f, j) := U(f, K, a)`")
Kind: D
Fidelity: exact (with the state distribution made explicit: the `C`-conditional of `q`) -/
def toSavage : Savage (F × J) A J where
  P := {
    p := fun x => M.q x.1 (some x.2) / M.qCtot
    nonneg := fun x => div_nonneg (M.q_nonneg _ _) M.qCtot_pos.le
    sum_one := by
      rw [← sum_div, Fintype.sum_prod_type, sum_comm]
      unfold qCtot qC
      exact div_self M.qCtot_pos.ne' }
  Uk := fun a x => M.Uf x.1 none a
  Uc := fun a x => M.Uf x.1 (some x.2) a
  out := Prod.snd
  out_pos := fun j => by
    unfold Prob.mass
    have hset : (univ : Finset (F × J)).filter (fun x => x.2 = j) = univ ×ˢ {j} := by
      ext ⟨f, j'⟩; simp [eq_comm]
    rw [hset, sum_product]
    simp only [sum_singleton]
    rw [← sum_div]
    exact div_pos (M.qC_pos j) M.qCtot_pos

/-- A sum over the Savage outcome event `{j}` is the fact-sum of the slice.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem toSavage_sum_outE (g : F × J → ℝ) (j : J) :
    ∑ x ∈ M.toSavage.outE j, g x = ∑ f, g (f, j) := by
  unfold Savage.outE toSavage
  have hset : (univ : Finset (F × J)).filter (fun x => x.2 = j) = univ ×ˢ {j} := by
    ext ⟨f, j'⟩; simp [eq_comm]
  simp only
  rw [hset, sum_product]; simp

/-- **T13(d), the equivalence (B.5)**: under the uninformative-choice assumption, the Savage model
of a product model has the same `p_j`, `v_j`, `w_j` (for every `j`, `a`) and the same `v_K` as the
evidential two-step model — hence the same `Val(K)`, `Val(C)`, and every term of the
decomposition. The uninformative-choice assumption is used exactly once: for `v_K` (the keep
side's fact distribution must be the change side's marginal).
Source: [[value-change-as-epistemic-update]] B.5 ("the evidential model *is* the causal one with the
configuration folded into the act")
Kind: P
Fidelity: exact
Hyps: (a) `h : Uninformative` (for `v_K` only; `p`, `v`, `w` agree unconditionally; load-bearing
there: `savage_needs_uninformative`) -/
theorem edt_eq_savage (h : M.Uninformative) :
    (∀ j, M.toSavage.p j = M.toTwoStep.p j) ∧
    (∀ j a, M.toSavage.v j a = M.toTwoStep.v M.U j a) ∧
    (∀ j a, M.toSavage.w j a = M.w j a) ∧
    (∀ a, M.toSavage.vK a = M.toTwoStep.vK M.U a) := by
  have hC := M.qCtot_pos
  have hmass : ∀ j, M.toSavage.P.mass (M.toSavage.outE j) = M.qC j / M.qCtot := by
    intro j; unfold Prob.mass; rw [M.toSavage_sum_outE]
    unfold toSavage qC; simp only; rw [sum_div]
  refine ⟨fun j => ?_, fun j a => ?_, fun j a => ?_, fun a => ?_⟩
  · rw [Savage.p, hmass, M.toTwoStep_p]
  · rw [Savage.v, Prob.condExp, hmass, Prob.integral, M.toSavage_sum_outE, M.toTwoStep_v]
    unfold vf toSavage qC
    simp only
    simp_rw [div_mul_eq_mul_div]
    rw [← sum_div, div_div_div_cancel_right₀ hC.ne']
  · rw [Savage.w, Prob.condExp, hmass, Prob.integral, M.toSavage_sum_outE]
    unfold w toSavage qC
    simp only
    simp_rw [div_mul_eq_mul_div]
    rw [← sum_div, div_div_div_cancel_right₀ hC.ne']
  · rw [Savage.vK, Prob.integral, M.toTwoStep_vK]
    unfold toSavage vKf
    simp only
    rw [Fintype.sum_prod_type]
    have hK : 0 < M.qK := M.qK_pos
    simp_rw [div_mul_eq_mul_div, ← sum_div]
    rw [div_eq_div_iff hC.ne' hK.ne']
    unfold qK
    rw [sum_mul, sum_mul]
    refine sum_congr rfl fun f _ => ?_
    rw [← sum_mul]
    have hf := h f
    unfold qK at hf
    calc (∑ j, M.q f (some j)) * M.Uf f none a * ∑ f, M.q f none
        = ((∑ j, M.q f (some j)) * ∑ f, M.q f none) * M.Uf f none a := by ring
      _ = (M.q f none * M.qCtot) * M.Uf f none a := by rw [hf]
      _ = M.q f none * M.Uf f none a * M.qCtot := by ring

end ProductModel


/-! ## The uninformative-choice assumption is load-bearing for `v_K` (F15's "exactly when") -/

/-- A product model with an *informative* step-1 choice: one fact bit, one outcome, one act; the
keep configuration carries `f = true` (mass `1/2`), the change configuration `f = false` (mass
`1/2`); `U(f, K, ·) = [f = true]`, `U(f, C, ·) = 0`.
Source: [[value-change-as-epistemic-update]] B.5; findings F15; audit r4 adversarial N2 (probe
`SavageNeedsUninformative.lean`)
Kind: D
Fidelity: n/a -/
def infoPM : ProductModel Bool Unit Unit where
  q := fun f c => match c with
    | none => if f then 1 / 2 else 0
    | some _ => if f then 0 else 1 / 2
  q_nonneg := fun f c => by cases c <;> cases f <;> simp
  q_sum := by simp [Fintype.sum_bool, Fintype.sum_option, Fintype.sum_unique]; norm_num
  σ := fun _ => 1
  σ_pos := fun _ => by norm_num
  σ_sum := by simp
  Uf := fun f c _ => match c with
    | none => if f then 1 else 0
    | some _ => 0
  qK_pos := by simp [Fintype.sum_bool]
  qC_pos := fun _ => by simp [Fintype.sum_bool]

/-- `infoPM` violates the uninformative-choice assumption (`0 · ½ ≠ ½ · ½` at `f = true`).
Source: findings F15
Kind: L
Fidelity: exact -/
theorem infoPM_not_uninformative : ¬ infoPM.Uninformative := by
  intro h
  have := h true
  simp [infoPM, ProductModel.qK, ProductModel.qCtot, ProductModel.qC, Fintype.sum_bool,
    Fintype.sum_unique] at this

/-- The evidential `v_K` of `infoPM` is `1` (the keep worlds all have `f = true`).
Source: findings F15
Kind: L
Fidelity: exact -/
theorem infoPM_vK_edt : infoPM.toTwoStep.vK infoPM.U () = 1 := by
  rw [ProductModel.toTwoStep_vK]
  simp [ProductModel.vKf, infoPM, ProductModel.qK, Fintype.sum_bool]

/-- The Savage `v_K` of `infoPM` is `0` (the Savage state law is the `C`-conditional of `q`, under
which `f = true` has probability zero).
Source: findings F15
Kind: L
Fidelity: exact -/
theorem infoPM_vK_savage : infoPM.toSavage.vK () = 0 := by
  simp [Savage.vK, ProductModel.toSavage, Prob.integral, infoPM, Fintype.sum_prod_type,
    Fintype.sum_bool, Fintype.sum_unique]

/-- **The uninformative-choice hypothesis of `edt_eq_savage` is load-bearing**: for `infoPM` it
fails and the two `v_K` differ (`0 ≠ 1`). With `edt_eq_savage` this is F15's "exactly when".
Source: [[value-change-as-epistemic-update]] B.5; findings F15; audit r4 adversarial N2
Kind: N+ (the only-if side of F15)
Fidelity: exact -/
theorem savage_needs_uninformative :
    ¬ infoPM.Uninformative ∧ infoPM.toSavage.vK () ≠ infoPM.toTwoStep.vK infoPM.U () := by
  refine ⟨infoPM_not_uninformative, ?_⟩
  rw [infoPM_vK_savage, infoPM_vK_edt]; norm_num

end

end Cleanroom.Corrigibility.CorrValueChange
