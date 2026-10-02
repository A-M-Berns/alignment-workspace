import Cleanroom.Found.FixKakutani
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.Fin.VecNotation

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.TaylorOlah`: the fixed-point objective of Taylor–Olah

Target 18 (corr-refs-020): "maximise `U(C)` ignoring the effect through `B`". Finite `A B C`,
stochastic kernels `PB : A → B → ℝ` and `PC : A → B → C → ℝ`, a utility `U : C → ℝ`, and the objective
`v d d' = ∑ a a' b c, d a * d' a' * PB a b * PC a' b c * U c` (the action `A ~ d` sets `B`; the action
`A' ~ d'` sets `C` given `B`). `d` is **optimal** iff `d ∈ Δ(A)` and `d ∈ argmax_{d' ∈ Δ(A)} v d d'`.

Headline 1 (`exists_toOptimal`): an optimal `d` exists — `kakutani_findim` on `Δ(A)` for the argmax
correspondence `d ↦ argmax_{d'} v d d'` (nonempty by compactness, convex because `v d ·` is linear,
closed graph because `v` is jointly continuous; all three proved here). Headline 2
(`toOptimal_ex_iff`): the note's four-action shutdown example has **no pure optimum, and its unique
optimum is `![1/2, 0, 1/2, 0]`** — the note says only "a mixture of 1 and 3"; uniqueness and the
weight `1/2` are `stronger`.
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set Cleanroom.Found.FixKakutani

section General

variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

/-- **The Taylor–Olah objective** `v_d(d') = E_{A∼d, A'∼d', B∼PB(A), C∼PC(A',B)} U(C)`, as a finite sum.
Source: [[taylor-2016-maximizing-a-quantity-while-ignoring-effect-through-some-channel]] ll. 21–27
(the display defining `v_d(d')`); [[corr-refs-inventory]] 020
Kind: D
Fidelity: exact (finite `A`, `B`, `C`; kernels as row-stochastic matrices)
Hyps: n/a -/
def toValue (PB : A → B → ℝ) (PC : A → B → C → ℝ) (U : C → ℝ) (d d' : A → ℝ) : ℝ :=
  ∑ a, ∑ a', ∑ b, ∑ c, d a * d' a' * PB a b * PC a' b c * U c

/-- **Optimality**: `d ∈ Δ(A)` and `v d d' ≤ v d d` for every `d' ∈ Δ(A)` (`d ∈ argmax_{d'} v_d(d')`).
Source: [[taylor-2016-maximizing-a-quantity-while-ignoring-effect-through-some-channel]] l. 29 ("A
distribution `d` over actions is optimal iff `d ∈ argmax_{d'} v_d(d')`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsTOOptimal (PB : A → B → ℝ) (PC : A → B → C → ℝ) (U : C → ℝ) (d : A → ℝ) : Prop :=
  d ∈ stdSimplex ℝ A ∧ ∀ d' ∈ stdSimplex ℝ A, toValue PB PC U d d' ≤ toValue PB PC U d d

/-- `v d ·` is linear (affine combinations pass through).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem toValue_combo (PB : A → B → ℝ) (PC : A → B → C → ℝ) (U : C → ℝ) (d d₁ d₂ : A → ℝ)
    (α β : ℝ) :
    toValue PB PC U d (α • d₁ + β • d₂) = α * toValue PB PC U d d₁ + β * toValue PB PC U d d₂ := by
  unfold toValue
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ =>
    Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- `v` is jointly continuous in `(d, d')` (a polynomial).
Source: [[taylor-2016-maximizing-a-quantity-while-ignoring-effect-through-some-channel]] l. 33
("has a closed graph")
Kind: L
Fidelity: n/a
Hyps: none -/
theorem continuous_toValue (PB : A → B → ℝ) (PC : A → B → C → ℝ) (U : C → ℝ) :
    Continuous fun p : (A → ℝ) × (A → ℝ) => toValue PB PC U p.1 p.2 := by
  unfold toValue
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun a' _ =>
    continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun c _ => ?_
  fun_prop

/-- **The argmax correspondence** `d ↦ {d' ∈ Δ(A) | ∀ d'' ∈ Δ(A), v d d'' ≤ v d d'}`.
Source: [[taylor-2016-maximizing-a-quantity-while-ignoring-effect-through-some-channel]] l. 33
("the function mapping the distribution `d` to the set `argmax_{d'} v_d(d')`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def argmaxCorr (PB : A → B → ℝ) (PC : A → B → C → ℝ) (U : C → ℝ) (d : A → ℝ) : Set (A → ℝ) :=
  {d' | d' ∈ stdSimplex ℝ A ∧ ∀ d'' ∈ stdSimplex ℝ A, toValue PB PC U d d'' ≤ toValue PB PC U d d'}

/-- The argmax is nonempty on `Δ(A)` (compactness, continuity).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem argmaxCorr_nonempty [Nonempty A] (PB : A → B → ℝ) (PC : A → B → C → ℝ) (U : C → ℝ)
    (d : A → ℝ) : (argmaxCorr PB PC U d).Nonempty := by
  classical
  have hc : ContinuousOn (fun d' => toValue PB PC U d d') (stdSimplex ℝ A) :=
    ((continuous_toValue PB PC U).comp (continuous_const.prodMk continuous_id)).continuousOn
  obtain ⟨d', hd', hmax⟩ := (isCompact_stdSimplex ℝ A).exists_isMaxOn
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary A)⟩ hc
  exact ⟨d', hd', fun d'' hd'' => hmax hd''⟩

/-- The argmax is convex (`v d ·` is linear).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem argmaxCorr_convex (PB : A → B → ℝ) (PC : A → B → C → ℝ) (U : C → ℝ) (d : A → ℝ) :
    Convex ℝ (argmaxCorr PB PC U d) := by
  intro d₁ ⟨h₁, hm₁⟩ d₂ ⟨h₂, hm₂⟩ α β hα hβ hαβ
  refine ⟨convex_stdSimplex ℝ A h₁ h₂ hα hβ hαβ, fun d'' hd'' => ?_⟩
  rw [toValue_combo]
  calc toValue PB PC U d d'' = α * toValue PB PC U d d'' + β * toValue PB PC U d d'' := by
        rw [← add_mul, hαβ, one_mul]
    _ ≤ α * toValue PB PC U d d₁ + β * toValue PB PC U d d₂ :=
        add_le_add (mul_le_mul_of_nonneg_left (hm₁ d'' hd'') hα)
          (mul_le_mul_of_nonneg_left (hm₂ d'' hd'') hβ)

/-- `d ↦ v d d''` is continuous for fixed `d''`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem continuous_toValue_left (PB : A → B → ℝ) (PC : A → B → C → ℝ) (U : C → ℝ) (d'' : A → ℝ) :
    Continuous fun d => toValue PB PC U d d'' := by
  unfold toValue
  refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun a' _ =>
    continuous_finsetSum _ fun b _ => continuous_finsetSum _ fun c _ => ?_
  fun_prop

/-- The graph of the argmax correspondence over `Δ(A)`, as an intersection of closed conditions.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem argmaxCorr_graph_eq (PB : A → B → ℝ) (PC : A → B → C → ℝ) (U : C → ℝ) :
    {q : (A → ℝ) × (A → ℝ) | q.1 ∈ stdSimplex ℝ A ∧ q.2 ∈ argmaxCorr PB PC U q.1} =
      ({q : (A → ℝ) × (A → ℝ) | q.1 ∈ stdSimplex ℝ A} ∩ {q | q.2 ∈ stdSimplex ℝ A}) ∩
      ⋂ d'' ∈ stdSimplex ℝ A,
        {q : (A → ℝ) × (A → ℝ) | toValue PB PC U q.1 d'' ≤ toValue PB PC U q.1 q.2} := by
  ext ⟨d, d'⟩
  simp only [argmaxCorr, mem_setOf_eq, mem_inter_iff, mem_iInter]
  constructor
  · rintro ⟨hd, hd', hm⟩; exact ⟨⟨hd, hd'⟩, hm⟩
  · rintro ⟨⟨hd, hd'⟩, hm⟩; exact ⟨hd, hd', hm⟩

/-- Each comparison set `{(d, d') | v d d'' ≤ v d d'}` is closed.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem isClosed_toValue_le (PB : A → B → ℝ) (PC : A → B → C → ℝ) (U : C → ℝ) (d'' : A → ℝ) :
    IsClosed {q : (A → ℝ) × (A → ℝ) | toValue PB PC U q.1 d'' ≤ toValue PB PC U q.1 q.2} :=
  isClosed_le ((continuous_toValue_left PB PC U d'').comp continuous_fst)
    (continuous_toValue PB PC U)

/-- The argmax correspondence has a closed graph over `Δ(A)` (joint continuity of `v`).
Source: [[taylor-2016-maximizing-a-quantity-while-ignoring-effect-through-some-channel]] l. 33
("has a closed graph")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem argmaxCorr_hasClosedGraphOn (PB : A → B → ℝ) (PC : A → B → C → ℝ) (U : C → ℝ) :
    HasClosedGraphOn (argmaxCorr PB PC U) (stdSimplex ℝ A) := by
  unfold HasClosedGraphOn
  have hK : IsClosed (stdSimplex ℝ A) := (isCompact_stdSimplex ℝ A).isClosed
  rw [argmaxCorr_graph_eq]
  exact ((hK.preimage continuous_fst).inter (hK.preimage continuous_snd)).inter
    (isClosed_biInter fun d'' _ => isClosed_toValue_le PB PC U d'')

/-- **Headline 1: an optimal `d` exists** — `kakutani_findim` on `Δ(A)` for `argmaxCorr` (values in
`Δ(A)`, nonempty, convex, closed graph: `argmaxCorr_nonempty`, `argmaxCorr_convex`,
`argmaxCorr_hasClosedGraphOn`).
Source: [[taylor-2016-maximizing-a-quantity-while-ignoring-effect-through-some-channel]] l. 33 ("A
solution `d` always exists by Kakutani's fixed point theorem"); [[corr-refs-inventory]] 020
Kind: C
Fidelity: stronger: no stochasticity of the kernels is needed (`v` is bilinear for any real arrays
`PB`, `PC`, so the note's "nonneg, rows sum to 1" is never used); finite action, channel and outcome
spaces
Hyps: (a) all: Kakutani is `Cleanroom.Found.FixKakutani.kakutani_findim` -/
theorem exists_toOptimal [Nonempty A] (PB : A → B → ℝ) (PC : A → B → C → ℝ) (U : C → ℝ) :
    ∃ d, IsTOOptimal PB PC U d := by
  classical
  obtain ⟨d, hd, hdF⟩ := kakutani_findim (E := A → ℝ) (isCompact_stdSimplex ℝ A)
    (convex_stdSimplex ℝ A) ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary A)⟩
    (argmaxCorr PB PC U) (fun _ _ _ h => h.1) (fun d _ => argmaxCorr_nonempty PB PC U d)
    (fun d _ => argmaxCorr_convex PB PC U d) (argmaxCorr_hasClosedGraphOn PB PC U)
  exact ⟨d, hd, hdF.2⟩

end General

/-! ### Headline 2: the four-action shutdown example -/

/-- Which actions press the shutdown button (0-based: action `1` "press then shut down" and action `2`
"produce 10 paperclips, get shut down").
Source: [[taylor-2016-maximizing-a-quantity-while-ignoring-effect-through-some-channel]] ll. 37–42
Kind: D
Fidelity: exact
Hyps: n/a -/
def pressed : Fin 4 → Bool := ![false, true, true, false]

/-- `PB a b = [b = pressed a]`: the button state is a deterministic function of the action.
Source: [[taylor-2016-maximizing-a-quantity-while-ignoring-effect-through-some-channel]] l. 44
("Define `B` to be whether the shutdown button is pressed")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def exPB (a : Fin 4) (b : Bool) : ℝ := if b = pressed a then 1 else 0

/-- `PC a' b c = [c = (a', b)]`: the outcome records the action taken and the button state.
Source: [[taylor-2016-maximizing-a-quantity-while-ignoring-effect-through-some-channel]] l. 44
("`C` to be the outcome")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def exPC (a' : Fin 4) (b : Bool) (c : Fin 4 × Bool) : ℝ := if c = (a', b) then 1 else 0

/-- The utility: not pressed → paperclips `0, 0, 10, 9`; pressed → `10, 5, 0, 0`.
Source: [[taylor-2016-maximizing-a-quantity-while-ignoring-effect-through-some-channel]] ll. 44–45
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def exU (c : Fin 4 × Bool) : ℝ :=
  if c.2 then ![10, 5, 0, 0] c.1 else ![0, 0, 10, 9] c.1

/-- The payoff of action `a'` when the button is pressed with probability `β = d 1 + d 2`:
`![10 β, 5 β, 10 (1 − β), 9 (1 − β)]`-shaped, written with `d 0 + d 3` for `1 − β`.
Source: [[taylor-2016-maximizing-a-quantity-while-ignoring-effect-through-some-channel]] ll. 46–52
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def exPay (d : Fin 4 → ℝ) (a' : Fin 4) : ℝ :=
  (d 1 + d 2) * exU (a', true) + (d 0 + d 3) * exU (a', false)

/-- Summing a deterministic kernel over the outcome.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_exPC (a' : Fin 4) (b : Bool) (g : Fin 4 × Bool → ℝ) :
    ∑ c, exPC a' b c * g c = g (a', b) := by
  simp [exPC, Finset.sum_ite_eq']

/-- Summing a deterministic kernel over the button state.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_exPB (a : Fin 4) (g : Bool → ℝ) : ∑ b, exPB a b * g b = g (pressed a) := by
  cases h : pressed a <;> simp [exPB, h]

/-- **The example's objective in closed form**: `v d d' = ∑ a', d' a' * exPay d a'`.
Source: [[taylor-2016-maximizing-a-quantity-while-ignoring-effect-through-some-channel]] ll. 46–52
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem toValue_ex (d d' : Fin 4 → ℝ) :
    toValue exPB exPC exU d d' = ∑ a', d' a' * exPay d a' := by
  unfold toValue
  have h1 : ∀ a a' : Fin 4, ∑ b, ∑ c, d a * d' a' * exPB a b * exPC a' b c * exU c =
      d a * d' a' * exU (a', pressed a) := by
    intro a a'
    have : ∀ b, ∑ c, d a * d' a' * exPB a b * exPC a' b c * exU c =
        exPB a b * (d a * d' a' * exU (a', b)) := by
      intro b
      rw [← sum_exPC a' b (fun c => d a * d' a' * exU c), Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      ring
    simp only [this]
    exact sum_exPB a fun b => d a * d' a' * exU (a', b)
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a' _ => ?_
  simp only [Fin.sum_univ_four, pressed, exPay]
  simp
  ring

/-- The vertex `e_a` of `Δ(Fin 4)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def vertex (a : Fin 4) : Fin 4 → ℝ := Pi.single a 1

/-- `v d e_a = exPay d a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem toValue_ex_vertex (d : Fin 4 → ℝ) (a : Fin 4) :
    toValue exPB exPC exU d (vertex a) = exPay d a := by
  rw [toValue_ex]
  simp [vertex, Pi.single_apply, Finset.sum_ite_eq']

/-- **Headline 2: the unique optimum of the shutdown example is `![1/2, 0, 1/2, 0]`.** With
`β = d 1 + d 2` the four action payoffs are `10β, 5β, 10(1−β), 9(1−β)`; support in the argmax forces
`β = 1/2` and kills actions `1` and `3`.
Source: [[taylor-2016-maximizing-a-quantity-while-ignoring-effect-through-some-channel]] l. 53 ("The
only optimal action distribution is a mixture of action 1 and 3"); [[corr-refs-inventory]] 020
Kind: N+
Fidelity: stronger: the note says "a mixture of 1 and 3"; here the mixture is unique with weights
`1/2, 1/2` (exact rationals)
Hyps: (a) none -/
theorem toOptimal_ex_iff (d : Fin 4 → ℝ) :
    IsTOOptimal exPB exPC exU d ↔ d = ![1 / 2, 0, 1 / 2, 0] := by
  constructor
  · rintro ⟨hd, hopt⟩
    have hnn := hd.1
    have hsum := hd.2
    simp only [Fin.sum_univ_four] at hsum
    have hv : ∀ a, exPay d a ≤ toValue exPB exPC exU d d := fun a => by
      rw [← toValue_ex_vertex]; exact hopt _ (single_mem_stdSimplex ℝ a)
    have hM : toValue exPB exPC exU d d = ∑ a, d a * exPay d a := toValue_ex d d
    -- support in the argmax
    have hsupp : ∀ a, 0 < d a → exPay d a = toValue exPB exPC exU d d := by
      intro a ha
      have hz : ∑ a', d a' * (toValue exPB exPC exU d d - exPay d a') = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hd.2, one_mul, hM, sub_self]
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun a' _ => mul_nonneg (hnn a') (by linarith [hv a']))]
        at hz
      have := hz a (Finset.mem_univ _)
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h ha.ne'
      · linarith
    have hpay : ∀ a, exPay d a = ![10 * (d 1 + d 2), 5 * (d 1 + d 2), 10 * (d 0 + d 3),
        9 * (d 0 + d 3)] a := by
      intro a; fin_cases a <;> simp [exPay, exU] <;> ring
    have h0 := hpay 0; have h1 := hpay 1; have h2 := hpay 2; have h3 := hpay 3
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.tail_cons] at h0 h1 h2 h3
    have hv0 := hv 0; have hv1 := hv 1; have hv2 := hv 2; have hv3 := hv 3
    have hn0 := hnn 0; have hn1 := hnn 1; have hn2 := hnn 2; have hn3 := hnn 3
    -- action 1 is never in the support
    have hd1 : d 1 = 0 := by
      by_contra h
      have hp := hsupp 1 (lt_of_le_of_ne hn1 (Ne.symm h))
      rcases lt_trichotomy (d 1 + d 2) (1 / 2) with hβ | hβ | hβ
      · linarith
      · linarith
      · linarith
    -- action 3 is never in the support
    have hd3 : d 3 = 0 := by
      by_contra h
      have hp := hsupp 3 (lt_of_le_of_ne hn3 (Ne.symm h))
      rcases lt_trichotomy (d 1 + d 2) (1 / 2) with hβ | hβ | hβ
      · linarith
      · linarith
      · linarith
    -- so d = (d 0, 0, d 2, 0) with d 0 + d 2 = 1, and both must be positive
    have hd0 : d 0 = 1 / 2 := by
      rcases lt_trichotomy (d 2) (1 / 2) with hβ | hβ | hβ
      · have hp := hsupp 0 (by linarith)
        linarith
      · linarith
      · have hp := hsupp 2 (by linarith)
        linarith
    ext a
    fin_cases a <;> simp <;> linarith
  · rintro rfl
    refine ⟨⟨fun a => by fin_cases a <;> simp, by simp [Fin.sum_univ_four]; norm_num⟩, ?_⟩
    intro d' hd'
    rw [toValue_ex, toValue_ex]
    have hpay : ∀ a, exPay ![1 / 2, 0, 1 / 2, 0] a = ![5, 5 / 2, 5, 9 / 2] a := by
      intro a; fin_cases a <;> simp [exPay, exU] <;> norm_num
    simp only [hpay, Fin.sum_univ_four]
    have hs := hd'.2
    simp only [Fin.sum_univ_four] at hs
    have := hd'.1 0; have := hd'.1 1; have := hd'.1 2; have := hd'.1 3
    simp
    nlinarith

/-- **No pure action is optimal** in the shutdown example (from uniqueness: no vertex equals
`![1/2, 0, 1/2, 0]`).
Source: [[taylor-2016-maximizing-a-quantity-while-ignoring-effect-through-some-channel]] ll. 46–52
("no individual action satisfies the optimality condition")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem not_toOptimal_ex_vertex (a : Fin 4) : ¬ IsTOOptimal exPB exPC exU (vertex a) := by
  rw [toOptimal_ex_iff]
  intro h
  have := congrFun h a
  fin_cases a <;> simp [vertex] at this

end Cleanroom.Fixpoint.FixOraclesCorresp
