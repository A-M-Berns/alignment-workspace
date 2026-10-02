import Cleanroom.Decision.DpCalibration.Recording
import Cleanroom.Decision.DpCalibration.Corollaries
import Cleanroom.Found.DpCoreTree.Screening
import Cleanroom.Decision.DpCausalConsist.Defs

/-!
# `dp-causal-consist`: Theorem 3 (ii)–(iv), the collapse at recorded points

The tree side of Theorem 3, stated over `dp-core-tree`'s run law (`RecordsFor`, `PreQuery`,
`screening_recorded` = Lemma 3′) and `dp-calibration`'s strict clauses, and connected to the DAG
side of `Truncate.lean` through the calibrated state's pushforward `(s d).castℝ.toDistr`.

* `pr_inter_eq_mul_of_recordsFor`: at a recorded point under clause 1, every pre-query event is
  independent of every act event under `P_{s_d}` — Lemma 3′ read in the state (derived, never
  assumed).
* `thm3_ii`: the collapse — for a latent-free structure whose act-parents are pre-query, the
  truncated law of every positive-probability act is the act-conditional. No positivity of the
  parent cells is needed: `prob_parentCell_pos_of_prod_pos` shows the truncated support of a
  positive act lies in `P`-positive cells, so the CPD's freedom on null cells never reaches it
  (finding §6.1 resolved for positive acts; at *null* acts it is Corollary 3.1(a),
  `Witness3.lean`'s `nullAct_truncate_ne`).
* `thm3_ii_limit`: the same under limit calibration, via `limitOCAt_iff_strictOCAt_of_pos`.
* `thm3_iii`: with the act **jointly** independent of all other coordinates, the collapse holds
  for every compatible latent-free structure (finding §6.2: the wiki's pairwise hypothesis is not
  the one the proof uses; `Witness3.lean`'s noisy-XOR tree refutes the pairwise reading).
* `thm3_iv`: `T_CDT` with `cf^G` and `T_EDT` approve the same labels at `d` when the causal argmax
  meets `A_d^+` (the proviso), through `V_eq_condExp_of_strict` (the strict `V`-clause is the
  conditional expectation of a supervenient payoff) and self-transparency.
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Decision.DpCalibration
  FactoredSpaces Finset

section treeSide

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)
  {C : Proc ι acts ℚ} {B : Tree Ω ι acts ℚ} {d : ι}

/-- **Lemma 3′ in the state**: at a recorded point with `ν(O_d) > 0` and clause 1 of Definition 8,
every pre-query event `X` is independent of every act event under `P_{s_d}`:
`P_{s_d}(X ∧ a) = P_{s_d}(X) · P_{s_d}(a)`. Derived from `screening_recorded` and
`StrictClause1At`, never assumed.
Source: [[learning-cdt-renderings]] Theorem 3 proof ("Recording makes `m` a function of the draw
alone and Definition 6 makes the draw independent of everything upstream, so `m ⊥ ⟨V₀⟩`
(Lemma 3)"); `dp-core-tree` `screening_recorded`
Kind: C
Fidelity: exact
Hyps: (a) recording; (a) `0 < ν(O_d)`; (a) clause 1; (a) `X` pre-query -/
theorem pr_inter_eq_mul_of_recordsFor (s : ι → State Ω ℚ) (hrec : RecordsFor obs actEv C B d)
    (hO : 0 < nu C B (obs d)) (h1 : StrictClause1At s obs C B d) {X : Finset Ω}
    (hX : PreQuery obs C B d X) (a : acts d) :
    (s d).pr (X ∩ actEv d a) = (s d).pr X * (s d).pr (actEv d a) := by
  have key : (s d).pr (X ∩ actEv d a) * nu C B (obs d) * nu C B (obs d)
      = (s d).pr X * (s d).pr (actEv d a) * nu C B (obs d) * nu C B (obs d) := by
    calc (s d).pr (X ∩ actEv d a) * nu C B (obs d) * nu C B (obs d)
        = nu C B (X ∩ actEv d a ∩ obs d) * nu C B (obs d) := by rw [h1 (X ∩ actEv d a)]
      _ = nu C B (X ∩ obs d) * nu C B (actEv d a ∩ obs d) :=
          screening_recorded obs actEv hrec hX a
      _ = ((s d).pr X * nu C B (obs d)) * ((s d).pr (actEv d a) * nu C B (obs d)) := by
          rw [h1 X, h1 (actEv d a)]
      _ = _ := by ring
  exact mul_right_cancel₀ hO.ne' (mul_right_cancel₀ hO.ne' key)

/-- `paySum` of a supervenient payoff `r = u ∘ λ` is `∑_{x ∈ Y} u(x) ν({x})`.
Source: none: infrastructure (v2 Remark 3.5, supervenient payoffs)
Kind: L -/
theorem paySum_eq_sum_of_supervenient (u : Ω → ℚ) (hu : ∀ ℓ, payoff B ℓ = u (world B ℓ))
    (Y : Finset Ω) : paySum C B Y = ∑ x ∈ Y, u x * nu C B {x} := by
  rw [paySum_eq_sum_ite]
  simp_rw [nu_eq_sum, Finset.mem_singleton, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases hY : world B ℓ ∈ Y
  · rw [if_pos hY, Finset.sum_eq_single (world B ℓ)]
    · rw [if_pos rfl, hu ℓ]; ring
    · intro x _ hx; rw [if_neg (Ne.symm hx)]; ring
    · intro h; exact absurd hY h
  · rw [if_neg hY]
    symm; apply Finset.sum_eq_zero
    intro x hx
    rw [if_neg (fun h => hY (by rw [h]; exact hx))]; ring

/-- **The strict `V`-clause is a conditional expectation** for a supervenient payoff: under
recording-free clauses 1 and 2 at `d` with `ν(O_d) > 0`, for every `X` with `P_{s_d}(X) > 0`,
`V_{s_d}(X) = ∑_{x ∈ X} P_{s_d}(x) u(x) / P_{s_d}(X)`.
Source: [[decision-problems-v2]] Definition 8 clause 2; mandate T2(iv) ("so `StrictClause2At`
gives `V_{s_d}(X) = 𝔼[u | X ∧ O_d]`")
Kind: C
Fidelity: exact
Hyps: (a) clauses 1–2; (a) `0 < ν(O_d)`; (a) `r = u ∘ λ`; (a) `0 < P_{s_d}(X)` -/
theorem V_eq_condExp_of_strict (s : ι → State Ω ℚ) (hO : 0 < nu C B (obs d))
    (hs : StrictClausesAt s obs C B d) (u : Ω → ℚ) (hu : ∀ ℓ, payoff B ℓ = u (world B ℓ))
    (X : Finset Ω) (hX : 0 < (s d).pr X) :
    (s d).V X = (∑ x ∈ X, (s d).P.w x * u x) / (s d).pr X := by
  obtain ⟨h1, h2⟩ := hs
  have hXO : 0 < nu C B (X ∩ obs d) := by rw [← h1 X]; exact mul_pos hX hO
  have hV := h2 X hX hXO
  have hpay : paySum C B (X ∩ obs d) = nu C B (obs d) * ∑ x ∈ X, (s d).P.w x * u x := by
    rw [paySum_eq_sum_of_supervenient u hu, Finset.mul_sum]
    rw [← Finset.sum_filter_add_sum_filter_not X (fun x => x ∈ obs d)]
    have h0 : ∑ x ∈ X.filter (fun x => x ∉ obs d), nu C B (obs d) * ((s d).P.w x * u x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [Finset.mem_filter] at hx
      have := h1 {x}
      simp only [State.pr, probOf_singleton] at this
      rw [Finset.singleton_inter_of_notMem hx.2, nu_empty] at this
      have hw : (s d).P.w x = 0 := by
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h hO.ne'
      rw [hw]; ring
    rw [h0, add_zero, Finset.filter_mem_eq_inter]
    refine Finset.sum_congr rfl fun x hx => ?_
    have := h1 {x}
    simp only [State.pr, probOf_singleton] at this
    rw [Finset.singleton_inter_of_mem (Finset.mem_inter.mp hx).2] at this
    rw [← this]; ring
  rw [hpay, ← h1 X] at hV
  have hVO : (s d).V X * ((s d).pr X * nu C B (obs d))
      = ((∑ x ∈ X, (s d).P.w x * u x) / (s d).pr X) * ((s d).pr X * nu C B (obs d)) := by
    rw [hV]; field_simp
  exact mul_right_cancel₀ (mul_pos hX hO).ne' hVO

/-- `A_d^+` membership as positivity of the cast law.
Source: none: infrastructure
Kind: L -/
theorem toDistr_prob_pos_of_mem_aPlus (s : ι → State Ω ℚ) {a : acts d}
    (ha : a ∈ APlus s actEv d) :
    0 < (State.toDistr (State.castℝ (s d))).prob ↑(actEv d a) := by
  rw [State.toDistr_prob, State.castℝ_pr]
  have := (Finset.mem_filter.mp ha).2
  exact_mod_cast this

end treeSide

/-! ## Theorem 3(ii): the collapse -/

section collapse

variable {V : Type} [Fintype V] [DecidableEq V] {Val : V → Type} [∀ v, Fintype (Val v)]
  [∀ v, DecidableEq (Val v)] [∀ v, Nonempty (Val v)]
  {ι : Type} [DecidableEq ι] {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  (obs : ι → Finset (Pt Val)) (actEv : (d : ι) → acts d → Finset (Pt Val))
  {C : Proc ι acts ℚ} {B : Tree (Pt Val) ι acts ℚ} {d : ι}

/-- The parent cell `{x | x_pa(m) = c}` of a structure, as a finset.
Source: none: infrastructure
Kind: D -/
def parentCell (Γ : CausalStructure Val) (m : V) (c : ParentVals Γ.G Val m) : Finset (Pt Val) :=
  Finset.univ.filter fun x => parentConfig Γ.G Val x m = c

/-- The coerced parent cell. Source: none: infrastructure. Kind: L -/
theorem coe_parentCell (Γ : CausalStructure Val) (m : V) (c : ParentVals Γ.G Val m) :
    (↑(parentCell Γ m c) : Set (Pt Val)) = {x | parentConfig Γ.G Val x m = c} := by
  ext x; simp [parentCell]

/-- **Theorem 3(ii), the collapse at a recorded point**: let `B` record at `d` for `C` with
`ν(O_d) > 0` and the strict clauses at `d`; let the action events be the act coordinate's
fibers (`actEv d a = {x | x_m = e a}`); let `Γ` be a latent-free structure for `P_{s_d}` whose
act-parent cells are pre-query and `P_{s_d}`-positive. Then for every act `a ∈ A_d^+`, the
truncated law `do(m := e a)` is the act-conditional `P_{s_d}(· | x_m = e a)`.
Derivation: clause 1 + Lemma 3′ give `P(a ∧ pa = c) = P(a) P(pa = c)` (`pr_inter_eq_mul_of_recordsFor`);
the local Markov identity gives `P(a ∧ pa = c) = φ_m(c)(a) P(pa = c)`; at a positive cell
`φ_m(c)(a) = P(a)`, which is (i)'s right side.
Source: [[learning-cdt-renderings]] Theorem 3(ii) ("the identity holds whenever
`pa_G(m) ⊆ V₀`"); mandate T2(ii)
Kind: C
Fidelity: exact — the wiki's "`O_d` pre-query or `⊤`" is not needed (Lemma 3′ has no such
hypothesis) and is dropped; no positivity of the parent cells is needed either
(`prob_parentCell_pos_of_prod_pos`: the truncated support of a positive act lies in `P`-positive
cells, finding §6.1 resolved); "`pa_G(m) ⊆ V₀`" rendered cellwise as `PreQuery` of every parent cell
Hyps: (a) recording; (a) `0 < ν(O_d)`; (a) strict clauses; (a) `actEv` = act-coordinate fibers;
(a) `Γ.IsFor P_{s_d}` (Markov compatibility); (a) parent cells pre-query; (a) `a ∈ A_d^+` -/
theorem thm3_ii (s : ι → State (Pt Val) ℚ) (hrec : RecordsFor obs actEv C B d)
    (hO : 0 < nu C B (obs d)) (hs : StrictClausesAt s obs C B d) (m : V) (e : acts d → Val m)
    (hact : ∀ a, actEv d a = actEvCoord m (e a)) (Γ : CausalStructure Val)
    (hΓ : Γ.IsFor (State.toDistr (State.castℝ (s d))))
    (hpa : ∀ c, PreQuery obs C B d (parentCell Γ m c)) (a : acts d)
    (hpos : 0 < (State.toDistr (State.castℝ (s d))).prob {x | x m = e a}) :
    Γ.truncate m (e a) = condDistr (State.toDistr (State.castℝ (s d))) {x | x m = e a} hpos := by
  set P := State.toDistr (State.castℝ (s d)) with hP
  rw [CausalStructure.truncate, thm3_i Γ.acyclic Γ.φ hΓ m (e a) hpos]
  intro x _ hT
  set c := parentConfig Γ.G Val x m with hc
  have hcpos : 0 < P.prob {y | parentConfig Γ.G Val y m = c} :=
    prob_parentCell_pos_of_prod_pos Γ.acyclic Γ.φ hΓ m x hT
  rw [← condProb_val_parentCell Γ.acyclic Γ.φ hΓ m (e a) c hcpos]
  unfold Distr.condProb
  rw [div_eq_iff hcpos.ne']
  have hsets : ({y : Pt Val | y m = e a} ∩ {y | parentConfig Γ.G Val y m = c})
      = ↑(parentCell Γ m c ∩ actEv d a) := by
    rw [hact a, Finset.coe_inter, coe_parentCell, coe_actEvCoord, Set.inter_comm]
  have hA : ({y : Pt Val | y m = e a}) = ↑(actEv d a) := by
    rw [hact a, coe_actEvCoord]
  rw [hsets, ← coe_parentCell, hA, hP, State.toDistr_prob, State.toDistr_prob, State.toDistr_prob,
    State.castℝ_pr, State.castℝ_pr, State.castℝ_pr,
    pr_inter_eq_mul_of_recordsFor obs actEv s hrec hO hs.1 (hpa c) a]
  push_cast; ring

/-- **Theorem 3(ii) under limit calibration**: at a realized point (`ν(O_d) > 0`) Definition 10
and Definition 8 coincide (`limitOCAt_iff_strictOCAt_of_pos`), so the collapse transfers.
Source: [[learning-cdt-renderings]] Theorem 3 ("strictly or limit observation-calibrated …
Limit calibration changes nothing")
Kind: C
Fidelity: exact
Hyps: as `thm3_ii` with `LimitOCAt` in place of the strict clauses -/
theorem thm3_ii_limit [∀ d, Nonempty (acts d)] (s : ι → State (Pt Val) ℚ)
    (hrec : RecordsFor obs actEv C B d) (hO : 0 < nu C B (obs d))
    (hlim : LimitOCAt s obs C B d) (m : V) (e : acts d → Val m)
    (hact : ∀ a, actEv d a = actEvCoord m (e a)) (Γ : CausalStructure Val)
    (hΓ : Γ.IsFor (State.toDistr (State.castℝ (s d))))
    (hpa : ∀ c, PreQuery obs C B d (parentCell Γ m c)) (a : acts d)
    (hpos : 0 < (State.toDistr (State.castℝ (s d))).prob {x | x m = e a}) :
    Γ.truncate m (e a) = condDistr (State.toDistr (State.castℝ (s d))) {x | x m = e a} hpos :=
  thm3_ii obs actEv s hrec hO
    (((limitOCAt_iff_strictOCAt_of_pos s obs C B d hO).mp hlim) hO) m e hact Γ hΓ hpa a hpos

end collapse

/-! ## Theorem 3(iii): joint independence gives the collapse for every compatible structure -/

section thm3iii

variable {V : Type} [Fintype V] [DecidableEq V] {Val : V → Type} [∀ v, Fintype (Val v)]
  [∀ v, DecidableEq (Val v)] [∀ v, Nonempty (Val v)]

/-- The fiber of the coordinates other than `m` through `y`: `{x | x_{−m} = y_{−m}}`.
Source: [[learning-cdt-renderings]] Theorem 3(iii) (`⟨V₀⟩`, `⟨V₁⟩` jointly, i.e. `x_{−m}`)
Kind: D -/
def fiberOff (m : V) (y : Pt Val) : Finset (Pt Val) :=
  Finset.univ.filter fun x => ∀ u, u ≠ m → x u = y u

/-- Membership in `fiberOff`. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_fiberOff (m : V) (y x : Pt Val) :
    x ∈ fiberOff m y ↔ ∀ u, u ≠ m → x u = y u := by simp [fiberOff]

/-- **Joint independence of the act from all other coordinates** under a distribution on the
coordinate space: `P(x_m = b ∧ x_{−m} = y_{−m}) = P(x_m = b) · P(x_{−m} = y_{−m})` for all `b`, `y`.
Source: [[learning-cdt-renderings]] Theorem 3(iii) (the hypothesis its proof needs: `m` independent
of every joint parent configuration drawn from `V₀ ∪ V₁`); mandate T2(iii)
Kind: D -/
def ActJointlyIndep (P : Distr (Pt Val)) (m : V) : Prop :=
  ∀ (b : Val m) (y : Pt Val), P.prob (↑(actEvCoord m b ∩ fiberOff m y))
    = P.prob ↑(actEvCoord m b) * P.prob ↑(fiberOff m y)

/-- An event is a union of `fiberOff` cells iff it does not read coordinate `m`.
Source: none: infrastructure
Kind: D -/
def IgnoresCoord (m : V) (X : Finset (Pt Val)) : Prop :=
  ∀ x (b : Val m), Function.update x m b ∈ X ↔ x ∈ X

/-- Under joint independence, the act is independent of every event that ignores `m`:
`P(x_m = a ∧ X) = P(x_m = a) P(X)`.
Source: [[learning-cdt-renderings]] Theorem 3(iii) proof ("(iii) follows")
Kind: P
Hyps: (a) joint independence; (a) `X` ignores `m`; (a) `0 < P(x_m = a)` -/
theorem prob_act_inter_eq_mul_of_ignores {P : Distr (Pt Val)} {m : V} (h : ActJointlyIndep P m)
    (a : Val m) (ha : 0 < P.prob ↑(actEvCoord m a)) {X : Finset (Pt Val)}
    (hX : IgnoresCoord m X) :
    P.prob ↑(actEvCoord m a ∩ X) = P.prob ↑(actEvCoord m a) * P.prob ↑X := by
  -- the singleton identity: `P(update x m a) = P(a) · ∑_b P(update x m b)`
  have hsing : ∀ x : Pt Val, P.mass (Function.update x m a)
      = P.prob ↑(actEvCoord m a) * ∑ b, P.mass (Function.update x m b) := by
    intro x
    have hy := h a x
    have h1 : actEvCoord m a ∩ fiberOff m x = {Function.update x m a} := by
      ext z
      simp only [Finset.mem_inter, mem_actEvCoord, mem_fiberOff, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        funext u
        by_cases hu : u = m
        · subst hu; rw [Function.update_self]; exact h1
        · rw [Function.update_of_ne hu]; exact h2 u hu
      · rintro rfl
        exact ⟨Function.update_self _ _ _, fun u hu => Function.update_of_ne hu _ _⟩
    have h2 : P.prob ↑(fiberOff m x) = ∑ b, P.mass (Function.update x m b) := by
      rw [prob_eq_sum_ite]
      have hfib : ∀ z : Pt Val, (z ∈ fiberOff m x) ↔ z = Function.update x m (z m) := by
        intro z
        rw [mem_fiberOff]
        constructor
        · intro hz; funext u
          by_cases hu : u = m
          · subst hu; rw [Function.update_self]
          · rw [Function.update_of_ne hu]; exact hz u hu
        · intro hz u hu
          rw [hz, Function.update_of_ne hu]
      rw [sum_fix_coord m (x m)]
      have : ∀ z : Pt Val, (if z m = x m then
          ∑ b, if Function.update z m b ∈ fiberOff m x then P.mass (Function.update z m b) else 0
          else 0) = if z = x then ∑ b, P.mass (Function.update x m b) else 0 := by
        intro z
        by_cases hz : z = x
        · subst hz
          rw [if_pos rfl, if_pos rfl]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [if_pos]
          rw [mem_fiberOff]; intro u hu; exact Function.update_of_ne hu _ _
        · rw [if_neg hz]
          by_cases hzm : z m = x m
          · rw [if_pos hzm]
            apply Finset.sum_eq_zero
            intro b _
            rw [if_neg]
            intro hmem
            rw [mem_fiberOff] at hmem
            apply hz
            funext u
            by_cases hu : u = m
            · subst hu; exact hzm
            · have := hmem u hu; rwa [Function.update_of_ne hu] at this
          · rw [if_neg hzm]
      simp_rw [this]
      rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    rw [h1, Finset.coe_singleton, Distr.prob_singleton, h2] at hy
    exact hy
  -- decompose `P(X)` along the fibers of `x_{−m}`
  have hXsum : P.prob ↑X = ∑ x : Pt Val, if x m = a ∧ x ∈ X then
      ∑ b, P.mass (Function.update x m b) else 0 := by
    rw [prob_eq_sum_ite, sum_fix_coord m a]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hxm : x m = a
    · rw [if_pos hxm]
      by_cases hxX : x ∈ X
      · rw [if_pos ⟨hxm, hxX⟩]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [if_pos ((hX x b).mpr hxX)]
      · rw [if_neg (fun h' => hxX h'.2)]
        apply Finset.sum_eq_zero
        intro b _
        rw [if_neg (fun h' => hxX ((hX x b).mp h'))]
    · rw [if_neg hxm, if_neg (fun h' => hxm h'.1)]
  have hAX : P.prob ↑(actEvCoord m a ∩ X) = ∑ x : Pt Val, if x m = a ∧ x ∈ X then P.mass x else 0 := by
    rw [prob_eq_sum_ite]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [Finset.mem_inter]
  rw [hAX, hXsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x m = a ∧ x ∈ X
  · rw [if_pos hx, if_pos hx]
    have := hsing x
    rw [← hx.1, Function.update_eq_self] at this
    rw [this, hx.1]
  · rw [if_neg hx, if_neg hx, mul_zero]

/-- **Theorem 3(iii)**: if the act is jointly independent of all the other coordinates under
`P`, then for **every** latent-free structure for `P` the truncated law of every
positive-probability act is the act-conditional (no positivity of the parent cells is assumed:
`prob_parentCell_pos_of_prod_pos`). The wiki's hypothesis is
the pairwise "`m ⊥ ⟨V₁⟩` moreover [`m ⊥ ⟨V₀⟩`]"; the proof needs, and the Lean carries, the
**joint** independence (finding §6.2, refuted pairwise on `xorTree` in `Witness3.lean`).
Source: [[learning-cdt-renderings]] Theorem 3(iii) ("if moreover `m ⊥ ⟨V₁⟩` under `P_{s_d}` … the
identity holds for every compatible `G`"); mandate T2(iii)
Kind: P
Fidelity: variant: joint independence in place of the wiki's pairwise hypothesis
Hyps: (a) joint independence; (a) `Γ.IsFor P`; (a) `0 < P(a)` -/
theorem thm3_iii {P : Distr (Pt Val)} {m : V} (h : ActJointlyIndep P m) (Γ : CausalStructure Val)
    (hΓ : Γ.IsFor P) (a : Val m) (hpos : 0 < P.prob {x | x m = a}) :
    Γ.truncate m a = condDistr P {x | x m = a} hpos := by
  rw [CausalStructure.truncate, thm3_i Γ.acyclic Γ.φ hΓ m a hpos]
  intro x _ hT
  set c := parentConfig Γ.G Val x m with hc
  have hcpos : 0 < P.prob {y | parentConfig Γ.G Val y m = c} :=
    prob_parentCell_pos_of_prod_pos Γ.acyclic Γ.φ hΓ m x hT
  rw [← condProb_val_parentCell Γ.acyclic Γ.φ hΓ m a c hcpos]
  unfold Distr.condProb
  rw [div_eq_iff hcpos.ne']
  have hign : IgnoresCoord m (parentCell Γ m c) := by
    intro y b
    simp only [parentCell, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [parentConfig_congr m (x := Function.update y m b) (y := y)]
    intro u hu
    refine Function.update_of_ne (fun h' => ?_) b y
    rw [h'] at hu
    exact Digraph.notMem_parents_self Γ.acyclic m hu
  have hA : ({y : Pt Val | y m = a}) = ↑(actEvCoord m a) := (coe_actEvCoord m a).symm
  have ha' : 0 < P.prob ↑(actEvCoord m a) := by rw [← hA]; exact hpos
  rw [hA, ← coe_parentCell, ← Finset.coe_inter,
    prob_act_inter_eq_mul_of_ignores h a ha' hign]

end thm3iii

/-! ## Theorem 3(iv): `T_CDT` with `cf^G` and `T_EDT` approve the same labels -/

section thm3iv

variable {V : Type} [Fintype V] [DecidableEq V] {Val : V → Type} [∀ v, Fintype (Val v)]
  [∀ v, DecidableEq (Val v)] [∀ v, Nonempty (Val v)]
  {ι : Type} [DecidableEq ι] {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  (obs : ι → Finset (Pt Val)) (actEv : (d : ι) → acts d → Finset (Pt Val))
  {C : Proc ι acts ℚ} {B : Tree (Pt Val) ι acts ℚ} {d : ι}

/-- The supposed value of an act under `cf^G` is the conditional expectation of `u` under the
truncated law; when that law is the act-conditional, it is `𝔼_P[u | x_m = a]`.
Source: [[learning-cdt-renderings]] Definition 24 (`V^{G,a}`)
Kind: L -/
theorem cfG_V_act_of_eq_cond (Γ : CausalStructure Val) (m : V) (u : Pt Val → ℝ) (a : Val m)
    {P : Distr (Pt Val)} (hpos : 0 < P.prob {x | x m = a})
    (heq : Γ.truncate m a = condDistr P {x | x m = a} hpos) :
    (cfG Γ m u a).V (actEvCoord m a)
      = (∑ x ∈ actEvCoord m a, P.mass x * u x) / ∑ x ∈ actEvCoord m a, P.mass x := by
  rw [cfG, expState_V, heq]
  have hnum : ∑ x ∈ actEvCoord m a, (condDistr P {x | x m = a} hpos).mass x * u x
      = (∑ x ∈ actEvCoord m a, P.mass x * u x) / P.prob {x | x m = a} := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [condDistr_mass, Set.indicator_of_mem (show x ∈ {x | x m = a} from (mem_actEvCoord m a x).mp hx)]
    ring
  have hden : ∑ x ∈ actEvCoord m a, (condDistr P {x | x m = a} hpos).mass x
      = (∑ x ∈ actEvCoord m a, P.mass x) / P.prob {x | x m = a} := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [condDistr_mass, Set.indicator_of_mem (show x ∈ {x | x m = a} from (mem_actEvCoord m a x).mp hx)]
  rw [hnum, hden, div_div_div_cancel_right₀ hpos.ne']

/-- **Under Theorem 3(ii)'s hypotheses the supposed value of every positive act is its
evidential value**: `V^{G,a}(a) = V_{s_d}(a)` for `a ∈ A_d^+`, with `r = u ∘ λ`.
Source: [[learning-cdt-renderings]] Theorem 3(iv); mandate T2(iv)
Kind: C
Hyps: as `thm3_ii`, plus (a) `r = u ∘ λ` -/
theorem cfG_V_eq_V_of_recordsFor (s : ι → State (Pt Val) ℚ) (hrec : RecordsFor obs actEv C B d)
    (hO : 0 < nu C B (obs d)) (hs : StrictClausesAt s obs C B d) (m : V) (e : acts d → Val m)
    (hact : ∀ a, actEv d a = actEvCoord m (e a)) (Γ : CausalStructure Val)
    (hΓ : Γ.IsFor (State.toDistr (State.castℝ (s d))))
    (hpa : ∀ c, PreQuery obs C B d (parentCell Γ m c)) (u : Pt Val → ℚ)
    (hu : ∀ ℓ, payoff B ℓ = u (world B ℓ)) (a : acts d) (ha : a ∈ APlus s actEv d) :
    (cfG Γ m (fun x => (u x : ℝ)) (e a)).V (actEv d a) = ((s d).V (actEv d a) : ℝ) := by
  have hpos : 0 < (State.toDistr (State.castℝ (s d))).prob {x | x m = e a} := by
    have := toDistr_prob_pos_of_mem_aPlus actEv s ha
    rwa [hact a, coe_actEvCoord] at this
  have heq := thm3_ii obs actEv s hrec hO hs m e hact Γ hΓ hpa a hpos
  have hapos : 0 < (s d).pr (actEv d a) := (Finset.mem_filter.mp ha).2
  rw [V_eq_condExp_of_strict obs s hO hs u hu (actEv d a) hapos]
  rw [hact a, cfG_V_act_of_eq_cond Γ m _ (e a) hpos heq]
  simp only [State.toDistr_mass, State.castℝ, FinDistr.castℝ, State.pr, probOf]
  push_cast
  rfl

/-- **Theorem 3(iv)**: under (ii)'s hypotheses with `cf := cf^G` and a supervenient payoff, if the
causal argmax (over all of `A_d`) meets `A_d^+`, then `T_CDT` and `T_EDT` approve the same
labels at `d`: `TCdtAt ↔ TEdtAt`. Self-transparency (`P_{s_d}(a) = C(d)(a)`) identifies the acts
`C` plays with `A_d^+`.
Source: [[learning-cdt-renderings]] Theorem 3(iv) ("consequently CDT with `cf^G` and EDT approve
the same labels at `d` whenever the causal argmax meets the positive-probability acts");
mandate T2(iv)
Kind: C
Fidelity: exact (the proviso is the wiki's own)
Hyps: as `cfG_V_eq_V_of_recordsFor`, plus (a) the proviso -/
theorem thm3_iv (s : ι → State (Pt Val) ℚ) (hrec : RecordsFor obs actEv C B d)
    (hO : 0 < nu C B (obs d)) (hs : StrictClausesAt s obs C B d) (m : V) (e : acts d → Val m)
    (hact : ∀ a, actEv d a = actEvCoord m (e a)) (Γ : CausalStructure Val)
    (hΓ : Γ.IsFor (State.toDistr (State.castℝ (s d))))
    (hpa : ∀ c, PreQuery obs C B d (parentCell Γ m c)) (u : Pt Val → ℚ)
    (hu : ∀ ℓ, payoff B ℓ = u (world B ℓ))
    (hprov : (argmaxAll (fun a => (cfG Γ m (fun x => (u x : ℝ)) (e a)).V (actEv d a))
      ∩ APlus s actEv d).Nonempty) :
    TCdtAt s actEv C d (fun a => cfG Γ m (fun x => (u x : ℝ)) (e a)) ↔ TEdtAt s actEv C d := by
  set v : acts d → ℝ := fun a => (cfG Γ m (fun x => (u x : ℝ)) (e a)).V (actEv d a) with hv
  have hagree : ∀ a ∈ APlus s actEv d, v a = ((s d).V (actEv d a) : ℝ) := fun a ha =>
    cfG_V_eq_V_of_recordsFor obs actEv s hrec hO hs m e hact Γ hΓ hpa u hu a ha
  obtain ⟨a₀, ha₀⟩ := hprov
  rw [Finset.mem_inter, mem_argmaxAll] at ha₀
  have hst : SelfTransparent s actEv C d :=
    selfTransparent_of_recordsFor_strict obs actEv C B s hrec hO (fun _ => hs)
  have hplay : ∀ a, 0 < (C d).w a → a ∈ APlus s actEv d := by
    intro a ha
    rw [APlus, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hst a]; exact ha⟩
  have hiff : ∀ a ∈ APlus s actEv d, (a ∈ argmaxAll v ↔ a ∈ argmaxPlus s actEv d) := by
    intro a ha
    rw [mem_argmaxAll, mem_argmaxPlus]
    constructor
    · intro h
      refine ⟨ha, fun b hb => ?_⟩
      have := h b
      rw [hagree a ha, hagree b hb] at this
      exact_mod_cast this
    · rintro ⟨-, h⟩ b
      have h1 : v a₀ ≤ v a := by
        rw [hagree a ha, hagree a₀ ha₀.2]
        exact_mod_cast h a₀ ha₀.2
      exact (ha₀.1 b).trans h1
  unfold TCdtAt TEdtAt
  constructor
  · intro h hne a ha
    exact (hiff a (hplay a ha)).mp (h hne a ha)
  · intro h hne a ha
    exact (hiff a (hplay a ha)).mpr (h hne a ha)

end thm3iv

end Cleanroom.Decision.DpCausalConsist
