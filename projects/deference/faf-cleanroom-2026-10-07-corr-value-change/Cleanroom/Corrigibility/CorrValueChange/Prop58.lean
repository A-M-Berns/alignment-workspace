import Cleanroom.Corrigibility.CorrValueChange.JeffreyBolker
import Mathlib.Tactic.LinearCombination

/-!
# corr-value-change — Proposition 5.8, atomic case (T11(f), S5)

Source: [[value-change-as-epistemic-update]] §5.8. Desirability reflection for a state `(Q, U_Q)`
toward `(P, U)` and an event `E`: `E_Q[U_Q ∣ X] = E_P[U ∣ X ∧ E]` for every `X` with `Q(X) > 0` and
`P(X ∧ E) > 0`. (a) the conditioned state satisfies it; (b) a `Q` concentrated on `E` satisfying it,
when `U` is not a.s. constant on `E`, is `P(· ∣ E)` with `U_Q = U` a.s. on `E`; (c) with `Q = P`
and `P(¬E) > 0` (a hypothesis the note omits, findings F6), reflection holds iff `U` is a.s.
constant on `E`, and then `U_Q` is that constant a.s.; at `P(E) = 1` the "only if" fails
(`prop58c_needs_compl_pos`). The pair-identity step of the note's sketch is closed in the case the
sketch skips (F7).
-/

namespace Cleanroom.Corrigibility.CorrValueChange

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- **Desirability reflection** of `(Q, U_Q)` toward `(P, U)` on the event `E`.
Source: [[value-change-as-epistemic-update]] §5.8 ("`E_Q[U_Q ∣ X] = E_P[U ∣ X ∧ E]` for every `X`
with `Q(X) > 0` and `P(X ∧ E) > 0`")
Kind: D
Fidelity: exact -/
def DesRefl (P : Prob Ω) (U : Ω → ℝ) (E : Finset Ω) (Q : Prob Ω) (UQ : Ω → ℝ) : Prop :=
  ∀ X : Finset Ω, 0 < Q.mass X → 0 < P.mass (X ∩ E) → Q.condExp UQ X = P.condExp U (X ∩ E)

/-- **5.8(a)**: `(P(· ∣ E), U)` satisfies desirability reflection.
Source: [[value-change-as-epistemic-update]] §5.8 (a)
Kind: P
Fidelity: exact
Hyps: (a) `0 < P(E)` -/
theorem prop58a (P : Prob Ω) (U : Ω → ℝ) {E : Finset Ω} (hE : 0 < P.mass E) :
    DesRefl P U E (condProb P E hE) U := by
  intro X _ hXE
  exact conditioning_preserves_rn P U hE X hXE

/-! ## (b) -/

/-- Masses of singletons.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_single (P : Prob Ω) (x : Ω) : P.mass {x} = P.p x := by simp [Prob.mass]

/-- The single-atom step of the sketch: at `x ∈ E` with `Q(x) > 0` and `P(x) > 0`, `U_Q(x) = U(x)`.
Source: [[value-change-as-epistemic-update]] §5.8 proof sketch ("On single atoms `x` of `E` …
so `U_Q = U` wherever `f > 0`")
Kind: L
Fidelity: exact -/
theorem desRefl_single {P : Prob Ω} {U : Ω → ℝ} {E : Finset Ω} {Q : Prob Ω} {UQ : Ω → ℝ}
    (h : DesRefl P U E Q UQ) {x : Ω} (hx : x ∈ E) (hQ : 0 < Q.p x) (hP : 0 < P.p x) :
    UQ x = U x := by
  have := h {x} (by rw [mass_single]; exact hQ) (by
    rw [singleton_inter_of_mem hx, mass_single]; exact hP)
  rw [singleton_inter_of_mem hx, Q.condExp_singleton _ hQ, P.condExp_singleton _ hP] at this
  exact this

/-- The pair identity of the sketch, in the form `(Q(x) P(y) − Q(y) P(x)) (U(x) − U(y)) = 0` for
distinct `x, y ∈ E` of positive `P`-probability — covering the case the sketch skips, where one of
`Q(x), Q(y)` vanishes (findings F7).
Source: [[value-change-as-epistemic-update]] §5.8 proof sketch ("On a pair of atoms `{x, y}` it
reads … `p_x p_y (f_x − f_y)(U_x − U_y) = 0`")
Kind: P
Fidelity: exact (the density `f` cleared of denominators)
Hyps: (a) `DesRefl`, `x ≠ y ∈ E`, `0 < P(x)`, `0 < P(y)` -/
theorem desRefl_pair {P : Prob Ω} {U : Ω → ℝ} {E : Finset Ω} {Q : Prob Ω} {UQ : Ω → ℝ}
    (h : DesRefl P U E Q UQ) {x y : Ω} (hxy : x ≠ y) (hx : x ∈ E) (hy : y ∈ E) (hPx : 0 < P.p x)
    (hPy : 0 < P.p y) : (Q.p x * P.p y - Q.p y * P.p x) * (U x - U y) = 0 := by
  have hpair : ({x, y} : Finset Ω) ∩ E = {x, y} := by
    ext z; simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro (rfl | rfl); exact ⟨Or.inl rfl, hx⟩; exact ⟨Or.inr rfl, hy⟩
  have hmassP : P.mass {x, y} = P.p x + P.p y := by simp [Prob.mass, sum_pair hxy]
  have hmassQ : Q.mass {x, y} = Q.p x + Q.p y := by simp [Prob.mass, sum_pair hxy]
  rcases (Q.nonneg x).lt_or_eq with hQx | hQx <;> rcases (Q.nonneg y).lt_or_eq with hQy | hQy
  · -- both positive: `U_Q = U` at both, expand
    have hUx := desRefl_single h hx hQx hPx
    have hUy := desRefl_single h hy hQy hPy
    have := h {x, y} (by rw [hmassQ]; linarith) (by rw [hpair, hmassP]; linarith)
    rw [hpair] at this
    unfold Prob.condExp Prob.integral at this
    rw [hmassP, hmassQ, sum_pair hxy, sum_pair hxy, hUx, hUy] at this
    rw [div_eq_div_iff (by linarith) (by linarith)] at this
    linear_combination this
  · -- `Q(y) = 0 < Q(x)`: the pair condition says `U(x)` is the `P`-average of `U(x), U(y)`
    have hUx := desRefl_single h hx hQx hPx
    have := h {x, y} (by rw [hmassQ, ← hQy]; linarith) (by rw [hpair, hmassP]; linarith)
    rw [hpair] at this
    unfold Prob.condExp Prob.integral at this
    rw [hmassP, hmassQ, sum_pair hxy, sum_pair hxy, hUx, ← hQy] at this
    rw [div_eq_div_iff (by linarith) (by linarith)] at this
    rw [← hQy]
    linear_combination this
  · have hUy := desRefl_single h hy hQy hPy
    have := h {x, y} (by rw [hmassQ, ← hQx]; linarith) (by rw [hpair, hmassP]; linarith)
    rw [hpair] at this
    unfold Prob.condExp Prob.integral at this
    rw [hmassP, hmassQ, sum_pair hxy, sum_pair hxy, hUy, ← hQx] at this
    rw [div_eq_div_iff (by linarith) (by linarith)] at this
    rw [← hQx]
    linear_combination this
  · rw [← hQx, ← hQy]; ring

/-- `Q(x) P(y) = Q(y) P(x)` for all `x, y ∈ E` of positive `P`-probability (the density of `Q`
with respect to `P` is constant on `E`), when `U` takes two values on such atoms.
Source: [[value-change-as-epistemic-update]] §5.8 proof sketch ("hence `f` is constant")
Kind: P
Fidelity: exact
Hyps: (a) `DesRefl`, `U` not a.s. constant on `E` -/
theorem desRefl_density_const {P : Prob Ω} {U : Ω → ℝ} {E : Finset Ω} {Q : Prob Ω} {UQ : Ω → ℝ}
    (h : DesRefl P U E Q UQ) {x₁ x₂ : Ω} (h₁ : x₁ ∈ E) (h₂ : x₂ ∈ E) (hP₁ : 0 < P.p x₁)
    (hP₂ : 0 < P.p x₂) (hU : U x₁ ≠ U x₂) :
    ∀ y ∈ E, 0 < P.p y → Q.p y * P.p x₁ = Q.p x₁ * P.p y := by
  have hne : x₁ ≠ x₂ := fun e => hU (by rw [e])
  have h12 : Q.p x₁ * P.p x₂ = Q.p x₂ * P.p x₁ := by
    have := desRefl_pair h hne h₁ h₂ hP₁ hP₂
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    · exact absurd (sub_eq_zero.1 h0) hU
  intro y hy hPy
  by_cases hy1 : y = x₁
  · subst hy1; ring
  rcases eq_or_ne (U y) (U x₁) with hUy | hUy
  · -- `U y = U x₁ ≠ U x₂`: pair `y, x₂` gives the density equality with `x₂`, then chain
    have hy2 : y ≠ x₂ := fun e => hU (by rw [← e, hUy])
    have := desRefl_pair h hy2 hy h₂ hPy hP₂
    have hd : Q.p y * P.p x₂ = Q.p x₂ * P.p y := by
      rcases mul_eq_zero.1 this with h0 | h0
      · linarith
      · exfalso; apply hU; rw [← hUy]; exact sub_eq_zero.1 h0
    -- from `Q y P x₂ = Q x₂ P y` and `Q x₁ P x₂ = Q x₂ P x₁`
    have hprod : (Q.p y * P.p x₁ - Q.p x₁ * P.p y) * P.p x₂ = 0 := by
      linear_combination P.p x₁ * hd - P.p y * h12
    rcases mul_eq_zero.1 hprod with h0 | h0
    · linarith
    · exact absurd h0 hP₂.ne'
  · have := desRefl_pair h hy1 hy h₁ hPy hP₁
    rcases mul_eq_zero.1 this with h0 | h0
    · linarith
    · exact absurd (sub_eq_zero.1 h0) hUy

/-- **5.8(b)**: if `Q ≪ P`, `Q` is concentrated on `E`, `(Q, U_Q)` satisfies desirability reflection
and `U` is not `P`-a.s. constant on `E`, then `Q = P(· ∣ E)` and `U_Q = U` on every atom of `E` of
positive probability: the belief-change realization is the only one.
Source: [[value-change-as-epistemic-update]] §5.8 (b)
Kind: P
Fidelity: exact (a.s. = on the atoms of positive `P`-probability)
Hyps: (a) `hac : Q ≪ P`, `hconc`, `h : DesRefl`, `hnc : U` not a.s. constant on `E`, `0 < P(E)` -/
theorem prop58b (P : Prob Ω) (U : Ω → ℝ) {E : Finset Ω} (hE : 0 < P.mass E) (Q : Prob Ω)
    (UQ : Ω → ℝ) (hac : ∀ ω, P.p ω = 0 → Q.p ω = 0) (hconc : ∀ ω, ω ∉ E → Q.p ω = 0)
    (h : DesRefl P U E Q UQ)
    (hnc : ∃ x₁ ∈ E, ∃ x₂ ∈ E, 0 < P.p x₁ ∧ 0 < P.p x₂ ∧ U x₁ ≠ U x₂) :
    (∀ ω, Q.p ω = (condProb P E hE).p ω) ∧ ∀ ω ∈ E, 0 < P.p ω → UQ ω = U ω := by
  obtain ⟨x₁, h₁, x₂, h₂, hP₁, hP₂, hU⟩ := hnc
  have hdens := desRefl_density_const h h₁ h₂ hP₁ hP₂ hU
  -- the constant density is `c = Q(x₁)/P(x₁)`; summing `Q = c P` over `E ∩ supp` gives `c = 1/P(E)`
  set c := Q.p x₁ / P.p x₁ with hc
  have hQc : ∀ ω, Q.p ω = if ω ∈ E then c * P.p ω else 0 := by
    intro ω
    split_ifs with hω
    · rcases (P.nonneg ω).lt_or_eq with hPω | hPω
      · have := hdens ω hω hPω
        rw [hc]; field_simp; linarith
      · rw [hac ω hPω.symm, ← hPω, mul_zero]
    · exact hconc ω hω
  have hsum : ∑ ω, Q.p ω = c * P.mass E := by
    simp_rw [hQc]
    rw [← sum_filter, filter_mem_eq_inter, univ_inter]
    unfold Prob.mass; rw [mul_sum]
  rw [Q.sum_one] at hsum
  have hcE : c = 1 / P.mass E := by field_simp; linarith
  refine ⟨fun ω => ?_, fun ω hω hPω => ?_⟩
  · rw [hQc ω]; unfold condProb; simp only
    split_ifs
    · rw [hcE]; ring
    · rfl
  · have hQω : 0 < Q.p ω := by
      rw [hQc ω, if_pos hω, hcE]; positivity
    exact desRefl_single h hω hQω hPω

/-- **`prop58b`'s hypothesis package is inhabited by conditioning**: for any `P`, `U`, `E` of positive
probability, `Q := P(· ∣ E)` with `U_Q := U` is absolutely continuous, concentrated on `E`, and
desirability-reflecting (`prop58a`); the non-constancy clause is supplied separately
(`prop58b_jb_nonconstant` for the §5.7 example).
Source: [[value-change-as-epistemic-update]] §5.8; audit r1 (N8)
Kind: N+
Fidelity: exact -/
theorem prop58b_package (P : Prob Ω) (U : Ω → ℝ) {E : Finset Ω} (hE : 0 < P.mass E) :
    (∀ ω, P.p ω = 0 → (condProb P E hE).p ω = 0) ∧ (∀ ω, ω ∉ E → (condProb P E hE).p ω = 0) ∧
    DesRefl P U E (condProb P E hE) U := by
  refine ⟨fun ω h => ?_, fun ω h => ?_, prop58a P U hE⟩
  · simp [condProb, h]
  · simp [condProb, h]

/-- The event `a₁` of the §5.7 algebra.
Source: [[value-change-as-epistemic-update]] §5.7
Kind: D
Fidelity: exact -/
def jbA1 : Finset (Bool × Bool × Fin 3) := univ.filter fun y => y.2.2 = 0

/-- **The non-constancy clause of `prop58b` holds in the §5.7 example** on `E = a₁`: the atoms
`(A, A, a₁)` and `(B, A, a₁)` have positive probability and utilities `1 ≠ 0`; with
`prop58b_package` the full package of `prop58b` is inhabited there.
Source: [[value-change-as-epistemic-update]] §5.7–5.8; audit r1 (N8)
Kind: N+
Fidelity: exact -/
theorem prop58b_jb_nonconstant :
    0 < jbProb.mass jbA1 ∧
    ∃ x₁ ∈ jbA1, ∃ x₂ ∈ jbA1, 0 < jbProb.p x₁ ∧ 0 < jbProb.p x₂ ∧ jbU x₁ ≠ jbU x₂ := by
  have hmem : (true, true, (0 : Fin 3)) ∈ jbA1 := by simp [jbA1]
  have hpos : 0 < jbProb.p (true, true, 0) := by simp [jbProb]
  refine ⟨lt_of_lt_of_le hpos (single_le_sum (fun y _ => jbProb.nonneg y) hmem), ?_⟩
  refine ⟨(true, true, 0), hmem, (false, true, 0), by simp [jbA1], hpos, by simp [jbProb], ?_⟩
  simp [jbU]

/-! ## (c) -/

/-- **5.8(c), ⇒ (with `P(¬E) > 0`)**: if `(P, U_Q)` — beliefs unchanged — satisfies desirability
reflection and `¬E` is non-null, then `U` is `P`-a.s. constant on `E`, equal to some `u₀`, and
`U_Q = u₀` `P`-a.s. everywhere.
Source: [[value-change-as-epistemic-update]] §5.8 (c); findings F6 (the hypothesis `P(¬E) > 0`)
Kind: P
Fidelity: exact with the added hypothesis `0 < P(Eᶜ)`
Hyps: (a) `h : DesRefl P U E P UQ`, `0 < P(E)`, `0 < P(Eᶜ)` -/
theorem prop58c_of_compl_pos (P : Prob Ω) (U : Ω → ℝ) {E : Finset Ω} (hE : 0 < P.mass E)
    (hEc : 0 < P.mass Eᶜ) (UQ : Ω → ℝ) (h : DesRefl P U E P UQ) :
    ∃ u₀, (∀ ω ∈ E, 0 < P.p ω → U ω = u₀) ∧ ∀ ω, 0 < P.p ω → UQ ω = u₀ := by
  obtain ⟨z₀, hz₀, hPz₀⟩ := P.exists_pos_of_mass_pos hEc
  rw [mem_compl] at hz₀
  obtain ⟨y₀, hy₀, hPy₀⟩ := P.exists_pos_of_mass_pos hE
  -- on `E`: `U_Q = U` at positive atoms
  have hon : ∀ y ∈ E, 0 < P.p y → UQ y = U y := fun y hy hPy => desRefl_single h hy hPy hPy
  -- across: for `y ∈ E`, `z ∉ E` positive, `U_Q z = U y`
  have hcross : ∀ y ∈ E, 0 < P.p y → ∀ z ∉ E, 0 < P.p z → UQ z = U y := by
    intro y hy hPy z hz hPz
    have hyz : y ≠ z := fun e => hz (e ▸ hy)
    have hpair : ({y, z} : Finset Ω) ∩ E = {y} := by
      ext w; simp only [mem_inter, mem_insert, mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hw⟩; rfl; exact absurd hw hz
      · rintro rfl; exact ⟨Or.inl rfl, hy⟩
    have := h {y, z} (by simp [Prob.mass, sum_pair hyz]; linarith) (by rw [hpair, mass_single]; exact hPy)
    rw [hpair, P.condExp_singleton _ hPy] at this
    unfold Prob.condExp Prob.integral Prob.mass at this
    rw [sum_pair hyz, sum_pair hyz, hon y hy hPy] at this
    rw [div_eq_iff (by linarith)] at this
    have : P.p z * UQ z = P.p z * U y := by linarith
    exact mul_left_cancel₀ hPz.ne' this
  refine ⟨UQ z₀, fun y hy hPy => (hcross y hy hPy z₀ hz₀ hPz₀).symm, fun ω hPω => ?_⟩
  by_cases hω : ω ∈ E
  · rw [hon ω hω hPω, (hcross ω hω hPω z₀ hz₀ hPz₀)]
  · rw [hcross y₀ hy₀ hPy₀ ω hω hPω, hcross y₀ hy₀ hPy₀ z₀ hz₀ hPz₀]

/-- **5.8(c), ⇐**: if `U = u₀` on the positive atoms of `E` and `U_Q = u₀` on all positive atoms,
then `(P, U_Q)` satisfies desirability reflection.
Source: [[value-change-as-epistemic-update]] §5.8 (c)
Kind: P
Fidelity: exact
Hyps: (a) the constancy hypotheses -/
theorem prop58c_converse (P : Prob Ω) (U : Ω → ℝ) (E : Finset Ω) (UQ : Ω → ℝ) (u₀ : ℝ)
    (hU : ∀ ω ∈ E, 0 < P.p ω → U ω = u₀) (hUQ : ∀ ω, 0 < P.p ω → UQ ω = u₀) :
    DesRefl P U E P UQ := by
  intro X hX hXE
  have e1 : P.condExp UQ X = u₀ := by
    rw [← P.condExp_const u₀ hX]
    unfold Prob.condExp Prob.integral
    congr 1
    refine sum_congr rfl fun ω _ => ?_
    rcases (P.nonneg ω).lt_or_eq with hp | hp
    · rw [hUQ ω hp]
    · rw [← hp, zero_mul, zero_mul]
  have e2 : P.condExp U (X ∩ E) = u₀ := by
    rw [← P.condExp_const u₀ hXE]
    unfold Prob.condExp Prob.integral
    congr 1
    refine sum_congr rfl fun ω hω => ?_
    rcases (P.nonneg ω).lt_or_eq with hp | hp
    · rw [hU ω (mem_inter.1 hω).2 hp]
    · rw [← hp, zero_mul, zero_mul]
  rw [e1, e2]

/-- **F6: 5.8(c) needs `P(¬E) > 0`**: when `P(¬E) = 0`, the state `(P, U)` itself satisfies
desirability reflection for *every* `U`, constant on `E` or not — because then
`E_P[U ∣ X] = E_P[U ∣ X ∧ E]` for every `X`. Instance: `Ω = Fin 3`, `P = (1/2, 1/2, 0)`, `E = {0, 1}`,
`U = (0, 1, 7)`: reflection holds and `U` takes two values on positive atoms of `E`.
Source: [[value-change-as-epistemic-update]] §5.8 (c) (refuted at `P(E) = 1`); findings F6
Kind: N+ (refutation of the unqualified statement)
Fidelity: exact -/
theorem prop58c_needs_compl_pos :
    let P : Prob (Fin 3) := ⟨![1 / 2, 1 / 2, 0], fun ω => by fin_cases ω <;> simp,
      by simp [Fin.sum_univ_three]; norm_num⟩
    let U : Fin 3 → ℝ := ![0, 1, 7]
    let E : Finset (Fin 3) := {0, 1}
    DesRefl P U E P U ∧ (0 : Fin 3) ∈ E ∧ (1 : Fin 3) ∈ E ∧ 0 < P.p 0 ∧ 0 < P.p 1 ∧ U 0 ≠ U 1 := by
  intro P U E
  refine ⟨?_, by simp [E], by simp [E], by simp [P], by simp [P], by simp [U]⟩
  intro X _ _
  -- `P` vanishes off `E`, so sums over `X` and `X ∩ E` agree
  have hoff : ∀ ω, ω ∉ E → P.p ω = 0 := by
    intro ω hω; fin_cases ω <;> simp [E] at hω <;> simp [P]
  have e : ∀ g : Fin 3 → ℝ, ∑ ω ∈ X, P.p ω * g ω = ∑ ω ∈ X ∩ E, P.p ω * g ω := by
    intro g
    rw [← sum_filter_add_sum_filter_not X (· ∈ E)]
    rw [filter_mem_eq_inter]
    have : ∑ ω ∈ X.filter (fun ω => ω ∉ E), P.p ω * g ω = 0 :=
      sum_eq_zero fun ω hω => by rw [hoff ω (mem_filter.1 hω).2, zero_mul]
    rw [this, add_zero]
  unfold Prob.condExp Prob.integral Prob.mass
  rw [e U]
  congr 1
  have := e (fun _ => 1)
  simpa using this

end

end Cleanroom.Corrigibility.CorrValueChange
