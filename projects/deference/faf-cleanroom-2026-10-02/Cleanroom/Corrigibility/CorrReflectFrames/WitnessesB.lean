import Cleanroom.Corrigibility.CorrReflectFrames.Compose
import Cleanroom.Corrigibility.CorrReflectFrames.WitnessesA
import Mathlib.Data.Fin.VecNotation

/-!
# corr-reflect-frames — witnesses B (eight worlds)

* radical `s1` **Model A** (`πA`, `modelF`, `φA`): `{a₁,a₃}` and `{a₁,a₄}` are legitimizing, their
  union and intersection are not (I5.3(c), N+); the summed bound of I5.5 is `7/8` while no
  legitimizing event has mass above `3/4` (non-attainment on atoms: finding).
* radical `s1` **Model B** (`πB`): calibrated cells, `Ω` legitimizing, bound `1` attained (N+).
* radical `s5` (`π5`, `F₂`, `F₃`, `φ5`): value-form reflection at both steps, composite fails
  (T7, N+); the function-form hypothesis of `legitimizingVal_compose` genuinely fails at step
  one (`¬ Reflects π5 F₂`).
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames.Witnesses

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames

noncomputable section

/-- A nonnegative octuple summing to one is a distribution on eight worlds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem simplex8 (v : Fin 8 → ℝ) (h0 : ∀ i, 0 ≤ v i) (h1 : ∑ i, v i = 1) :
    v ∈ stdSimplex ℝ (Fin 8) := ⟨h0, h1⟩

/-! ## Models A and B -/

/-- Model A's masses `(2,1,2,2,3,3,1,2)/16` on `a₁..a₄, b₁..b₄`.
Source: [[radical]] `s1` Model A; Theorem I5.3(c) l. 154
Kind: D
Fidelity: exact -/
def πA : Fin 8 → ℝ := ![2 / 16, 1 / 16, 2 / 16, 2 / 16, 3 / 16, 3 / 16, 1 / 16, 2 / 16]

/-- Model B's masses `(2,2,2,2,3,3,1,1)/16`.
Source: [[radical]] `s1` Model B; Theorem I5.5(a) l. 161
Kind: D
Fidelity: exact -/
def πB : Fin 8 → ℝ := ![2 / 16, 2 / 16, 2 / 16, 2 / 16, 3 / 16, 3 / 16, 1 / 16, 1 / 16]

/-- The hits: `φ = {a₁, a₂, b₁, b₂} = {0, 1, 4, 5}`.
Source: [[radical]] `s1`
Kind: D
Fidelity: exact -/
abbrev φA : Finset (Fin 8) := {0, 1, 4, 5}

/-- The `a`-row: uniform on the four `a`-atoms (announces `1/2`).
Source: [[radical]] `s1` (cell `c = 1/2`)
Kind: D
Fidelity: exact -/
def ra : Fin 8 → ℝ := ![1 / 4, 1 / 4, 1 / 4, 1 / 4, 0, 0, 0, 0]

/-- The `b`-row: `(3/8, 3/8, 1/8, 1/8)` on the four `b`-atoms (announces `3/4`).
Source: [[radical]] `s1` (cell `c = 3/4`)
Kind: D
Fidelity: exact -/
def rb : Fin 8 → ℝ := ![0, 0, 0, 0, 3 / 8, 3 / 8, 1 / 8, 1 / 8]

/-- `ra` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ra_mem : ra ∈ stdSimplex ℝ (Fin 8) :=
  simplex8 _ (fun i => by fin_cases i <;> norm_num [ra]) (by simp [Fin.sum_univ_eight, ra]; norm_num)

/-- `rb` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rb_mem : rb ∈ stdSimplex ℝ (Fin 8) :=
  simplex8 _ (fun i => by fin_cases i <;> norm_num [rb]) (by simp [Fin.sum_univ_eight, rb]; norm_num)

/-- The Model A/B frame: `a`-worlds carry `ra`, `b`-worlds carry `rb` (immodest).
Source: [[radical]] `s1`
Kind: D
Fidelity: exact -/
def modelF : Frame (Fin 8) where
  P := ![ra, ra, ra, ra, rb, rb, rb, rb]
  P_mem := fun w => by fin_cases w <;> first | exact ra_mem | exact rb_mem

/-- The announced values: `ra(φ) = 1/2`, `rb(φ) = 3/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_ra_rb : mass ra φA = 1 / 2 ∧ mass rb φA = 3 / 4 := by
  simp only [mass, φA, sum_insert, mem_insert, mem_singleton, Fin.reduceEq, or_self,
    not_false_eq_true, or_false, false_or, sum_singleton, ra, rb, Matrix.cons_val]
  norm_num

/-- **I5.3(c), first event.** `{a₁, a₃} = {0, 2}` is legitimizing in Model A (hits `2/16`
against `L ∩ C = 4/16` at `c = 1/2`; empty at `c = 3/4`).
Source: [[radical]] Theorem I5.3(c) l. 154
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem modelA_legit_02 : LegitimizingVal πA modelF φA {0, 2} := by
  intro c
  rw [mass_inter_valCell, mass_inter_valCell]
  have e : φA ∩ {0, 2} = {0} := by decide
  rw [e, sum_singleton, sum_pair (by decide)]
  simp only [modelF, Matrix.cons_val, mass_ra_rb.1, mass_ra_rb.2, πA]
  split_ifs <;> (try subst_vars) <;> norm_num at *

/-- **I5.3(c), second event.** `{a₁, a₄} = {0, 3}` is legitimizing in Model A.
Source: [[radical]] Theorem I5.3(c) l. 154
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem modelA_legit_03 : LegitimizingVal πA modelF φA {0, 3} := by
  intro c
  rw [mass_inter_valCell, mass_inter_valCell]
  have e : φA ∩ {0, 3} = {0} := by decide
  rw [e, sum_singleton, sum_pair (by decide)]
  simp only [modelF, Matrix.cons_val, mass_ra_rb.1, mass_ra_rb.2, πA]
  split_ifs <;> (try subst_vars) <;> norm_num at *

/-- **I5.3(c): not closed under union.** `{0, 2} ∪ {0, 3} = {0, 2, 3}` is not legitimizing
(hits `2/16` against `6/16` at `c = 1/2`).
Source: [[radical]] Theorem I5.3(c) l. 154 ("union has hits 2/16 against misses 4/16")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem modelA_not_legit_union : ¬ LegitimizingVal πA modelF φA ({0, 2} ∪ {0, 3}) := by
  intro h
  have := h (1 / 2)
  rw [mass_inter_valCell, mass_inter_valCell] at this
  have e1 : φA ∩ ({0, 2} ∪ {0, 3}) = {0} := by decide
  have e2 : ({0, 2} ∪ {0, 3} : Finset (Fin 8)) = {0, 2, 3} := by decide
  rw [e1, e2, sum_singleton, sum_insert (by decide), sum_pair (by decide)] at this
  simp [modelF, mass_ra_rb.1, πA] at this <;> norm_num at this

/-- **I5.3(c): not closed under intersection.** `{0, 2} ∩ {0, 3} = {0}` is not legitimizing
(hits `2/16` against `2/16` at `c = 1/2`).
Source: [[radical]] Theorem I5.3(c) l. 154
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem modelA_not_legit_inter : ¬ LegitimizingVal πA modelF φA ({0, 2} ∩ {0, 3}) := by
  intro h
  have := h (1 / 2)
  rw [mass_inter_valCell, mass_inter_valCell] at this
  have e1 : φA ∩ ({0, 2} ∩ {0, 3}) = {0} := by decide
  have e2 : ({0, 2} ∩ {0, 3} : Finset (Fin 8)) = {0} := by decide
  rw [e1, e2, sum_singleton] at this
  simp [modelF, mass_ra_rb.1, πA] at this <;> norm_num at this

/-- The announced values of Model A/B are exactly `{1/2, 3/4}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem modelF_image : univ.image (fun w => mass (modelF.P w) φA) = {1 / 2, 3 / 4} := by
  ext c
  simp only [mem_image, mem_univ, true_and, mem_insert, mem_singleton]
  constructor
  · rintro ⟨w, rfl⟩
    fin_cases w <;> simp [modelF, Matrix.cons_val, mass_ra_rb.1, mass_ra_rb.2]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp [modelF, Matrix.cons_val, mass_ra_rb.1]⟩
    · exact ⟨4, by simp [modelF, Matrix.cons_val, mass_ra_rb.2]⟩

/-- **I5.5's bound in Model A is `7/8`**: `min(3/8, 1/2) + min(1/2, 3/4)`.
Source: [[radical]] Theorem I5.5(a) l. 161 ("Model A bound 7/8")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem modelA_bound :
    ∑ c ∈ univ.image (fun w => mass (modelF.P w) φA), cellBound πA modelF φA c = 7 / 8 := by
  rw [modelF_image, sum_pair (by norm_num)]
  unfold cellBound
  rw [mass_valCell_sdiff, mass_valCell_sdiff, mass_inter_valCell, mass_inter_valCell]
  simp only [φA, sum_insert, mem_insert, mem_singleton, Fin.reduceEq, or_self,
    not_false_eq_true, or_false, false_or, sum_singleton, Fin.sum_univ_eight, modelF, Matrix.cons_val,
    mass_ra_rb.1, mass_ra_rb.2, πA]
  norm_num [min_def]

/-- **I5.5's bound in Model B is `1`, attained by `Ω`** (both cells calibrated).
Source: [[radical]] Theorem I5.5(a) l. 161 ("calibrated Model B bound 1, attained")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem modelB_attained :
    LegitimizingVal πB modelF φA univ ∧
      ∑ c ∈ univ.image (fun w => mass (modelF.P w) φA), cellBound πB modelF φA c = 1 ∧
      mass πB univ = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro c
    rw [inter_univ, univ_inter, mass_inter_valCell, mass_valCell]
    simp only [φA, sum_insert, mem_insert, mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, or_false, false_or, sum_singleton, Fin.sum_univ_eight, modelF, Matrix.cons_val,
      mass_ra_rb.1, mass_ra_rb.2, πB]
    split_ifs <;> (try subst_vars) <;> norm_num at *
  · rw [modelF_image, sum_pair (by norm_num)]
    unfold cellBound
    rw [mass_valCell_sdiff, mass_valCell_sdiff, mass_inter_valCell, mass_inter_valCell]
    simp only [φA, sum_insert, mem_insert, mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, or_false, false_or, sum_singleton, Fin.sum_univ_eight, modelF, Matrix.cons_val,
      mass_ra_rb.1, mass_ra_rb.2, πB]
    norm_num [min_def]
  · simp [mass, Fin.sum_univ_eight, πB]; norm_num

/-! ## The `s5` composition counterexample -/

/-- The `s5` deferrer on atoms `(φ, b₁, b₂)` ordered `(1,A,a), (1,A,b), (1,B,a), (1,B,b), (0,A,a),
(0,A,b), (0,B,a), (0,B,b)`: branch `A` uniform `1/8`, branch `B` `(3,1,1,3)/16`.
Source: [[radical]] `s5`; Theorem I5.6(c) l. 175
Kind: D
Fidelity: exact -/
def π5 : Fin 8 → ℝ := ![1 / 8, 1 / 8, 3 / 16, 1 / 16, 1 / 8, 1 / 8, 1 / 16, 3 / 16]

/-- `ρ_A`: the `t₂`-state on branch `A`, `(3, 1, 1, 3)/8` over `(φ,a), (φ,b), (¬φ,a), (¬φ,b)` — same
`φ`-marginal `1/2` as `π(· | A)`, different correlation with `b₂`.
Source: [[radical]] `s5`
Kind: D
Fidelity: exact -/
def ρA : Fin 8 → ℝ := ![3 / 8, 1 / 8, 0, 0, 1 / 8, 3 / 8, 0, 0]

/-- `ρ_B = π(· | B)`: the `t₂`-state on branch `B`.
Source: [[radical]] `s5`
Kind: D
Fidelity: exact -/
def ρB : Fin 8 → ℝ := ![0, 0, 3 / 8, 1 / 8, 0, 0, 1 / 8, 3 / 8]

/-- `ρ_A` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ρA_mem : ρA ∈ stdSimplex ℝ (Fin 8) :=
  simplex8 _ (fun i => by fin_cases i <;> norm_num [ρA]) (by simp [Fin.sum_univ_eight, ρA]; norm_num)

/-- `ρ_B` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ρB_mem : ρB ∈ stdSimplex ℝ (Fin 8) :=
  simplex8 _ (fun i => by fin_cases i <;> norm_num [ρB]) (by simp [Fin.sum_univ_eight, ρB]; norm_num)

/-- The entries of `π5`, `ρ_A` and `ρ_B` (for finite evaluation).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem s5_vals :
    (π5 0 = 1 / 8 ∧ π5 1 = 1 / 8 ∧ π5 2 = 3 / 16 ∧ π5 3 = 1 / 16 ∧ π5 4 = 1 / 8 ∧ π5 5 = 1 / 8 ∧
      π5 6 = 1 / 16 ∧ π5 7 = 3 / 16) ∧
    (ρA 0 = 3 / 8 ∧ ρA 1 = 1 / 8 ∧ ρA 2 = 0 ∧ ρA 3 = 0 ∧ ρA 4 = 1 / 8 ∧ ρA 5 = 3 / 8 ∧
      ρA 6 = 0 ∧ ρA 7 = 0) ∧
    (ρB 0 = 0 ∧ ρB 1 = 0 ∧ ρB 2 = 3 / 8 ∧ ρB 3 = 1 / 8 ∧ ρB 4 = 0 ∧ ρB 5 = 0 ∧ ρB 6 = 1 / 8 ∧
      ρB 7 = 3 / 8) :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-- The `t₂` frame: `ρ_A` on the `A`-atoms, `ρ_B` on the `B`-atoms.
Source: [[radical]] `s5`
Kind: D
Fidelity: exact -/
def F₂ : Frame (Fin 8) where
  P := ![ρA, ρA, ρB, ρB, ρA, ρA, ρB, ρB]
  P_mem := fun w => by fin_cases w <;> first | exact ρA_mem | exact ρB_mem

/-- The `t₃` rows: each `t₂`-state's own conditional on `b₂`.
Source: [[radical]] `s5`
Kind: D
Fidelity: exact -/
def r3 : Fin 4 → Fin 8 → ℝ :=
  ![![3 / 4, 0, 0, 0, 1 / 4, 0, 0, 0], ![0, 1 / 4, 0, 0, 0, 3 / 4, 0, 0],
    ![0, 0, 3 / 4, 0, 0, 0, 1 / 4, 0], ![0, 0, 0, 1 / 4, 0, 0, 0, 3 / 4]]

/-- The `t₃` rows are distributions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem r3_mem : ∀ k, r3 k ∈ stdSimplex ℝ (Fin 8) := by
  intro k
  fin_cases k <;>
    exact simplex8 _ (fun i => by fin_cases i <;> norm_num [r3])
      (by simp [Fin.sum_univ_eight, r3]; norm_num)

/-- The `t₃` frame: `(A,a)`-atoms `{0, 4}`, `(A,b)` `{1, 5}`, `(B,a)` `{2, 6}`, `(B,b)` `{3, 7}`.
Source: [[radical]] `s5`
Kind: D
Fidelity: exact -/
def F₃ : Frame (Fin 8) where
  P := ![r3 0, r3 1, r3 2, r3 3, r3 0, r3 1, r3 2, r3 3]
  P_mem := fun w => by
    fin_cases w <;> first | exact r3_mem 0 | exact r3_mem 1 | exact r3_mem 2 | exact r3_mem 3

/-- `φ = {0, 1, 2, 3}` (the atoms with `φ = 1`).
Source: [[radical]] `s5`
Kind: D
Fidelity: exact -/
abbrev φ5 : Finset (Fin 8) := {0, 1, 2, 3}

/-- The `t₂` announcements: both states give `φ` probability `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_ρ_φ5 : mass ρA φ5 = 1 / 2 ∧ mass ρB φ5 = 1 / 2 := by
  simp only [mass, φ5, sum_insert, mem_insert, mem_singleton, Fin.reduceEq, or_self,
    not_false_eq_true, or_false, false_or, sum_singleton, ρA, ρB, Matrix.cons_val]
  norm_num

/-- The `t₃` announcements: `3/4` on the `a`-atoms, `1/4` on the `b`-atoms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_r3_φ5 : mass (r3 0) φ5 = 3 / 4 ∧ mass (r3 1) φ5 = 1 / 4 ∧ mass (r3 2) φ5 = 3 / 4 ∧
    mass (r3 3) φ5 = 1 / 4 := by
  simp only [mass, φ5, sum_insert, mem_insert, mem_singleton, Fin.reduceEq, or_self,
    not_false_eq_true, or_false, false_or, sum_singleton, r3, Matrix.cons_val]
  norm_num

/-- **Step one holds in value form** for `φ`: `π(φ | A) = 1/2 = ρ_A(φ)` and
`π(φ | B) = 1/2 = ρ_B(φ)`.
Source: [[radical]] Theorem I5.6(c) l. 175; `s5` ("step-1 value-form holds")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem s5_step1_valueReflectsOn : ValueReflectsOn π5 F₂ φ5 := by
  intro c
  rw [mass_inter_valCell, mass_valCell]
  simp only [φ5, sum_insert, mem_insert, mem_singleton, Fin.reduceEq, or_self,
    not_false_eq_true, or_false, false_or, sum_singleton, Fin.sum_univ_eight, F₂, Matrix.cons_val,
    mass_ρ_φ5.1, mass_ρ_φ5.2, s5_vals]
  split_ifs <;> (try subst_vars) <;> norm_num at *

/-- `ρ_A` is value-reflective for `φ` toward `F₃`.
Source: [[radical]] `s5`
Kind: L
Fidelity: n/a -/
theorem ρA_valueReflectsOn : ValueReflectsOn ρA F₃ φ5 := by
  intro c
  rw [mass_inter_valCell, mass_valCell]
  simp only [φ5, sum_insert, mem_insert, mem_singleton, Fin.reduceEq, or_self,
    not_false_eq_true, or_false, false_or, sum_singleton, Fin.sum_univ_eight, F₃, Matrix.cons_val,
    mass_r3_φ5.1, mass_r3_φ5.2.1, mass_r3_φ5.2.2.1, mass_r3_φ5.2.2.2, s5_vals]
  split_ifs <;> (try subst_vars) <;> norm_num at *

/-- `ρ_B` is value-reflective for `φ` toward `F₃`.
Source: [[radical]] `s5`
Kind: L
Fidelity: n/a -/
theorem ρB_valueReflectsOn : ValueReflectsOn ρB F₃ φ5 := by
  intro c
  rw [mass_inter_valCell, mass_valCell]
  simp only [φ5, sum_insert, mem_insert, mem_singleton, Fin.reduceEq, or_self,
    not_false_eq_true, or_false, false_or, sum_singleton, Fin.sum_univ_eight, F₃, Matrix.cons_val,
    mass_r3_φ5.1, mass_r3_φ5.2.1, mass_r3_φ5.2.2.1, mass_r3_φ5.2.2.2, s5_vals]
  split_ifs <;> (try subst_vars) <;> norm_num at *

/-- **Step two holds in value form by each `t₂`-state's lights**: `ρ_A` and `ρ_B` are
value-reflective for `φ` toward `F₃` (each `t₃` row is the state's own conditional on `b₂`).
Source: [[radical]] Theorem I5.6(c) l. 175; `s5` ("each `ρ` is value-reflective toward `P_2`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem s5_step2_valueReflectsOn : ∀ ρ ∈ F₂.cands π5, ValueReflectsOn ρ F₃ φ5 := by
  intro ρ hρ
  obtain ⟨w, _, rfl⟩ := Frame.mem_cands.1 hρ
  have hrow : F₂.P w = ρA ∨ F₂.P w = ρB := by fin_cases w <;> simp [F₂]
  rcases hrow with h | h <;> rw [h]
  · exact ρA_valueReflectsOn
  · exact ρB_valueReflectsOn

/-- **The composite fails**: `π(φ ∩ {P₃(φ) = 3/4}) = 5/16 ≠ 3/8 = (3/4) · π({P₃(φ) = 3/4})` —
both `(A,a)` and `(B,a)` announce `3/4`.
Source: [[radical]] Theorem I5.6(c) l. 175 ("`P_{t₁}(φ | cell(A,a)) = 1/2 ≠ 3/4`"); `s5`
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem s5_composite_fails : ¬ ValueReflectsOn π5 F₃ φ5 := by
  intro h
  have := h (3 / 4)
  rw [mass_inter_valCell, mass_valCell] at this
  simp only [φ5, sum_insert, mem_insert, mem_singleton, Fin.reduceEq, or_self,
    not_false_eq_true, or_false, false_or, sum_singleton, Fin.sum_univ_eight, F₃, Matrix.cons_val,
    mass_r3_φ5.1, mass_r3_φ5.2.1, mass_r3_φ5.2.2.1, mass_r3_φ5.2.2.2, s5_vals] at this
  norm_num at this

/-- **The function-form hypothesis genuinely fails at step one**: `π` does not reflect `F₂`
(on branch `A`, `π(· | A)` is uniform while `ρ_A` is not).
Source: [[radical]] `s5` ("step-1 function-form `P0(.|b1=A) == rho_A`: False")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem s5_not_reflects : ¬ Reflects π5 F₂ := by
  intro h
  have hc : F₂.P 0 ∈ F₂.cands π5 := F₂.P_mem_cands (by norm_num [π5])
  have h0 := h _ hc 0
  have hind : ind (F₂.cell (F₂.P 0)) 0 = 1 := by simp [ind, F₂.mem_cell_self]
  rw [hind, mul_one] at h0
  have hsub : ({0, 1, 4, 5} : Finset (Fin 8)) ⊆ F₂.cell (F₂.P 0) := by
    intro v hv
    simp only [mem_insert, mem_singleton] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> simp [Frame.mem_cell, F₂, Matrix.cons_val]
  have hle : mass π5 {0, 1, 4, 5} ≤ mass π5 (F₂.cell (F₂.P 0)) :=
    mass_mono (fun w => by fin_cases w <;> norm_num [π5]) hsub
  have hm : mass π5 {0, 1, 4, 5} = 1 / 2 := by
    simp only [mass, sum_insert, mem_insert, mem_singleton, Fin.reduceEq, or_self,
      not_false_eq_true, or_false, false_or, sum_singleton, π5, Matrix.cons_val]
    norm_num
  rw [show F₂.P 0 0 = 3 / 8 from rfl, show π5 0 = 1 / 8 from rfl] at h0
  rw [hm] at hle
  norm_num at h0
  linarith

/-- **T7's negative half, assembled.** Value form at both steps (`L₁₂ = L₂₃ = Ω`, in exactly the
sense `valueReflectsOn_compose` uses at step two), function form failing at step one, and the
composite failing: legitimacy composes only at function-form grade. Two disclosures (audit r1):
the step-one value form is inhabited degenerately — both `t₂`-rows announce `φ` at `1/2`, so the
step-one value cell is `univ` and `ValueReflectsOn π5 F₂ φ5` is the single identity
`π5(φ5) = 1/2`; step two is non-degenerate (cells `3/4`, `1/4`). And the composite failure
shown is the *value-form* cell `5/16 ≠ 3/8` (`π(φ | P₃(φ) = 3/4) = 5/8 ≠ 3/4` over the merged
`{(A,a),(B,a)}` cell); radical's own sentence quotes the function-form cell
`P(φ | cell(A,a)) = 1/2 ≠ 3/4` — both refute, the number here is not the note's.
Source: [[radical]] Theorem I5.6(c) l. 175; [[joint-final]] Prop 7 l. 128; [[joint]] P.8 l. 217
Kind: N+
Fidelity: exact (for the negative claim; step-one cell trivial, as disclosed)
Hyps: (a) none -/
theorem s5_value_form_does_not_compose :
    ValueReflectsOn π5 F₂ φ5 ∧ (∀ ρ ∈ F₂.cands π5, ValueReflectsOn ρ F₃ φ5) ∧
      ¬ Reflects π5 F₂ ∧ ¬ ValueReflectsOn π5 F₃ φ5 :=
  ⟨s5_step1_valueReflectsOn, s5_step2_valueReflectsOn, s5_not_reflects, s5_composite_fails⟩

end

end Cleanroom.Corrigibility.CorrReflectFrames.Witnesses
