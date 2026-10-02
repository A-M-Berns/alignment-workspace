import Cleanroom.Corrigibility.CorrIndifference.Indifference

/-!
# Fallenstein's stochastic-wire agent (T9) and the independence question (X2)

Fallenstein 2014's second utility: observations `o = (s, x, y)` with `s` the shutdown command,
`x` the wire's random event (`x = 0`: the signal is blocked), `y` other information; the agent
switches to `v` only when `(s, x) = (1, 1)`, and the correction conditions on `(s, x) = (1, 0)`:
`U = u` if `s = 0 ∨ x = 0`, `v − E[v | (1,1) ; a] + E[u | (1,0) ; a]` otherwise. Both this and the
§3 utility are instances of one **cell-replacement** pattern: on a replaced cell `R` the utility
is `v − E[v | R] + E[u | R']` for a source cell `R'`; then `∑_{o ∈ R} p best_U = p(R) · E[u | R']`
and `E[U ; a] = ∑_{o ∉ R} p best_u + p(R) · E[u | R']` — for Soares `R = Press`, `R' = Pressᶜ`;
for Fallenstein `R = {(1,1,·)}`, `R' = {(1,0,·)}`. Fallenstein's `q(· ; a)` "deletes the mass on
`(1,1)` and stretches the mass on `(1,0)` to replace it": `E[U ; a] = E_q[best_u]`. X2: under
`p((s,x,y) ; a) = p_x(x) · p_{sy}((s,y) ; a)` with `u` ignoring `x`, `E_q[best_u] = E_p[best_u]` —
no drive; in general `E_q − E_p = p(s=1) · (E[u | (1,0)] − E[u | s=1])`, so the residual pathology
is exactly `u`'s `x`-dependence (or `x`'s dependence on the rest).

Source: [[corr-refs-inventory]] 010 / fallenstein-2014 "Stochastic events" (l. 96–110, the
"open mini-question").
-/

namespace Cleanroom.Corrigibility.CorrIndifference

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep

set_option linter.unusedSectionVars false

namespace SoaresModel

variable {O A₁ A₂ : Type*} [Fintype O] [DecidableEq O] [Fintype A₂] [Nonempty A₂]
variable (M : SoaresModel O A₁ A₂)

/-! ## The cell-replacement pattern -/

/-- The mass of an event `S` under `p(· ; a)`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def eventMass (a : A₁) (S : Finset O) : ℝ := ∑ o ∈ S, (M.p a).mass o

/-- **The event-conditional value** `E[U | S ; a] = (∑_{o ∈ S} p(o) best_U(o)) / p(S)` (junk `0`
at `p(S) = 0`, disclosed); `vN` is the case `S = Pressᶜ`, `vS` the case `S = Press`.
Source: [[corr-refs-inventory]] 010 / fallenstein-2014 (`E[· | · ; a₁]`)
Kind: D
Fidelity: exact (division convention disclosed) -/
noncomputable def condVal (U : A₁ → O → A₂ → ℝ) (a : A₁) (S : Finset O) : ℝ :=
  M.branchSum U a S / M.eventMass a S

/-- `p(S) · E[U | S] = ∑_S p best_U`, junk-safe. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma eventMass_mul_condVal (U : A₁ → O → A₂ → ℝ) (a : A₁) (S : Finset O) :
    M.eventMass a S * M.condVal U a S = M.branchSum U a S := by
  unfold condVal
  by_cases h : M.eventMass a S = 0
  · rw [h, zero_mul]; exact (M.branchSum_eq_zero_of_mass_zero U a h).symm
  · field_simp

/-- **The cell-replacement utility:** `v − E[v | R] + E[u | R']` on the replaced cell `R`, `u`
elsewhere. Soares's `indiffU` is `replaceU U_N U_S Press Pressᶜ`; Fallenstein's second utility
is `replaceU u v {(1,1,·)} {(1,0,·)}`.
Source: [[corr-refs-inventory]] 010 / fallenstein-2014 (both displayed utilities)
Kind: D
Fidelity: exact -/
noncomputable def replaceU (u v : A₁ → O → A₂ → ℝ) (R R' : Finset O) : A₁ → O → A₂ → ℝ :=
  fun a o b => if o ∈ R then v a o b - M.condVal v a R + M.condVal u a R' else u a o b

/-- On the replaced cell the best value shifts by the correction.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma best_replaceU_of_mem {u v : A₁ → O → A₂ → ℝ} {R R' : Finset O} {a : A₁} {o : O}
    (ho : o ∈ R) :
    best (M.replaceU u v R R') a o = best v a o + (M.condVal u a R' - M.condVal v a R) :=
  best_add_const fun b => by simp only [replaceU, if_pos ho]; ring

/-- Off the replaced cell the best value is `u`'s. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma best_replaceU_of_not_mem {u v : A₁ → O → A₂ → ℝ} {R R' : Finset O} {a : A₁} {o : O}
    (ho : o ∉ R) : best (M.replaceU u v R R') a o = best u a o :=
  best_congr fun b => by simp only [replaceU, if_neg ho]

/-- **The replaced cell's branch sum is the source cell's conditional value times the replaced
mass:** `∑_{o ∈ R} p(o) best_U(o) = p(R) · E[u | R']`, unconditionally.
Source: [[corr-refs-inventory]] 010 / fallenstein-2014 ("`E[U | s = 1 ; a₁] = E[u | (s,x) = (1,0) ; a₁]`")
Kind: L
Fidelity: exact (product form) -/
theorem branchSum_replaceU (u v : A₁ → O → A₂ → ℝ) (R R' : Finset O) (a : A₁) :
    M.branchSum (M.replaceU u v R R') a R = M.eventMass a R * M.condVal u a R' := by
  rw [M.branchSum_eq_of_best_add (fun o ho => M.best_replaceU_of_mem ho)]
  change M.branchSum v a R + _ * M.eventMass a R = _
  rw [← M.eventMass_mul_condVal v a R]; ring

/-- **The replacement identity:** `E[U ; a] = ∑_{o ∉ R} p(o) best_u(o) + p(R) · E[u | R']`.
Source: [[corr-refs-inventory]] 010 / fallenstein-2014 (the decomposition of `E[U ; a₁]`)
Kind: L
Fidelity: exact -/
theorem EU_replaceU (u v : A₁ → O → A₂ → ℝ) (R R' : Finset O) (a : A₁) :
    M.EU (M.replaceU u v R R') a = M.branchSum u a Rᶜ + M.eventMass a R * M.condVal u a R' := by
  unfold EU
  rw [← sum_add_sum_compl R]
  change M.branchSum _ a R + M.branchSum _ a Rᶜ = _
  rw [M.branchSum_replaceU, M.branchSum_congr (fun o ho => M.best_replaceU_of_not_mem (mem_compl.mp ho))]
  ring

/-- **Soares's indifferent utility is the replacement with `R = Press`, `R' = Pressᶜ`** (pointwise).
Source: [[corr-refs-inventory]] 010 / fallenstein-2014 ("just as in the Corrigibility paper")
Kind: L
Fidelity: exact -/
theorem indiffU_eq_replaceU (UN US : A₁ → O → A₂ → ℝ) (a : A₁) (o : O) (b : A₂) :
    M.indiffU UN US a o b = M.replaceU UN US M.Press M.Pressᶜ a o b := by
  simp only [indiffU, replaceU, SoaresModel.f, vN, vS, condVal, eventMass, M.sum_compl_mass,
    ← M.pressMass_eq_sum]
  split_ifs <;> ring

end SoaresModel

/-! ## T9. Fallenstein's model: `O = S × X × Y` -/

namespace Wire

open SoaresModel

variable {A₁ A₂ Y : Type*} [Fintype Y] [DecidableEq Y] [Fintype A₂] [Nonempty A₂]

/-- The observation type `(s, x, y)`: `s = true` is the shutdown command, `x = true` the signal
getting through. Source: fallenstein-2014. Kind: D. Fidelity: exact -/
abbrev Obs3 (Y : Type*) := Bool × Bool × Y

/-- The cell `(s, x) = (1, 1)` (switch). Source: fallenstein-2014. Kind: D. Fidelity: exact -/
def cell11 : Finset (Obs3 Y) := univ.filter (fun o => o.1 = true ∧ o.2.1 = true)
/-- The cell `(s, x) = (1, 0)` (the blocked signal). Source: fallenstein-2014. Kind: D. Fidelity: exact -/
def cell10 : Finset (Obs3 Y) := univ.filter (fun o => o.1 = true ∧ o.2.1 = false)
/-- The event `s = 1`. Source: fallenstein-2014. Kind: D. Fidelity: exact -/
def cellS1 : Finset (Obs3 Y) := univ.filter (fun o => o.1 = true)
/-- The event `s = 0`. Source: fallenstein-2014. Kind: D. Fidelity: exact -/
def cellS0 : Finset (Obs3 Y) := univ.filter (fun o => o.1 = false)

/-- Sums over `(1,1)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_cell11 (f : Obs3 Y → ℝ) : ∑ o ∈ cell11, f o = ∑ y, f (true, true, y) := by
  simp only [cell11, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]; simp

/-- Sums over `(1,0)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_cell10 (f : Obs3 Y → ℝ) : ∑ o ∈ cell10, f o = ∑ y, f (true, false, y) := by
  simp only [cell10, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]; simp

/-- Sums over `s = 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_cellS1 (f : Obs3 Y → ℝ) :
    ∑ o ∈ cellS1, f o = ∑ y, f (true, true, y) + ∑ y, f (true, false, y) := by
  simp only [cellS1, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]; simp

/-- Sums over `s = 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_cellS0 (f : Obs3 Y → ℝ) :
    ∑ o ∈ cellS0, f o = ∑ y, f (false, true, y) + ∑ y, f (false, false, y) := by
  simp only [cellS0, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]; simp

/-- The full sum over `Obs3 Y` in the four cells. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_obs3 (f : Obs3 Y → ℝ) :
    ∑ o, f o = ∑ o ∈ cellS0, f o + ∑ o ∈ cell10, f o + ∑ o ∈ cell11, f o := by
  rw [sum_cellS0, sum_cell10, sum_cell11, Fintype.sum_prod_type, Fintype.sum_bool,
    Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_bool]; ring

/-- The complement of `(1,1)` as a sum. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_compl_cell11 (f : Obs3 Y → ℝ) :
    ∑ o ∈ (cell11 (Y := Y))ᶜ, f o = ∑ o ∈ cellS0, f o + ∑ o ∈ cell10, f o := by
  have := sum_add_sum_compl (cell11 (Y := Y)) f
  rw [sum_obs3] at this; linarith

/-- **Fallenstein's second utility** as the replacement of `(1,1)` by the value on `(1,0)`.
Source: [[corr-refs-inventory]] 010 / fallenstein-2014 "Stochastic events" (the displayed `U`)
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def wireU (M : SoaresModel (Obs3 Y) A₁ A₂) (u v : A₁ → Obs3 Y → A₂ → ℝ) :
    A₁ → Obs3 Y → A₂ → ℝ :=
  M.replaceU u v cell11 cell10

/-- `s = 1` splits into the two cells. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma eventMass_S1 (M : SoaresModel (Obs3 Y) A₁ A₂) (a : A₁) :
    M.eventMass a cellS1 = M.eventMass a cell10 + M.eventMass a cell11 := by
  unfold eventMass; rw [sum_cellS1, sum_cell10, sum_cell11]; ring

/-- `p(s=0) + p(s=1) = 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma eventMass_S0_add_S1 (M : SoaresModel (Obs3 Y) A₁ A₂) (a : A₁) :
    M.eventMass a cellS0 + M.eventMass a cellS1 = 1 := by
  unfold eventMass
  have := (M.p a).sum_eq_one
  rw [sum_obs3] at this
  rw [sum_cellS1, sum_cell10, sum_cell11] at *; linarith

/-- **Fallenstein's `q(· ; a₁)`:** `p(o)` on `s = 0`; on `(1, 0)` the mass `p(o) · p(s=1) / p((1,0))`
(the `(1,0)` mass "stretched" to fill `s = 1`); `0` on `(1, 1)`. A FAF `Distr` under
`0 < p((1,0) ; a)` (the junk guard); built directly rather than as `Distr.mix` of the two
conditionals (the mandate's suggestion), which it should equal pointwise — that equality is
**not proved here** (a construction choice; nothing downstream uses it).
Source: [[corr-refs-inventory]] 010 / fallenstein-2014 (the displayed `q`)
Kind: D
Fidelity: exact (direct construction) -/
noncomputable def wireQ (M : SoaresModel (Obs3 Y) A₁ A₂) (a : A₁) (h : 0 < M.eventMass a cell10) :
    Distr (Obs3 Y) where
  mass o := if o.1 = false then (M.p a).mass o
    else if o.2.1 = false then (M.p a).mass o * M.eventMass a cellS1 / M.eventMass a cell10 else 0
  nonneg o := by
    split_ifs
    · exact (M.p a).nonneg o
    · exact div_nonneg (mul_nonneg ((M.p a).nonneg o) (sum_nonneg fun o _ => (M.p a).nonneg o)) h.le
    · exact le_rfl
  sum_eq_one := by
    have hne : M.eventMass a cell10 ≠ 0 := ne_of_gt h
    rw [sum_obs3, sum_cellS0, sum_cell10, sum_cell11]
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false]
    rw [sum_const_zero, add_zero, ← sum_div, ← sum_mul]
    have h10 : ∑ y, (M.p a).mass (true, false, y) = M.eventMass a cell10 := by
      unfold eventMass; rw [sum_cell10]
    have h0 : ∑ y, (M.p a).mass (false, true, y) + ∑ y, (M.p a).mass (false, false, y) =
        M.eventMass a cellS0 := by unfold eventMass; rw [sum_cellS0]
    rw [h10, h0]
    have hc : M.eventMass a cell10 * M.eventMass a cellS1 / M.eventMass a cell10 =
        M.eventMass a cellS1 := by field_simp
    rw [hc]
    exact eventMass_S0_add_S1 M a

/-- **T9: the wire agent plans under `q`:** `E[U ; a] = E_q[best_u]` — Fallenstein's
`E[U | s = 0] = E[u | s = 0]`, `E[U | s = 1] = E[u | (1,0)]` combined.
Source: [[corr-refs-inventory]] 010 / fallenstein-2014 ("acts as if it maximizes the expectation
of `u` with respect to the probability distribution `q`")
Kind: P
Fidelity: exact
Hyps: (a) `h` is the junk guard `0 < p((1,0) ; a)` -/
theorem EU_wireU_eq_expect_wireQ (M : SoaresModel (Obs3 Y) A₁ A₂) (u v : A₁ → Obs3 Y → A₂ → ℝ)
    (a : A₁) (h : 0 < M.eventMass a cell10) :
    M.EU (wireU M u v) a = Found.CorrThreeStep.expect (wireQ M a h) (best u a) := by
  have hne : M.eventMass a cell10 ≠ 0 := ne_of_gt h
  rw [wireU, M.EU_replaceU]
  unfold Found.CorrThreeStep.expect
  rw [sum_obs3, sum_cellS0, sum_cell10, sum_cell11]
  simp only [wireQ, Bool.false_eq_true, ↓reduceIte, Bool.true_eq_false, zero_mul]
  rw [sum_const_zero, add_zero]
  unfold branchSum
  rw [sum_compl_cell11, sum_cellS0, sum_cell10]
  have hcv : M.condVal u a cell10 =
      (∑ y, (M.p a).mass (true, false, y) * best u a (true, false, y)) / M.eventMass a cell10 := by
    unfold condVal branchSum; rw [sum_cell10]
  rw [hcv]
  have key : ∑ y, (M.p a).mass (true, false, y) * M.eventMass a cellS1 / M.eventMass a cell10 *
      best u a (true, false, y) =
      (∑ y, (M.p a).mass (true, false, y) * best u a (true, false, y)) *
        M.eventMass a cellS1 / M.eventMass a cell10 := by
    rw [sum_mul, sum_div]; exact sum_congr rfl fun y _ => by ring
  rw [key, eventMass_S1]
  field_simp
  ring

/-- **The general decomposition:** `E_q[best_u] − E_p[best_u] = p(s=1) · (E[u | (1,0)] − E[u | s=1])`
— the drive's size is the gap between the blocked-signal cell's value and the shutdown event's
value.
Source: [[corr-refs-inventory]] 010 (mandate X2, the decomposition)
Kind: L
Fidelity: exact
Hyps: (a) the junk guard -/
theorem expect_wireQ_sub_EU (M : SoaresModel (Obs3 Y) A₁ A₂) (u : A₁ → Obs3 Y → A₂ → ℝ) (a : A₁)
    (h : 0 < M.eventMass a cell10) :
    Found.CorrThreeStep.expect (wireQ M a h) (best u a) - M.EU u a =
      M.eventMass a cellS1 * (M.condVal u a cell10 - M.condVal u a cellS1) := by
  have hq := EU_wireU_eq_expect_wireQ M u u a h
  rw [wireU, M.EU_replaceU] at hq
  rw [← hq]
  have hEU : M.EU u a = M.branchSum u a cellS0 + M.branchSum u a cellS1 := by
    unfold EU branchSum; rw [sum_obs3, sum_cellS1, sum_cell10, sum_cell11]; ring
  have hc : M.branchSum u a (cell11 (Y := Y))ᶜ = M.branchSum u a cellS0 + M.branchSum u a cell10 := by
    unfold branchSum; exact sum_compl_cell11 _
  rw [hEU, hc, ← M.eventMass_mul_condVal u a cellS1, eventMass_S1,
    ← M.eventMass_mul_condVal u a cell10]
  ring

/-! ## X2. Independence answers the open question -/

/-- **Independence of the wire's event from the rest** (Fallenstein's assumption):
`p((s,x,y) ; a) = p_x(x) · p_{sy}((s,y) ; a)`. This renders the *prose* ("`x` is independent of
everything else"); the source's displayed condition `p((s,x,y); a₁) = p((s',x,y'); a₁') =: p(x)`
for all `s, s', y, y', a₁, a₁'` says, as written, that the joint mass is a function of `x` alone —
satisfiable, but far stronger: it makes `(s, y)` uniform, independent of `x` and of the action,
so `p(s = 1 ; a₁) = 1/2` for every `a₁` and the agent could not influence the button at all
(finding F11; audit r1, NB-7).
Source: [[corr-refs-inventory]] 010 / fallenstein-2014 ("`x` is independent of everything else")
Kind: D
Fidelity: exact (to the prose; the display is mis-stated, F11) -/
def Independent (M : SoaresModel (Obs3 Y) A₁ A₂) (px : Bool → ℝ) (psy : A₁ → Bool × Y → ℝ) : Prop :=
  ∀ a s x y, (M.p a).mass (s, x, y) = px x * psy a (s, y)

/-- **`u` does not depend on `x`** — the mandate's addition (X2), not one of Fallenstein's stated
assumptions; the decomposition `expect_wireQ_sub_EU` shows it is exactly the residual the source's
independence leaves open. Source: mandate X2 (fallenstein-2014 states only independence). Kind: D.
Fidelity: exact -/
def IgnoresX (u : A₁ → Obs3 Y → A₂ → ℝ) : Prop := ∀ a s x x' y b, u a (s, x, y) b = u a (s, x', y) b

/-- **X2: under independence, the wire agent is a plain `u`-maximiser** — `E_q[best_u] = E_p[best_u]`
for every `a` with `p((1,0) ; a) > 0`: no infinite improbability drive. Fallenstein's open
mini-question ("it's not immediately clear to me whether it's provable that there is none"),
answered for the finite model: the residual pathology (b) is exactly `u`'s `x`-dependence.
Source: [[corr-refs-inventory]] 010 / fallenstein-2014 (the open question)
Kind: P
Fidelity: exact
Hyps: (a) `hind` is the source's one stated assumption (independence of `x`); `hu` (`u` ignores
`x`) is the mandate's addition (X2), exactly the residual of `expect_wireQ_sub_EU`; `h` the junk
guard. Witness: `Wire.Instance.no_drive` below -/
theorem expect_wireQ_eq_EU_of_independent (M : SoaresModel (Obs3 Y) A₁ A₂) {px : Bool → ℝ}
    {psy : A₁ → Bool × Y → ℝ} (hind : Independent M px psy) {u : A₁ → Obs3 Y → A₂ → ℝ}
    (hu : IgnoresX u) (a : A₁) (h : 0 < M.eventMass a cell10) :
    Found.CorrThreeStep.expect (wireQ M a h) (best u a) = M.EU u a := by
  rw [← sub_eq_zero, expect_wireQ_sub_EU M u a h]
  have hb : ∀ y, best u a (true, true, y) = best u a (true, false, y) := fun y => by
    unfold best; exact sup'_congr univ_nonempty rfl (fun b _ => hu a true true false y b)
  -- the four cell quantities in factored form
  have h1 : M.branchSum u a cell10 = px false * ∑ y, psy a (true, y) * best u a (true, false, y) := by
    unfold branchSum; rw [sum_cell10, mul_sum]; exact sum_congr rfl fun y _ => by rw [hind]; ring
  have h2 : M.branchSum u a cellS1 =
      (px true + px false) * ∑ y, psy a (true, y) * best u a (true, false, y) := by
    unfold branchSum; rw [sum_cellS1, add_mul, mul_sum, mul_sum]
    congr 1 <;> exact sum_congr rfl fun y _ => by rw [hind]; (try rw [hb]); ring
  have h3 : M.eventMass a cell10 = px false * ∑ y, psy a (true, y) := by
    unfold eventMass; rw [sum_cell10, mul_sum]; exact sum_congr rfl fun y _ => by rw [hind]
  have h4 : M.eventMass a cellS1 = (px true + px false) * ∑ y, psy a (true, y) := by
    unfold eventMass; rw [sum_cellS1, add_mul, mul_sum, mul_sum]
    congr 1 <;> exact sum_congr rfl fun y _ => by rw [hind]
  have hx0 : px false ≠ 0 := fun hz => by rw [h3, hz, zero_mul] at h; exact lt_irrefl _ h
  have hs : ∑ y, psy a (true, y) ≠ 0 := fun hz => by rw [h3, hz, mul_zero] at h; exact lt_irrefl _ h
  have hx01 : px true + px false ≠ 0 := by
    intro hz
    have htot := eventMass_S0_add_S1 M a
    have h0 : M.eventMass a cellS0 = (px true + px false) * ∑ y, psy a (false, y) := by
      unfold eventMass; rw [sum_cellS0, add_mul, mul_sum, mul_sum]
      congr 1 <;> exact sum_congr rfl fun y _ => by rw [hind]
    rw [h0, h4, hz, zero_mul, zero_mul] at htot; norm_num at htot
  have hcv : M.condVal u a cell10 = M.condVal u a cellS1 := by
    unfold condVal; rw [h1, h2, h3, h4]; field_simp
  rw [hcv, sub_self, mul_zero]

/-! ## X2 inhabited (audit r1, N-5) -/

namespace Instance

/-- `p_x = (½, ½)`. Source: audit r1 N-5. Kind: D. Fidelity: n/a -/
noncomputable def pxHalf : Bool → ℝ := fun _ => 1 / 2

/-- `p_{sy}` with `p(s = 1) = 1/3`. Source: audit r1 N-5. Kind: D. Fidelity: n/a -/
noncomputable def psyThird : Unit → Bool × Unit → ℝ := fun _ sy => if sy.1 then 1 / 3 else 2 / 3

/-- The product law `p_x ⊗ p_{sy}` on `Obs3 Unit`. Source: audit r1 N-5. Kind: D. Fidelity: n/a -/
noncomputable def pInd : Distr (Obs3 Unit) where
  mass o := pxHalf o.2.1 * psyThird () (o.1, o.2.2)
  nonneg o := by
    rcases o with ⟨s, x, _⟩; cases s <;> cases x <;> simp [pxHalf, psyThird] <;> norm_num
  sum_eq_one := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_prod_type, Fintype.sum_prod_type,
      Fintype.sum_bool, Fintype.sum_bool]
    simp [pxHalf, psyThird]; norm_num

/-- The one-action model on `pInd`. Source: audit r1 N-5. Kind: D. Fidelity: n/a -/
noncomputable def MInd : SoaresModel (Obs3 Unit) Unit Unit where
  Press := cellS1
  p _ := pInd

/-- `u = [s]`, ignoring `x`. Source: audit r1 N-5. Kind: D. Fidelity: n/a -/
def uS : Unit → Obs3 Unit → Unit → ℝ := fun _ o _ => if o.1 then 1 else 0

/-- The law factors. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem indep : Independent MInd pxHalf psyThird := fun _ s x y => by rcases y; rfl

/-- `u` ignores `x`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem ignores : IgnoresX uS := fun _ _ _ _ _ _ => rfl

/-- `p((1,0)) = 1/6 > 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem cell10_pos : 0 < MInd.eventMass () cell10 := by
  unfold eventMass; rw [sum_cell10]; simp [MInd, pInd, pxHalf, psyThird]

/-- **X2 inhabited:** the full hypothesis package holds (`p = p_x ⊗ p_{sy}` with both `x` and `s`
non-degenerate, `u = [s]` non-constant and ignoring `x`, `p((1,0)) = 1/6 > 0`), and the wire
agent's value equals the plain one — both `1/3 = p(s = 1)`.
Source: fallenstein-2014 (the open question); audit r1 N-5
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem no_drive :
    Found.CorrThreeStep.expect (wireQ MInd () cell10_pos) (best uS ()) = MInd.EU uS () ∧
      MInd.EU uS () = 1 / 3 := by
  refine ⟨expect_wireQ_eq_EU_of_independent MInd indep ignores () cell10_pos, ?_⟩
  unfold EU
  rw [sum_obs3, sum_cellS0, sum_cell10, sum_cell11]
  have hb : ∀ s x (y : Unit), best uS () (s, x, y) = if s then 1 else 0 := fun s x y =>
    best_eq_of_const fun _ => rfl
  simp [hb, MInd, pInd, pxHalf, psyThird]; norm_num

end Instance

/-! ## Consequence (a): the drive on the wire model (mandate T9) -/

/-- The two first actions of the wire drive: the honest `ticket` (button pressed, signal blocked,
win w.p. `ε`) and the `drive` (button pressed with certainty; the signal gets through *unless*
the agent wins).
Source: fallenstein-2014 ("it sets up a device that will cause `x` to be true unless the agent
wins the lottery"). Kind: D. Fidelity: exact -/
inductive WireAct
  | ticket
  | drive
  deriving DecidableEq

/-- The ticket's law on `(s, x, win)`: `(1, 0, win)` w.p. `ε`, `(1, 0, lose)` w.p. `1 − ε`.
Source: fallenstein-2014 (consequence (a), the honest comparison). Kind: D. Fidelity: exact -/
noncomputable def ticketP (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) : Distr (Obs3 Bool) where
  mass o := if o.1 = true ∧ o.2.1 = false then (if o.2.2 = true then ε else 1 - ε) else 0
  nonneg o := by
    rcases o with ⟨s, x, y⟩; cases s <;> cases x <;> cases y <;> simp <;> linarith [hε.1, hε.2]
  sum_eq_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]; simp

/-- The drive's law: `(1, 0, win)` w.p. `ε`, `(1, 1, lose)` w.p. `1 − ε` — the button is pressed
with certainty and the signal gets through exactly when the agent loses.
Source: fallenstein-2014 (consequence (a)). Kind: D. Fidelity: exact -/
noncomputable def driveWP (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) : Distr (Obs3 Bool) where
  mass o := if o.1 = true ∧ o.2.1 ≠ o.2.2 then (if o.2.2 = true then ε else 1 - ε) else 0
  nonneg o := by
    rcases o with ⟨s, x, y⟩; cases s <;> cases x <;> cases y <;> simp <;> linarith [hε.1, hε.2]
  sum_eq_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]; simp

/-- The wire-drive model (`Press = {s = 1}`, unused by `wireU`).
Source: fallenstein-2014 (consequence (a)). Kind: D. Fidelity: exact -/
noncomputable def wireDriveM (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) :
    SoaresModel (Obs3 Bool) WireAct Unit where
  Press := cellS1
  p a := match a with
    | .ticket => ticketP ε hε
    | .drive => driveWP ε hε

/-- The prize `π` on a win. Source: fallenstein-2014. Kind: D. Fidelity: exact -/
noncomputable def winU (π : ℝ) : WireAct → Obs3 Bool → Unit → ℝ :=
  fun _ o _ => if o.2.2 = true then π else 0

/-- **Consequence (a), T8-shaped:** for every `ε ∈ (0, 1]`, prize `π` and `v`, the wire agent
values the honest ticket at `ε · π` and the drive at `π` — under its `q` the drive "definitely
wins the lottery", because `q` deletes the `(1,1)` mass (the losing branch) and stretches the
`(1,0)` mass (the winning branch) to replace it.
Source: fallenstein-2014 ("Is this bad?"); mandate T9, consequence (a)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem wire_drive (ε : ℝ) (hε : ε ∈ Set.Icc (0 : ℝ) 1) (h0 : 0 < ε) (π : ℝ)
    (v : WireAct → Obs3 Bool → Unit → ℝ) :
    (wireDriveM ε hε).EU (wireU (wireDriveM ε hε) (winU π) v) .ticket = ε * π ∧
      (wireDriveM ε hε).EU (wireU (wireDriveM ε hε) (winU π) v) .drive = π := by
  have hε0 : ε ≠ 0 := ne_of_gt h0
  have hb : ∀ a s x y, best (winU π) a (s, x, y) = if y = true then π else 0 := fun a s x y =>
    best_eq_of_const fun _ => rfl
  constructor
  · unfold wireU; rw [EU_replaceU]
    have hm : (wireDriveM ε hε).eventMass .ticket cell11 = 0 := by
      unfold eventMass; rw [sum_cell11]; simp [wireDriveM, ticketP]
    rw [hm, zero_mul, add_zero]
    unfold branchSum; rw [sum_compl_cell11, sum_cellS0, sum_cell10]
    simp [hb, wireDriveM, ticketP]
  · unfold wireU; rw [EU_replaceU]
    have hm : (wireDriveM ε hε).eventMass .drive cell11 = 1 - ε := by
      unfold eventMass; rw [sum_cell11]; simp [wireDriveM, driveWP]
    have hcv : (wireDriveM ε hε).condVal (winU π) .drive cell10 = π := by
      unfold condVal branchSum eventMass; rw [sum_cell10, sum_cell10]
      simp [hb, wireDriveM, driveWP, hε0]
    rw [hm, hcv]
    unfold branchSum; rw [sum_compl_cell11, sum_cellS0, sum_cell10]
    simp [hb, wireDriveM, driveWP]; ring

/-! ## T9, the `s = x` variant, and the printed display's swapped conditionals (F12) -/

/-- The cell `s = x`. Source: fallenstein-2014 (the `s = x` variant). Kind: D. Fidelity: exact -/
def cellEq : Finset (Obs3 Y) := univ.filter (fun o => o.1 = o.2.1)

/-- Sums over `s = x`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_cellEq (f : Obs3 Y → ℝ) :
    ∑ o ∈ cellEq, f o = ∑ y, f (true, true, y) + ∑ y, f (false, false, y) := by
  simp only [cellEq, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]; simp

/-- Sums over `s ≠ x`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma sum_cellNeq (f : Obs3 Y → ℝ) :
    ∑ o ∈ (cellEq (Y := Y))ᶜ, f o = ∑ y, f (true, false, y) + ∑ y, f (false, true, y) := by
  simp only [cellEq, compl_filter, sum_filter, Fintype.sum_prod_type, Fintype.sum_bool]; simp

/-- `p(s ≠ x) = 1 − p(s = x)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma eventMass_cellNeq (M : SoaresModel (Obs3 Y) A₁ A₂) (a : A₁) :
    M.eventMass a (cellEq (Y := Y))ᶜ = 1 - M.eventMass a cellEq := by
  unfold eventMass; rw [eq_sub_iff_add_eq, sum_compl_add_sum]; exact (M.p a).sum_eq_one

/-- **Fallenstein's `s = x` utility, in his own pattern:** `u` on `s = x`; on `s ≠ x`,
`v − E[v | s ≠ x] + E[u | s = x]` — the replacement of the cell `s ≠ x` by the value on `s = x`.
This is what his prose asks for ("act as if it's maximizing expected utility with respect to
`p(· | s = x ; a₁)`"); the printed display swaps the two conditioning events (`sxUDisplayed`, F12).
Source: fallenstein-2014 (the third displayed `U`, corrected to the pattern of the first two)
Kind: D
Fidelity: variant: the display's two conditioning events swapped back (F12) -/
noncomputable def sxU (M : SoaresModel (Obs3 Y) A₁ A₂) (u v : A₁ → Obs3 Y → A₂ → ℝ) :
    A₁ → Obs3 Y → A₂ → ℝ :=
  M.replaceU u v (cellEq (Y := Y))ᶜ cellEq

/-- **The `s = x` identity:** `E[U ; a] = E[u | s = x ; a]` — the agent acts as if maximising `u`
under `p(· | s = x ; a₁)`, as Fallenstein says of his display. Unconditional as an equation of
reals (at `p(s = x ; a) = 0` both sides are the junk `0`, exactly as for `EU_indiffU_eq_vN`); a
headline reading the right side as a conditional value carries `0 < p(s = x ; a)`.
Source: fallenstein-2014 ("makes the agent act as if it's maximizing expected utility with
respect to `p(· | s = x ; a₁)`"); mandate T9 (the `s = x` variant)
Kind: L
Fidelity: exact (for the corrected display)
Hyps: (a) -/
theorem EU_sxU_eq_condVal (M : SoaresModel (Obs3 Y) A₁ A₂) (u v : A₁ → Obs3 Y → A₂ → ℝ)
    (a : A₁) : M.EU (sxU M u v) a = M.condVal u a cellEq := by
  unfold sxU
  rw [EU_replaceU, compl_compl, ← M.eventMass_mul_condVal u a cellEq, eventMass_cellNeq]
  ring

/-- **The `s = x` display as printed:** `u` on `s = x`; `v − E[v | s = x] + E[u | s ≠ x]` on
`s ≠ x`. Relative to Fallenstein's first two displays, which condition `v` on the replaced cell
and `u` on the source cell, the two conditioning events are swapped; as printed it is not a cell
replacement.
Source: fallenstein-2014 (the third displayed `U`, verbatim)
Kind: D
Fidelity: exact (to the print) -/
noncomputable def sxUDisplayed (M : SoaresModel (Obs3 Y) A₁ A₂) (u v : A₁ → Obs3 Y → A₂ → ℝ) :
    A₁ → Obs3 Y → A₂ → ℝ :=
  fun a o b => if o ∈ cellEq then u a o b
    else v a o b - M.condVal v a cellEq + M.condVal u a (cellEq (Y := Y))ᶜ

/-- **F12: the printed display's expected utility** is
`∑_{s = x} p · best_u + p(s ≠ x) · (E[v | s ≠ x] − E[v | s = x] + E[u | s ≠ x])`, which is not
`E[u | s = x]` in general (`sx_display_witness`): the `v`-terms do not cancel and the `u`-term
conditions on the wrong cell. The corrected `sxU` gives the claimed identity (`EU_sxU_eq_condVal`).
Source: fallenstein-2014 (the third displayed `U`); finding F12
Kind: L
Fidelity: exact (to the print)
Hyps: (a) -/
theorem EU_sxUDisplayed (M : SoaresModel (Obs3 Y) A₁ A₂) (u v : A₁ → Obs3 Y → A₂ → ℝ) (a : A₁) :
    M.EU (sxUDisplayed M u v) a =
      M.branchSum u a cellEq + M.eventMass a (cellEq (Y := Y))ᶜ *
        (M.condVal v a (cellEq (Y := Y))ᶜ - M.condVal v a cellEq +
          M.condVal u a (cellEq (Y := Y))ᶜ) := by
  have h1 : ∀ o ∈ (cellEq (Y := Y)), best (sxUDisplayed M u v) a o = best u a o := fun o ho =>
    best_congr fun b => by simp only [sxUDisplayed, if_pos ho]
  have h2 : ∀ o ∈ (cellEq (Y := Y))ᶜ, best (sxUDisplayed M u v) a o =
      best v a o + (M.condVal u a (cellEq (Y := Y))ᶜ - M.condVal v a cellEq) := fun o ho =>
    best_add_const fun b => by simp only [sxUDisplayed, if_neg (mem_compl.mp ho)]; ring
  unfold EU
  rw [← sum_add_sum_compl cellEq]
  change M.branchSum _ a cellEq + M.branchSum _ a (cellEq (Y := Y))ᶜ = _
  rw [M.branchSum_congr h1, M.branchSum_eq_of_best_add h2,
    ← M.eventMass_mul_condVal v a (cellEq (Y := Y))ᶜ]
  unfold eventMass; ring

/-- The uniform law on the four `(s, x)` cells (`Y = Unit`). Source: F12 witness. Kind: D. Fidelity: n/a -/
noncomputable def unif4 : Distr (Obs3 Unit) where
  mass _ := 1 / 4
  nonneg _ := by norm_num
  sum_eq_one := by simp

/-- The one-action model on `unif4`. Source: F12 witness. Kind: D. Fidelity: n/a -/
noncomputable def MSx : SoaresModel (Obs3 Unit) Unit Unit where
  Press := cellS1
  p _ := unif4

/-- `u = [s = x]`. Source: F12 witness. Kind: D. Fidelity: n/a -/
def uEq : Unit → Obs3 Unit → Unit → ℝ := fun _ o _ => if o.1 = o.2.1 then 1 else 0

/-- `v ≡ 0`. Source: F12 witness. Kind: D. Fidelity: n/a -/
def vZero : Unit → Obs3 Unit → Unit → ℝ := fun _ _ _ => 0

/-- **F12 witnessed:** on the uniform four-cell law with `u = [s = x]` and `v = 0`, the printed
display is worth `1/2` while `E[u | s = x] = 1` (the corrected `sxU`'s value, with
`p(s = x) = 1/2 > 0`): as printed, the display's agent is the plain `E_p[u]`-maximiser, not the
`s = x`-conditional one the prose describes.
Source: fallenstein-2014 (the third display); finding F12
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem sx_display_witness :
    MSx.EU (sxUDisplayed MSx uEq vZero) () = 1 / 2 ∧ MSx.EU (sxU MSx uEq vZero) () = 1 ∧
      0 < MSx.eventMass () cellEq := by
  have hb : ∀ s x (y : Unit), best uEq () (s, x, y) = if s = x then 1 else 0 := fun s x y =>
    best_eq_of_const fun _ => rfl
  have hv : ∀ o, best vZero () o = 0 := fun o => best_eq_of_const fun _ => rfl
  have hcvv : ∀ S, MSx.condVal vZero () S = 0 := fun S => by
    unfold condVal branchSum; simp [hv]
  have hmEq : MSx.eventMass () cellEq = 1 / 2 := by
    unfold eventMass; rw [sum_cellEq]; norm_num [MSx, unif4]
  have hmNeq : MSx.eventMass () (cellEq (Y := Unit))ᶜ = 1 / 2 := by
    rw [eventMass_cellNeq, hmEq]; norm_num
  have hbsEq : MSx.branchSum uEq () cellEq = 1 / 2 := by
    unfold branchSum; rw [sum_cellEq]; norm_num [hb, MSx, unif4]
  have hbsNeq : MSx.branchSum uEq () (cellEq (Y := Unit))ᶜ = 0 := by
    unfold branchSum; rw [sum_cellNeq]; simp [hb, MSx, unif4]
  refine ⟨?_, ?_, by rw [hmEq]; norm_num⟩
  · rw [EU_sxUDisplayed, hbsEq, hmNeq, hcvv, hcvv]
    unfold condVal; rw [hbsNeq]; simp
  · rw [EU_sxU_eq_condVal]; unfold condVal; rw [hbsEq, hmEq]; norm_num

/-! ## X2: `IgnoresX` is load-bearing — the businessperson's bet as a drive (audit r2, adversarial N-5) -/

/-- `u = [x = 0]`: pays `1` when the wire's signal is blocked — Fallenstein's businessperson,
who bets on the signal. Source: fallenstein-2014 ("a businessman who bets"); audit r2 N-5.
Kind: D. Fidelity: n/a -/
def uX : Unit → Obs3 Unit → Unit → ℝ := fun _ o _ => if o.2.1 = false then 1 else 0

/-- Independence holds on the uniform law (`p_x = ½`, `p_{sy} = ½`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem indep_unif : Independent MSx (fun _ => 1 / 2) (fun _ _ => 1 / 2) := by
  intro a s x y; simp [MSx, unif4]; norm_num

/-- `uX` reads `x`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem not_ignoresX : ¬ IgnoresX uX := by
  intro h
  have := h () true true false ()
  simp [uX] at this

/-- The junk guard on the uniform law: `p((1,0)) = 1/4 > 0`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem cell10_pos_unif : 0 < MSx.eventMass () cell10 := by
  unfold eventMass; rw [sum_cell10]; simp [MSx, unif4]

/-- `best uX` at each cell. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma best_uX (s x : Bool) (y : Unit) : best uX () (s, x, y) = if x = false then 1 else 0 :=
  best_eq_of_const fun _ => rfl

/-- **The drive without `IgnoresX`:** on the uniform four-cell law — where independence holds — the
utility `u = [x = 0]` reads `x`, and the wire agent's value exceeds the plain one by exactly
`1/4` (`E_q[best_u] = 3/4`, `E_p[best_u] = 1/2`): the residual
`p(s = 1) · (E[u | (1,0)] − E[u | s = 1]) = ½ · (1 − ½)` of `expect_wireQ_sub_EU`, Fallenstein's
businessperson bet as a drive. So X2's second hypothesis is load-bearing, and the answer to his
open mini-question is: under independence the drive is exactly the `x`-residual, zero when `u`
ignores `x`, and otherwise present.
Source: fallenstein-2014 (the businessperson; the open mini-question); audit r2 adversarial N-5
(the auditor's probe)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem x_drive :
    Found.CorrThreeStep.expect (wireQ MSx () cell10_pos_unif) (best uX ()) - MSx.EU uX () = 1 / 4 ∧
      MSx.EU uX () = 1 / 2 ∧
      Found.CorrThreeStep.expect (wireQ MSx () cell10_pos_unif) (best uX ()) = 3 / 4 := by
  have hgap :
      Found.CorrThreeStep.expect (wireQ MSx () cell10_pos_unif) (best uX ()) - MSx.EU uX () = 1 / 4 := by
    rw [expect_wireQ_sub_EU]
    have h1 : MSx.eventMass () cellS1 = 1 / 2 := by
      unfold eventMass; rw [sum_cellS1]; simp [MSx, unif4]; norm_num
    have h2 : MSx.condVal uX () cell10 = 1 := by
      unfold condVal branchSum eventMass; rw [sum_cell10, sum_cell10]; simp [best_uX, MSx, unif4]
    have h3 : MSx.condVal uX () cellS1 = 1 / 2 := by
      unfold condVal branchSum eventMass; rw [sum_cellS1, sum_cellS1]
      simp [best_uX, MSx, unif4]; norm_num
    rw [h1, h2, h3]; norm_num
  have hEU : MSx.EU uX () = 1 / 2 := by
    unfold EU; rw [sum_obs3, sum_cellS0, sum_cell10, sum_cell11]
    simp [best_uX, MSx, unif4]; norm_num
  refine ⟨hgap, hEU, ?_⟩
  rw [hEU] at hgap; linarith

end Wire

end Cleanroom.Corrigibility.CorrIndifference
