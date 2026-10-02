import Cleanroom.Corrigibility.LegitNegDynamic.Dinkelbach

/-!
# Extension: D2's dichotomy under partial revelation — the crossing lemma and the threshold `σ̂ = 7/9`

Package `legit-neg-dynamic`, the required extension (mandate "Extension"; plan §0.4 rule 6; 065's
agenda). Sources: `clusters/D/NEGATIVES.md` D2(iii) (the `λ*` / `λ_I` dichotomy), instance A of
`d2_conditioning_dynamic.py`; no source states the family — it is this package's.

At a cell with two actions `x = 0`, `y = 1`, cell cdot values `n a` and legitimacy masses `d a`, the
verdict of the shifted value `n a − λ d a` as a function of `λ` flips exactly once, at
`λ̂ = (n x − n y)/(d x − d y)` (`crossing`); so the updateless verdict (at `λ*`) and the updateful one
(at `λ_C`) part iff `λ*` and `λ_C` lie on different sides of `λ̂` (`verdicts_part_of`,
`verdicts_agree_of_lt/gt`, ties spelled out). The family `d2Aσ σ` is instance A observed through a
signal of accuracy `σ ∈ [1/2, 1]` about the cell: the derived closed forms are `λ̂_C = 41/90` and
`λ* = 2/5` (both constant in `σ`), `λ_C(σ) = max ((3 + 2σ)/10, (30 − 21σ)/(100 − 90σ))`, and the
verdicts part exactly at **`σ̂ = 7/9`** (a tie there, strictly above it): an exact rational root,
not a bracketing interval.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.LegitNegDynamic

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem
  Cleanroom.Corrigibility.LegitNegPricing

/-! ### The crossing lemma -/

section Crossing

variable (n d : Fin 2 → ℚ)

/-- **`λ̂`**: the void grade at which the two actions' shifted values coincide,
`(n x − n y)/(d x − d y)` (junk `… / 0` when the masses coincide, excluded by hypothesis).
Source: mandate "Extension"
Kind: D
Fidelity: exact -/
noncomputable def lamHat : ℚ := (n 0 - n 1) / (d 0 - d 1)

/-- **The crossing lemma**: when `d y < d x`, the verdict of `a ↦ n a − λ d a` is `{x}` for
`λ < λ̂`, a tie at `λ = λ̂`, and `{y}` for `λ > λ̂`. (For `d x < d y` swap the roles of `x` and `y`.)
Source: mandate "Extension" (the crossing lemma)
Kind: P
Fidelity: exact
Hyps: (a) `d 1 < d 0` -/
theorem crossing (hd : d 1 < d 0) (lam : ℚ) :
    (argmax (fun a => n a - lam * d a) = {0} ↔ lam < lamHat n d) ∧
    (argmax (fun a => n a - lam * d a) = univ ↔ lam = lamHat n d) ∧
    (argmax (fun a => n a - lam * d a) = {1} ↔ lamHat n d < lam) := by
  have hpos : 0 < d 0 - d 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_zero_iff]; unfold lamHat; rw [lt_div_iff₀ hpos]
    constructor <;> intro h <;> nlinarith
  · rw [argmax_fin2_eq_univ_iff]; unfold lamHat; rw [eq_div_iff hpos.ne']
    constructor <;> intro h <;> linarith
  · rw [argmax_fin2_eq_one_iff]; unfold lamHat; rw [div_lt_iff₀ hpos]
    constructor <;> intro h <;> nlinarith

/-- **The verdicts part** when `λ₁ < λ̂ ≤ λ₂` (the `λ₂ = λ̂` case is a tie against a strict `{x}`).
Source: mandate "Extension"
Kind: C
Fidelity: exact
Hyps: (a) `d 1 < d 0` -/
theorem verdicts_part_of (hd : d 1 < d 0) {lam₁ lam₂ : ℚ} (h1 : lam₁ < lamHat n d)
    (h2 : lamHat n d ≤ lam₂) :
    argmax (fun a => n a - lam₁ * d a) ≠ argmax (fun a => n a - lam₂ * d a) := by
  rw [(crossing n d hd lam₁).1.2 h1]
  rcases lt_or_eq_of_le h2 with h2 | h2
  · rw [(crossing n d hd lam₂).2.2.2 h2]; decide
  · rw [(crossing n d hd lam₂).2.1.2 h2.symm]; decide

/-- **The verdicts agree** when both grades lie strictly below `λ̂` (both `{x}`) …
Source: mandate "Extension"
Kind: C
Fidelity: exact
Hyps: (a) `d 1 < d 0` -/
theorem verdicts_agree_of_lt (hd : d 1 < d 0) {lam₁ lam₂ : ℚ} (h1 : lam₁ < lamHat n d)
    (h2 : lam₂ < lamHat n d) :
    argmax (fun a => n a - lam₁ * d a) = argmax (fun a => n a - lam₂ * d a) := by
  rw [(crossing n d hd lam₁).1.2 h1, (crossing n d hd lam₂).1.2 h2]

/-- … or both strictly above it (both `{y}`).
Source: mandate "Extension"
Kind: C
Fidelity: exact
Hyps: (a) `d 1 < d 0` -/
theorem verdicts_agree_of_gt (hd : d 1 < d 0) {lam₁ lam₂ : ℚ} (h1 : lamHat n d < lam₁)
    (h2 : lamHat n d < lam₂) :
    argmax (fun a => n a - lam₁ * d a) = argmax (fun a => n a - lam₂ * d a) := by
  rw [(crossing n d hd lam₁).2.2.2 h1, (crossing n d hd lam₂).2.2.2 h2]

/-- The shifted verdict is the P3 verdict with the constant void grade: `argmax (P3 (W ≡ λ) 1 V) =
argmax (a ↦ P1 a − λ P(L | a))`.
Source: none: infrastructure (`P3_const_one_eq` + `argmax_add_const`)
Kind: L
Fidelity: n/a -/
lemma argmax_P3_const_eq_shifted {S A : Type} [Fintype S] [Fintype A] [DecidableEq A]
    (Q : Problem S A) (V : MenuVec S A) (lam : ℚ) :
    argmax (Q.P3 (fun _ _ _ => lam) 1 V) = argmax (fun a => Q.P1 V a - lam * Q.PL a) := by
  rw [argmax_congr (fun a => P3_const_one_eq Q V lam a)]
  exact argmax_add_const _ lam

end Crossing

/-! ### The family: instance A observed through a signal of accuracy `σ` -/

section Family

/-- The signal's correct reading of a state: `true` = "in `i₁`" (states `0`, `1`), `false` = "in
`i₂`" (state `2`).
Source: mandate "Extension"
Kind: D
Fidelity: exact -/
def sig : Fin 3 → Bool := fun s => decide (s ≠ 2)

/-- **Instance A with a signal of accuracy `σ ∈ [1/2, 1]`**: states `(s, b)` — `s` the state of
`d2A`, `b` the signal's reading — with prior `d2A.prior s · (σ if b = sig s else 1 − σ)`; legitimacy
and scores as in `d2A`. `σ = 1/2` is no information, `σ = 1` full revelation of the cell.
Source: mandate "Extension"
Kind: D
Fidelity: exact -/
def d2Aσ (σ : ℚ) (hσ0 : 1/2 ≤ σ) (hσ1 : σ ≤ 1) : Problem (Fin 3 × Bool) (Fin 2) where
  prior := fun p => d2A.prior p.1 * (if p.2 = sig p.1 then σ else 1 - σ)
  prior_nonneg := by
    rintro ⟨s, b⟩; apply mul_nonneg (d2A.prior_nonneg s); split_ifs <;> linarith
  prior_sum := by
    simp [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, d2A, sig]; ring
  leg := fun p a => d2A.leg p.1 a
  u := fun p a => d2A.u p.1 a

/-- The agent's cells: the two readings of the signal.
Source: mandate "Extension"
Kind: D
Fidelity: exact -/
def sigCell (b : Bool) : Finset (Fin 3 × Bool) := univ.filter fun p => p.2 = b

/-- The cell of a state.
Source: mandate "Extension"
Kind: D
Fidelity: exact -/
def sigCellOf (p : Fin 3 × Bool) : Finset (Fin 3 × Bool) := sigCell p.2

/-- `C₁`: the cell where the signal says `i₁`.
Source: mandate "Extension"
Kind: D
Fidelity: exact -/
def C1 : Finset (Fin 3 × Bool) := sigCell true

variable (σ : ℚ) (hσ0 : 1/2 ≤ σ) (hσ1 : σ ≤ 1)

/-- Each signal cell has mass `1/2`, for every `σ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sigCell_mass (b : Bool) : ∑ t ∈ sigCell b, (d2Aσ σ hσ0 hσ1).prior t = 1/2 := by
  unfold sigCell
  rw [Finset.sum_filter]
  cases b <;> simp [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, d2Aσ, d2A, sig] <;>
    ring

/-- The signal cells form a partition of `d2Aσ σ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sigCell_partition : IsPartition (d2Aσ σ hσ0 hσ1) sigCellOf where
  mem := by rintro ⟨s, b⟩; simp [sigCellOf, sigCell]
  cell := by
    rintro ⟨s, b⟩ ⟨t, b'⟩ h
    simp only [sigCellOf, sigCell, Finset.mem_filter, mem_univ, true_and] at h
    simp [sigCellOf, h]
  pos := by
    rintro ⟨s, b⟩; simp only [sigCellOf]; rw [sigCell_mass σ hσ0 hσ1]; norm_num

/-- `C1_pos`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma C1_pos : 0 < ∑ t ∈ C1, (d2Aσ σ hσ0 hσ1).prior t := by
  unfold C1; rw [sigCell_mass σ hσ0 hσ1]; norm_num

/-- **The cell's cdot values and masses**: at `C₁`, `n x = (3 + 2σ)/10`, `d x = 1`,
`n y = (30 − 21σ)/100`, `d y = (10 − 9σ)/10`.
Source: mandate "Extension" (derived)
Kind: L
Fidelity: exact -/
lemma C1_values :
    ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).P1 (S1 (d2Aσ σ hσ0 hσ1).u) 0 = (3 + 2 * σ) / 10 ∧
    ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).P1 (S1 (d2Aσ σ hσ0 hσ1).u) 1 = (30 - 21 * σ) / 100 ∧
    ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).PL 0 = 1 ∧
    ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).PL 1 = (10 - 9 * σ) / 10 := by
  have hmass : ∑ t ∈ C1, (d2Aσ σ hσ0 hσ1).prior t = 1/2 := by
    unfold C1; exact sigCell_mass σ hσ0 hσ1 true
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (simp only [Problem.P1, Problem.PL, Problem.mass, restrict_prior, restrict_leg, restrict_u,
      Problem.cellprior, hmass]
     simp [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_bool, C1, sigCell, d2Aσ, d2A, sig, S1]
     try ring)

/-- **`λ̂_C = 41/90`**, for every `σ` in range (the fixture's `41/90` at `σ = 1`, and constant in `σ`).
Source: mandate "Extension" (derived)
Kind: P
Fidelity: exact
Hyps: (a) `1/2 ≤ σ ≤ 1` -/
theorem C1_lamHat :
    lamHat (((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).P1 (S1 (d2Aσ σ hσ0 hσ1).u))
      (((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).PL) = 41/90 := by
  obtain ⟨n0, n1, d0, d1⟩ := C1_values σ hσ0 hσ1
  unfold lamHat; rw [n0, n1, d0, d1]
  have hσ : (0 : ℚ) < σ := by linarith
  have : (1 : ℚ) - (10 - 9 * σ) / 10 ≠ 0 := by
    intro h; have : σ = 0 := by linarith
    linarith
  field_simp; ring

/-- Both actions have positive mass at `C₁` (so nothing is excluded), and the masses differ.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma C1_posMass :
    posMass ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)) = univ ∧
    ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).PL 1
      < ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).PL 0 := by
  obtain ⟨_, _, d0, d1⟩ := C1_values σ hσ0 hσ1
  constructor
  · apply Finset.eq_univ_of_forall
    rw [Fin.forall_fin_two]
    constructor
    · rw [mem_posMass, d0]; norm_num
    · rw [mem_posMass, d1]; linarith
  · rw [d0, d1]; linarith

/-- `posMass` at `C₁` is inhabited (both actions), so the extension's witnesses assume nothing.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma C1_posMass_nonempty :
    (posMass ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1))).Nonempty := by
  rw [(C1_posMass σ hσ0 hσ1).1]; exact univ_nonempty

/-- `Λ` is inhabited for every `σ`: "`x` everywhere" is legitimate on every state, mass `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma family_Lambda_nonempty : (Lambda (d2Aσ σ hσ0 hσ1) sigCellOf).Nonempty :=
  Lambda_nonempty_of_PL_pos (d2Aσ σ hσ0 hσ1) sigCellOf (a := 0) (by
    unfold Problem.PL Problem.mass
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    simp [Fin.sum_univ_three, d2Aσ, d2A, sig]
    try norm_num
    try linarith)

/-- **`λ_C(σ) = max ((3 + 2σ)/10, (30 − 21σ)/(100 − 90σ))`**: the cell's own Dinkelbach grade.
Source: mandate "Extension" (derived)
Kind: P
Fidelity: exact
Hyps: (a) `1/2 ≤ σ ≤ 1` -/
theorem C1_lamC (h : (posMass ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1))).Nonempty) :
    lamStar ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)) (S1 (d2Aσ σ hσ0 hσ1).u) h
      = max ((3 + 2 * σ) / 10) ((30 - 21 * σ) / (100 - 90 * σ)) := by
  obtain ⟨n0, n1, d0, d1⟩ := C1_values σ hσ0 hσ1
  have r0 : ratio ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)) (S1 (d2Aσ σ hσ0 hσ1).u) 0
      = (3 + 2 * σ) / 10 := by
    unfold ratio; rw [n0, d0, div_one]
  have r1 : ratio ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)) (S1 (d2Aσ σ hσ0 hσ1).u) 1
      = (30 - 21 * σ) / (100 - 90 * σ) := by
    unfold ratio; rw [n1, d1]
    have h10 : (10 : ℚ) - 9 * σ ≠ 0 := by linarith
    have h100 : (100 : ℚ) - 90 * σ = 10 * (10 - 9 * σ) := by ring
    rw [h100]
    field_simp
    ring
  have hall : ∀ a : Fin 2, ratio ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)) (S1 (d2Aσ σ hσ0 hσ1).u) a
      ≤ max ((3 + 2 * σ) / 10) ((30 - 21 * σ) / (100 - 90 * σ)) := by
    rw [Fin.forall_fin_two]; exact ⟨r0 ▸ le_max_left _ _, r1 ▸ le_max_right _ _⟩
  have hmem : ∀ a : Fin 2, a ∈ posMass ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)) := by
    intro a; rw [(C1_posMass σ hσ0 hσ1).1]; exact mem_univ a
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun a _ => hall a
  · rcases le_total ((30 - 21 * σ) / (100 - 90 * σ)) ((3 + 2 * σ) / 10) with hle | hle
    · rw [max_eq_left hle, ← r0]; exact Finset.le_sup' _ (hmem 0)
    · rw [max_eq_right hle, ← r1]; exact Finset.le_sup' _ (hmem 1)

include hσ0 hσ1 in
/-- **The updateful verdict at `C₁` as a function of `σ`**: `λ_C(σ) < 41/90` iff `σ < 7/9`,
`= 41/90` iff `σ = 7/9`, `> 41/90` iff `σ > 7/9`.
Source: mandate "Extension" (derived)
Kind: P
Fidelity: exact
Hyps: (a) `1/2 ≤ σ ≤ 1` -/
theorem lamC_vs_lamHat :
    (max ((3 + 2 * σ) / 10) ((30 - 21 * σ) / (100 - 90 * σ)) < 41/90 ↔ σ < 7/9) ∧
    (max ((3 + 2 * σ) / 10) ((30 - 21 * σ) / (100 - 90 * σ)) = 41/90 ↔ σ = 7/9) ∧
    (41/90 < max ((3 + 2 * σ) / 10) ((30 - 21 * σ) / (100 - 90 * σ)) ↔ 7/9 < σ) := by
  have hden : (0 : ℚ) < 100 - 90 * σ := by linarith
  have hx : (3 + 2 * σ) / 10 < 41/90 ↔ σ < 7/9 := by constructor <;> intro h <;> linarith
  have hy : (30 - 21 * σ) / (100 - 90 * σ) < 41/90 ↔ σ < 7/9 := by
    rw [div_lt_iff₀ hden]; constructor <;> intro h <;> linarith
  have hx' : 41/90 < (3 + 2 * σ) / 10 ↔ 7/9 < σ := by constructor <;> intro h <;> linarith
  have hy' : 41/90 < (30 - 21 * σ) / (100 - 90 * σ) ↔ 7/9 < σ := by
    rw [lt_div_iff₀ hden]; constructor <;> intro h <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [max_lt_iff, hx, hy]; simp
  · constructor
    · intro h
      rcases lt_trichotomy σ (7/9) with hs | hs | hs
      · have := max_lt_iff.2 ⟨hx.2 hs, hy.2 hs⟩; linarith
      · exact hs
      · have : 41/90 < max ((3 + 2 * σ) / 10) ((30 - 21 * σ) / (100 - 90 * σ)) :=
          lt_max_iff.2 (Or.inl (hx'.2 hs))
        linarith
    · rintro rfl; norm_num
  · rw [lt_max_iff, hx', hy']; simp

/-- **`λ* = 2/5`**, for every `σ ∈ [1/2, 1]`: the maximum of the T1 conditioning value over the
cell policies is attained by "`x` everywhere" and is constant in `σ` (the four cell policies'
ratios are `2/5`, `39/110`, `(39 + 41σ)/(110 + 90σ)` and `(80 − 41σ)/(200 − 90σ)`, all `≤ 2/5`).
Source: mandate "Extension" (derived)
Kind: P
Fidelity: exact (`λ*` is the `sup'` of record over `Λ`, not a parameter)
Hyps: (a) `1/2 ≤ σ ≤ 1` -/
theorem family_lamStar (h : (Lambda (d2Aσ σ hσ0 hσ1) sigCellOf).Nonempty) :
    lamStarT1 (d2Aσ σ hσ0 hσ1) sigCellOf (S1 (d2Aσ σ hσ0 hσ1).u) h = 2/5 := by
  have hc : ∀ π : CellPol (A := Fin 2) sigCellOf, ∀ s b, π.1 (s, b) = π.1 (0, b) :=
    fun π s b => π.2 (0, b) (s, b) (by simp [sigCellOf, sigCell])
  have hval : ∀ π : CellPol (A := Fin 2) sigCellOf, policyValue (d2Aσ σ hσ0 hσ1) (S1 (d2Aσ σ hσ0 hσ1).u) π.1 =
      (∑ s : Fin 3, (d2Aσ σ hσ0 hσ1).prior (s, true) * ind ((d2Aσ σ hσ0 hσ1).leg (s, true) (π.1 (0, true)))
        * (d2Aσ σ hσ0 hσ1).u (s, true) (π.1 (0, true))) +
      (∑ s : Fin 3, (d2Aσ σ hσ0 hσ1).prior (s, false) * ind ((d2Aσ σ hσ0 hσ1).leg (s, false) (π.1 (0, false)))
        * (d2Aσ σ hσ0 hσ1).u (s, false) (π.1 (0, false))) := by
    intro π
    unfold policyValue
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, S1]
    rw [Finset.sum_add_distrib]
    congr 1 <;> exact Finset.sum_congr rfl fun s _ => by rw [hc π s]
  have hPL : ∀ π : CellPol (A := Fin 2) sigCellOf, policyPL (d2Aσ σ hσ0 hσ1) π.1 =
      (∑ s : Fin 3, (d2Aσ σ hσ0 hσ1).prior (s, true) * ind ((d2Aσ σ hσ0 hσ1).leg (s, true) (π.1 (0, true)))) +
      (∑ s : Fin 3, (d2Aσ σ hσ0 hσ1).prior (s, false) * ind ((d2Aσ σ hσ0 hσ1).leg (s, false) (π.1 (0, false)))) := by
    intro π
    unfold policyPL
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [Finset.sum_add_distrib]
    congr 1 <;> exact Finset.sum_congr rfl fun s _ => by rw [hc π s]
  -- the ratio of every positive-mass cell policy is at most `2/5`
  have hbound : ∀ π ∈ Lambda (d2Aσ σ hσ0 hσ1) sigCellOf,
      ratio (policyProblem (d2Aσ σ hσ0 hσ1) sigCellOf) (policyVec sigCellOf (S1 (d2Aσ σ hσ0 hσ1).u)) π ≤ 2/5 := by
    intro π hπ
    have hpos : 0 < policyPL (d2Aσ σ hσ0 hσ1) π.1 := (mem_Lambda _ _).1 hπ
    unfold ratio
    rw [policyProblem_P1, policyProblem_PL, div_le_iff₀ hpos, hval, hPL]
    generalize π.1 (0, true) = a₁
    generalize π.1 (0, false) = a₂
    fin_cases a₁ <;> fin_cases a₂ <;>
      simp [Fin.sum_univ_three, d2Aσ, d2A, sig] <;> nlinarith
  -- and `x` everywhere attains `2/5`
  have hx : ratio (policyProblem (d2Aσ σ hσ0 hσ1) sigCellOf) (policyVec sigCellOf (S1 (d2Aσ σ hσ0 hσ1).u))
      ⟨fun _ => 0, cellPolicy_const _ _⟩ = 2/5 := by
    unfold ratio
    rw [policyProblem_P1, policyProblem_PL, hval, hPL]
    simp [Fin.sum_univ_three, d2Aσ, d2A, sig]
    ring_nf
  have hxmem : (⟨fun _ => 0, cellPolicy_const _ _⟩ : CellPol (A := Fin 2) sigCellOf)
      ∈ Lambda (d2Aσ σ hσ0 hσ1) sigCellOf := by
    rw [mem_Lambda, hPL]; simp [Fin.sum_univ_three, d2Aσ, d2A, sig]
    try norm_num
    try linarith
  unfold lamStarT1 lamStar
  apply le_antisymm
  · exact Finset.sup'_le _ _ hbound
  · rw [← hx]; exact Finset.le_sup' _ hxmem

/-- **The threshold `σ̂ = 7/9` (the extension's headline).** Over the family: the updateless P2
verdict at `C₁` is `{x}` for every `σ ∈ [1/2, 1]` (`λ* = 2/5 < 41/90 = λ̂_C`), and the updateful P2
verdict at `C₁` is `{x}` for `σ < 7/9`, the tie `{x, y}` at `σ = 7/9`, and `{y}` for `σ > 7/9`. So
the two verdicts first part at `σ̂ = 7/9` — a single exact rational threshold, no union of
intervals — and the fixture's full-revelation instance (`σ = 1`, `x` against `y`) is its far end.
Exclusion convention (nothing is excluded at `C₁`). No non-emptiness hypothesis: the `sup'`s of
record take `family_Lambda_nonempty` and `C1_posMass_nonempty`.
Source: mandate "Extension" (derived; plan §0.4 rule 4: an exact root)
Kind: P
Fidelity: exact
Hyps: (a) `1/2 ≤ σ ≤ 1` -/
theorem family_threshold :
    argmax (((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).P3
      (fun _ _ _ => lamStarT1 (d2Aσ σ hσ0 hσ1) sigCellOf (S1 (d2Aσ σ hσ0 hσ1).u)
        (family_Lambda_nonempty σ hσ0 hσ1)) 1
      (S1 (d2Aσ σ hσ0 hσ1).u)) = {0} ∧
    (σ < 7/9 → argmaxOpt (((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).P2 (S1 (d2Aσ σ hσ0 hσ1).u)) = {0}) ∧
    (σ = 7/9 → argmaxOpt (((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).P2 (S1 (d2Aσ σ hσ0 hσ1).u)) = univ) ∧
    (7/9 < σ → argmaxOpt (((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).P2 (S1 (d2Aσ σ hσ0 hσ1).u)) = {1}) := by
  have hd := (C1_posMass σ hσ0 hσ1).2
  have hhat := C1_lamHat σ hσ0 hσ1
  have hstar := family_lamStar σ hσ0 hσ1 (family_Lambda_nonempty σ hσ0 hσ1)
  have hlamC := C1_lamC σ hσ0 hσ1 (C1_posMass_nonempty σ hσ0 hσ1)
  have hvs := lamC_vs_lamHat σ hσ0 hσ1
  -- the T2 verdict is the shifted verdict at `λ_C`
  have hT2 : argmaxOpt (((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).P2 (S1 (d2Aσ σ hσ0 hσ1).u)) =
      argmax (fun a => ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).P1 (S1 (d2Aσ σ hσ0 hσ1).u) a
        - lamStar ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)) (S1 (d2Aσ σ hσ0 hσ1).u)
            (C1_posMass_nonempty σ hσ0 hσ1)
          * ((d2Aσ σ hσ0 hσ1).restrict C1 (C1_pos σ hσ0 hσ1)).PL a) := by
    rw [T2_argmaxOpt_P2_eq (d2Aσ σ hσ0 hσ1) (S1 (d2Aσ σ hσ0 hσ1).u) C1 (C1_pos σ hσ0 hσ1)
        (C1_posMass_nonempty σ hσ0 hσ1),
      (C1_posMass σ hσ0 hσ1).1, Finset.inter_univ, argmax_P3_const_eq_shifted]
  refine ⟨?_, fun hs => ?_, fun hs => ?_, fun hs => ?_⟩
  · rw [argmax_P3_const_eq_shifted, hstar, (crossing _ _ hd _).1, hhat]; norm_num
  · rw [hT2, (crossing _ _ hd _).1, hhat, hlamC]; exact hvs.1.2 hs
  · rw [hT2, (crossing _ _ hd _).2.1, hhat, hlamC]; exact hvs.2.1.2 hs
  · rw [hT2, (crossing _ _ hd _).2.2, hhat, hlamC]; exact hvs.2.2.2 hs

/-- **The endpoints**: at `σ = 1/2` (no information) the updateful verdict is `{x}`, agreeing with
the updateless one; at `σ = 1` (full revelation, instance A) it is `{y}` — the fixture's
inconsistency. Both are instances of `family_threshold`; no hypothesis.
Source: mandate "Extension" (the proved endpoints)
Kind: N+
Fidelity: exact -/
theorem family_endpoints :
    argmaxOpt (((d2Aσ (1/2) le_rfl (by norm_num)).restrict C1 (C1_pos (1/2) le_rfl (by norm_num))).P2
      (S1 (d2Aσ (1/2) le_rfl (by norm_num)).u)) = {0} ∧
    argmaxOpt (((d2Aσ 1 (by norm_num) le_rfl).restrict C1 (C1_pos 1 (by norm_num) le_rfl)).P2
      (S1 (d2Aσ 1 (by norm_num) le_rfl).u)) = {1} :=
  ⟨(family_threshold (1/2) le_rfl (by norm_num)).2.1 (by norm_num),
   (family_threshold 1 (by norm_num) le_rfl).2.2.2 (by norm_num)⟩

end Family

end Cleanroom.Corrigibility.LegitNegDynamic
