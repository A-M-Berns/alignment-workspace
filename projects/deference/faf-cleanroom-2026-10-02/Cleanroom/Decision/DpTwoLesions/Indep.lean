import Cleanroom.Decision.DpTwoLesions.Laws

/-!
# T3's Remark — the independent anti-lesion: `Δ(1)` under both precedence conventions

The doc's §4 Remark: "Were the anti-lesion independent of the lesion, forced abstention would
carry the base rate of cancer, `Δ(1)` would be of order `δ`, vanishing with the lesion's grip,
and smoking would be a fixed point for every sufficiently small `δ`." The mandate (§3.6, §6)
recomputed the variant as `Δ(1) = 0` **exactly** and asked for the Lean value. Audit r1 (fidelity
N4) observed that the exact value depends on a **precedence convention** the doc does not fix:
when both forcings fire, which wins. This file builds the variant tree with the convention as a
parameter and settles both:

* `indepTree P aFirst` — the lesion and the anti-lesion are drawn **independently** (root
  chance over the lesion's status `fires / present-still / absent` with weights
  `(ρδL, ρ(1−δL), 1−ρ)`, then the anti-lesion's status with `(ρAδA, ρA(1−δA), 1−ρA)`; the
  status coins carry the forcing, so the law is Definition 2's with the exclusion dropped), then
  the draw, then the cancer coin by the lesion's presence (`γ₁` if present, `γ₀` if not). The act:
  with `aFirst = true` a fired anti-lesion wins (forced abstention), else a fired lesion wins.
* **`indep_aFirst_Delta_one`**: with the anti-lesion's forcing taking precedence,
  `Δ(1) = 0` exactly, for every parameter set — forced abstention is independent of the lesion
  and carries the population rate, and so does everyone else (the mandate's reading).
* **`indep_lFirst_Delta_one`**: with the lesion's forcing taking precedence,
  `Δ(1) = βρδL(1−ρ)(γ₁−γ₀) / ((1−ρδL)(1 − (1−ρδL)ρAδA))` exactly — positive when `γ₀ < γ₁`, and
  of order `δL` (the doc's phrase is exactly right under this convention): forced abstention
  now happens only when the lesion did *not* fire, which is weak evidence against the lesion.
* **`indep_smoke_fixed_at_doc`**: the doc's conclusion — smoking is a fixed point for small
  `δ` — holds under **both** conventions at the doc's parameters: `Δ(1) = 0 < α` always under
  anti-first, and `Δ(1) < α` for every `δ ∈ (0, 1/20]` under lesion-first.

So the Remark's "of order `δ`" is right or an imprecision depending on the convention, and its
conclusion is right under either (finding F6). The variant has no fixed-point apparatus of its
own here: `Δ(1)` is stated directly as the quotient of `nu`'s, and "smoking is a fixed point"
as `Δ(1) < α` (Claim 1.1's iff `isFixedPt_one_iff` transfers verbatim).
Serves [[dp-two-lesions-mandate]] T3 (the Remark), §6 ("verify in Lean"); repair round 1.
-/

namespace Cleanroom.Decision.DpTwoLesions

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Worlds of the independent-anti-lesion variant: `(lesion present, anti-lesion present, m, k)`.
Source: [[two-lesions-doc-2026-09-18]] §4 Remark ("Were the anti-lesion independent of the
lesion")
Kind: D -/
abbrev DlWi : Type := Bool × Bool × Bool × Bool

/-- The smoke event. Source: doc §3. Kind: D -/
def evSmokeI : Finset DlWi := univ.filter fun w => w.2.2.1 = true
/-- The abstain event. Source: doc §3. Kind: D -/
def evAbstainI : Finset DlWi := univ.filter fun w => w.2.2.1 = false
/-- The cancer event. Source: doc §3. Kind: D -/
def evCancerI : Finset DlWi := univ.filter fun w => w.2.2.2 = true

/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evSmokeI (w : DlWi) : w ∈ evSmokeI ↔ w.2.2.1 = true := by simp [evSmokeI]
/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evAbstainI (w : DlWi) : w ∈ evAbstainI ↔ w.2.2.1 = false := by
  simp [evAbstainI]
/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evCancerI (w : DlWi) : w ∈ evCancerI ↔ w.2.2.2 = true := by simp [evCancerI]

/-- A status index is "present": `0` (fires) or `1` (present, not firing).
Source: none: infrastructure. Kind: D -/
def present (s : Fin 3) : Bool := decide (s ≠ 2)

/-- Reductions. Source: none: infrastructure. Kind: L -/
@[simp] theorem present_zero : present 0 = true := by decide
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem present_one : present 1 = true := by decide
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem present_two : present 2 = false := by decide

/-- **The realized act under a precedence convention**: `aFirst = true` lets a fired anti-lesion
(`as = 0`) force abstention before a fired lesion (`ls = 0`) forces smoking; `aFirst = false` the
reverse; otherwise the draw stands.
Source: [[two-lesions-doc-2026-09-18]] §4 Remark ("forced abstention would carry the base rate"
— the anti-first reading); audit r1 N4 (the convention is unstated)
Kind: D -/
def actIndep (aFirst : Bool) (ls as : Fin 3) (m' : Bool) : Bool :=
  if aFirst then (if as = 0 then false else if ls = 0 then true else m')
  else (if ls = 0 then true else if as = 0 then false else m')

/-- A three-outcome status coin `(fires, present-still, absent)` with weights
`(ρ·δ, ρ·(1−δ), 1−ρ)`. Source: none: infrastructure. Kind: D -/
def statusK (ρ δ : K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    FinDistr K (Fin 3) where
  w := ![ρ * δ, ρ * (1 - δ), 1 - ρ]
  nonneg := by
    intro i; fin_cases i
    · simpa using mul_nonneg hρ0 hδ0
    · simpa using mul_nonneg hρ0 (by linarith)
    · simp; linarith
  sum_one := by simp [Fin.sum_univ_three]; ring

/-- Equation lemma. Source: none: infrastructure. Kind: L -/
@[simp] theorem statusK_w (ρ δ : K) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (i : Fin 3) :
    (statusK ρ δ hρ0 hρ1 hδ0 hδ1).w i =
      if i = 0 then ρ * δ else if i = 1 then ρ * (1 - δ) else 1 - ρ := by
  fin_cases i <;> simp [statusK]

namespace DlParams

variable (P : DlParams K)

/-- `ρ ≤ 1`. Source: none: infrastructure. Kind: L -/
theorem ρ_le_one : P.ρ ≤ 1 := by linarith [P.ρ_add_ρA_lt_one, P.ρA_pos]
/-- `ρA ≤ 1`. Source: none: infrastructure. Kind: L -/
theorem ρA_le_one : P.ρA ≤ 1 := by linarith [P.ρ_add_ρA_lt_one, P.ρ_pos]
/-- `ρδL < 1`. Source: none: infrastructure. Kind: L -/
theorem ρδL_lt_one : P.ρ * P.δL < 1 := by
  have := mul_le_of_le_one_right P.ρ_pos.le P.δL_le_one
  linarith [P.ρ_add_ρA_lt_one, P.ρA_pos]
/-- `ρAδA < 1`. Source: none: infrastructure. Kind: L -/
theorem ρAδA_lt_one : P.ρA * P.δA < 1 := by
  have := mul_le_of_le_one_right P.ρA_pos.le P.δA_le_one
  linarith [P.ρ_add_ρA_lt_one, P.ρ_pos]

/-- The cancer rate by the lesion's presence. Source: doc §3 Definition 2. Kind: D -/
def gamI (ls : Fin 3) : K := if present ls then P.γ₁ else P.γ₀

/-- `0 ≤ gamI`. Source: none: infrastructure. Kind: L -/
theorem gamI_nonneg (ls : Fin 3) : 0 ≤ P.gamI ls := by
  unfold gamI; split_ifs
  · linarith [P.γ₀_nonneg, P.γ₀_le_γ₁]
  · exact P.γ₀_nonneg
/-- `gamI ≤ 1`. Source: none: infrastructure. Kind: L -/
theorem gamI_le_one (ls : Fin 3) : P.gamI ls ≤ 1 := by
  unfold gamI; split_ifs
  · exact P.γ₁_le_one
  · linarith [P.γ₀_le_γ₁, P.γ₁_le_one]

/-- **The independent-anti-lesion tree** under precedence `aFirst`: the lesion's status, the
anti-lesion's status (independent), the draw, the cancer coin by the lesion's presence; leaf
`(lesion present, anti present, m, k)`.
Source: [[two-lesions-doc-2026-09-18]] §4 Remark; mandate T3 (`overwriteIndep`)
Kind: D
Fidelity: variant: the two forcing coins are merged into the status coins (the same law as
"present with probability `ε`, then fires with probability `δ`"); the precedence is a parameter -/
def indepTree (aFirst : Bool) : Tree DlWi Unit (fun _ => Bool) K :=
  .chance 3 (statusK P.ρ P.δL P.ρ_pos.le P.ρ_le_one P.δL_pos.le P.δL_le_one) fun ls =>
    .chance 3 (statusK P.ρA P.δA P.ρA_pos.le P.ρA_le_one P.δA_pos.le P.δA_le_one) fun as =>
      .decision () fun m' =>
        .chance 2 (coinK (P.gamI ls) (P.gamI_nonneg ls) (P.gamI_le_one ls)) fun k =>
          .leaf (present ls, present as, actIndep aFirst ls as m', decide (k = 0))
            (P.pay (actIndep aFirst ls as m') (decide (k = 0)))

/-- A sum over the 36 leaves of `indepTree P aFirst`. Source: none: infrastructure. Kind: L -/
theorem indep_sum (aFirst : Bool) (f : (P.indepTree aFirst).Leaves → K) :
    ∑ ℓ, f ℓ = ∑ ls : Fin 3, ∑ as : Fin 3, ∑ m' : Bool, ∑ k : Fin 2, f ⟨ls, as, m', k, ()⟩ := by
  unfold indepTree at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun ls _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun as _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact sum_leaves_leafK _ _ _

/-- The leaf law of `indepTree P aFirst`. Source: Definition 6 on the variant tree. Kind: L -/
theorem indep_leafLaw (aFirst : Bool) (C : Proc Unit (fun _ => Bool) K) (ls as : Fin 3)
    (m' : Bool) (k : Fin 2) :
    leafLaw C (P.indepTree aFirst) ⟨ls, as, m', k, ()⟩ =
      (if ls = 0 then P.ρ * P.δL else if ls = 1 then P.ρ * (1 - P.δL) else 1 - P.ρ) *
        (if as = 0 then P.ρA * P.δA else if as = 1 then P.ρA * (1 - P.δA) else 1 - P.ρA) *
        (C ()).w m' * (if k = 0 then P.gamI ls else 1 - P.gamI ls) := by
  unfold indepTree
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, statusK_w, coinK_w]
  ring

/-- `ν` on `indepTree P aFirst` as a 36-term sum. Source: none: infrastructure. Kind: L -/
theorem indep_nu (aFirst : Bool) (C : Proc Unit (fun _ => Bool) K) (X : Finset DlWi) :
    nu C (P.indepTree aFirst) X =
      ∑ ls : Fin 3, ∑ as : Fin 3, ∑ m' : Bool, ∑ k : Fin 2,
        if (present ls, present as, actIndep aFirst ls as m', decide (k = 0)) ∈ X then
          leafLaw C (P.indepTree aFirst) ⟨ls, as, m', k, ()⟩ else 0 := by
  rw [nu_eq_sum, indep_sum]
  rfl

/-- **The evidential penalty of the variant** at label `p`, as quotients of `ν` on
`indepTree P aFirst` (never a closed form).
Source: [[two-lesions-doc-2026-09-18]] §3 (the display `Δ(p)`) on the Remark's variant
Kind: D -/
def DeltaIndep (aFirst : Bool) (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) : K :=
  P.β * (nu (procBoolK p h0 h1) (P.indepTree aFirst) (evCancerI ∩ evSmokeI) /
      nu (procBoolK p h0 h1) (P.indepTree aFirst) evSmokeI -
    nu (procBoolK p h0 h1) (P.indepTree aFirst) (evCancerI ∩ evAbstainI) /
      nu (procBoolK p h0 h1) (P.indepTree aFirst) evAbstainI)

/-- The four cells at `p = 1` under anti-first precedence: abstention happens iff the
anti-lesion fired (`ρAδA`), independently of the lesion, so both act cells carry the
population cancer rate `ργ₁ + (1−ρ)γ₀`.
Source: [[two-lesions-doc-2026-09-18]] §4 Remark ("forced abstention would carry the base rate
of cancer")
Kind: P
Fidelity: exact
Hyps: none -/
theorem indep_aFirst_cells_one :
    nu (procBoolK (1 : K) zero_le_one le_rfl) (P.indepTree true) evAbstainI = P.ρA * P.δA ∧
    nu (procBoolK (1 : K) zero_le_one le_rfl) (P.indepTree true) (evCancerI ∩ evAbstainI) =
      (P.ρ * P.γ₁ + (1 - P.ρ) * P.γ₀) * (P.ρA * P.δA) ∧
    nu (procBoolK (1 : K) zero_le_one le_rfl) (P.indepTree true) evSmokeI = 1 - P.ρA * P.δA ∧
    nu (procBoolK (1 : K) zero_le_one le_rfl) (P.indepTree true) (evCancerI ∩ evSmokeI) =
      (P.ρ * P.γ₁ + (1 - P.ρ) * P.γ₀) * (1 - P.ρA * P.δA) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [indep_nu]
    simp only [indep_leafLaw, procBoolK_w]
    conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two, actIndep, gamI]
    ring

/-- **With the anti-lesion's forcing taking precedence, `Δ(1) = 0` exactly**, for every
parameter set: forced abstention is independent of the lesion and carries the population rate,
and so does smoking (everyone else).
Source: [[two-lesions-doc-2026-09-18]] §4 Remark ("`Δ(1)` would be of order `δ`"); mandate §3.6
("`Δ(1) = 0` exactly") — confirmed under this convention
Kind: P
Fidelity: exact
Hyps: none -/
theorem indep_aFirst_Delta_one : P.DeltaIndep true 1 zero_le_one le_rfl = 0 := by
  obtain ⟨c1, c2, c3, c4⟩ := P.indep_aFirst_cells_one
  unfold DeltaIndep
  rw [c1, c2, c3, c4]
  have h1 : P.ρA * P.δA ≠ 0 := (mul_pos P.ρA_pos P.δA_pos).ne'
  have h2 : 1 - P.ρA * P.δA ≠ 0 := (sub_pos.mpr P.ρAδA_lt_one).ne'
  rw [mul_div_assoc, div_self h2, mul_div_assoc, div_self h1]; ring

/-- The four cells at `p = 1` under lesion-first precedence: abstention happens iff the
anti-lesion fired *and the lesion did not*; smoking carries the rest.
Source: [[two-lesions-doc-2026-09-18]] §4 Remark, the other convention (audit r1 N4)
Kind: P
Fidelity: exact
Hyps: none -/
theorem indep_lFirst_cells_one :
    nu (procBoolK (1 : K) zero_le_one le_rfl) (P.indepTree false) evAbstainI =
      (1 - P.ρ * P.δL) * (P.ρA * P.δA) ∧
    nu (procBoolK (1 : K) zero_le_one le_rfl) (P.indepTree false) (evCancerI ∩ evAbstainI) =
      (P.ρ * (1 - P.δL) * P.γ₁ + (1 - P.ρ) * P.γ₀) * (P.ρA * P.δA) ∧
    nu (procBoolK (1 : K) zero_le_one le_rfl) (P.indepTree false) evSmokeI =
      1 - (1 - P.ρ * P.δL) * (P.ρA * P.δA) ∧
    nu (procBoolK (1 : K) zero_le_one le_rfl) (P.indepTree false) (evCancerI ∩ evSmokeI) =
      P.ρ * P.γ₁ + (1 - P.ρ) * P.γ₀ -
        (P.ρ * (1 - P.δL) * P.γ₁ + (1 - P.ρ) * P.γ₀) * (P.ρA * P.δA) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [indep_nu]
    simp only [indep_leafLaw, procBoolK_w]
    conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two, actIndep, gamI]
    ring

/-- `(1 − ρδL)·ρAδA < 1`. Source: none: infrastructure. Kind: L -/
theorem indep_abstain_lt_one : (1 - P.ρ * P.δL) * (P.ρA * P.δA) < 1 := by
  have hρδ : 0 < P.ρ * P.δL := mul_pos P.ρ_pos P.δL_pos
  have hρδ1 : P.ρ * P.δL < 1 := P.ρδL_lt_one
  have hA1 : P.ρA * P.δA < 1 := P.ρAδA_lt_one
  have hA0 : 0 ≤ P.ρA * P.δA := (mul_pos P.ρA_pos P.δA_pos).le
  nlinarith

/-- **With the lesion's forcing taking precedence, `Δ(1)` is of order `δL`, not `0`**:
`Δ(1) = βρδL(1−ρ)(γ₁−γ₀) / ((1−ρδL)(1 − (1−ρδL)ρAδA))` exactly — forced abstention now
happens only when the lesion did not fire, which is (weak) evidence against the lesion. The
doc's "of order `δ`" is exactly right under this convention.
Source: [[two-lesions-doc-2026-09-18]] §4 Remark ("`Δ(1)` would be of order `δ`, vanishing with
the lesion's grip"); audit r1 N4
Kind: P
Fidelity: exact
Hyps: none -/
theorem indep_lFirst_Delta_one :
    P.DeltaIndep false 1 zero_le_one le_rfl =
      P.β * (P.ρ * P.δL * (1 - P.ρ) * (P.γ₁ - P.γ₀) /
        ((1 - P.ρ * P.δL) * (1 - (1 - P.ρ * P.δL) * (P.ρA * P.δA)))) := by
  obtain ⟨c1, c2, c3, c4⟩ := P.indep_lFirst_cells_one
  unfold DeltaIndep
  rw [c1, c2, c3, c4]
  have h1 : 1 - P.ρ * P.δL ≠ 0 := (sub_pos.mpr P.ρδL_lt_one).ne'
  have h2 : P.ρA * P.δA ≠ 0 := (mul_pos P.ρA_pos P.δA_pos).ne'
  have h3 : 1 - (1 - P.ρ * P.δL) * (P.ρA * P.δA) ≠ 0 := (sub_pos.mpr P.indep_abstain_lt_one).ne'
  congr 1
  rw [div_sub_div _ _ h3 (mul_ne_zero h1 h2), div_eq_div_iff (mul_ne_zero h3 (mul_ne_zero h1 h2))
    (mul_ne_zero h1 h3)]
  ring

/-- Under lesion-first precedence `Δ(1) > 0` when `γ₀ < γ₁`: the variant's smoke-penalty does not
vanish, only shrinks with the grip.
Source: [[two-lesions-doc-2026-09-18]] §4 Remark
Kind: P
Fidelity: exact
Hyps: none -/
theorem indep_lFirst_Delta_one_pos (hγ : P.γ₀ < P.γ₁) : 0 < P.DeltaIndep false 1 zero_le_one le_rfl := by
  rw [indep_lFirst_Delta_one]
  have hρ1 : P.ρ < 1 := by linarith [P.ρ_add_ρA_lt_one, P.ρA_pos]
  have hρδ1 : P.ρ * P.δL < 1 := P.ρδL_lt_one
  apply mul_pos P.β_pos
  apply div_pos
  · have := mul_pos (mul_pos (mul_pos P.ρ_pos P.δL_pos) (sub_pos.mpr hρ1)) (sub_pos.mpr hγ)
    linarith
  · exact mul_pos (sub_pos.mpr hρδ1) (sub_pos.mpr P.indep_abstain_lt_one)

/-- **The Remark's conclusion holds under both conventions at the doc's parameters**: smoking
is a fixed point of the variant (`Δ(1) < α`, Claim 1.1's criterion) — for every grip under
anti-first precedence (`Δ(1) = 0 < 1`), and for every grip `δ ∈ (0, 1/20]` under lesion-first
precedence, where `Δ(1) = 16δ / ((1 − δ/5)(1 − (1 − δ/5)δ/5)) < 1`.
Source: [[two-lesions-doc-2026-09-18]] §4 Remark ("smoking would be a fixed point for every
sufficiently small `δ`")
Kind: N+
Fidelity: exact ("sufficiently small" witnessed by `(0, 1/20]`) -/
theorem indep_smoke_fixed_at_doc (δ : ℚ) (h0 : 0 < δ) (h1 : δ ≤ 1) :
    (docP δ h0 h1).DeltaIndep true 1 zero_le_one le_rfl < (docP δ h0 h1).α ∧
    (δ ≤ 1/20 → (docP δ h0 h1).DeltaIndep false 1 zero_le_one le_rfl < (docP δ h0 h1).α) := by
  constructor
  · rw [indep_aFirst_Delta_one]; simp only [docP]; norm_num
  · intro hδ
    rw [indep_lFirst_Delta_one]
    simp only [docP]
    have hd1 : (0 : ℚ) < 1 - 1/5 * δ := by linarith
    have hd2 : (0 : ℚ) < 1 - (1 - 1/5 * δ) * (1/5 * δ) := by nlinarith
    rw [mul_div_assoc', div_lt_iff₀ (mul_pos hd1 hd2)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hδ) h0.le, mul_pos h0 h0, mul_pos hd1 hd2]

end DlParams

end Cleanroom.Decision.DpTwoLesions
