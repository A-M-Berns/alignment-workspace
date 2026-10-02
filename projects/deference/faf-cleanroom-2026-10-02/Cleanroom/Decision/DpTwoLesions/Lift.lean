import Cleanroom.Decision.DpTwoLesions.Laws

/-!
# The full-world overwrite tree: the draw and the tag as coordinates

`overwriteFull P` is `overwrite P` with the world enriched to `(s, m′, forced, m, k)`: the
draw `m′` (the IV note's `a_d`, dp-core-097's draw coordinate; `e13Rec`'s pattern) and the
forcing coin's outcome `forced` (the doc's Definition 3 tag, an oracle for the forcing event)
are both written into the leaf. The mandate's `overwriteLift` (world `(s, m′, m, k)`) and
`tagged` (world `(s, forced, m, k)`) are the two projections; one tree carries both, and every
statement below names only the coordinates it reads. Serves T10(c) (draw-recording holds for
every `C`; the draw-conditional cancer gap is `0`), T11 (the uncoupled draw-conditional
estimands: first stage `κ`, ITT on cancer `0`, ITT on payoff `ακ`, Wald `α`, the two forced
cells `γ₀`, `γ₁`, all label-invariant) and T12 (Proposition 6: the tagged conditionals equal
`c_C`, the forced cells `γ₁`, `γ₀`; the per-protocol estimator on the draw coordinate is biased,
`11/3980` at the session parameters).
-/

namespace Cleanroom.Decision.DpTwoLesions

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Full worlds `(s, m′, forced, m, k)`: state, draw, tag, act, cancer.
Source: [[iv-design-draw-as-instrument]] §4 (the draw coordinate `a_d`);
[[two-lesions-doc-2026-09-18]] §6 Definition 3 (the tag)
Kind: D -/
abbrev DlWf : Type := DlState × Bool × Bool × Bool × Bool

/-- The tag: the forcing coin fired at a forcing state (`L` or `A`).
Source: [[two-lesions-doc-2026-09-18]] §6 Definition 3 ("whether the act was forced or chosen")
Kind: D -/
def forcedOf (i : Fin 3) (j : Fin 2) : Bool := decide (j = 0 ∧ i ≠ 2)

/-- Reductions of `forcedOf`. Source: none: infrastructure. Kind: L -/
@[simp] theorem forcedOf_L_fire : forcedOf 0 0 = true := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem forcedOf_L_still : forcedOf 0 1 = false := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem forcedOf_A_fire : forcedOf 1 0 = true := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem forcedOf_A_still : forcedOf 1 1 = false := rfl
/-- Source: none: infrastructure. Kind: L -/
@[simp] theorem forcedOf_N (j : Fin 2) : forcedOf 2 j = false := by fin_cases j <;> rfl

/-- The draw event `{m′ = a}` (the IV note's `{a_d = a}`). Source: IV note §4. Kind: D -/
def evDraw (a : Bool) : Finset DlWf := Finset.univ.filter fun w => w.2.1 = a
/-- The tag event `{forced}`. Source: doc §6 Definition 3. Kind: D -/
def evForced : Finset DlWf := Finset.univ.filter fun w => w.2.2.1 = true
/-- The tag event `{chosen}`. Source: doc §6 Definition 3. Kind: D -/
def evChosen : Finset DlWf := Finset.univ.filter fun w => w.2.2.1 = false
/-- The act event `{m = a}` on the full world. Source: doc §3. Kind: D -/
def evActF (a : Bool) : Finset DlWf := Finset.univ.filter fun w => w.2.2.2.1 = a
/-- The cancer event on the full world. Source: doc §3. Kind: D -/
def evCancerF : Finset DlWf := Finset.univ.filter fun w => w.2.2.2.2 = true
/-- The state event on the full world. Source: doc §3. Kind: D -/
def evStateF (s : DlState) : Finset DlWf := Finset.univ.filter fun w => w.1 = s

/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evDraw (a : Bool) (w : DlWf) : w ∈ evDraw a ↔ w.2.1 = a := by simp [evDraw]
/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evForced (w : DlWf) : w ∈ evForced ↔ w.2.2.1 = true := by simp [evForced]
/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evChosen (w : DlWf) : w ∈ evChosen ↔ w.2.2.1 = false := by simp [evChosen]
/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evActF (a : Bool) (w : DlWf) : w ∈ evActF a ↔ w.2.2.2.1 = a := by
  simp [evActF]
/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evCancerF (w : DlWf) : w ∈ evCancerF ↔ w.2.2.2.2 = true := by simp [evCancerF]
/-- Membership. Source: none: infrastructure. Kind: L -/
@[simp] theorem mem_evStateF (s : DlState) (w : DlWf) : w ∈ evStateF s ↔ w.1 = s := by
  simp [evStateF]

/-- `O_d = ⊤` on the full world. Source: v2 (S3). Kind: D -/
def fullObs : Unit → Finset DlWf := fun _ => Finset.univ

/-- The draw as the action event: `{m′ = a}` (the draw-coordinate reading of Definition 7′).
Source: [[iv-design-draw-as-instrument]] §4 Definition 7′
Kind: D -/
def drawActEv : Unit → Bool → Finset DlWf := fun _ a => evDraw a

/-- The realized act as the action event: `{m = a}`. Source: v2 (S1). Kind: D -/
def actActEv : Unit → Bool → Finset DlWf := fun _ a => evActF a

namespace DlParams

variable (P : DlParams K)

/-- **The full-world overwrite tree**: `overwrite P` with leaf `(s, m′, forced, m, k)`.
Source: [[iv-design-draw-as-instrument]] §4 ("the draw-lifted problem `B^a`");
[[two-lesions-doc-2026-09-18]] §6 Definition 3 (the tag); mandate §3.3 (`overwriteLift`, `tagged`)
Kind: D
Fidelity: variant: one enriched algebra carrying both the draw and the tag (the mandate's two
lifts are its projections), disclosed -/
def overwriteFull : Tree DlWf Unit (fun _ => Bool) K :=
  .chance 3 P.stateDistr fun i =>
    .decision () fun m' =>
      .chance 2 (coinK (P.force i) (P.force_nonneg i) (P.force_le_one i)) fun j =>
        .chance 2 (coinK (P.gam i) (P.gam_nonneg i) (P.gam_le_one i)) fun k =>
          .leaf (stateOf i, m', forcedOf i j, actOf i m' j, decide (k = 0))
            (P.pay (actOf i m' j) (decide (k = 0)))

/-- A sum over the 24 leaves of `overwriteFull P`. Source: none: infrastructure. Kind: L -/
theorem full_sum (f : P.overwriteFull.Leaves → K) :
    ∑ ℓ, f ℓ = ∑ i : Fin 3, ∑ m' : Bool, ∑ j : Fin 2, ∑ k : Fin 2, f ⟨i, m', j, k, ()⟩ := by
  unfold overwriteFull at f ⊢
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact sum_leaves_leafK _ _ _

/-- The leaf law of `overwriteFull P` (the same as `overwrite P`'s).
Source: Definition 6 on the full tree
Kind: L -/
theorem full_leafLaw (C : Proc Unit (fun _ => Bool) K) (i : Fin 3) (m' : Bool) (j k : Fin 2) :
    leafLaw C P.overwriteFull ⟨i, m', j, k, ()⟩ =
      P.stateW i * (C ()).w m' * (if j = 0 then P.force i else 1 - P.force i) *
        (if k = 0 then P.gam i else 1 - P.gam i) := by
  unfold overwriteFull
  simp only [leafLaw_chance, leafLaw_decision, leafLaw_leaf, stateDistr_w, coinK_w]
  ring

/-- The world at a leaf of `overwriteFull P`. Source: none: infrastructure. Kind: L -/
theorem full_world (i : Fin 3) (m' : Bool) (j k : Fin 2) :
    world P.overwriteFull ⟨i, m', j, k, ()⟩ =
      (stateOf i, m', forcedOf i j, actOf i m' j, decide (k = 0)) := rfl

/-- The payoff at a leaf of `overwriteFull P`. Source: none: infrastructure. Kind: L -/
theorem full_payoff (i : Fin 3) (m' : Bool) (j k : Fin 2) :
    payoff P.overwriteFull ⟨i, m', j, k, ()⟩ = P.pay (actOf i m' j) (decide (k = 0)) := rfl

/-- `ν` on `overwriteFull P` as a 24-term sum. Source: none: infrastructure. Kind: L -/
theorem full_nu (C : Proc Unit (fun _ => Bool) K) (X : Finset DlWf) :
    nu C P.overwriteFull X =
      ∑ i : Fin 3, ∑ m' : Bool, ∑ j : Fin 2, ∑ k : Fin 2,
        if (stateOf i, m', forcedOf i j, actOf i m' j, decide (k = 0)) ∈ X then
          leafLaw C P.overwriteFull ⟨i, m', j, k, ()⟩ else 0 := by
  rw [nu_eq_sum, full_sum]
  rfl

/-- `paySum` on `overwriteFull P` as a 24-term sum. Source: none: infrastructure. Kind: L -/
theorem full_paySum (C : Proc Unit (fun _ => Bool) K) (X : Finset DlWf) :
    Cleanroom.Decision.DpCalibration.paySum C P.overwriteFull X =
      ∑ i : Fin 3, ∑ m' : Bool, ∑ j : Fin 2, ∑ k : Fin 2,
        if (stateOf i, m', forcedOf i j, actOf i m' j, decide (k = 0)) ∈ X then
          leafLaw C P.overwriteFull ⟨i, m', j, k, ()⟩ * P.pay (actOf i m' j) (decide (k = 0))
        else 0 := by
  rw [Cleanroom.Decision.DpCalibration.paySum_eq_sum_ite, full_sum]
  rfl

/-- `#_d = 1` on every run of `overwriteFull P`. Source: none: infrastructure. Kind: L -/
theorem full_count (ℓ : P.overwriteFull.Leaves) : count () P.overwriteFull ℓ = 1 := by
  unfold overwriteFull at ℓ ⊢
  rcases ℓ with ⟨i, m', j, k, _⟩
  rfl

/-- The population cancer rate `ργ₁ + (1 − ρ)γ₀`. Source: exchange line 63. Kind: D -/
def popRate : K := P.ρ * P.γ₁ + (1 - P.ρ) * P.γ₀

/-! ## The cells, from `nu` (label `p`) -/

/-- **The tagged cells (Proposition 6's inputs)**: on chosen runs the act carries the label and
the compliers' cancer mass (`ν(m ∧ chosen) = κ·label(m)`, `ν(k ∧ m ∧ chosen) = κc_C·label(m)`);
on forced runs the act is the lesion's (`ν(smoke ∧ forced) = ρδL`, `ν(k ∧ smoke ∧ forced) =
ρδLγ₁`, `ν(abstain ∧ forced) = ρAδA`, `ν(k ∧ abstain ∧ forced) = ρAδAγ₀`).
Source: [[two-lesions-doc-2026-09-18]] §6 Proposition 6 proof ("Chosen acts occur in state `L`
with probability `ε_L(1−δ)`, …"); Remark ("`P(cancer | smoke, forced) = 1`")
Kind: P
Fidelity: exact (general `γ`)
Hyps: none -/
theorem full_tag_cells (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    nu (procBoolK p h0 h1) P.overwriteFull (evActF true ∩ evChosen) = P.kappa * p ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evCancerF ∩ evActF true ∩ evChosen) = P.kcC * p ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evActF false ∩ evChosen) = P.kappa * (1 - p) ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evCancerF ∩ evActF false ∩ evChosen) =
      P.kcC * (1 - p) ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evActF true ∩ evForced) = P.ρ * P.δL ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evCancerF ∩ evActF true ∩ evForced) =
      P.ρ * P.δL * P.γ₁ ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evActF false ∩ evForced) = P.ρA * P.δA ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evCancerF ∩ evActF false ∩ evForced) =
      P.ρA * P.δA * P.γ₀ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [full_nu]
    simp only [full_leafLaw, procBoolK_w]
    conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two]
    try unfold kappa
    try unfold kcC
    ring

/-- **The draw cells (Proposition D′'s inputs)**: `ν(m′ = a) = label(a)`; the draw carries the
population cancer rate (`ν(k ∧ m′=a) = popRate·label(a)`); compliance
(`ν(m=1 ∧ m′=1) = (1 − ρAδA)p`, `ν(m=1 ∧ m′=0) = ρδL(1−p)`); the two forced-against-the-draw
cells (`ν(m′=1 ∧ m=0) = ρAδA p`, `ν(k ∧ m′=1 ∧ m=0) = ρAδAγ₀ p`, `ν(m′=0 ∧ m=1) = ρδL(1−p)`,
`ν(k ∧ m′=0 ∧ m=1) = ρδLγ₁(1−p)`).
Source: [[iv-design-draw-as-instrument]] §2 (B3)
Kind: P
Fidelity: exact (general `γ`)
Hyps: none -/
theorem full_draw_cells (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    nu (procBoolK p h0 h1) P.overwriteFull (evDraw true) = p ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evDraw false) = 1 - p ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evCancerF ∩ evDraw true) = P.popRate * p ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evCancerF ∩ evDraw false) = P.popRate * (1 - p) ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evActF true ∩ evDraw true) = (1 - P.ρA * P.δA) * p ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evActF true ∩ evDraw false) = P.ρ * P.δL * (1 - p) ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evCancerF ∩ evDraw true ∩ evActF false) =
      P.ρA * P.δA * P.γ₀ * p ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evDraw true ∩ evActF false) = P.ρA * P.δA * p ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evCancerF ∩ evDraw false ∩ evActF true) =
      P.ρ * P.δL * P.γ₁ * (1 - p) ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evDraw false ∩ evActF true) = P.ρ * P.δL * (1 - p) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · rw [full_nu]
    simp only [full_leafLaw, procBoolK_w]
    conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two]
    try unfold popRate
    ring

/-- **The per-protocol cells**: `ν(k ∧ m′=1 ∧ m=1) = p[ργ₁ + (1 − ρ − ρAδA)γ₀]`,
`ν(m′=1 ∧ m=1) = p(1 − ρAδA)`, `ν(k ∧ m′=0 ∧ m=0) = (1−p)[ρ(1−δL)γ₁ + (1−ρ)γ₀]`,
`ν(m′=0 ∧ m=0) = (1−p)(1 − ρδL)`.
Source: [[iv-design-draw-as-instrument]] §2 (B3) ("the naive matched-episodes estimator")
Kind: P
Fidelity: exact
Hyps: none -/
theorem full_perProtocol_cells (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    nu (procBoolK p h0 h1) P.overwriteFull (evCancerF ∩ evDraw true ∩ evActF true) =
      (P.ρ * P.γ₁ + (1 - P.ρ - P.ρA * P.δA) * P.γ₀) * p ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evDraw true ∩ evActF true) = (1 - P.ρA * P.δA) * p ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evCancerF ∩ evDraw false ∩ evActF false) =
      (P.ρ * (1 - P.δL) * P.γ₁ + (1 - P.ρ) * P.γ₀) * (1 - p) ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evDraw false ∩ evActF false) =
      (1 - P.ρ * P.δL) * (1 - p) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · rw [full_nu]
    simp only [full_leafLaw, procBoolK_w]
    conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two]
    ring

/-- **The draw-conditional payoff masses**: `paySum(m′=1) = p[α(1 − ρAδA) − β·popRate]` and
`paySum(m′=0) = (1−p)[αρδL − β·popRate]`.
Source: [[iv-design-draw-as-instrument]] §2 (B3) ("ITT on payoff = `ακ`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem full_draw_pay (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    Cleanroom.Decision.DpCalibration.paySum (procBoolK p h0 h1) P.overwriteFull (evDraw true) =
      (P.α * (1 - P.ρA * P.δA) - P.β * P.popRate) * p ∧
    Cleanroom.Decision.DpCalibration.paySum (procBoolK p h0 h1) P.overwriteFull (evDraw false) =
      (P.α * (P.ρ * P.δL) - P.β * P.popRate) * (1 - p) := by
  refine ⟨?_, ?_⟩ <;>
  · rw [full_paySum]
    simp only [full_leafLaw, procBoolK_w]
    conv_lhs => simp [Fin.sum_univ_three, Fin.sum_univ_two, pay]
    unfold popRate
    ring

/-! ## T12 — Proposition 6: tags dissolve the problem -/

/-- **Proposition 6 (tags dissolve the problem)**: for every `p ∈ (0, 1)`,
`P_p(cancer | smoke, chosen) = P_p(cancer | abstain, chosen) = c_C` (the doc's
`ε_L(1−δ)/κ` at `γ = (1, 0)`), as quotients of `ν` on the tagged tree.
Source: [[two-lesions-doc-2026-09-18]] §6 Proposition 6
Kind: P
Fidelity: exact (general `γ`; the tag is the forcing oracle, Definition 3)
Hyps: none -/
theorem prop6_tagged_flat (p : K) (h0 : 0 < p) (h1 : p < 1) :
    nu (procBoolK p h0.le h1.le) P.overwriteFull (evCancerF ∩ evActF true ∩ evChosen) /
        nu (procBoolK p h0.le h1.le) P.overwriteFull (evActF true ∩ evChosen) = P.cC ∧
    nu (procBoolK p h0.le h1.le) P.overwriteFull (evCancerF ∩ evActF false ∩ evChosen) /
        nu (procBoolK p h0.le h1.le) P.overwriteFull (evActF false ∩ evChosen) = P.cC := by
  obtain ⟨c1, c2, c3, c4, -, -, -, -⟩ := P.full_tag_cells p h0.le h1.le
  have hk := P.kappa_pos
  rw [c1, c2, c3, c4]
  unfold cC
  constructor
  · rw [div_eq_div_iff (mul_pos hk h0).ne' hk.ne']; ring
  · rw [div_eq_div_iff (mul_pos hk (sub_pos.mpr h1)).ne' hk.ne']; ring

/-- **The forced cells**: `P_p(cancer | smoke, forced) = γ₁`, `P_p(cancer | abstain, forced) = γ₀`
(the doc's `1` and `0`), for every label.
Source: [[two-lesions-doc-2026-09-18]] §6 Remark ("`P(cancer | smoke, forced) = 1` and
`P(cancer | abstain, forced) = 0`")
Kind: P
Fidelity: exact (general `γ`)
Hyps: none -/
theorem prop6_forced_cells (p : K) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    nu (procBoolK p h0 h1) P.overwriteFull (evCancerF ∩ evActF true ∩ evForced) /
        nu (procBoolK p h0 h1) P.overwriteFull (evActF true ∩ evForced) = P.γ₁ ∧
    nu (procBoolK p h0 h1) P.overwriteFull (evCancerF ∩ evActF false ∩ evForced) /
        nu (procBoolK p h0 h1) P.overwriteFull (evActF false ∩ evForced) = P.γ₀ := by
  obtain ⟨-, -, -, -, c5, c6, c7, c8⟩ := P.full_tag_cells p h0 h1
  rw [c5, c6, c7, c8]
  constructor
  · rw [div_eq_iff (mul_pos P.ρ_pos P.δL_pos).ne']; ring
  · rw [div_eq_iff (mul_pos P.ρA_pos P.δA_pos).ne']; ring

/-- **The tagged penalty** `Δ_tag(p) := β[P_p(k | smoke, chosen) − P_p(k | abstain, chosen)]`,
a quotient of `ν`'s on the tagged tree (never a `def` of `0`). **Junk at the pure labels**: at
`p = 1` chosen abstention has mass `0` and Lean's `0/0 = 0` gives `taggedDelta 1 = β·c_C`; at
`p = 0` likewise `taggedDelta 0 = −β·c_C` (audit r1). No headline reads it outside `(0, 1)`;
the pure labels are handled through exploration, as in the doc's proof.
Source: [[two-lesions-doc-2026-09-18]] §6 Proposition 6 ("the tagged agent's penalty on chosen
acts")
Kind: D
Fidelity: exact on `(0, 1)`; junk at `0` and `1`, disclosed -/
def taggedDelta (p : K) : K :=
  if h : 0 ≤ p ∧ p ≤ 1 then
    P.β * (nu (procBoolK p h.1 h.2) P.overwriteFull (evCancerF ∩ evActF true ∩ evChosen) /
        nu (procBoolK p h.1 h.2) P.overwriteFull (evActF true ∩ evChosen) -
      nu (procBoolK p h.1 h.2) P.overwriteFull (evCancerF ∩ evActF false ∩ evChosen) /
        nu (procBoolK p h.1 h.2) P.overwriteFull (evActF false ∩ evChosen))
  else 0

/-- The tagged best response (the doc's `β` with the tagged penalty). Source: doc §6. Kind: D -/
def taggedBestResp (p : K) : Set K :=
  {b | (P.α > P.taggedDelta p → b = 1) ∧ (P.α < P.taggedDelta p → b = 0) ∧ 0 ≤ b ∧ b ≤ 1}

/-- **The tagged penalty is `0` on `(0, 1)`**, hence `< α`.
Source: [[two-lesions-doc-2026-09-18]] §6 Proposition 6 ("the tagged agent's penalty on chosen
acts is `0`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem taggedDelta_eq_zero (p : K) (h0 : 0 < p) (h1 : p < 1) : P.taggedDelta p = 0 := by
  unfold taggedDelta
  rw [dif_pos ⟨h0.le, h1.le⟩]
  obtain ⟨e1, e2⟩ := P.prop6_tagged_flat p h0 h1
  rw [e1, e2, sub_self, mul_zero]

/-- **The tagged best response is `{1}` at every interior label**: the tagged agent smokes.
Source: [[two-lesions-doc-2026-09-18]] §6 Proposition 6 ("its best response is `{1}` at every
policy at which both conditionals are defined")
Kind: P
Fidelity: exact
Hyps: none -/
theorem taggedBestResp_eq_one (p : K) (h0 : 0 < p) (h1 : p < 1) : P.taggedBestResp p = {1} := by
  have h := P.taggedDelta_eq_zero p h0 h1
  ext b
  unfold taggedBestResp
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hb, -, -, -⟩; exact hb (by rw [h]; exact P.α_pos)
  · rintro rfl
    exact ⟨fun _ => rfl, fun hlt => absurd hlt (by rw [h]; exact not_lt.mpr P.α_pos.le), zero_le_one,
      le_rfl⟩

/-- **Proposition 6, the fixed points (no interior tagged fixed point; the explored tagged
agent smokes)**: no interior label is a tagged fixed point, and with any exploration
`ε ∈ (0, 1)` the labels `1 − ε` and `ε` both have best response `{1}` — the explored tagged
dynamics move to the smoke end from either side. What this does **not** say (audit r1): that
`1` is literally a tagged fixed point — at `p = 1` the chosen-abstention conditional is the junk
`0/0 = 0`, so `taggedDelta 1 = β·c_C`, which at the doc's `δ = 1/100` exceeds `α` and makes
`1 ∉ taggedBestResp 1`; the doc's own proof defines the pure-label verdict through exploration
("supplied by any positive exploration"), and so does this theorem. The rest point of the
`ε`-explored recency map is `1 − ε/2`, which `taggedBestResp (1 − ε) = {1}` delivers.
Source: [[two-lesions-doc-2026-09-18]] §6 Proposition 6 ("its unique fixed point is to smoke";
proof: "at `p = 1` the conditional on chosen abstention is undefined and is supplied by any
positive exploration")
Kind: P
Fidelity: weaker: the pure label `1` only through exploration (as the doc's proof); the literal
"`1` is a tagged fixed point" is false in the formalization because of the junk value
Hyps: none -/
theorem prop6_no_interior_fixedPt_explored_smokes :
    (∀ p : K, 0 < p → p < 1 → p ∉ P.taggedBestResp p) ∧
    (∀ ε : K, 0 < ε → ε < 1 → P.taggedBestResp (1 - ε) = {1} ∧ P.taggedBestResp ε = {1}) := by
  constructor
  · intro p h0 h1 hp
    rw [P.taggedBestResp_eq_one p h0 h1, Set.mem_singleton_iff] at hp
    exact h1.ne hp
  · intro ε h0 h1
    exact ⟨P.taggedBestResp_eq_one _ (by linarith) (by linarith), P.taggedBestResp_eq_one _ h0 h1⟩

/-! ## T10(c) — draw-recording on the full tree; the draw-conditional gap dissolves -/

/-- Every decision node of `overwriteFull P` is a root `d`-node `⟨i, none⟩`.
Source: none: infrastructure
Kind: L -/
theorem full_nodes_cases (q : P.overwriteFull.DecNode) :
    ∃ i : Fin 3, q = (⟨i, none⟩ : P.overwriteFull.DecNode) := by
  unfold overwriteFull at q
  rcases q with ⟨i, (_ | ⟨m', j, k, e⟩)⟩
  · exact ⟨i, rfl⟩
  · exact e.elim

/-- Every leaf of `overwriteFull P` is some `⟨i, m', j, k, ()⟩`. Source: none: infrastructure.
Kind: L -/
theorem full_leaves (ℓ : P.overwriteFull.Leaves) :
    ∃ (i : Fin 3) (m' : Bool) (j k : Fin 2), ℓ = ⟨i, m', j, k, ()⟩ := by
  unfold overwriteFull at ℓ
  rcases ℓ with ⟨i, m', j, k, ⟨⟩⟩
  exact ⟨i, m', j, k, rfl⟩

/-- The edge taken at the `d`-node `⟨i, none⟩` by the leaf `⟨i', m', j, k, ()⟩`.
Source: none: infrastructure
Kind: L -/
theorem full_edgeOf (i i' : Fin 3) (m' : Bool) (j k : Fin 2) :
    edgeOf P.overwriteFull (⟨i, none⟩ : P.overwriteFull.DecNode) ⟨i', m', j, k, ()⟩ =
      if i' = i then some m' else none := by
  unfold overwriteFull
  by_cases h : i' = i
  · subst h; simp [edgeOf_chance, edgeOf_decision_none]
  · simp [edgeOf_chance, h]

/-- **Draw-recording holds on the full tree for every procedure** (the draw-coordinate reading
of Definition 7: `RecordsFor fullObs drawActEv C (overwriteFull P) ()`): every run meets `d`
once, `O_d = ⊤` makes every node subtree-veridical, and the draw coordinate is the draw at the
unique `d`-node — action-veridicality for the *draw* holds by construction.
Source: [[iv-design-draw-as-instrument]] §4 Definition 7′ ("The overwrite tree is draw-recorded,
not act-recorded"); dp-core-097; `dp-smoking-lesion`'s `e13Rec_recordsFor`
Kind: P
Fidelity: exact
Hyps: none -/
theorem full_recordsFor_draw (C : Proc Unit (fun _ => Bool) K) :
    RecordsFor fullObs drawActEv C P.overwriteFull () := by
  intro ℓ _ _
  refine ⟨P.full_count ℓ, ?_⟩
  intro q _ a ha
  obtain ⟨i, rfl⟩ := P.full_nodes_cases q
  obtain ⟨i', m', j, k, rfl⟩ := P.full_leaves ℓ
  rw [P.full_edgeOf] at ha
  by_cases h : i' = i
  · subst h
    simp only [if_true, Option.some.injEq] at ha
    subst ha
    refine ⟨fun _ _ => Finset.mem_univ _, ?_, ?_⟩
    · rw [P.full_world]; simp [drawActEv]
    · intro a' ha'
      rw [P.full_world] at ha'
      simp [drawActEv] at ha'
      exact ha'.symm
  · simp [h] at ha

/-- **The full tree is not act-recorded** at any interior label: the forced run
`(L, m′ = abstain, fired)` has positive mass and its act `m = smoke` is not its draw.
Source: [[iv-design-draw-as-instrument]] §4 ("not act-recorded (action-veridicality fails)");
`dp-core-tree`'s `overwrite_not_recordsFor`
Kind: N+ -/
theorem full_not_recordsFor_act (p : K) (h0 : 0 < p) (h1 : p < 1) :
    ¬ RecordsFor fullObs actActEv (procBoolK p h0.le h1.le) P.overwriteFull () := by
  intro hrec
  -- a forced run `(L, drew abstain, fired)` of positive mass: cancer or not, one of the two
  have hbase : 0 < P.ρ * (1 - p) * P.δL :=
    mul_pos (mul_pos P.ρ_pos (sub_pos.mpr h1)) P.δL_pos
  have hpos : ∃ k : Fin 2,
      0 < leafLaw (procBoolK p h0.le h1.le) P.overwriteFull ⟨0, false, 0, k, ()⟩ := by
    rcases (P.gam_nonneg 0).lt_or_eq with hγ | hγ
    · refine ⟨0, ?_⟩
      rw [full_leafLaw]
      simp only [stateW_zero, procBoolK_w, Bool.false_eq_true, if_false, force_zero, gam_zero]
      simp only [if_true]
      rw [gam_zero] at hγ
      exact mul_pos hbase hγ
    · refine ⟨1, ?_⟩
      rw [full_leafLaw]
      simp only [stateW_zero, procBoolK_w, Bool.false_eq_true, if_false, force_zero, gam_zero]
      simp only [if_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
      rw [gam_zero] at hγ
      rw [← hγ]
      simpa using hbase
  obtain ⟨k, hk⟩ := hpos
  obtain ⟨-, h⟩ := hrec ⟨0, false, 0, k, ()⟩ hk (Finset.mem_univ _)
  have he : edgeOf P.overwriteFull (⟨0, none⟩ : P.overwriteFull.DecNode) ⟨0, false, 0, k, ()⟩ =
      some false := by rw [P.full_edgeOf]; simp
  obtain ⟨-, hav, -⟩ := h ⟨0, none⟩ rfl false he
  rw [P.full_world] at hav
  simp [actActEv] at hav

/-- **The draw-conditional cancer gap is `0` on the full tree at every label** (`dissolve_draw`):
`P_p(k | m′ = 1) = P_p(k | m′ = 0) = ργ₁ + (1 − ρ)γ₀` for `p ∈ (0, 1)`.
Source: [[iv-design-draw-as-instrument]] §2 (B3) ("ITT on cancer = **0** exactly"); dp-core-097
("recording the draw as a coordinate dissolves it"); [[smoking-lesion-exploration-and-boundaries]]
§1 Claim 1.2 ("conditioning on `{a=1}` instead of `{m=1}` restores Lemma 3 and dissolves it")
Kind: P
Fidelity: exact
Hyps: none -/
theorem dissolve_draw (p : K) (h0 : 0 < p) (h1 : p < 1) :
    nu (procBoolK p h0.le h1.le) P.overwriteFull (evCancerF ∩ evDraw true) /
        nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw true) = P.popRate ∧
    nu (procBoolK p h0.le h1.le) P.overwriteFull (evCancerF ∩ evDraw false) /
        nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw false) = P.popRate := by
  obtain ⟨d1, d2, d3, d4, -, -, -, -, -, -⟩ := P.full_draw_cells p h0.le h1.le
  rw [d1, d2, d3, d4]
  constructor
  · rw [mul_div_assoc, div_self h0.ne', mul_one]
  · rw [mul_div_assoc, div_self (sub_pos.mpr h1).ne', mul_one]

/-! ## T11 — Corollary D′, uncoupled: first stage, ITT, Wald -/

/-- **The first stage is `κ`**: `P(m=1 | m′=1) − P(m=1 | m′=0) = (1 − ρAδA) − ρδL = κ`, for every
`p ∈ (0, 1)`.
Source: [[iv-design-draw-as-instrument]] §2 (B3) ("first stage … `= κ = 99/100`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem iv_firstStage (p : K) (h0 : 0 < p) (h1 : p < 1) :
    nu (procBoolK p h0.le h1.le) P.overwriteFull (evActF true ∩ evDraw true) /
        nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw true) -
      nu (procBoolK p h0.le h1.le) P.overwriteFull (evActF true ∩ evDraw false) /
        nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw false) = P.kappa := by
  obtain ⟨d1, d2, -, -, d5, d6, -, -, -, -⟩ := P.full_draw_cells p h0.le h1.le
  rw [d1, d2, d5, d6, mul_div_assoc, div_self h0.ne', mul_div_assoc, div_self (sub_pos.mpr h1).ne']
  unfold kappa; ring

/-- **ITT on cancer is `0`** (as a difference of conditionals), for every `p ∈ (0, 1)`.
Source: [[iv-design-draw-as-instrument]] §2 (B3) ("ITT on cancer = **0** exactly")
Kind: P
Fidelity: exact
Hyps: none -/
theorem iv_ittCancer (p : K) (h0 : 0 < p) (h1 : p < 1) :
    nu (procBoolK p h0.le h1.le) P.overwriteFull (evCancerF ∩ evDraw true) /
        nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw true) -
      nu (procBoolK p h0.le h1.le) P.overwriteFull (evCancerF ∩ evDraw false) /
        nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw false) = 0 := by
  obtain ⟨e1, e2⟩ := P.dissolve_draw p h0 h1
  rw [e1, e2, sub_self]

/-- **ITT on payoff is `ακ`**: `E[r | m′=1] − E[r | m′=0] = ακ`, for every `p ∈ (0, 1)`.
Source: [[iv-design-draw-as-instrument]] §2 (B3) ("ITT on payoff = `ακ`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem iv_ittPayoff (p : K) (h0 : 0 < p) (h1 : p < 1) :
    Cleanroom.Decision.DpCalibration.paySum (procBoolK p h0.le h1.le) P.overwriteFull
        (evDraw true) / nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw true) -
      Cleanroom.Decision.DpCalibration.paySum (procBoolK p h0.le h1.le) P.overwriteFull
        (evDraw false) / nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw false) =
      P.α * P.kappa := by
  obtain ⟨d1, d2, -, -, -, -, -, -, -, -⟩ := P.full_draw_cells p h0.le h1.le
  obtain ⟨y1, y2⟩ := P.full_draw_pay p h0.le h1.le
  rw [d1, d2, y1, y2, mul_div_assoc, div_self h0.ne', mul_div_assoc, div_self (sub_pos.mpr h1).ne']
  unfold kappa; ring

/-- **Wald = `α`**: the ITT on payoff over the first stage is `α`, the effect of the act on
compliers, label-invariant.
Source: [[iv-design-draw-as-instrument]] §2 (B3) ("**Wald = α = 1**, the effect of the act on
compliers"); Corollary D′
Kind: C
Fidelity: exact (uncoupled: no compliance types, no LATE — the Wald *ratio* only)
Hyps: none -/
theorem iv_wald (p : K) (h0 : 0 < p) (h1 : p < 1) :
    (Cleanroom.Decision.DpCalibration.paySum (procBoolK p h0.le h1.le) P.overwriteFull
        (evDraw true) / nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw true) -
      Cleanroom.Decision.DpCalibration.paySum (procBoolK p h0.le h1.le) P.overwriteFull
        (evDraw false) / nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw false)) /
    (nu (procBoolK p h0.le h1.le) P.overwriteFull (evActF true ∩ evDraw true) /
        nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw true) -
      nu (procBoolK p h0.le h1.le) P.overwriteFull (evActF true ∩ evDraw false) /
        nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw false)) = P.α := by
  rw [P.iv_ittPayoff p h0 h1, P.iv_firstStage p h0 h1, mul_div_assoc, div_self P.kappa_pos.ne',
    mul_one]

/-- **The never-takers and always-takers read off directly**: `P(k | m′=1, m=0) = γ₀` (drawn
smoke, forced abstention: the anti-lesion, no cancer excess) and `P(k | m′=0, m=1) = γ₁`
(drawn abstention, forced smoke: the lesion).
Source: [[iv-design-draw-as-instrument]] §2 (B3) ("`P(k | a=1, m=0) = γ₀` and `P(k | a=0, m=1)
= γ₁` are the never-takers and always-takers read off directly")
Kind: P
Fidelity: exact
Hyps: none -/
theorem iv_forced_cells (p : K) (h0 : 0 < p) (h1 : p < 1) :
    nu (procBoolK p h0.le h1.le) P.overwriteFull (evCancerF ∩ evDraw true ∩ evActF false) /
        nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw true ∩ evActF false) = P.γ₀ ∧
    nu (procBoolK p h0.le h1.le) P.overwriteFull (evCancerF ∩ evDraw false ∩ evActF true) /
        nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw false ∩ evActF true) = P.γ₁ := by
  obtain ⟨-, -, -, -, -, -, d7, d8, d9, d10⟩ := P.full_draw_cells p h0.le h1.le
  rw [d7, d8, d9, d10]
  constructor
  · rw [div_eq_iff (mul_pos (mul_pos P.ρA_pos P.δA_pos) h0).ne']; ring
  · rw [div_eq_iff (mul_pos (mul_pos P.ρ_pos P.δL_pos) (sub_pos.mpr h1)).ne']; ring

/-- **The as-treated gap depends on the label** (`P_p(k | m=1) − P_p(k | m=0) = Δ(p)/β`): it is
`11/2000` at `p = ½` and `(431/8000·2 − …)` — exactly the untagged evidential conditional, which
the IV estimands above are not.
Source: [[iv-design-draw-as-instrument]] §2 (B3) ("The as-treated gap … is `0.0055` at `p = ½`
… — the confounded conditional the untagged learner acts on"); dp-core-2-004
Kind: N+ -/
theorem asTreated_gap_sessP_half : (sessP : DlParams ℚ).Delta (1/2) / 10 = 11/2000 := by
  rw [DlParams.Delta_eq _ _ (by norm_num) (by norm_num)]
  unfold DlParams.condSmoke DlParams.condAbstain
  simp [sessP, DlParams.kappa, DlParams.kcC]
  norm_num

/-- The as-treated gap at `p = 1/20` on the session parameters, exactly: `Δ(1/20)/β = 9460/206119`
(`≈ 0.0459`, the note's decimal).
Source: [[iv-design-draw-as-instrument]] §2 (B3) ("`0.0459` at `p = 1/20`")
Kind: N+ -/
theorem asTreated_gap_sessP_twentieth : (sessP : DlParams ℚ).Delta (1/20) / 10 = 9460/206119 := by
  rw [DlParams.Delta_eq _ _ (by norm_num) (by norm_num)]
  unfold DlParams.condSmoke DlParams.condAbstain
  simp [sessP, DlParams.kappa, DlParams.kcC]
  norm_num

/-! ## T12 — the oracle tag vs the draw coordinate -/

/-- **The per-protocol estimator on the draw coordinate is biased**: at the session parameters
and `p = ½`, `P(k | m′=1, m=1) − P(k | m′=0, m=0) = 11/3980 ≠ 0`, while the oracle-tagged
difference is `0` (`prop6_tagged_flat`) and the ITT is `0` (`iv_ittCancer`): lesion-forced
always-takers who drew smoke are indistinguishable from compliers.
Source: [[iv-design-draw-as-instrument]] §2 (B3) ("naive `P(k|a=1,m=1)−P(k|a=0,m=0) =
11/3980`"); §0 ("The doc's tag … is **not** the draw coordinate on the overwrite tree");
dp-core-096
Kind: N+
Fidelity: exact -/
theorem perProtocol_biased_sessP_half :
    nu (procBoolK (1/2 : ℚ) (by norm_num) (by norm_num)) (sessP : DlParams ℚ).overwriteFull
        (evCancerF ∩ evDraw true ∩ evActF true) /
      nu (procBoolK (1/2 : ℚ) (by norm_num) (by norm_num)) (sessP : DlParams ℚ).overwriteFull
        (evDraw true ∩ evActF true) -
    nu (procBoolK (1/2 : ℚ) (by norm_num) (by norm_num)) (sessP : DlParams ℚ).overwriteFull
        (evCancerF ∩ evDraw false ∩ evActF false) /
      nu (procBoolK (1/2 : ℚ) (by norm_num) (by norm_num)) (sessP : DlParams ℚ).overwriteFull
        (evDraw false ∩ evActF false) = 11/3980 := by
  obtain ⟨c1, c2, c3, c4⟩ := DlParams.full_perProtocol_cells (sessP : DlParams ℚ) (1/2)
    (by norm_num) (by norm_num)
  rw [c1, c2, c3, c4]
  simp only [sessP]; norm_num

/-- The per-protocol estimator is label-invariant and generally nonzero: it equals
`[ργ₁ + (1−ρ−ρAδA)γ₀]/(1−ρAδA) − [ρ(1−δL)γ₁ + (1−ρ)γ₀]/(1−ρδL)` at every `p ∈ (0, 1)`.
Source: [[iv-design-draw-as-instrument]] §2 (B3)
Kind: P
Fidelity: exact
Hyps: none -/
theorem perProtocol_eq (p : K) (h0 : 0 < p) (h1 : p < 1) :
    nu (procBoolK p h0.le h1.le) P.overwriteFull (evCancerF ∩ evDraw true ∩ evActF true) /
        nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw true ∩ evActF true) -
      nu (procBoolK p h0.le h1.le) P.overwriteFull (evCancerF ∩ evDraw false ∩ evActF false) /
        nu (procBoolK p h0.le h1.le) P.overwriteFull (evDraw false ∩ evActF false) =
      (P.ρ * P.γ₁ + (1 - P.ρ - P.ρA * P.δA) * P.γ₀) / (1 - P.ρA * P.δA) -
        (P.ρ * (1 - P.δL) * P.γ₁ + (1 - P.ρ) * P.γ₀) / (1 - P.ρ * P.δL) := by
  obtain ⟨c1, c2, c3, c4⟩ := P.full_perProtocol_cells p h0.le h1.le
  rw [c1, c2, c3, c4, mul_div_mul_right _ _ h0.ne', mul_div_mul_right _ _ (sub_pos.mpr h1).ne']

end DlParams

end Cleanroom.Decision.DpTwoLesions
