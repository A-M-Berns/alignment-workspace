import Cleanroom.Bli.UdtBliTiling.IndepCalc
import Cleanroom.Bli.UdtBliCore.Mugging
import Cleanroom.Udt.UdtPaperTiling.Vingean

/-!
# `udt-bli-tiling` · Vingean: the Vingean shape is blocked on the mugging (T6(i), stretch)

Theorem 3 of the Understanding Trust paper (the Vingean tiling, `udt-paper-tiling`'s
`thm3_vingean_tiling`) rests on Faith in Joint Argmax, whose prior-level content is
`FaithInJointArgmaxPrior P A' o o'` (paper-tiling, `Vingean.lean`): every positive joint cell
`(pp·o = a, pp·o' = a')` with `a ∈ A'` is dominated by some positive marginal `EU o b`.

* **The mandate's formulation of the obstruction is false** (finding F13): at `o = o' = Ask` the
  only positive joint cells are the diagonal ones, whose value is the marginal itself, so
  `FaithInJointArgmaxPrior (muggingPrior r) univ askT askT` **holds** (`faith_ask_ask`).
* **The obstruction is at the cross table**: at `o = Rec`, `o' = Ask`, the joint cell
  `(Rec ↦ a, Ask ↦ pay)` has the value `EU Ask pay = 441/10 + …` (the utility reads only the `Ask`
  point: `cellEU_rec_ask`), while every marginal `EU Rec b` is the ex-ante average
  `½ (EU Ask pay + EU Ask refuse)` (`EU_rec`); for `|r| ≤ 10` the cell exceeds every marginal, so
  Faith in Joint Argmax fails there (`not_faith_rec_ask`). The one prior on which
  updatelessness has content (the `Rec` branch cares about the `Ask` point) is exactly where
  Theorem 3's hypothesis cannot hold.
* (ii) Faith in the prior's *own* argmax over a BLI built on an inductor is a reflection
  statement about 𝙿's large sentences; `bli-exactness` (X1) is not built, so neither the exact
  nor the δ-smoothed form can be stated here. Recorded in the report and findings (F9), not as a
  `sorry`.

Sources: [[bli-program]] §3.9 U9(5); bli-paper-009/010 (`main.tex` 211–225, Theorem 3's package);
mandate T6.
-/

namespace Cleanroom.Bli.UdtBliTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.Mugging
  Cleanroom.Udt.UdtPaperTiling Finset

namespace VingeanMugging

variable (r : Bool → ℚ)

/-- The policy-law mass of the joint point event `(Rec ↦ a, Ask ↦ a')` is `1/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma massOf_ν_pair (a a' : Bool) :
    massOf (muggingData r).ν (fun π => π recT = a ∧ π askT = a') = 1 / 4 := by
  change massOf (prodLaw mugHalf) (fun π => π recT = a ∧ π askT = a') = 1 / 4
  unfold massOf
  have e : ∀ π : Policy mugTables Bool,
      (if π recT = a ∧ π askT = a' then prodLaw mugHalf π else 0) =
        prodLaw mugHalf π * ((if π recT = a then (1 : ℚ) else 0) * (if π askT = a' then 1 else 0)) := by
    intro π
    by_cases h1 : π recT = a <;> by_cases h2 : π askT = a' <;> simp [h1, h2]
  simp only [e]
  rw [sum_prodLaw_mul_ind₂ mugHalf_sum askT_ne_recT.symm a a']
  simp [mugHalf]; norm_num

/-- The joint cell `(Rec ↦ a, Ask ↦ a')` has mass `1/4` (positive).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma pairMass_rec_ask (a a' : Bool) : (muggingPrior r).pairMass recT askT a a' = 1 / 4 := by
  have := (muggingData r).massOf_rect (fun _ => True) (fun π => π recT = a ∧ π askT = a')
  simp only [true_and] at this
  have hμ : massOf (muggingData r).μ₀ (fun _ => True) = 1 := by
    unfold massOf; simp [(muggingData r).μ₀_sum_one]
  rw [hμ, one_mul, massOf_ν_pair] at this
  exact this

/-- **The joint cell reads the `Ask` point**: `cellEU Rec Ask a a' = EU Ask a'` on the mugging
prior (the utility is a function of the state and the `Ask` point only).
Source: none: infrastructure (core F-13: the mugging's utility reads the `Ask` point)
Kind: L
Fidelity: n/a -/
lemma cellEU_rec_ask (a a' : Bool) :
    cellEU (muggingPrior r) recT askT a a' = (muggingPrior r).EU askT a' := by
  unfold cellEU
  have hint := (muggingData r).integralOf_U_rect (fun _ => True)
    (fun π => π recT = a ∧ π askT = a')
  simp only [true_and, if_true] at hint
  have hmass := (muggingData r).massOf_rect (fun _ => True) (fun π => π recT = a ∧ π askT = a')
  simp only [true_and] at hmass
  have hμ : massOf (muggingData r).μ₀ (fun _ => True) = 1 := by
    unfold massOf; simp [(muggingData r).μ₀_sum_one]
  rw [hμ, one_mul, massOf_ν_pair] at hmass
  change condExp (muggingData r).μ (fun ω => (muggingData r).U₀ ω.1 ω.2)
    (fun ω => ω.2 recT = a ∧ ω.2 askT = a') = _
  unfold condExp
  rw [hint, hmass]
  have hinner : ∀ ω₀ : Fin 3, (∑ π : Policy mugTables Bool, if π recT = a ∧ π askT = a' then
      (muggingData r).ν π * (muggingData r).U₀ ω₀ π else 0) = 1 / 4 * mugU r ω₀ a' := by
    intro ω₀
    have e : ∀ π : Policy mugTables Bool, (if π recT = a ∧ π askT = a' then
        (muggingData r).ν π * (muggingData r).U₀ ω₀ π else 0) =
        mugU r ω₀ a' * (prodLaw mugHalf π *
          ((if π recT = a then (1 : ℚ) else 0) * (if π askT = a' then 1 else 0))) := by
      intro π
      change (if π recT = a ∧ π askT = a' then prodLaw mugHalf π * mugU r ω₀ (π askT) else 0) = _
      by_cases h1 : π recT = a <;> by_cases h2 : π askT = a' <;> simp [h1, h2] <;> ring
    simp only [e]
    rw [← Finset.mul_sum, sum_prodLaw_mul_ind₂ mugHalf_sum askT_ne_recT.symm a a']
    simp [mugHalf]; ring
  simp only [hinner]
  unfold muggingPrior
  rw [(muggingData r).EU_single mugHalf mugHalf_sum rfl askT (mugU r) (U₀_eq r) a'
    (mugHalf_pos _ _)]
  rw [div_eq_iff (by norm_num), Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro ω₀ _; ring

/-- **The marginal at `Rec` is the ex-ante average**: `EU Rec b = ½ (EU Ask pay + EU Ask refuse)`
for every `b` (the `Rec` point is read by nothing).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma EU_rec (b : Bool) :
    (muggingPrior r).EU recT b =
      1 / 2 * ((muggingPrior r).EU askT true + (muggingPrior r).EU askT false) := by
  unfold muggingPrior
  rw [IndepCalc.EU_toPrior (muggingData r) recT b,
    (muggingData r).EU_single mugHalf mugHalf_sum rfl askT (mugU r) (U₀_eq r) true
      (mugHalf_pos _ _),
    (muggingData r).EU_single mugHalf mugHalf_sum rfl askT (mugU r) (U₀_eq r) false
      (mugHalf_pos _ _)]
  have hmass : massOf (muggingData r).ν (fun π => π recT = b) = 1 / 2 := by
    change massOf (prodLaw mugHalf) (fun π => π recT = b) = 1 / 2
    rw [IndepData.massOf_prodLaw_point mugHalf mugHalf_sum]; rfl
  rw [hmass]
  have hinner : ∀ ω₀ : Fin 3, (∑ π : Policy mugTables Bool, if π recT = b then
      (muggingData r).ν π * (muggingData r).U₀ ω₀ π else 0) =
      1 / 4 * (mugU r ω₀ true + mugU r ω₀ false) := by
    intro ω₀
    have e : ∀ π : Policy mugTables Bool, (if π recT = b then
        (muggingData r).ν π * (muggingData r).U₀ ω₀ π else 0) =
        prodLaw mugHalf π * ((if π recT = b then (1 : ℚ) else 0) * mugU r ω₀ (π askT)) := by
      intro π
      change (if π recT = b then prodLaw mugHalf π * mugU r ω₀ (π askT) else 0) = _
      by_cases h : π recT = b <;> simp [h]
    simp only [e]
    rw [sum_prodLaw_mul_fun₂ mugHalf_sum askT_ne_recT.symm
      (fun j₀ j₁ => (if j₀ = b then (1 : ℚ) else 0) * mugU r ω₀ j₁)]
    simp only [Fintype.sum_bool, mugHalf]
    cases b <;> simp <;> ring
  simp only [hinner]
  rw [div_eq_iff (by norm_num)]
  have e : ∀ x : Fin 3, (muggingData r).μ₀ x * (1 / 4 * (mugU r x true + mugU r x false)) =
      ((muggingData r).μ₀ x * mugU r x true) * (1 / 4) +
        ((muggingData r).μ₀ x * mugU r x false) * (1 / 4) := by
    intro x; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_mul]
  ring

/-- **The mandate's formulation holds, so it is no obstruction**: Faith in Joint Argmax at
`(Ask, Ask)` is true on the mugging prior — the positive joint cells are the diagonal ones, whose
value is the marginal, dominated by `EU Ask pay`.
Source: mandate T6(i) (stated there as a failure — finding F13)
Kind: N+ (of the predicate; N− of the mandate's claimed obstruction)
Fidelity: exact
Hyps: (a) `|r a| ≤ 10`; does not use faith -/
theorem faith_ask_ask (hr : ∀ a, |r a| ≤ 10) :
    FaithInJointArgmaxPrior (muggingPrior r) Finset.univ askT askT := by
  intro a' a _ hpos
  have haa : a = a' := by
    by_contra hne
    have hz : (muggingPrior r).pairMass askT askT a a' = 0 := by
      unfold FiniteBLIPrior.pairMass massOf
      apply Finset.sum_eq_zero
      intro ω _
      rw [if_neg]
      rintro ⟨h1, h2⟩
      exact hne (h1.symm.trans h2)
    rw [hz] at hpos
    exact lt_irrefl _ hpos
  subst haa
  refine ⟨true, Finset.mem_univ _, ndpol r askT true, ?_⟩
  have e : cellEU (muggingPrior r) askT askT a a = (muggingPrior r).EU askT a := by
    unfold cellEU FiniteBLIPrior.EU
    apply condExp_congr
    intro ω
    exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩
  rw [e]
  exact isOneStepChoice_ask_pay r hr a

/-- **Faith in Joint Argmax fails at the cross table `(Rec, Ask)` on the mugging prior**: the
joint cell `(Rec ↦ pay, Ask ↦ pay)` is positive with value `441/10 + (2/100)·r pay`, and every
marginal `EU Rec b` is `½ (441/10 + (2/100)(r pay + r refuse))`, smaller for `|r| ≤ 10`. So
Theorem 3's own hypothesis fails on the one prior where updatelessness has content: the Vingean
shape (faith in the prior's own argmax) is not available there.
Source: [[bli-program]] §3.9 U9(5) ("the Vingean shape … is not available exactly"); bli-paper-010
(`main.tex` 219–225); mandate T6(i), corrected (F13)
Kind: N−
Fidelity: exact (the corrected table pair; the mandate's `(Ask, Ask)` is `faith_ask_ask`)
Hyps: (a) `|r a| ≤ 10`; does not use faith -/
theorem not_faith_rec_ask (hr : ∀ a, |r a| ≤ 10) :
    ¬ FaithInJointArgmaxPrior (muggingPrior r) Finset.univ recT askT := by
  intro h
  obtain ⟨b, _, _, hle⟩ := h true true (Finset.mem_univ _) (by rw [pairMass_rec_ask]; norm_num)
  rw [cellEU_rec_ask, EU_rec, EU_ask_pay, EU_ask_refuse] at hle
  have h1 := (abs_le.mp (hr true)).1
  have h2 := (abs_le.mp (hr false)).2
  linarith

end VingeanMugging

end Cleanroom.Bli.UdtBliTiling
