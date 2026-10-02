import Cleanroom.Decision.DpCalibLimits.Defs

/-!
# T8 — The Definition-6 sampler's act-accuracy from the run law; stipulated accuracies are
inconsistent under Definition 6 and consistent under 6′

[[dp-calib-limits-mandate]] T8 (dp-sl-030, S11, C2-2′(b)).

On the catalogue's opaque Newcomb `opaqueNewcomb p L S` (a predictor `d`-node samples `C(d)`,
the box is filled according to the sample with probability `p`, then the live `d`-node is
queried; worlds `(fill, act)`, `O = ⊤`; two `d`-nodes per run so `RecordsFor` fails — nothing
here assumes recording):

* **The accuracy identity** (`opaque_accuracy`): under `procQ q`, the event "fill ↔ one-box"
  has mass `p (q² + (1−q)²) + (1−p)·2q(1−q)`; at `q = ½` it is `½` for every `p`
  (`opaque_accuracy_half`). Derived from `leafLaw`, not stipulated (the sequence's `acc6` was
  algebra over a `def`).
* **Under the shared seed** (`opaque_accuracy_seed`): the same event has mass `p` at every
  label — the memoised draw makes sample = live act.
* **The two conditional accuracies sum to one under Definition 6** at every label
  (`opaque_cond_acc_sum`, cross-multiplied): `ν(fill ∧ one)·ν(two) + ν(¬fill ∧ two)·ν(one) =
  ν(one)·ν(two)`.
* **Definition-15 inconsistency** (`sigmaPi_not_consistent`): the abstract problem `Σ_π` of
  opaque-Newcomb instantiations (any `p`) with the stipulated state `P_s(fill | one) = π =
  P_s(¬fill | two)`, `π > ½`, is not strictly consistent for any mixed `procQ q`, `q ∈ (0,1)` —
  strict calibration forces the two conditionals to sum to one. Under 6′ the stipulation is
  met by the 6′-statistics at `π = p` (`opaque_seed_stipulation`; N+ at `p = 9/10`, `q = ½`,
  `opaque_seed_instance`).
* **The marginal reading**: the accuracy is at most `q² + (1−q)²` for every `p`, with
  equality at `p = 1` (`opaque_accuracy_le`, `opaque_accuracy_one`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Finset

/-- A sum over the leaves of opaque Newcomb: sample, coin index, live act.
Source: none: infrastructure. Kind: L -/
theorem opaque_sum (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)
    (f : (opaqueNewcomb p h0 h1 L S).Leaves → ℚ) :
    ∑ ℓ, f ℓ = ∑ s : Act2, ∑ i : Fin 2, ∑ l : Act2, f ⟨s, i, l, ()⟩ := by
  unfold opaqueNewcomb at f ⊢
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Tree.sum_leaves_leaf _ _ _

/-- The accuracy event "fill ↔ one-box" (`fill = [act = one]`).
Source: C2-2′(b) (the sampler's act-accuracy); dp-sl-030
Kind: D -/
def accEv : Finset OpaqueW := Finset.univ.filter fun w => w.1 = decide (w.2 = .a)

/-- The events `fill`, `¬fill`, `one`, `two`. Source: dp-sl-030. Kind: D -/
def fillEv : Finset OpaqueW := Finset.univ.filter fun w => w.1 = true

/-- `¬fill`. Source: dp-sl-030. Kind: D -/
def notFillEv : Finset OpaqueW := Finset.univ.filter fun w => w.1 = false

/-- `one` (one-box). Source: dp-sl-030. Kind: D -/
def oneEv : Finset OpaqueW := Finset.univ.filter fun w => w.2 = .a

/-- `two` (two-box). Source: dp-sl-030. Kind: D -/
def twoEv : Finset OpaqueW := Finset.univ.filter fun w => w.2 = .b

section accuracy

variable (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)

local macro "op_eval" : tactic =>
  `(tactic| (simp [opaqueNewcomb, leafLaw, opaqueFill, accEv, fillEv, notFillEv, oneEv, twoEv, Fin.sum_univ_two, Act2.sum_univ, FinDistr.coin, procQ]; try ring))

/-- **The accuracy identity**: `ν_{procQ q}(fill ↔ one) = p(q² + (1−q)²) + (1−p)·2q(1−q)`, from
the run law (index `0`, fill follows the sample: the event is "sample = live act"; index `1`,
fill contradicts the sample: "sample ≠ live act").
Source: C2-2′(b); `C2-msr-identities.lean` `acc6` (algebra over a `def` — re-founded here on
the tree); dp-sl-030
Kind: P
Fidelity: exact
Hyps: none -/
theorem opaque_accuracy :
    nu (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) accEv =
      p * (q ^ 2 + (1 - q) ^ 2) + (1 - p) * (2 * q * (1 - q)) := by
  rw [nu_eq_sum, opaque_sum]; op_eval

/-- At `q = ½` the accuracy is `½` for every `p`. Source: dp-sl-030. Kind: L -/
theorem opaque_accuracy_half :
    nu (procQ (1 / 2) (by norm_num) (by norm_num)) (opaqueNewcomb p h0 h1 L S) accEv = 1 / 2 := by
  rw [opaque_accuracy]; ring

/-- **The marginal reading**: the accuracy is at most `q² + (1−q)²` for every `p`.
Source: mandate T8 ("`P(pred = act) = π` attainable iff `π ≤ q² + (1−q)²` at `p = 1`")
Kind: L -/
theorem opaque_accuracy_le :
    nu (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) accEv ≤ q ^ 2 + (1 - q) ^ 2 := by
  rw [opaque_accuracy]
  nlinarith [sq_nonneg (1 - 2 * q)]

/-- At `p = 1` the accuracy is exactly `q² + (1−q)²`. Source: mandate T8. Kind: L -/
theorem opaque_accuracy_one :
    nu (procQ q hq0 hq1) (opaqueNewcomb 1 zero_le_one le_rfl L S) accEv = q ^ 2 + (1 - q) ^ 2 := by
  rw [opaque_accuracy]; ring

/-- **Under the shared seed the accuracy event has mass `p` at every label**: the memoised
draw makes the live act equal the sample, so the event is "the fill followed the sample".
Source: `seeds.md` Definition 6′; dp-sl-030 ("under 6′ … `p`")
Kind: P
Fidelity: exact
Hyps: none -/
theorem opaque_accuracy_seed :
    nu' (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) accEv = p := by
  unfold nu' worldEv
  rw [Finset.sum_filter, opaque_sum]
  simp [opaqueNewcomb, leafLaw', leafLawSeed, opaqueFill, accEv, Fin.sum_univ_two, Act2.sum_univ,
    FinDistr.coin, procQ, Function.update_self]
  ring

/-- **The two conditional accuracies sum to one under Definition 6** at every label,
cross-multiplied: `ν(fill ∧ one)·ν(two) + ν(¬fill ∧ two)·ν(one) = ν(one)·ν(two)`.
Source: dp-sl-030 ("the two conditional accuracies sum to one"); C2-2′(b)
Kind: P
Fidelity: exact
Hyps: none -/
theorem opaque_cond_acc_sum :
    nu (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) (fillEv ∩ oneEv) *
        nu (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) twoEv +
      nu (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) (notFillEv ∩ twoEv) *
        nu (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) oneEv =
      nu (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) oneEv *
        nu (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) twoEv := by
  simp only [nu_eq_sum, opaque_sum]; op_eval

/-- The four marginal/joint masses under Definition 6. Source: dp-sl-030. Kind: L -/
theorem opaque_masses :
    nu (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) oneEv = q ∧
    nu (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) twoEv = 1 - q ∧
    nu (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) (fillEv ∩ oneEv) =
      q * (p * q + (1 - p) * (1 - q)) ∧
    nu (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) (notFillEv ∩ twoEv) =
      (1 - q) * ((1 - p) * q + p * (1 - q)) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (rw [nu_eq_sum, opaque_sum]; op_eval)

/-- The four masses under the shared seed: `ν'(fill ∧ one) = p q`, `ν'(one) = q`,
`ν'(¬fill ∧ two) = p(1−q)`, `ν'(two) = 1 − q`. Source: `seeds.md` 6′; dp-sl-030. Kind: L -/
theorem opaque_masses_seed :
    nu' (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) oneEv = q ∧
    nu' (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) twoEv = 1 - q ∧
    nu' (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) (fillEv ∩ oneEv) = p * q ∧
    nu' (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) (notFillEv ∩ twoEv) = p * (1 - q) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    (unfold nu' worldEv
     rw [Finset.sum_filter, opaque_sum]
     simp [opaqueNewcomb, leafLaw', leafLawSeed, opaqueFill, fillEv, notFillEv, oneEv, twoEv,
       Fin.sum_univ_two, Act2.sum_univ, FinDistr.coin, procQ, Function.update_self]
     try ring)

end accuracy

/-! ## Definition 15: the stipulated accuracies -/

/-- **The abstract problem `Σ_π`**: opaque-Newcomb instantiations (any reliability `p`) whose
state stipulates the conditional act-accuracies `P_s(fill | one) = π = P_s(¬fill | two)`
(cross-multiplied).
Source: [[decision-problems-v2]] Definition 14; S11; dp-sl-030 ("stipulated accuracies")
Kind: D -/
def sigmaPi (L S π : ℚ) : AbstractProblem OpaqueW Unit (fun _ => Act2) ℚ :=
  {I | (∃ p h0 h1, I.B = opaqueNewcomb p h0 h1 L S) ∧
    (I.s ()).pr (fillEv ∩ oneEv) = π * (I.s ()).pr oneEv ∧
    (I.s ()).pr (notFillEv ∩ twoEv) = π * (I.s ()).pr twoEv}

/-- The live point is queried. Source: none: infrastructure. Kind: L -/
theorem opaque_queried (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) :
    () ∈ queried (opaqueNewcomb p h0 h1 L S) := by
  unfold opaqueNewcomb
  rw [queried_decision]
  exact Finset.mem_insert_self _ _

/-- **Definition-15 inconsistency**: for `π > ½` and any mixed label `q ∈ (0,1)`, `Σ_π` is not
strictly consistent for `procQ q` — a strictly calibrated state has `P_s = ν` (`O = ⊤`), and
the two conditional accuracies under Definition 6 sum to one, so `2π = 1`.
Source: S11; dp-sl-030 ("stipulated accuracies are inconsistent"); C2-2′(b)
Kind: P
Fidelity: exact (the class of sampler trees is quantified through `p`)
Hyps: (a) `½ < π`, (a) `0 < q < 1` -/
theorem sigmaPi_not_consistent (L S π : ℚ) (hπ : 1 / 2 < π) (q : ℚ) (hq0 : 0 < q) (hq1 : q < 1) :
    ¬ Consistent .strict opaqueObs (sigmaPi L S π) (procQ q hq0.le hq1.le) := by
  rintro ⟨I, ⟨⟨p, h0, h1, hB⟩, hs1, hs2⟩, hcal⟩
  have hq := hcal () (by rw [hB]; exact opaque_queried p h0 h1 L S)
  have hpos : 0 < nu (procQ q hq0.le hq1.le) I.B (opaqueObs ()) := by
    show 0 < nu _ I.B Finset.univ; exact nu_univ_pos _ _
  obtain ⟨hc1, -⟩ := hq hpos
  have hP : ∀ X, (I.s ()).pr X = nu (procQ q hq0.le hq1.le) I.B X := fun X => by
    have := hc1 X
    simp only [opaqueObs, nu_univ, mul_one, Finset.inter_univ] at this
    exact this
  rw [hP, hP] at hs1 hs2
  rw [hB] at hs1 hs2
  obtain ⟨hone, htwo, hfo, hnt⟩ := opaque_masses p h0 h1 L S q hq0.le hq1.le
  rw [hfo, hone] at hs1
  rw [hnt, htwo] at hs2
  have e1 : p * q + (1 - p) * (1 - q) = π := by
    have := mul_right_cancel₀ hq0.ne' (by linarith : (p * q + (1 - p) * (1 - q)) * q = π * q)
    exact this
  have e2 : (1 - p) * q + p * (1 - q) = π := by
    have h1q : (1 - q) ≠ 0 := by linarith
    have := mul_right_cancel₀ h1q
      (by linarith : ((1 - p) * q + p * (1 - q)) * (1 - q) = π * (1 - q))
    exact this
  linarith

/-- **Under the shared seed the stipulation is met by the 6′-statistics at `π = p`**: the
state whose probability is `ν'` satisfies `P(fill ∧ one) = p·P(one)` and
`P(¬fill ∧ two) = p·P(two)` for every label.
Source: dp-sl-030 ("consistent under 6′"); `seeds.md` Definition 6′
Kind: P
Fidelity: variant: stated on the 6′-statistics (`dp-calibration` has no 6′ calibration sense)
Hyps: none -/
theorem opaque_seed_stipulation (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S q : ℚ) (hq0 : 0 ≤ q)
    (hq1 : q ≤ 1) :
    nu' (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) (fillEv ∩ oneEv) =
        p * nu' (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) oneEv ∧
    nu' (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) (notFillEv ∩ twoEv) =
        p * nu' (procQ q hq0 hq1) (opaqueNewcomb p h0 h1 L S) twoEv := by
  obtain ⟨hone, htwo, hfo, hnt⟩ := opaque_masses_seed p h0 h1 L S q hq0 hq1
  rw [hone, htwo, hfo, hnt]
  exact ⟨rfl, rfl⟩

/-- N+ at `p = 9/10`, `q = ½`: the 6′-statistics give the stipulated accuracies `9/10`, while
under Definition 6 no state can (`sigmaPi_not_consistent` at `π = 9/10`).
Source: dp-sl-030; mandate T8(d)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem opaque_seed_instance (L S : ℚ) :
    nu' (procQ (1 / 2) (by norm_num) (by norm_num)) (opaqueNewcomb (9 / 10) (by norm_num) (by norm_num) L S)
        (fillEv ∩ oneEv) =
      9 / 10 * nu' (procQ (1 / 2) (by norm_num) (by norm_num))
        (opaqueNewcomb (9 / 10) (by norm_num) (by norm_num) L S) oneEv ∧
    ¬ Consistent .strict opaqueObs (sigmaPi L S (9 / 10)) (procQ (1 / 2) (by norm_num) (by norm_num)) :=
  ⟨(opaque_seed_stipulation _ _ _ L S _ _ _).1,
    sigmaPi_not_consistent L S (9 / 10) (by norm_num) (1 / 2) (by norm_num) (by norm_num)⟩

end Cleanroom.Decision.DpCalibLimits
