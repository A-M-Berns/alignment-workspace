import Cleanroom.Found.DpCoreTree.Overwrite
import Cleanroom.Decision.DpCalibration.Mugging
import Cleanroom.Decision.DpCausalConsist.TbTheta
import Cleanroom.Decision.DpCausalConsist.Witness3

/-!
# `dp-causal-consist`: Definition PR and the battery rows (T10)

`Responsive C B d X := ∃ a b, ν_{C[d↦a]}(X) ≠ ν_{C[d↦b]}(X)` (`Defs.lean`). Definition 22's
evaluator satisfies PR by construction — that is a tautology (dp-core-103's own flag), stated as
`dev_satisfies_PR` with `Kind: T` and not promoted. The content is the rows, each an exact
computation on a catalogue tree:

* **overwrite** (`dp-core-tree`'s `overwrite`, `ℓ ∼ Bern(1/2)`, `δ = 1/2`, `γ = (1/4, 3/4)`): the
  cancer coordinate `k` is **non-responsive** — `ν_{C[d↦m]}(k) = 1/2` for both `m`
  (`overwrite_k_nonResponsive`); on the (S1) family likewise (`s1Fam_k_nonResponsive`).
* **opaque Newcomb** (`opaqueNewcomb p L S`, policy-reading predictor): the fill is **responsive**
  for `p ≠ 1/2` — `ν_{C[d↦one]}(fill) = p`, `ν_{C[d↦two]}(fill) = 1 − p` — and the deviation gap is
  `V(C[d↦one]) − V(C[d↦two]) = (2p − 1)L − S` (`opaque_fill_responsive`, `opaque_dev_gap`).
* **`TB(θ)`**: `bot` is **non-responsive** (`ν(bot) = θ` at every label) and the deviation gap is
  `10(1 − θ)` (`tb_bot_nonResponsive`, `tb_dev_gap`).
* **counterfactual mugging** (`mug1 x y`): Omega's prediction — the `T`-branch transfer event
  `{tPay}` — is **responsive** (`ν_{C[d↦pay]} = 1/2`, `ν_{C[d↦refuse]} = 0`), and the deviation
  pays iff `y > x` (`mug_prediction_responsive`, `mug_pay_iff`).
-/

namespace Cleanroom.Decision.DpCausalConsist

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue
  Cleanroom.Decision.DpCalibration Finset

/-- **Definition 22's evaluator satisfies PR by construction** — a tautology: an evaluator that
ranks acts by `V_B(C[d ↦ a])` moves exactly the events whose `ν_{C[d↦a]}` varies with `a`. Stated
so that it is not mistaken for a theorem: it is `Iff.rfl`.
Source: [[policy-responsiveness]] ("Definition 22's evaluator satisfies PR by construction");
mandate T10 (`dev_satisfies_PR`, "a tautology (kind `T`, say so)")
Kind: T -/
theorem dev_satisfies_PR {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
    [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)] (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ)
    (d : ι) (X : Finset Ω) :
    Responsive C B d X ↔ ∃ a b : acts d, nu (C.deviatePure d a) B X ≠ nu (C.deviatePure d b) B X :=
  Iff.rfl

/-! ## Overwrite: the cancer coordinate is non-responsive -/

/-- `ν_{C[d↦m]}(k = 1) = 1/2` on the overwrite tree for both `m`: the lesion rate `1/2` and
`γ = (1/4, 3/4)` give `1/2 · 3/4 + 1/2 · 1/4` whatever the label.
Source: [[policy-responsiveness]] battery row 1 ("lesion / cancer: `ν(k) = ε_L γ₁ + (1−ε_L) γ₀`
at every `p`"); mandate T10
Kind: N+ -/
theorem overwrite_k_value (m : Bool) :
    nu (owProc.deviatePure () m) overwrite (Finset.univ.filter fun w => w.2.2 = true) = 1/2 := by
  rw [overwrite_nu]
  simp only [Fin.sum_univ_two, Fintype.sum_bool, Finset.mem_filter, Finset.mem_univ, true_and]
  simp [overwrite, FinDistr.fair, FinDistr.coin, Proc.deviatePure, Proc.deviate, owM]
  cases m <;> norm_num

/-- **The cancer coordinate is not policy-responsive on the overwrite tree.**
Source: [[policy-responsiveness]] battery row 1 ("responsive? no"); mandate T10
Kind: N+ -/
theorem overwrite_k_nonResponsive :
    ¬ Responsive owProc overwrite () (Finset.univ.filter fun w => w.2.2 = true) := by
  rw [not_responsive_iff]
  intro a b
  rw [overwrite_k_value, overwrite_k_value]

/-- **The cancer coordinate is not policy-responsive on the (S1) tree** (no direct effect), for
every label.
Source: [[policy-responsiveness]] battery row 1 ("and on `s1Tree`"); mandate T10
Kind: N+ -/
theorem s1Fam_k_nonResponsive (ρ : ℚ) (r0 : 0 ≤ ρ) (r1 : ρ ≤ 1) (γ : Bool → ℚ)
    (g0 : ∀ ℓ, 0 ≤ γ ℓ) (g1 : ∀ ℓ, γ ℓ ≤ 1) (u : W3 → ℚ) (C : Proc Unit (fun _ => Bool) ℚ) :
    ¬ Responsive C (s1Fam ρ r0 r1 (fun ℓ _ => γ ℓ) (fun ℓ _ => g0 ℓ) (fun ℓ _ => g1 ℓ) u) ()
      (Finset.univ.filter fun x : W3 => x 2 = true) := by
  rw [not_responsive_iff]
  intro a b
  have hX : (Finset.univ.filter fun x : W3 => x 2 = true)
      = {pt3 false false true, pt3 false true true, pt3 true false true, pt3 true true true} := by
    decide
  have hsum : ∀ C' : Proc Unit (fun _ => Bool) ℚ,
      nu C' (s1Fam ρ r0 r1 (fun ℓ _ => γ ℓ) (fun ℓ _ => g0 ℓ) (fun ℓ _ => g1 ℓ) u)
        (Finset.univ.filter fun x : W3 => x 2 = true)
      = (1 - ρ) * γ false * ((C' ()).w false + (C' ()).w true)
        + ρ * γ true * ((C' ()).w false + (C' ()).w true) := by
    intro C'
    rw [hX, nu_eq_sum_singleton, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
    simp only [s1Fam_nu_singleton]
    simp
    ring
  rw [hsum, hsum]
  have ha : (C.deviatePure () a ()).w false + (C.deviatePure () a ()).w true = 1 := by
    have := (C.deviatePure () a ()).sum_one
    rwa [Fintype.sum_bool, add_comm] at this
  have hb : (C.deviatePure () b ()).w false + (C.deviatePure () b ()).w true = 1 := by
    have := (C.deviatePure () b ()).sum_one
    rwa [Fintype.sum_bool, add_comm] at this
  rw [ha, hb]

/-! ## Opaque Newcomb: the fill is responsive -/

/-- `ν` on opaque Newcomb as an eight-term sum. Source: none: infrastructure. Kind: L -/
theorem opaqueNewcomb_nu (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)
    (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset OpaqueW) :
    nu C (opaqueNewcomb p h0 h1 L S) X =
      ∑ s : Act2, ∑ i : Fin 2, ∑ l : Act2,
        if (opaqueFill s i, l) ∈ X then
          (C ()).w s * ((FinDistr.coin p h0 h1).w i * (C ()).w l) else 0 := by
  rw [nu_eq_sum]
  unfold opaqueNewcomb
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Tree.sum_leaves_leaf]
  simp only [leafLaw_decision, leafLaw_chance, leafLaw_leaf, mul_one]
  rfl

/-- `V_B(C)` on opaque Newcomb. Source: none: infrastructure. Kind: L -/
theorem opaqueNewcomb_value (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ)
    (C : Proc Unit (fun _ => Act2) ℚ) :
    value C (opaqueNewcomb p h0 h1 L S) =
      ∑ s : Act2, ∑ i : Fin 2, ∑ l : Act2,
        (C ()).w s * ((FinDistr.coin p h0 h1).w i * (C ()).w l) * opaquePay L S (opaqueFill s i, l) := by
  unfold value
  unfold opaqueNewcomb
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [sum_leaves_chance]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sum_leaves_decision]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Tree.sum_leaves_leaf]
  simp only [leafLaw_decision, leafLaw_chance, leafLaw_leaf, mul_one]
  rfl

/-- The fill event `{fill = 1}`. Source: `sl-synthesis.md` line 120. Kind: D -/
def fillEv : Finset OpaqueW := Finset.univ.filter fun w => w.1 = true

/-- `ν_{C[d↦one]}(fill) = p`, `ν_{C[d↦two]}(fill) = 1 − p`: the deviation moves the predictor.
Source: [[policy-responsiveness]] battery row 2 ("Newcomb, perfect policy-reading Omega … `Ω`
responsive: yes"); mandate T10
Kind: N+ -/
theorem opaque_fill_dev (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) (C : Proc Unit (fun _ => Act2) ℚ) :
    nu (C.deviatePure () Act2.a) (opaqueNewcomb p h0 h1 L S) fillEv = p ∧
    nu (C.deviatePure () Act2.b) (opaqueNewcomb p h0 h1 L S) fillEv = 1 - p := by
  constructor <;>
  · rw [opaqueNewcomb_nu]
    simp [Act2.sum_univ, Fin.sum_univ_two, fillEv, opaqueFill, FinDistr.coin, Proc.deviatePure,
      Proc.deviate]

/-- **The fill is policy-responsive on opaque Newcomb** for `p ≠ 1/2`.
Source: [[policy-responsiveness]] battery rows 2–3 ("yes iff `r_D ≠ 1/2`"); mandate T10
Kind: N+ -/
theorem opaque_fill_responsive (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (hp : p ≠ 1/2) (L S : ℚ)
    (C : Proc Unit (fun _ => Act2) ℚ) :
    Responsive C (opaqueNewcomb p h0 h1 L S) () fillEv := by
  refine ⟨Act2.a, Act2.b, ?_⟩
  rw [(opaque_fill_dev p h0 h1 L S C).1, (opaque_fill_dev p h0 h1 L S C).2]
  intro h; apply hp; linarith

/-- **The deviation gap on opaque Newcomb**: `V(C[d↦one]) − V(C[d↦two]) = (2p − 1)L − S`.
Source: [[policy-responsiveness]] ("Newcomb with a simulation node: the deviation moves Omega's
draw too"); mandate T10 (`value (dev one) − value (dev two) = (2p−1)L − S`)
Kind: N+ -/
theorem opaque_dev_gap (p : ℚ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (L S : ℚ) (C : Proc Unit (fun _ => Act2) ℚ) :
    value (C.deviatePure () Act2.a) (opaqueNewcomb p h0 h1 L S)
      - value (C.deviatePure () Act2.b) (opaqueNewcomb p h0 h1 L S) = (2 * p - 1) * L - S := by
  rw [opaqueNewcomb_value, opaqueNewcomb_value]
  simp [Fin.sum_univ_two, opaqueFill, opaquePay, FinDistr.coin, Proc.deviatePure, Proc.deviate]
  ring

/-! ## `TB(θ)`: `bot` is non-responsive -/

/-- `ν_{C[d↦a]}(bot) = θ` for every label and act.
Source: [[policy-responsiveness]] ("`bot` is a root, unmoved"); mandate T10
Kind: N+ -/
theorem tb_bot_dev (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (C : Proc Unit (fun _ => Act2) ℚ) (a : Act2) :
    nu (C.deviatePure () a) (tbTheta θ h0 h1) (cell exoBot true) = θ := by
  rw [tbTheta_nu]
  simp [cell, exoBot, Act2.sum_univ]

/-- **`bot` is not policy-responsive on `TB(θ)`.**
Source: [[policy-responsiveness]] battery row 7 ("Con(PA): a root, `ν` constant in `C`: no");
mandate T10
Kind: N+ -/
theorem tb_bot_nonResponsive (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (C : Proc Unit (fun _ => Act2) ℚ) :
    ¬ Responsive C (tbTheta θ h0 h1) () (cell exoBot true) := by
  rw [not_responsive_iff]
  intro a b
  rw [tb_bot_dev, tb_bot_dev]

/-- **The deviation gap on `TB(θ)` is `10(1 − θ)`.**
Source: [[policy-responsiveness]] ("the run's bypass-shaped TB(θ) gap `10(1−θ)`"); mandate T10
Kind: N+ -/
theorem tb_dev_gap (θ : ℚ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) (C : Proc Unit (fun _ => Act2) ℚ) :
    value (C.deviatePure () Act2.a) (tbTheta θ h0 h1) - value (C.deviatePure () Act2.b) (tbTheta θ h0 h1)
      = 10 * (1 - θ) := by
  rw [tbTheta_value, tbTheta_value]
  simp [Proc.deviatePure, Proc.deviate]
  ring

/-! ## Counterfactual mugging: Omega's prediction is responsive -/

/-- `ν_{C[d↦pay]}({tPay}) = 1/2`, `ν_{C[d↦refuse]}({tPay}) = 0`: the transfer on the `T` branch
tracks the label.
Source: [[policy-responsiveness]] battery row 6 ("counterfactual mugging: Omega's prediction:
yes"); mandate T10
Kind: N+ -/
theorem mug_tPay_dev (x y : ℚ) (C : Proc Unit (fun _ => Act2) ℚ) :
    nu (C.deviatePure () Act2.a) (mug1 x y) {MugW.tPay} = 1/2 ∧
    nu (C.deviatePure () Act2.b) (mug1 x y) {MugW.tPay} = 0 := by
  constructor <;>
  · rw [mug1_nu]
    simp [Proc.deviatePure, Proc.deviate]

/-- **Omega's prediction is policy-responsive on the mugging.**
Source: [[policy-responsiveness]] battery row 6; mandate T10
Kind: N+ -/
theorem mug_prediction_responsive (x y : ℚ) (C : Proc Unit (fun _ => Act2) ℚ) :
    Responsive C (mug1 x y) () {MugW.tPay} := by
  refine ⟨Act2.a, Act2.b, ?_⟩
  rw [(mug_tPay_dev x y C).1, (mug_tPay_dev x y C).2]
  norm_num

/-- **The deviation pays iff `y > x`**: `V(C[d↦pay]) − V(C[d↦refuse]) = (y − x)/2`.
Source: [[policy-responsiveness]] battery row 6 ("PR verdict: pay iff `y > x`"); mandate T10
Kind: N+ -/
theorem mug_pay_iff (x y : ℚ) (C : Proc Unit (fun _ => Act2) ℚ) :
    value (C.deviatePure () Act2.b) (mug1 x y) < value (C.deviatePure () Act2.a) (mug1 x y) ↔ x < y := by
  rw [mug1_value, mug1_value]
  simp [Proc.deviatePure, Proc.deviate]

end Cleanroom.Decision.DpCausalConsist
