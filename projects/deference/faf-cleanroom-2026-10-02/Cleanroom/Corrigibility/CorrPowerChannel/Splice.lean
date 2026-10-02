import Cleanroom.Found.CorrThreeStep.TwoState
import Cleanroom.Corrigibility.CorrPowerChannel.Power
import Mathlib.Data.Fin.VecNotation

/-!
# `corr-power-channel` — T5: the splice bound and the J2-shaped external cap

* **Objects (D).** A behavioural evaluation is a context law `μE : Distr X` and a predicate
  `pass : X → Y → Bool` on context–output pairs; a policy is `π : X → Distr Y`; its pass rate is
  `passRate μE π pass = ∑ x, μE x · ∑ y, π x y · 𝟙[pass x y]`. A discriminator `d : X → Bool`
  (`true` = "this is the test") has test error `discErr μE d = μE(d = false)`; the splice
  `splice d πw πb` plays `πw` where `d` says test and `πb` elsewhere. `Reliable μE pass η α wise
  cls`: wise policies pass at rate `≥ 1 − η`, unwise policies in the class at rate `≤ α`.
* **(a) `splice_bound`** (load-bearing 1): `1 − η ≤ passRate μE πw` gives
  `passRate μE (splice d πw πb) ≥ (1 − η) − discErr μE d` (a union bound on finite sums);
  `splice_alpha_bound` adds (H2) the splice is in the class and (H3) it is not wise, and
  reliability, to get `α ≥ passRate (splice) ≥ (1 − η) − δE`. Every one of (H1)–(H3) is a named
  hypothesis; the bound is a worst case over the class, not a statement about the agent in hand
  (S5.3). Witness E4 (`e4_realized`): `X = Fin 5` uniform, `Y = Fin 2`, `η = 1/20`, a discriminator
  wrong on one context (`δE = 1/5`), `πw` passing at `19/20`, `πb` never passing: the splice
  passes at `19/25 ≥ 3/4`.
* **(b) `unlock_iff`**: `εα/(εα + (1−ε)β) ≤ c′/(c′+h′) ↔ α/β ≤ ((1−ε)/ε)(c′/h′)`, which is
  `corr-three-step`'s base-rate inequality with roles renamed (`unlock_iff_deltaMinus`: it is
  `0 ≤ Δ₋` of `twoState (1 − ε) α β h′ c′`, hence `epsStar α β h′ c′ ≤ 1 − ε` —
  `unlock_iff_epsStar`, repair round 2).
* **(c) The mixture identity** `alphaE σ pS pN = σ pS + (1 − σ) pN` and the R5 table.

Sources: power-wisdom-final.md S5 (l. 109), S6 (l. 113), P4 (l. 165–167), D19–D20 (l. 91–93);
power-wisdom-adversary.md D.5 (l. 23), S5.3 (l. 85), S6.1–S6.2 (l. 53–55); scripts E4, R5.
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect expect_const

noncomputable section

set_option linter.unusedSectionVars false

section Splice

variable {X Y : Type} [Fintype X] [Fintype Y]

/-- **Pass probability of a policy at a context**: `∑ y, π x y · 𝟙[pass x y]`.
Source: power-wisdom-final.md D19 (l. 91)
Kind: D
Fidelity: exact -/
def passProb (π : X → Distr Y) (pass : X → Y → Bool) (x : X) : ℝ :=
  ∑ y, (π x).mass y * (if pass x y then 1 else 0)

/-- **Pass rate** `p_E(π) = P_{x∼μE, y∼π(x)}[pass = 1]`.
Source: power-wisdom-final.md D19 (l. 91)
Kind: D
Fidelity: exact -/
def passRate (μ : Distr X) (π : X → Distr Y) (pass : X → Y → Bool) : ℝ :=
  ∑ x, μ.mass x * passProb π pass x

/-- `0 ≤ passProb`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem passProb_nonneg (π : X → Distr Y) (pass : X → Y → Bool) (x : X) : 0 ≤ passProb π pass x :=
  sum_nonneg fun y _ => mul_nonneg ((π x).nonneg y) (by split_ifs <;> norm_num)

/-- `passProb ≤ 1`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem passProb_le_one (π : X → Distr Y) (pass : X → Y → Bool) (x : X) : passProb π pass x ≤ 1 := by
  unfold passProb
  calc ∑ y, (π x).mass y * (if pass x y then 1 else 0) ≤ ∑ y, (π x).mass y :=
        sum_le_sum fun y _ => by
          split_ifs
          · simp
          · simp [(π x).nonneg y]
    _ = 1 := (π x).sum_eq_one

/-- **The discriminator's test error** `δE = μE(d = false)`: the mass of test contexts the
discriminator mistakes for deployment.
Source: power-wisdom-final.md D20 (l. 93)
Kind: D
Fidelity: exact -/
def discErr (μ : Distr X) (d : X → Bool) : ℝ := ∑ x, μ.mass x * (if d x then 0 else 1)

/-- **The splice** `πw ▷_d πb`: play `πw` where `d` says "test", `πb` elsewhere.
Source: power-wisdom-final.md D20 (l. 93)
Kind: D
Fidelity: exact -/
def splice (d : X → Bool) (πw πb : X → Distr Y) : X → Distr Y := fun x => if d x then πw x else πb x

/-- The pass probability of the splice at a context is that of `πw` or `πb` as `d` decides.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem passProb_splice (d : X → Bool) (πw πb : X → Distr Y) (pass : X → Y → Bool) (x : X) :
    passProb (splice d πw πb) pass x = if d x then passProb πw pass x else passProb πb pass x := by
  unfold passProb splice
  split_ifs <;> rfl

/-- **Reliability of an evaluation at `(η, α)`** on a capability class: wise policies pass at rate
`≥ 1 − η`; unwise policies in the class pass at rate `≤ α`. `α` is a worst case over the class
(D.5), not the base rate `P(pass | unwise)` of S6.
Source: power-wisdom-final.md D19 (l. 91); power-wisdom-adversary.md D.5 (l. 23)
Kind: D
Fidelity: exact -/
structure Reliable (μE : Distr X) (pass : X → Y → Bool) (η α : ℝ) (wise cls : Set (X → Distr Y)) :
    Prop where
  /-- wise policies pass -/
  wise_pass : ∀ π ∈ wise, 1 - η ≤ passRate μE π pass
  /-- unwise policies in the class fail -/
  unwise_fail : ∀ π ∈ cls, π ∉ wise → passRate μE π pass ≤ α

/-- **The splice bound (S5, the arithmetic): `p_E(πw ▷_d πb) ≥ (1 − η) − δE`** whenever
`p_E(πw) ≥ 1 − η`. Union bound: the splice agrees with `πw` on `{d = true}`, and `πw`'s pass
mass on `{d = false}` is at most `δE`.
Source: power-wisdom-final.md S5 (l. 109); P4 (l. 167, "union bound")
Kind: P
Fidelity: exact
Hyps: (a) `1 − η ≤ p_E(πw)` is (H1)'s wise-policy clause, named -/
theorem splice_bound (μE : Distr X) (pass : X → Y → Bool) (d : X → Bool) (πw πb : X → Distr Y)
    {η : ℝ} (hw : 1 - η ≤ passRate μE πw pass) :
    (1 - η) - discErr μE d ≤ passRate μE (splice d πw πb) pass := by
  have h1 : ∀ x, μE.mass x * passProb πw pass x ≤
      μE.mass x * (if d x then passProb πw pass x else 0) + μE.mass x * (if d x then 0 else 1) := by
    intro x
    split_ifs with hd
    · simp
    · simp only [mul_zero, zero_add, mul_one]
      exact le_trans (mul_le_mul_of_nonneg_left (passProb_le_one πw pass x) (μE.nonneg x))
        (le_of_eq (mul_one _))
  have h2 : ∀ x, μE.mass x * (if d x then passProb πw pass x else 0) ≤
      μE.mass x * passProb (splice d πw πb) pass x := by
    intro x
    rw [passProb_splice]
    split_ifs with hd
    · exact le_rfl
    · simp only [mul_zero]
      exact mul_nonneg (μE.nonneg x) (passProb_nonneg _ _ _)
  have hA : passRate μE πw pass ≤
      (∑ x, μE.mass x * (if d x then passProb πw pass x else 0)) + discErr μE d := by
    unfold passRate discErr
    rw [← sum_add_distrib]
    exact sum_le_sum fun x _ => h1 x
  have hB : (∑ x, μE.mass x * (if d x then passProb πw pass x else 0)) ≤
      passRate μE (splice d πw πb) pass := by
    unfold passRate
    exact sum_le_sum fun x _ => h2 x
  linarith

/-- **S5 in full: `α ≥ p_E(πw ▷_d πb) ≥ (1 − η) − δE`** under reliability and the three
hypotheses — (H1) `πw` is wise (so it passes at `≥ 1 − η`), (H2) the splice is in the capability
class, (H3) the splice is not wise. **This bounds the meter's worst case over the class, not its
behaviour on the agent in hand**: a wise agent never chooses the splice (S5.3). **Kind L** (repair
round 1): the `≤ α` clause is the field `Reliable.unwise_fail` applied at (H2), (H3) — `α` is a
free parameter of `Reliable`, so that clause has exactly the content of the hypothesis; the content
of the theorem is `splice_bound` (P). The Lean's (H1) is the wise-policy clause; the source's (H1)
(`d ∈ C_t`, the class contains the discriminator) is not modelled, since `d` ranges over all
functions. The full package is inhabited by `e4_reliable`/`e4_alpha_bound` (`Witnesses.lean`).
Source: power-wisdom-final.md S5 (l. 109); power-wisdom-adversary.md S5.3 (l. 85)
Kind: L
Fidelity: exact
Hyps: (a) reliability and (H1)–(H3), all named; the premise that a capable class contains a
discriminator and the splice (Carlsmith's prerequisites, D20) is what (H1)–(H2) assume -/
theorem splice_alpha_bound (μE : Distr X) (pass : X → Y → Bool) {η α : ℝ}
    {wise cls : Set (X → Distr Y)} (hR : Reliable μE pass η α wise cls) (d : X → Bool)
    {πw πb : X → Distr Y} (H1 : πw ∈ wise) (H2 : splice d πw πb ∈ cls)
    (H3 : splice d πw πb ∉ wise) :
    (1 - η) - discErr μE d ≤ passRate μE (splice d πw πb) pass ∧
      passRate μE (splice d πw πb) pass ≤ α :=
  ⟨splice_bound μE pass d πw πb (hR.wise_pass πw H1), hR.unwise_fail _ H2 H3⟩

end Splice

/-! ## E4 — the floors, realized -/

/-- A two-point `Distr (Fin 2)` with mass `p` on `1`. Source: none: infrastructure. Kind: D.
Fidelity: n/a -/
def twoPtFin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : Distr (Fin 2) where
  mass := ![1 - p, p]
  nonneg := fun s => by fin_cases s <;> simp <;> linarith
  sum_eq_one := by simp [Fin.sum_univ_two]

/-- E4's wise policy: passes with probability `19/20` on every context (output `0` passes).
Source: power-wisdom-final.md P4 (l. 167, "E4 at `η = 1/20`"); script E4
Kind: D
Fidelity: n/a (witness) -/
def e4W : Fin 5 → Distr (Fin 2) := fun _ => twoPtFin (1 / 20) (by norm_num) (by norm_num)

/-- E4's bad policy: never passes (always output `1`).
Source: script E4. Kind: D. Fidelity: n/a (witness) -/
def e4B : Fin 5 → Distr (Fin 2) := fun _ => twoPtFin 1 (by norm_num) le_rfl

/-- E4's pass predicate: output `0` passes. Source: script E4. Kind: D. Fidelity: n/a -/
def e4Pass : Fin 5 → Fin 2 → Bool := fun _ y => decide (y = 0)

/-- E4's discriminator: right on four of five uniform contexts (`δE = 1/5`).
Source: script E4 (the `δE = 1/5` row). Kind: D. Fidelity: n/a -/
def e4D : Fin 5 → Bool := fun x => decide (x ≠ 4)

/-- Sum over `Fin 5`, expanded. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sum_fin5 (f : Fin 5 → ℝ) : ∑ x, f x = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp [Fin.sum_univ_succ]
  ring

/-- **E4 realized (N+):** on `X = Fin 5` uniform with `η = 1/20`: the wise policy passes at
exactly `19/20 = 1 − η`, the discriminator errs on mass `1/5`, and the splice passes at `19/25`,
at or above the floor `(1 − η) − δE = 3/4`. (The other three E4 floors `9/20, 9/10, 47/50` are
the same arithmetic at `δE = 1/2, 1/20, 1/100`: `e4_floors`.)
Source: power-wisdom-final.md P4 (l. 167, "floors `9/20, 3/4, 9/10, 47/50`"); script E4
Kind: N+
Fidelity: exact
Hyps: none -/
theorem e4_realized :
    passRate (Distr.uniform : Distr (Fin 5)) e4W e4Pass = 19 / 20 ∧
      discErr (Distr.uniform : Distr (Fin 5)) e4D = 1 / 5 ∧
      passRate (Distr.uniform : Distr (Fin 5)) (splice e4D e4W e4B) e4Pass = 19 / 25 ∧
      (1 - 1 / 20 : ℝ) - 1 / 5 ≤ 19 / 25 := by
  have hu : ∀ x : Fin 5, (Distr.uniform : Distr (Fin 5)).mass x = 1 / 5 := fun x => by
    simp [Distr.uniform]
  have hw : ∀ x, passProb e4W e4Pass x = 19 / 20 := fun x => by
    simp [passProb, e4W, e4Pass, twoPtFin, Fin.sum_univ_two]
    norm_num
  have hb : ∀ x, passProb e4B e4Pass x = 0 := fun x => by
    simp [passProb, e4B, e4Pass, twoPtFin, Fin.sum_univ_two]
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · simp only [passRate, hu, hw, sum_fin5]
    norm_num
  · simp only [discErr, hu, sum_fin5, e4D]
    rw [if_pos (by decide), if_pos (by decide), if_pos (by decide), if_pos (by decide),
      if_neg (by decide)]
    norm_num
  · have hsx : ∀ x, x ≠ 4 → passProb (splice e4D e4W e4B) e4Pass x = 19 / 20 := by
      intro x hx
      rw [passProb_splice]
      simp [e4D, hx, hw]
    have hs4 : passProb (splice e4D e4W e4B) e4Pass 4 = 0 := by
      rw [passProb_splice]
      simp [e4D, hb]
    simp only [passRate, sum_fin5]
    rw [hu 0, hu 1, hu 2, hu 3, hu 4, hsx 0 (by decide), hsx 1 (by decide), hsx 2 (by decide),
      hsx 3 (by decide), hs4]
    norm_num

/-- **The four E4 floors** `(1 − η) − δE` at `η = 1/20` and `δE = 1/2, 1/5, 1/20, 1/100`:
`9/20, 3/4, 9/10, 47/50`.
Source: power-wisdom-final.md P4 (l. 167); script E4
Kind: N+
Fidelity: exact
Hyps: none -/
theorem e4_floors :
    (1 - 1 / 20 : ℝ) - 1 / 2 = 9 / 20 ∧ (1 - 1 / 20 : ℝ) - 1 / 5 = 3 / 4 ∧
      (1 - 1 / 20 : ℝ) - 1 / 20 = 9 / 10 ∧ (1 - 1 / 20 : ℝ) - 1 / 100 = 47 / 50 := by
  norm_num

/-! ## (b) The unlock inequality -/

/-- **S6/108: the unlock arithmetic.** `P(unwise | pass) = εα/(εα + (1−ε)β) ≤ c′/(c′+h′)` iff
`α/β ≤ ((1−ε)/ε)(c′/h′)`, under `0 < ε < 1`, `0 < β`, `0 < h′`, `0 ≤ α`, `0 ≤ c′`. This is
`corr-three-step`'s base-rate inequality (position statement §2.13(b)) with the roles renamed
(`unlock_iff_deltaMinus`); 108 is 004 relabelled.
Source: power-wisdom-final.md S6 (l. 113); P4 (l. 167, "Unlock arithmetic");
power-wisdom-adversary.md S6.1 (l. 95)
Kind: L
Fidelity: exact (finding: the source's "`≲`" is "`≤`")
Hyps: (a) the positivity hypotheses are where the ratios are defined -/
theorem unlock_iff {ε α β c h : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hβ : 0 < β) (hh : 0 < h)
    (hα : 0 ≤ α) (hc : 0 ≤ c) :
    ε * α / (ε * α + (1 - ε) * β) ≤ c / (c + h) ↔ α / β ≤ (1 - ε) / ε * (c / h) := by
  have hden : 0 < ε * α + (1 - ε) * β :=
    add_pos_of_nonneg_of_pos (mul_nonneg hε0.le hα) (mul_pos (by linarith) hβ)
  have hch : 0 < c + h := by linarith
  rw [div_le_div_iff₀ hden hch, div_mul_div_comm, div_le_div_iff₀ hβ (mul_pos hε0 hh)]
  constructor <;> intro H <;> nlinarith

/-- **The unlock inequality is `corr-three-step`'s `0 ≤ Δ₋` with roles renamed**: with
`ε′ = 1 − ε` (the wise base rate as the "wrong" mass), the pass rates `(α, β)` as the press rates,
and the stakes `(h′, c′)` as `(c, h)`, `εαh′ ≤ (1 − ε)βc′` is `twoState_deltaMinus_nonneg_iff`'s
`(1 − ε′)αc ≤ ε′βh`; hence by `twoState_deltaMinus_nonneg_iff_epsStar` it is
`epsStar α β h′ c′ ≤ 1 − ε`.
Source: power-wisdom-final.md S6 (l. 113); [[corr-power-channel-mandate]] T5(b) ("cite `epsStar`")
Kind: L
Fidelity: exact
Hyps: (a) the pass rates and `ε` lie in `[0, 1]` (so the two-state instance exists); positivity as
in `unlock_iff` -/
theorem unlock_iff_deltaMinus {ε α β c h : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hβ : 0 < β) (hh : 0 < h)
    (hα : 0 ≤ α) (hc : 0 ≤ c) (hα1 : α ≤ 1) (hβ1 : β ≤ 1) :
    ε * α / (ε * α + (1 - ε) * β) ≤ c / (c + h) ↔
      0 ≤ (twoState (1 - ε) α β h c ⟨by linarith, by linarith⟩ ⟨hα, hα1⟩ ⟨hβ.le, hβ1⟩).deltaMinus
        () .cont .stop := by
  rw [twoState_deltaMinus_nonneg_iff, unlock_iff hε0 hε1 hβ hh hα hc, div_mul_div_comm,
    div_le_div_iff₀ hβ (mul_pos hε0 hh)]
  constructor <;> intro H <;> nlinarith

/-- **The unlock inequality as `corr-three-step`'s `ε*`**: `P(unwise | pass) ≤ c′/(c′+h′)` iff
`epsStar α β h′ c′ ≤ 1 − ε` — `twoState_deltaMinus_nonneg_iff_epsStar` at the two-state instance
of `unlock_iff_deltaMinus`; the mandate's "cite `epsStar`" line, stated rather than re-derived.
Source: power-wisdom-final.md S6 (l. 113); [[corr-power-channel-mandate]] T5(b) ("cite
`epsStar`"); [[corr-power-channel-audit-r2-fidelity]] N7
Kind: L
Fidelity: exact
Hyps: (a) as in `unlock_iff_deltaMinus`, plus `0 < αh′ + βc′` (`corr-three-step`'s junk-value
guard for `ε*`; it holds whenever `0 < α` or `0 < c′`) -/
theorem unlock_iff_epsStar {ε α β c h : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) (hβ : 0 < β) (hh : 0 < h)
    (hα : 0 ≤ α) (hc : 0 ≤ c) (hα1 : α ≤ 1) (hβ1 : β ≤ 1) (hpos : 0 < α * h + β * c) :
    ε * α / (ε * α + (1 - ε) * β) ≤ c / (c + h) ↔ epsStar α β h c ≤ 1 - ε := by
  rw [unlock_iff_deltaMinus hε0 hε1 hβ hh hα hc hα1 hβ1,
    twoState_deltaMinus_nonneg_iff_epsStar (hpos := hpos)]

/-! ## (c) The schemer-fraction mixture and the R5 table -/

/-- **The false-pass base rate as a mixture**: `α^E = σ · p_E(splice) + (1 − σ) · p_E(non-splice
unwise)`, `σ` the fraction of unwise agents that are discriminating splices.
Source: power-wisdom-final.md S6 (l. 113); power-wisdom-adversary.md S6.2 (l. 97)
Kind: D
Fidelity: exact -/
def alphaE (σ pS pN : ℝ) : ℝ := σ * pS + (1 - σ) * pN

/-- The required false-pass rate for a rational unlock: `((1−ε)/ε)(c′/h′)β`.
Source: power-wisdom-final.md P4 (l. 167, "required `α ≤ …`")
Kind: D
Fidelity: exact -/
def reqAlpha (ε β c h : ℝ) : ℝ := (1 - ε) / ε * (c / h) * β

/-- R5's harm schedule `h′ = 1/2, 1, 2, 4`. Source: script R5. Kind: D. Fidelity: n/a -/
def r5H : Fin 4 → ℝ := ![1 / 2, 1, 2, 4]

/-- R5's discriminator errors `δE = 1/2, 1/5, 1/20, 1/100`. Source: script R5. Kind: D.
Fidelity: n/a -/
def r5DE : Fin 4 → ℝ := ![1 / 2, 1 / 5, 1 / 20, 1 / 100]

/-- R5's splice floors `(1 − 1/20) − δE`. Source: script R5. Kind: D. Fidelity: n/a -/
def r5Floor (t : Fin 4) : ℝ := (1 - 1 / 20) - r5DE t

/-- **R5 (N+): a fixed behavioural test passes at every step for a small schemer fraction and
fails at `t = 2, 3` for a large one.** With `ε = 1/10`, `β = 19/20`, `c′ = 1/10`, non-splice
pass rate `1/20` and `(h′, δE)` as in `r5H`, `r5DE`: `alphaE σ floor_t (1/20) ≤ reqAlpha` at all
four `t` for `σ ∈ {0, 1/10}`, and fails at `t = 2, 3` for `σ ∈ {1/2, 1}` (it passes at `t = 0, 1`
for those too). "`h′_t` rises with POWER" is `[conjectured]` in the source and is not a claim here.
Source: power-wisdom-final.md S6 (l. 113, "R5"); P4 (l. 167); script R5
Kind: N+
Fidelity: exact
Hyps: none -/
theorem r5_table :
    (∀ t : Fin 4, alphaE 0 (r5Floor t) (1 / 20) ≤ reqAlpha (1 / 10) (19 / 20) (1 / 10) (r5H t)) ∧
      (∀ t : Fin 4, alphaE (1 / 10) (r5Floor t) (1 / 20) ≤
        reqAlpha (1 / 10) (19 / 20) (1 / 10) (r5H t)) ∧
      (∀ t : Fin 4, (t : ℕ) ≤ 1 →
        alphaE (1 / 2) (r5Floor t) (1 / 20) ≤ reqAlpha (1 / 10) (19 / 20) (1 / 10) (r5H t) ∧
        alphaE 1 (r5Floor t) (1 / 20) ≤ reqAlpha (1 / 10) (19 / 20) (1 / 10) (r5H t)) ∧
      (∀ t : Fin 4, 2 ≤ (t : ℕ) →
        ¬ alphaE (1 / 2) (r5Floor t) (1 / 20) ≤ reqAlpha (1 / 10) (19 / 20) (1 / 10) (r5H t) ∧
        ¬ alphaE 1 (r5Floor t) (1 / 20) ≤ reqAlpha (1 / 10) (19 / 20) (1 / 10) (r5H t)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t; fin_cases t <;> norm_num [alphaE, reqAlpha, r5Floor, r5H, r5DE]
  · intro t; fin_cases t <;> norm_num [alphaE, reqAlpha, r5Floor, r5H, r5DE]
  · intro t ht; fin_cases t <;> norm_num at ht <;> norm_num [alphaE, reqAlpha, r5Floor, r5H, r5DE]
  · intro t ht; fin_cases t <;> norm_num at ht <;> norm_num [alphaE, reqAlpha, r5Floor, r5H, r5DE]

end

end Cleanroom.Corrigibility.CorrPowerChannel
