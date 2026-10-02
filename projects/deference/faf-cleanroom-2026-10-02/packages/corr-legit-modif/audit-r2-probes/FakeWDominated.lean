import Cleanroom.Corrigibility.CorrLegitModif.Y1Model

/-!
# Audit probe (corr-legit-modif, round 2, adversarial): faking where `σ_A = w` loses

The report's surviving neighbour (ii) of the refuted sentence reads "legitimate" as `L^refl`
(Reflection toward the install from the agent's `σ_A`-informed state) and says "the dodged
modification is *not* legitimate and the sentence stands". `y1_informed_not_reflectsWrt` shows
`L^refl` fails on **both** cells, `σ_A = r` and `σ_A = w`. This probe adds what the package does
not state: the policy that dodges in the *other* cell, `fake_w` (modify-rate `0` on the `σ_A = w`
cells), is worth `29/40 = 725/1000 < 77/100` at `P(L) = 1` — lgf Statement 8(d)'s "faking where
`σ_A = w` … is also never chosen", machine-checked. So under a *per-cell* `L^refl` reading the
sentence "correct iff illegitimate" still fails in the if-direction (illegitimate at `w`, and
dodging there is wrong); the neighbour survives at the *modification* level only (the overwriting
install fails `L^refl`, is dodged; the additive one passes, is not). The report should say which.

Model as `Y1Model`; the own continuation at a faked `σ_A = w` cell is `P(· | σ_A = w)`, with
`P(W | σ_A = w) = 1/2` → stop; the `σ_A = r` cells are honest. Hand check: the `r` cells contribute
`725/1000` under both policies, the `w` cells `45/1000` under honesty and `0` under `fake_w`.
-/

namespace AuditProbe

open Finset Cleanroom.Corrigibility.CorrLegitModif

noncomputable section

/-- The modify-rate under `fake_w`: zero on the `σ_A = w` cells of both `ℓ`-branches. -/
def modRateW (ℓ s a : Bool) : ℝ := if a then 0 else pMod ℓ s

/-- The `fake_w` policy joint. -/
def y1FakeW (lam : ℝ) : Y1W → ℝ := fun w =>
  pL lam w.1 * pS w.2.1 * pSig w.2.1 w.2.2.1 *
    (if w.2.2.2 then modRateW w.1 w.2.1 w.2.2.1 else 1 - modRateW w.1 w.2.1 w.2.2.1)

def ownWW (lam : ℝ) (a : Bool) : ℝ := ∑ ℓ, y1FakeW lam (ℓ, true, a, false)

def ownRW (lam : ℝ) (a : Bool) : ℝ := ∑ ℓ, y1FakeW lam (ℓ, false, a, false)

def decidesW (lam : ℝ) (w : Y1W) : Prop :=
  if w.2.2.2 then contOf qowW qowR else contOf (ownWW lam w.2.2.1) (ownRW lam w.2.2.1)

open Classical in
def valueW (lam : ℝ) : ℝ := ∑ w, y1FakeW lam w * (if decidesW lam w then X w.2.1 else 0)

/-- Under `fake_w` the faked `σ_A = w` cell stops (`P(W | σ_A = w) = 1/2`) and the honest
`σ_A = r` keep cell continues (`1/730`). -/
theorem own_decisions_W :
    ¬ contOf (ownWW 1 true) (ownRW 1 true) ∧ contOf (ownWW 1 false) (ownRW 1 false) := by
  constructor <;>
    norm_num [contOf, ownWW, ownRW, y1FakeW, pL, pS, pSig, pMod, modRateW, eps, Fintype.sum_bool]

theorem fake_w_value : valueW 1 = 29 / 40 := by
  have hd := installed_decisions.1
  have ho := own_decisions_W
  simp only [valueW, decidesW, Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_false, if_true, hd, ho.1, ho.2]
  norm_num [y1FakeW, pL, pS, pSig, pMod, modRateW, X, eps]

/-- `V(fake_w) = 29/40 < 77/100 = V(honest)` at `P(L) = 1`. -/
theorem fake_w_dominated : valueW 1 < y1Value 1 false false := by
  rw [fake_w_value, y1_values.1]; norm_num

end

end AuditProbe
