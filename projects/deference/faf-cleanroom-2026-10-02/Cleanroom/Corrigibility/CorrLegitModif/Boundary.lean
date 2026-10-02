import Cleanroom.Corrigibility.CorrLegitModif.Y1Model

/-!
# corr-legit-modif — T14 (extension of record): the dodge boundary

The Y1 family with `P(L) = λ ∈ [0, 1]` and own-signal rates `(a, b) = (P(σ_A = w | R),
P(σ_A = w | W))`, kernel and stakes fixed. The two policies differ only on the `σ_A = r` cells, so
`V(fake_r) − V(honest)` is the sum over those cells of mass × [payoff of the own decision without a
verdict − (modify-rate × payoff of the install + keep-rate × payoff of the own decision after
keep)], piecewise linear in `λ` with breakpoints where decisions flip. The install `Q_ow` always
stops (`installed_decisions`). With `A := [9 (1 − a) − 4 (1 − b)]/10` (the `σ_A = r` cells' total
expectation, deciding the faked continuation: `own_faked_continue_iff`) and
`K := [9 (1 − a)(1 + 8λ) − 4 (1 − b)(9 − 8λ)]/100` (their keep part, deciding the honest
continuation after `keep`: `own_keep_continue_iff`), the gain is `[A > 0] · A − [K > 0] · K` on
every `(λ, a, b)` (`gain_eq`), so **the dodge set is exactly `A > 0 ∧ A − K > 0`**:
`4 (1 − b) < 9 (1 − a) ∧ 4 (1 − b)(1 + 8λ) < 9 (1 − a)(9 − 8λ)` (`dodge_iff`, no regime
hypothesis; repair round 1). On Y1's regime (`A > 0`, `K > 0`) the gain is
`A − K = [9 (1 − a)(9 − 8λ) − 4 (1 − b)(1 + 8λ)]/100` (`gain_on_regime`, `dodge_iff_on_regime`);
off the regime a dodge still happens, e.g. at `λ = 0`, `(a, b) = (0, 1/10)` (`dodge_off_regime`).
At Y1's rates both regime conditions and the dodge condition hold for every `λ ∈ [0, 1]`
(`y1_rates_regime`).

**The retention form** (corr-wf14b-2-016): the install interpolated between `Q_ow` and `Q_add(σ_A)`
by a retention `r ∈ [0, 1]` as a mixture of the two distributions (a modelling choice, (c)). The
mixture's decision at `σ_A = r` flips at `r = 3/4` (`retention_step`), so the gain is a **step**:
`9/200` for `r ≤ 3/4`, `0` for `r > 3/4` (`retention_gain`) — it vanishes at `r = 1` and is positive
at `r = 0`, as the mandate says, but it is *not* continuous in `r`. Under the other construal — a
*randomized* install, the additive state with probability `r` — the gain is `(1 − r) · 9/200`,
linear (`randomized_gain`); so "continuous in `r`" is construal-dependent (findings F10).
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

/-! ## The `(λ, a, b)` family -/

/-- The own signal with rates `(a, b)`: `P(σ_A = w | R) = a`, `P(σ_A = w | W) = b`.
Source: mandate T14 ("own-signal rates `(a, b)`")
Kind: D
Fidelity: exact -/
def pSigF (a b : ℝ) (s aa : Bool) : ℝ :=
  if s then (if aa then b else 1 - b) else (if aa then a else 1 - a)

/-- The policy joint of the `(λ, a, b)` family.
Source: mandate T14
Kind: D
Fidelity: exact -/
def y1Fam (lam a b : ℝ) (fake : Bool) : Y1W → ℝ := fun w =>
  pL lam w.1 * pS w.2.1 * pSigF a b w.2.1 w.2.2.1 *
    (if w.2.2.2 then modRate fake w.1 w.2.1 w.2.2.1 else 1 - modRate fake w.1 w.2.1 w.2.2.1)

/-- At Y1's rates the family is the model of record.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem y1Fam_eq_y1Pol (lam : ℝ) (fake : Bool) (w : Y1W) :
    y1Fam lam (1 / 10) (9 / 10) fake w = y1Pol lam fake w := by
  simp only [y1Fam, y1Pol, pSigF, pSig]
  norm_num

/-- The own continuation's `W`-mass at `(keep, σ_A = aa)` in the family.
Source: mandate T14
Kind: D
Fidelity: exact -/
def ownWF (lam a b : ℝ) (fake aa : Bool) : ℝ := ∑ ℓ, y1Fam lam a b fake (ℓ, true, aa, false)

/-- The own continuation's `R`-mass at `(keep, σ_A = aa)` in the family.
Source: mandate T14
Kind: D
Fidelity: exact -/
def ownRF (lam a b : ℝ) (fake aa : Bool) : ℝ := ∑ ℓ, y1Fam lam a b fake (ℓ, false, aa, false)

/-- The family's decision at a world (overwriting install, which always stops).
Source: mandate T14
Kind: D
Fidelity: exact -/
def decidesF (lam a b : ℝ) (fake : Bool) (w : Y1W) : Prop :=
  if w.2.2.2 then contOf qowW qowR else contOf (ownWF lam a b fake w.2.2.1) (ownRF lam a b fake w.2.2.1)

open Classical in
/-- The family's policy value.
Source: mandate T14
Kind: D
Fidelity: exact -/
def famValue (lam a b : ℝ) (fake : Bool) : ℝ :=
  ∑ w, y1Fam lam a b fake w * (if decidesF lam a b fake w then X w.2.1 else 0)

open Classical in
/-- At Y1's rates the family value is the overwriting value of record.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem famValue_eq_y1Value (lam : ℝ) (fake : Bool) :
    famValue lam (1 / 10) (9 / 10) fake = y1Value lam fake false := by
  unfold famValue y1Value
  apply sum_congr rfl
  intro w _
  simp only [decidesF, decides, ownWF, ownRF, ownW, ownR, y1Fam_eq_y1Pol, Bool.false_eq_true,
    if_false]

/-- The own continuation at `σ_A = w` is the same under both policies (`fake_r` touches only the
`σ_A = r` cells).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ownF_w_eq (lam a b : ℝ) :
    ownWF lam a b true true = ownWF lam a b false true ∧ ownRF lam a b true true = ownRF lam a b false true := by
  constructor <;> simp [ownWF, ownRF, y1Fam, modRate]

/-! ## The regime boundaries -/

/-- **Own decision without a verdict** (the faked cell): continue iff `4 (1 − b) < 9 (1 − a)`
(`λ` cancels).
Source: mandate T14 ("the regime's boundaries proved")
Kind: L
Fidelity: exact -/
theorem own_faked_continue_iff (lam a b : ℝ) :
    contOf (ownWF lam a b true false) (ownRF lam a b true false) ↔ 4 * (1 - b) < 9 * (1 - a) := by
  simp only [contOf, ownWF, ownRF, y1Fam, pL, pS, pSigF, modRate, pMod, eps, Fintype.sum_bool]
  norm_num
  constructor <;> intro h <;> nlinarith

/-- **Own decision after `keep`** (honest, `σ_A = r`): continue iff
`4 (1 − b)(9 − 8λ) < 9 (1 − a)(1 + 8λ)`.
Source: mandate T14
Kind: L
Fidelity: exact -/
theorem own_keep_continue_iff (lam a b : ℝ) :
    contOf (ownWF lam a b false false) (ownRF lam a b false false) ↔
      4 * (1 - b) * (9 - 8 * lam) < 9 * (1 - a) * (1 + 8 * lam) := by
  simp only [contOf, ownWF, ownRF, y1Fam, pL, pS, pSigF, modRate, pMod, eps, Fintype.sum_bool]
  norm_num
  constructor <;> intro h <;> nlinarith

/-! ## The gain -/

open Classical in
/-- **The gain in closed form, on every regime** (`gain_eq`): with `A := [9 (1 − a) − 4 (1 − b)]/10`
(the `σ_A = r` cells' total expectation of `X`, which decides the own faked continuation) and
`K := [9 (1 − a)(1 + 8λ) − 4 (1 − b)(9 − 8λ)]/100` (their keep part, which decides the own honest
continuation after `keep`), `V(fake_r) − V(honest) = [A > 0] · A − [K > 0] · K`: the faked policy
collects `A` when it continues, and the honest policy collects `K` when its keep branch continues,
the install always stopping. The four decision cells of the mandate's "piecewise linear in `λ` with
breakpoints where decisions flip", in one identity.
Source: mandate T14; [[legitimacy-general-final]] Statement 15(b) l. 81; audit round 1
(fidelity N1)
Kind: P
Fidelity: exact (every `(λ, a, b)`; no regime hypothesis)
Hyps: (a) none -/
theorem gain_eq (lam a b : ℝ) :
    famValue lam a b true - famValue lam a b false =
      (if 4 * (1 - b) < 9 * (1 - a) then (9 * (1 - a) - 4 * (1 - b)) / 10 else 0) -
      (if 4 * (1 - b) * (9 - 8 * lam) < 9 * (1 - a) * (1 + 8 * lam) then
        (9 * (1 - a) * (1 + 8 * lam) - 4 * (1 - b) * (9 - 8 * lam)) / 100 else 0) := by
  have h3 := installed_decisions.1
  obtain ⟨hw1, hw2⟩ := ownF_w_eq lam a b
  by_cases hF : 4 * (1 - b) < 9 * (1 - a) <;>
    by_cases hK : 4 * (1 - b) * (9 - 8 * lam) < 9 * (1 - a) * (1 + 8 * lam) <;>
    · unfold famValue
      simp only [decidesF, Fintype.sum_prod_type, Fintype.sum_bool]
      simp only [hw1, hw2, own_faked_continue_iff, own_keep_continue_iff, hF, hK, h3, if_true,
        if_false]
      norm_num [y1Fam, pL, pS, pSigF, modRate, pMod, X, eps] <;> ring

/-- **`dodge_iff`, the full characterization**: the overwriting modification is dodged iff
`4 (1 − b) < 9 (1 − a)` (the faked own continuation continues: `A > 0`) and
`4 (1 − b)(1 + 8λ) < 9 (1 − a)(9 − 8λ)` (the modify part of the `σ_A = r` cells is positive:
`A − K > 0`) — `{(λ, a, b) : V(fake_r) > V(honest)}` exactly, with no regime hypothesis. The
former `dodge_iff_on_regime`'s second regime condition (`K > 0`) was superfluous: when the honest
keep branch stops, the dodge collects all of `A`.
Source: mandate T14 ("characterise `{(λ, a, b) : V(fake_r) > V(honest)}`"); audit round 1
(fidelity N1: brute force on 8 400 grid points agrees)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem dodge_iff (lam a b : ℝ) :
    famValue lam a b false < famValue lam a b true ↔
      4 * (1 - b) < 9 * (1 - a) ∧ 4 * (1 - b) * (1 + 8 * lam) < 9 * (1 - a) * (9 - 8 * lam) := by
  rw [← sub_pos, gain_eq lam a b]
  by_cases hF : 4 * (1 - b) < 9 * (1 - a)
  · rw [if_pos hF]
    by_cases hK : 4 * (1 - b) * (9 - 8 * lam) < 9 * (1 - a) * (1 + 8 * lam)
    · rw [if_pos hK]
      exact ⟨fun H => ⟨hF, by linarith⟩, fun H => by linarith [H.2]⟩
    · rw [if_neg hK]
      have hK' := not_lt.1 hK
      exact ⟨fun _ => ⟨hF, by linarith⟩, fun _ => by linarith⟩
  · rw [if_neg hF]
    refine ⟨fun H => ?_, fun H => absurd H.1 hF⟩
    exfalso
    by_cases hK : 4 * (1 - b) * (9 - 8 * lam) < 9 * (1 - a) * (1 + 8 * lam)
    · rw [if_pos hK] at H; linarith
    · rw [if_neg hK] at H; linarith

/-- **The gain on Y1's regime** (`gain_on_regime`): when the own decision at `σ_A = r` is "continue"
both without a verdict and after `keep`, `V(fake_r) − V(honest) = [9 (1 − a)(9 − 8λ) − 4 (1 − b)(1 + 8λ)]/100`
— the mass of the `σ_A = r` cells that the honest policy hands to the (stopping) install, weighted
by the stakes. The `(A > 0, K > 0)` cell of `gain_eq`.
Source: mandate T14; [[legitimacy-general-final]] Statement 15(b) l. 81
Kind: C (`gain_eq`)
Fidelity: exact (on the regime; `gain_eq` has the other three cells)
Hyps: (a) the two regime conditions -/
theorem gain_on_regime (lam a b : ℝ) (hR1 : 4 * (1 - b) < 9 * (1 - a))
    (hR2 : 4 * (1 - b) * (9 - 8 * lam) < 9 * (1 - a) * (1 + 8 * lam)) :
    famValue lam a b true - famValue lam a b false =
      (9 * (1 - a) * (9 - 8 * lam) - 4 * (1 - b) * (1 + 8 * lam)) / 100 := by
  rw [gain_eq, if_pos hR1, if_pos hR2]; ring

/-- **`dodge_iff_on_regime`**: on Y1's regime the overwriting modification is dodged iff
`9 (1 − a)(9 − 8λ) > 4 (1 − b)(1 + 8λ)`. Kept as the mandate's regime form; `dodge_iff` is the
full characterization (and shows `hR2` is not needed).
Source: mandate T14 (the exact set of `(λ, a, b)` at which an overwriting modification is dodged,
on the regime)
Kind: C (`dodge_iff`)
Fidelity: exact (on the regime)
Hyps: (a) the two regime conditions (the second superfluous) -/
theorem dodge_iff_on_regime (lam a b : ℝ) (hR1 : 4 * (1 - b) < 9 * (1 - a))
    (_hR2 : 4 * (1 - b) * (9 - 8 * lam) < 9 * (1 - a) * (1 + 8 * lam)) :
    famValue lam a b false < famValue lam a b true ↔
      4 * (1 - b) * (1 + 8 * lam) < 9 * (1 - a) * (9 - 8 * lam) := by
  rw [dodge_iff]
  exact ⟨fun h => h.2, fun h => ⟨hR1, h⟩⟩

/-- **A dodge outside Y1's regime**: at `λ = 0`, `(a, b) = (0, 1/10)` the honest keep branch at
`σ_A = r` stops (`K = −9/50 ≤ 0`, outside the regime) and the faked policy still wins, with gain
`A = 27/50`. Added at audit round 1 (fidelity N1: 1 333 of 2 929 off-regime grid points dodge).
Source: audit round 1 (fidelity N1); mandate T14
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem dodge_off_regime :
    ¬ (4 * (1 - 1 / 10 : ℝ) * (9 - 8 * 0) < 9 * (1 - 0) * (1 + 8 * 0)) ∧
    famValue 0 0 (1 / 10) false < famValue 0 0 (1 / 10) true ∧
    famValue 0 0 (1 / 10) true - famValue 0 0 (1 / 10) false = 27 / 50 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [dodge_iff]; norm_num
  · rw [gain_eq]; norm_num

/-- **Y1's rates are inside the regime for every `λ ∈ [0, 1]`**, and the dodge condition holds
throughout: `fake_r` beats honesty at every `P(L)`, with gain `(725 − 680 λ)/1000`.
Source: mandate T14; [[legitimacy-general-final]] Proofs ll. 124–134 (the Y1 table's column)
Kind: N+
Fidelity: exact
Hyps: (a) `0 ≤ λ ≤ 1` -/
theorem y1_rates_regime (lam : ℝ) (hl : 0 ≤ lam ∧ lam ≤ 1) :
    4 * (1 - 9 / 10 : ℝ) < 9 * (1 - 1 / 10) ∧
    4 * (1 - 9 / 10 : ℝ) * (9 - 8 * lam) < 9 * (1 - 1 / 10) * (1 + 8 * lam) ∧
    4 * (1 - 9 / 10 : ℝ) * (1 + 8 * lam) < 9 * (1 - 1 / 10) * (9 - 8 * lam) ∧
    y1Value lam true false - y1Value lam false false = (725 - 680 * lam) / 1000 := by
  refine ⟨by norm_num, by nlinarith [hl.1, hl.2], by nlinarith [hl.1, hl.2], ?_⟩
  rw [← famValue_eq_y1Value, ← famValue_eq_y1Value,
    gain_on_regime lam (1 / 10) (9 / 10) (by norm_num) (by nlinarith [hl.1, hl.2])]
  ring

/-! ## The retention form -/

/-- The retention install's `W`-mass: the mixture `(1 − r) Q_ow + r Q_add(σ_A)` of the two
distributions, in product form (`Q_ow` carried by `(qowW, qowR)`, `Q_add` by `(qaddW, qaddR)`).
A modelling choice (c): the retention is a mixture of states, not a refinement.
Source: corr-wf14b-2-016 (the retention form); mandate T14 (second form)
Kind: D
Fidelity: variant: mixture interpolation (disclosed, (c)) -/
def qrW (r : ℝ) (aa : Bool) : ℝ :=
  (1 - r) * qowW * (qaddW aa + qaddR aa) + r * qaddW aa * (qowW + qowR)

/-- The retention install's `R`-mass.
Source: as `qrW`
Kind: D
Fidelity: variant: mixture interpolation (disclosed, (c)) -/
def qrR (r : ℝ) (aa : Bool) : ℝ :=
  (1 - r) * qowR * (qaddW aa + qaddR aa) + r * qaddR aa * (qowW + qowR)

/-- The decision rule with the retention install.
Source: mandate T14 (second form)
Kind: D
Fidelity: exact -/
def decidesR (r : ℝ) (fake : Bool) (w : Y1W) : Prop :=
  if w.2.2.2 then contOf (qrW r w.2.2.1) (qrR r w.2.2.1)
  else contOf (ownW 1 fake w.2.2.1) (ownR 1 fake w.2.2.1)

open Classical in
/-- The policy value at `P(L) = 1` with the retention install.
Source: mandate T14 (second form)
Kind: D
Fidelity: exact -/
def retValue (r : ℝ) (fake : Bool) : ℝ :=
  ∑ w, y1Pol 1 fake w * (if decidesR r fake w then X w.2.1 else 0)

/-- **The mixture's decision flips at `r = 3/4`**: at `σ_A = r` the retention install continues iff
`3/4 < r`; at `σ_A = w` it stops for every `r ∈ [0, 1]`.
Source: mandate T14 (second form)
Kind: L
Fidelity: exact -/
theorem retention_step (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) :
    (contOf (qrW r false) (qrR r false) ↔ 3 / 4 < r) ∧ ¬ contOf (qrW r true) (qrR r true) := by
  constructor
  · simp only [contOf, qrW, qrR, qowW, qowR, qaddW, qaddR, eps, pMod, pSig]
    norm_num
    constructor <;> intro h <;> linarith
  · simp only [contOf, qrW, qrR, qowW, qowR, qaddW, qaddR, eps, pMod, pSig]
    norm_num
    nlinarith [hr.1, hr.2]

open Classical in
/-- **`retention_gain`**: the gain `V(fake_r) − V(honest)` with the retention install is the step
`9/200` for `r ≤ 3/4` and `0` for `r > 3/4` — positive at `r = 0`, vanishing at `r = 1`, and
discontinuous at `3/4` (the mandate's "continuous in `r`" is false for hard decisions; findings).
Source: corr-wf14b-2-016; mandate T14 (second form)
Kind: C (`retention_step`, `own_decisions`, then closed numerals)
Fidelity: exact (mixture form, (c) disclosed)
Hyps: (a) `0 ≤ r ≤ 1` -/
theorem retention_gain (r : ℝ) (hr : 0 ≤ r ∧ r ≤ 1) :
    retValue r true - retValue r false = if r ≤ 3 / 4 then 9 / 200 else 0 := by
  obtain ⟨hstep, hw⟩ := retention_step r hr
  have ho := own_decisions
  unfold retValue
  simp only [decidesR, Fintype.sum_prod_type, Fintype.sum_bool, Bool.false_eq_true, if_false,
    if_true, hstep, hw, ho.1 true, ho.1 false, ho.2.1 true, ho.2.1 false]
  simp only [y1Pol, pL, pS, pSig, modRate, pMod, X, eps]
  by_cases h : 3 / 4 < r
  · simp [h, not_le.2 h]; norm_num
  · simp [h, not_lt.1 h]; norm_num

/-- **The randomized install** (the other reading of corr-wf14b-2-016's retention measure, "the
fraction of the agent's decision-relevant information the installed state conditions on"): with
probability `r` the additive state is installed, with `1 − r` the overwriting one, the decisions
staying hard. Its value is the mixture of the two policy values. A second (c) construal, disclosed.
Source: corr-wf14b-2-016; mandate T14 (second form); audit round 1 (fidelity N2)
Kind: D
Fidelity: variant: randomized install (c) -/
def randValue (r : ℝ) (fake : Bool) : ℝ :=
  r * y1Value 1 fake true + (1 - r) * y1Value 1 fake false

/-- **The randomized install's gain is linear**: `(1 − r) · 9/200` — continuous, positive at `0`,
zero at `1`. So the mandate's "continuous in `r`" is construal-dependent: a step for the state
mixture (`retention_gain`), linear for the randomized install (findings F10).
Source: corr-wf14b-2-016; mandate T14 (second form); audit round 1 (fidelity N2)
Kind: L (`y1_values`)
Fidelity: exact for the randomized construal
Hyps: (a) none -/
theorem randomized_gain (r : ℝ) : randValue r true - randValue r false = (1 - r) * (9 / 200) := by
  obtain ⟨h1, h2, h3, h4, -, -, -, -⟩ := y1_values
  unfold randValue
  rw [h1, h2, h3, h4]; ring

end

end Cleanroom.Corrigibility.CorrLegitModif
