import Cleanroom.Corrigibility.CorrPowerChannel.Evpi
import Cleanroom.Corrigibility.CorrChannelVoi.Sensors

/-!
# `corr-power-channel` — T4(a): J3 in the E3 family, the legitimate channel, `δ ≤ μh`

The E3 family at `n + 1` plans: hypotheses `ω = (π, mind) : Fin (n+1) × Bool` with `π` uniform
and `P(mind) = μ`; options `plan j` worth `𝟙[j = π]`, `∅` worth `0`, the scan `s` a pure
experiment (gain `0`, harm `h·𝟙[mind]`) revealing `π` (`ofMap Prod.fst`); the legitimate channel
`q` revealing `π` with probability `1 − δ` and sending the silent signal `none` otherwise (its
kernel is stated explicitly — a uniform-noise channel would be a different experiment).

Closed forms (all proved): `EVPI(plans) = 1 − 1/(n+1)`, `VOI(s) = 1 − 1/(n+1)`,
`E[harm(s)] = μh`, `VOI(q) = (1−δ)(1 − 1/(n+1))`, `VOI(s, q) = 1 − 1/(n+1)` (Blackwell squeeze),
marginal `VOI(s | q) = δ(1 − 1/(n+1))`. Hence absolute J3 at `n+1` plans iff `1 − 1/(n+1) < μh`
(`e3_j3_iff`; at `μ = h = 1/2` iff `n = 0`), and **J3 against asking first at every `n` iff
`δ ≤ μh`** (`e3_j3Given_all_iff`, under `0 < μh`). The degenerate cells `δ = 0` and `n = 0` are
in range.

General theorems used: `voiExp_mono_blackwell` (a garbling has no more VOI — Blackwell
monotonicity for `voiExp`), `voiExp_perfect_eq_evpi` (needs `[DecidableEq Ω]`), `voiExp_trivial`.

Continuation set: the J3 iffs below are over the plan set; D18's full `A_{t+1} = plans ∪ {∅, s}`
gives the same iffs because `∅` and `s` are dominated (`e3_j3_iff_cont`, `e3_j3Given_iff_cont`,
`Witnesses.lean`, via `voiExp_insert_dominated`).

Sources: power-wisdom-final.md S2 (l. 103), P2 (l. 157–159); power-wisdom-adversary.md S2.1–S2.2
(l. 34–36); script E3 (`j3_table`).
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Corrigibility.CorrChannelVoi (expProd expProd_k trivialExp perfectExp
  blackwellLE_right_prod blackwellLE_left_prod)
open Cleanroom.Corrigibility.CorrCautionPower (harmOf harmOf_nonneg harmOf_nul)
open Finset hiding expect expect_const

noncomputable section

set_option linter.unusedSectionVars false

variable {A Ω : Type} [Fintype A] [DecidableEq A] [Fintype Ω]

/-! ## General facts about `voiExp` -/

/-- `sup'` of a nonnegative multiple. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sup'_const_mul {B : Finset A} (hB : B.Nonempty) {c : ℝ} (hc : 0 ≤ c) (f : A → ℝ) :
    B.sup' hB (fun b => c * f b) = c * B.sup' hB f := by
  apply le_antisymm
  · rw [sup'_le_iff]
    intro b hb
    exact mul_le_mul_of_nonneg_left (le_sup' f hb) hc
  · obtain ⟨b, hb, h⟩ := exists_mem_eq_sup' hB f
    rw [h]
    exact le_sup' (fun b => c * f b) hb

/-- `sup'` over `univ` of `c · 𝟙[s = j]` is `c` for `c ≥ 0`. Source: none: infrastructure.
Kind: L. Fidelity: n/a -/
theorem sup'_univ_scaled_indicator {T : Type} [Fintype T] [DecidableEq T] [Nonempty T] {c : ℝ}
    (hc : 0 ≤ c) (s : T) :
    univ.sup' univ_nonempty (fun j => c * if s = j then 1 else 0) = c := by
  apply le_antisymm
  · rw [sup'_le_iff]
    intro j _
    split_ifs <;> simp [hc]
  · refine le_trans ?_ (le_sup' (fun j => c * if s = j then 1 else 0) (mem_univ s))
    simp

/-- **Blackwell monotonicity for `voiExp`**: a garbling of an experiment has no more value of
information, for every posterior, value table and option set. Proof: the garbled informed value
is `∑_t max_b ∑_s g s t · (signal gain at s)`, which by Jensen (`sup'_sum_le_sum_sup'_finset`
with the nonnegative weights `g s t`) is at most `∑_s max_b (signal gain at s)` since `∑_t g s t = 1`.
Source: none: infrastructure (Blackwell 1953 for the finite experiment of record; used for the
E3 product channel)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem voiExp_mono_blackwell {S T : Type} [Fintype S] [Fintype T] (P : Distr Ω) (V : Ω → A → ℝ)
    {k₁ : Experiment Ω S} {k₂ : Experiment Ω T} (h : BlackwellLE k₂ k₁) {B : Finset A}
    (hB : B.Nonempty) : voiExp P V k₂ B hB ≤ voiExp P V k₁ B hB := by
  obtain ⟨g, hg, hgar⟩ := h
  unfold voiExp
  apply sub_le_sub_right
  -- rewrite the garbled signal gains through `g`
  have e : ∀ t b, ∑ ω, P.mass ω * k₂.k ω t * V ω b =
      ∑ s, g s t * ∑ ω, P.mass ω * k₁.k ω s * V ω b := by
    intro t b
    calc ∑ ω, P.mass ω * k₂.k ω t * V ω b
        = ∑ ω, ∑ s, g s t * (P.mass ω * k₁.k ω s * V ω b) := by
          refine sum_congr rfl fun ω _ => ?_
          rw [hgar ω t, mul_sum, sum_mul]
          exact sum_congr rfl fun s _ => by ring
      _ = ∑ s, g s t * ∑ ω, P.mass ω * k₁.k ω s * V ω b := by
          rw [sum_comm]
          simp only [mul_sum]
  simp only [e]
  calc ∑ t, B.sup' hB (fun b => ∑ s, g s t * ∑ ω, P.mass ω * k₁.k ω s * V ω b)
      ≤ ∑ t, ∑ s, g s t * B.sup' hB (fun b => ∑ ω, P.mass ω * k₁.k ω s * V ω b) :=
        sum_le_sum fun t _ =>
          sup'_sum_le_sum_sup'_finset hB (p := fun s => g s t) (fun s => (hg s).1 t) _
    _ = ∑ s, B.sup' hB (fun b => ∑ ω, P.mass ω * k₁.k ω s * V ω b) := by
        rw [sum_comm]
        refine sum_congr rfl fun s _ => ?_
        rw [← sum_mul, (hg s).2, one_mul]

/-- **The perfect experiment is worth exactly `EVPI`**: `voiExp P V perfectExp B = evpi P V B`.
Source: power-wisdom-final.md D12/D16 (l. 61, 73: EVPI is the VOI of perfect information)
Kind: L
Fidelity: exact -/
theorem voiExp_perfect_eq_evpi [DecidableEq Ω] (P : Distr Ω) (V : Ω → A → ℝ) {B : Finset A}
    (hB : B.Nonempty) : voiExp P V perfectExp B hB = evpi P V B hB := by
  unfold voiExp evpi power attainable expect
  congr 1
  refine sum_congr rfl fun s _ => ?_
  have e : (fun b => ∑ ω, P.mass ω * (perfectExp : Experiment Ω Ω).k ω s * V ω b) =
      fun b => P.mass s * V s b := by
    funext b
    simp only [perfectExp, ofMap, id]
    rw [sum_eq_single s]
    · simp
    · intro ω _ hω; simp [hω]
    · intro h; exact absurd (mem_univ s) h
  rw [e, sup'_const_mul hB (P.nonneg s)]

/-- **The trivial experiment is worth nothing**: `voiExp P V trivialExp B = 0`.
Source: none: infrastructure (the "no channel" cell of D18)
Kind: L
Fidelity: n/a -/
theorem voiExp_trivial (P : Distr Ω) (V : Ω → A → ℝ) {B : Finset A} (hB : B.Nonempty) :
    voiExp P V trivialExp B hB = 0 := by
  unfold voiExp bestMix
  rw [sub_eq_zero, Fintype.sum_unique]
  refine sup'_congr hB rfl fun b _ => ?_
  simp [trivialExp, mixValue, expect]

/-! ## The E3 family -/

/-- E3 hypotheses `(π, mind)`: the preferred plan and whether the humans mind being scanned.
Source: power-wisdom-final.md P2 (l. 159, E3)
Kind: D
Fidelity: exact -/
abbrev E3Ω (n : ℕ) : Type := Fin (n + 1) × Bool

/-- E3 options: `Sum.inl j` the plan `b_j`, `Sum.inr false` the null option `∅`, `Sum.inr true`
the scan `s`.
Source: power-wisdom-final.md P2 (l. 159, E3)
Kind: D
Fidelity: exact -/
abbrev E3A (n : ℕ) : Type := Fin (n + 1) ⊕ Bool

/-- The null option of E3. Source: power-wisdom-final.md P2 (l. 159). Kind: D. Fidelity: exact -/
def e3Nul (n : ℕ) : E3A n := Sum.inr false

/-- The scan of E3. Source: power-wisdom-final.md P2 (l. 159). Kind: D. Fidelity: exact -/
def e3Scan (n : ℕ) : E3A n := Sum.inr true

/-- The E3 posterior: `π` uniform on `Fin (n+1)`, independent of `mind` with `P(mind) = μ`
(the product of the uniform and the two-point law, written as its mass function).
Source: power-wisdom-final.md P2 (l. 159, "`π` uniform … `P_t(mind = 1) = μ`")
Kind: D
Fidelity: exact -/
def e3P (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) : Distr (E3Ω n) where
  mass := fun ω => ((n : ℝ) + 1)⁻¹ * (if ω.2 then μ else 1 - μ)
  nonneg := fun ω => by
    apply mul_nonneg (by positivity)
    split_ifs <;> linarith [hμ.1, hμ.2]
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    have hrow : ∀ i : Fin (n + 1),
        ∑ m : Bool, ((n : ℝ) + 1)⁻¹ * (if (i, m).2 then μ else 1 - μ) = ((n : ℝ) + 1)⁻¹ := by
      intro i
      simp only [Fintype.sum_bool, Bool.true_eq_false, Bool.false_eq_true, if_true, if_false]
      ring
    simp only [hrow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp

/-- Mass of the E3 posterior. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem e3P_mass (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (ω : E3Ω n) :
    (e3P n μ hμ).mass ω = ((n : ℝ) + 1)⁻¹ * (if ω.2 then μ else 1 - μ) := rfl

/-- The E3 value table: plan `j` worth `𝟙[j = π]`, `∅` worth `0`, the scan worth `−h` when the
humans mind and `0` otherwise (a pure experiment: harm only).
Source: power-wisdom-final.md P2 (l. 159, E3)
Kind: D
Fidelity: exact -/
def e3V (n : ℕ) (h : ℝ) : E3Ω n → E3A n → ℝ := fun ω a =>
  match a with
  | Sum.inl j => if ω.1 = j then 1 else 0
  | Sum.inr false => 0
  | Sum.inr true => if ω.2 then -h else 0

/-- Value of a plan. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem e3V_plan (n : ℕ) (h : ℝ) (ω : E3Ω n) (j : Fin (n + 1)) :
    e3V n h ω (Sum.inl j) = if ω.1 = j then 1 else 0 := rfl

/-- Value of the null option. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem e3V_nul (n : ℕ) (h : ℝ) (ω : E3Ω n) : e3V n h ω (Sum.inr false) = 0 := rfl

/-- Value of the scan. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem e3V_scan (n : ℕ) (h : ℝ) (ω : E3Ω n) :
    e3V n h ω (Sum.inr true) = if ω.2 then -h else 0 := rfl

/-- The plan set `{b_0, …, b_n}` as the image of `Sum.inl`.
Source: power-wisdom-final.md P2 (l. 159)
Kind: D
Fidelity: exact -/
def e3Plans (n : ℕ) : Finset (E3A n) := univ.map ⟨Sum.inl, Sum.inl_injective⟩

/-- The plan set is nonempty. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem e3Plans_nonempty (n : ℕ) : (e3Plans n).Nonempty := ⟨Sum.inl 0, by simp [e3Plans]⟩

/-- `sup'` over the plan set is `sup'` over `Fin (n+1)` through `Sum.inl`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sup'_e3Plans (n : ℕ) (f : E3A n → ℝ) :
    (e3Plans n).sup' (e3Plans_nonempty n) f = univ.sup' univ_nonempty (fun j => f (Sum.inl j)) := by
  unfold e3Plans
  rw [sup'_map]
  rfl

/-- The attainable value on the plans is `1` under every hypothesis (plan `π` attains it).
Source: power-wisdom-final.md P2 (l. 159)
Kind: L
Fidelity: n/a -/
theorem e3_attainable (n : ℕ) (h : ℝ) (ω : E3Ω n) :
    attainable (e3V n h) (e3Plans n) (e3Plans_nonempty n) ω = 1 := by
  unfold attainable
  rw [sup'_e3Plans]
  apply le_antisymm
  · rw [sup'_le_iff]
    intro j _
    simp only [e3V_plan]
    split_ifs <;> norm_num
  · refine le_trans ?_ (le_sup' (fun j => e3V n h ω (Sum.inl j)) (mem_univ ω.1))
    simp

/-- `POWER_P(plans) = 1`. Source: power-wisdom-final.md P2 (l. 159). Kind: L. Fidelity: n/a -/
theorem e3_power (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h : ℝ) :
    power (e3P n μ hμ) (e3V n h) (e3Plans n) (e3Plans_nonempty n) = 1 := by
  unfold power
  rw [show attainable (e3V n h) (e3Plans n) (e3Plans_nonempty n) = fun _ => 1 from
    funext (e3_attainable n h)]
  exact expect_const _ 1

/-- The mixture value of every plan is `1/(n+1)`.
Source: power-wisdom-final.md P2 (l. 159). Kind: L. Fidelity: n/a -/
theorem e3_mixValue_plan (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h : ℝ) (j : Fin (n + 1)) :
    mixValue (e3P n μ hμ) (e3V n h) (Sum.inl j) = ((n : ℝ) + 1)⁻¹ := by
  unfold mixValue expect
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, e3P_mass, e3V_plan, Bool.true_eq_false, Bool.false_eq_true,
    if_true, if_false]
  rw [sum_eq_single j]
  · simp; ring
  · intro i _ hij; simp [hij]
  · intro h; exact absurd (mem_univ j) h

/-- `max_{plans} V̄ = 1/(n+1)`. Source: power-wisdom-final.md P2 (l. 159). Kind: L. Fidelity: n/a -/
theorem e3_bestMix (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h : ℝ) :
    bestMix (e3P n μ hμ) (e3V n h) (e3Plans n) (e3Plans_nonempty n) = ((n : ℝ) + 1)⁻¹ := by
  unfold bestMix
  rw [sup'_e3Plans]
  simp only [e3_mixValue_plan]
  exact sup'_const _ _

/-- **E3: `EVPI(plans) = 1 − 1/(n+1)`.**
Source: power-wisdom-final.md P2 (l. 159, "`EVPI_t({b_i}) = 1 − 1/n`"); script E3
Kind: P
Fidelity: exact (indexed by `n+1` plans)
Hyps: (a) none -/
theorem e3_evpi (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h : ℝ) :
    evpi (e3P n μ hμ) (e3V n h) (e3Plans n) (e3Plans_nonempty n) = 1 - ((n : ℝ) + 1)⁻¹ := by
  unfold evpi
  rw [e3_power, e3_bestMix]

/-- The scan's signal gain for plan `j` on signal `s` is `𝟙[s = j]/(n+1)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem e3_scan_inner (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h : ℝ) (s j : Fin (n + 1)) :
    ∑ ω : E3Ω n, (e3P n μ hμ).mass ω *
      (ofMap Prod.fst : Experiment (E3Ω n) (Fin (n + 1))).k ω s * e3V n h ω (Sum.inl j) =
      ((n : ℝ) + 1)⁻¹ * if s = j then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, e3P_mass, e3V_plan, ofMap, Bool.true_eq_false, Bool.false_eq_true,
    if_true, if_false]
  rw [sum_eq_single s]
  · simp only [if_true]
    split_ifs <;> ring
  · intro i _ his; simp [his]
  · intro h; exact absurd (mem_univ s) h

/-- **E3: `VOI(scan) = 1 − 1/(n+1)`** — the scan reveals `π` exactly.
Source: power-wisdom-final.md P2 (l. 159, "`VOI_t(s) = 1 − 1/n`"); script E3
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem e3_voiExp_scan (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h : ℝ) :
    voiExp (e3P n μ hμ) (e3V n h) (ofMap Prod.fst) (e3Plans n) (e3Plans_nonempty n) =
      1 - ((n : ℝ) + 1)⁻¹ := by
  unfold voiExp
  rw [e3_bestMix]
  congr 1
  have hs : ∀ s : Fin (n + 1), (e3Plans n).sup' (e3Plans_nonempty n)
      (fun b => ∑ ω, (e3P n μ hμ).mass ω *
        (ofMap Prod.fst : Experiment (E3Ω n) (Fin (n + 1))).k ω s * e3V n h ω b) =
      ((n : ℝ) + 1)⁻¹ := by
    intro s
    rw [sup'_e3Plans]
    simp only [e3_scan_inner]
    exact sup'_univ_scaled_indicator (by positivity) s
  simp only [hs, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- The scan's harm under `(π, mind)` is `h` if the humans mind and `0` otherwise (`h ≥ 0`).
Source: power-wisdom-final.md P2 (l. 159, "harm `= h 𝟙[mind = 1]`")
Kind: L
Fidelity: exact -/
theorem e3_harm_scan (n : ℕ) {h : ℝ} (hh : 0 ≤ h) (ω : E3Ω n) :
    harmOf (e3Nul n) (e3V n h ω) (e3Scan n) = if ω.2 then h else 0 := by
  unfold harmOf e3Nul e3Scan
  rcases ω with ⟨i, m⟩
  cases m
  · simp
  · simp [hh]

/-- **E3: `E[harm(scan)] = μh`** (for `h ≥ 0`).
Source: power-wisdom-final.md P2 (l. 159, "`E[harm(s)] = μh`"); script E3
Kind: L
Fidelity: exact -/
theorem e3_expect_harm_scan (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) {h : ℝ} (hh : 0 ≤ h) :
    expect (e3P n μ hμ) (fun ω => harmOf (e3Nul n) (e3V n h ω) (e3Scan n)) = μ * h := by
  simp only [expect, e3_harm_scan n hh, e3P_mass]
  rw [Fintype.sum_prod_type]
  have hrow : ∀ i : Fin (n + 1),
      ∑ m : Bool, ((n : ℝ) + 1)⁻¹ * (if (i, m).2 then μ else 1 - μ) * (if (i, m).2 then h else 0) =
        ((n : ℝ) + 1)⁻¹ * (μ * h) := by
    intro i
    simp only [Fintype.sum_bool, Bool.true_eq_false, Bool.false_eq_true, if_true, if_false]
    ring
  simp only [hrow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp

/-- The scan has no direct gain under any hypothesis (`h ≥ 0`).
Source: power-wisdom-final.md P2 (l. 159, "`g ≡ 0`"). Kind: L. Fidelity: exact -/
theorem e3_expect_gain_scan (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) {h : ℝ} (hh : 0 ≤ h) :
    expect (e3P n μ hμ) (fun ω => gainOf (e3Nul n) (e3V n h ω) (e3Scan n)) = 0 := by
  unfold expect
  refine sum_eq_zero fun ω _ => ?_
  dsimp only
  rw [gainOf_eq_zero_of_le, mul_zero]
  simp only [e3Nul, e3Scan, e3V_nul, e3V_scan]
  split_ifs <;> linarith

/-- **S2, absolute J3 in E3**: the agent declines the scan (against skipping) iff
`1 − 1/(n+1) < μh`.
Source: power-wisdom-final.md S2 (l. 103, "absolute J3 holds only at `n = 1` and fails for all
`n ≥ 2`"); P2 (l. 159)
Kind: P
Fidelity: exact (indexed by `n+1` plans; over the plan set — the same iff over D18's full
continuation set `plans ∪ {∅, s}` is `e3_j3_iff_cont`)
Hyps: (a) `0 ≤ h` -/
theorem e3_j3_iff (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) {h : ℝ} (hh : 0 ≤ h) :
    J3 (e3P n μ hμ) (e3V n h) (ofMap Prod.fst) (e3Scan n) (e3Nul n) (e3Plans n)
      (e3Plans_nonempty n) ↔ 1 - ((n : ℝ) + 1)⁻¹ < μ * h := by
  unfold J3
  rw [e3_expect_gain_scan n μ hμ hh, e3_voiExp_scan, e3_expect_harm_scan n μ hμ hh, zero_add]

/-- **At `μ = h = 1/2`, absolute J3 holds iff there is one plan** (`n = 0`): `0 < 1/4` at one
plan; `1 − 1/(n+1) ≥ 1/2 > 1/4` at two or more.
Source: power-wisdom-final.md S2 (l. 103); script E3 (`j3_table`, "J3 vs skip")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem e3_j3_half_iff (n : ℕ) :
    J3 (e3P n (1 / 2) (by norm_num)) (e3V n (1 / 2)) (ofMap Prod.fst) (e3Scan n) (e3Nul n)
      (e3Plans n) (e3Plans_nonempty n) ↔ n = 0 := by
  rw [e3_j3_iff n (1 / 2) (by norm_num) (by norm_num)]
  constructor
  · intro H
    by_contra hn
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    have h2 : ((n : ℝ) + 1)⁻¹ ≤ 1 / 2 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    linarith
  · rintro rfl
    norm_num

/-! ## The legitimate channel `q` -/

/-- **The legitimate channel**: asking reveals `π` with probability `1 − δ` (signal `some π`) and
is silent (signal `none`) with probability `δ`. The kernel is stated explicitly; `δ = 0` is the
perfect channel and `δ = 1` the trivial one.
Source: power-wisdom-final.md P2 (l. 159, "`q` reveals `π` w.p. `1 − δ`"); script E3
Kind: D
Fidelity: exact (the silent-signal reading of "else uninformative") -/
def e3Q (n : ℕ) (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) : Experiment (E3Ω n) (Option (Fin (n + 1))) where
  k := fun ω o => match o with
    | none => δ
    | some s => (1 - δ) * if ω.1 = s then 1 else 0
  k_mem := fun ω => ⟨fun o => by
      cases o with
      | none => exact hδ.1
      | some s =>
        simp only
        apply mul_nonneg (by linarith [hδ.2])
        split_ifs <;> norm_num,
    by
      rw [Fintype.sum_option]
      simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, if_true]
      ring⟩

/-- Kernel of `q` on the silent signal. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem e3Q_none (n : ℕ) (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (ω : E3Ω n) :
    (e3Q n δ hδ).k ω none = δ := rfl

/-- Kernel of `q` on a revealing signal. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem e3Q_some (n : ℕ) (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (ω : E3Ω n)
    (s : Fin (n + 1)) : (e3Q n δ hδ).k ω (some s) = (1 - δ) * if ω.1 = s then 1 else 0 := rfl

/-- Signal gain of `q` on the silent signal: `δ/(n+1)` for every plan.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem e3_q_inner_none (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h δ : ℝ)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (j : Fin (n + 1)) :
    ∑ ω : E3Ω n, (e3P n μ hμ).mass ω * (e3Q n δ hδ).k ω none * e3V n h ω (Sum.inl j) =
      δ * ((n : ℝ) + 1)⁻¹ := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, e3P_mass, e3V_plan, e3Q_none, Bool.true_eq_false,
    Bool.false_eq_true, if_true, if_false]
  rw [sum_eq_single j]
  · simp only [if_true]; ring
  · intro i _ hij; simp [hij]
  · intro h; exact absurd (mem_univ j) h

/-- Signal gain of `q` on a revealing signal: `(1 − δ) 𝟙[s = j]/(n+1)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem e3_q_inner_some (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h δ : ℝ)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) (s j : Fin (n + 1)) :
    ∑ ω : E3Ω n, (e3P n μ hμ).mass ω * (e3Q n δ hδ).k ω (some s) * e3V n h ω (Sum.inl j) =
      ((1 - δ) * ((n : ℝ) + 1)⁻¹) * if s = j then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, e3P_mass, e3V_plan, e3Q_some, Bool.true_eq_false,
    Bool.false_eq_true, if_true, if_false]
  rw [sum_eq_single s]
  · simp only [if_true]
    split_ifs <;> ring
  · intro i _ his; simp [his]
  · intro h; exact absurd (mem_univ s) h

/-- **E3: `VOI(q) = (1 − δ)(1 − 1/(n+1))`.**
Source: power-wisdom-final.md P2 (l. 159, "`VOI_t(q) = (1 − δ)(1 − 1/n)`"); script E3
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem e3_voiExp_q (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h δ : ℝ)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    voiExp (e3P n μ hμ) (e3V n h) (e3Q n δ hδ) (e3Plans n) (e3Plans_nonempty n) =
      (1 - δ) * (1 - ((n : ℝ) + 1)⁻¹) := by
  unfold voiExp
  rw [e3_bestMix, Fintype.sum_option]
  have hnone : (e3Plans n).sup' (e3Plans_nonempty n)
      (fun b => ∑ ω, (e3P n μ hμ).mass ω * (e3Q n δ hδ).k ω none * e3V n h ω b) =
      δ * ((n : ℝ) + 1)⁻¹ := by
    rw [sup'_e3Plans]
    simp only [e3_q_inner_none]
    exact sup'_const _ _
  have hsome : ∀ s : Fin (n + 1), (e3Plans n).sup' (e3Plans_nonempty n)
      (fun b => ∑ ω, (e3P n μ hμ).mass ω * (e3Q n δ hδ).k ω (some s) * e3V n h ω b) =
      (1 - δ) * ((n : ℝ) + 1)⁻¹ := by
    intro s
    rw [sup'_e3Plans]
    simp only [e3_q_inner_some]
    exact sup'_univ_scaled_indicator (mul_nonneg (by linarith [hδ.2]) (by positivity)) s
  rw [hnone]
  simp only [hsome, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  field_simp
  ring

/-- **E3: `VOI(s, q) = 1 − 1/(n+1)`** — the product channel is squeezed between the scan (which it
refines, Blackwell) and perfect information (`EVPI`).
Source: power-wisdom-final.md P2 (l. 159, "`VOI_t(s | q) = VOI_t(s, q) − VOI_t(q)`")
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem e3_voiExp_prod (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h δ : ℝ)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    voiExp (e3P n μ hμ) (e3V n h) (expProd (e3Q n δ hδ) (ofMap Prod.fst)) (e3Plans n)
      (e3Plans_nonempty n) = 1 - ((n : ℝ) + 1)⁻¹ := by
  apply le_antisymm
  · rw [← e3_evpi n μ hμ h]
    exact voiExp_le_evpi _ _ _ _
  · rw [← e3_voiExp_scan n μ hμ h]
    exact voiExp_mono_blackwell _ _ (blackwellLE_right_prod _ _) _

/-- **J3 against asking first** (D16's marginal form): the agent declines `a` *given that it can
ask through `k₁` first* iff `E[g(a)] + (VOI(k₁, k₂) − VOI(k₁)) < E[harm(a)]`, where `k₂` is the
observation `a` yields.
Source: power-wisdom-final.md D16 (l. 73, "the marginal `VOI_t(a | q)`"); S2 (l. 103)
Kind: D
Fidelity: exact -/
def J3Given {S T : Type} [Fintype S] [Fintype T] (P : Distr Ω) (V : Ω → A → ℝ)
    (k₁ : Experiment Ω S) (k₂ : Experiment Ω T) (a nul : A) (B : Finset A) (hB : B.Nonempty) :
    Prop :=
  expect P (fun ω => gainOf nul (V ω) a) +
    (voiExp P V (expProd k₁ k₂) B hB - voiExp P V k₁ B hB) <
    expect P (fun ω => harmOf nul (V ω) a)

/-- **E3: the marginal `VOI(s | q) = δ(1 − 1/(n+1))`**, and J3 against asking first at `n+1`
plans reads `δ(1 − 1/(n+1)) < μh`.
Source: power-wisdom-final.md P2 (l. 159, "`VOI_t(s | q) = δ(1 − 1/n)`; J3 against asking first
reads `μh > δ(1 − 1/n)`"); script E3
Kind: P
Fidelity: exact (over the plan set; over `plans ∪ {∅, s}` it is `e3_j3Given_iff_cont`)
Hyps: (a) `0 ≤ h` -/
theorem e3_j3Given_iff (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) {h : ℝ} (hh : 0 ≤ h) (δ : ℝ)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    J3Given (e3P n μ hμ) (e3V n h) (e3Q n δ hδ) (ofMap Prod.fst) (e3Scan n) (e3Nul n) (e3Plans n)
      (e3Plans_nonempty n) ↔ δ * (1 - ((n : ℝ) + 1)⁻¹) < μ * h := by
  unfold J3Given
  rw [e3_expect_gain_scan n μ hμ hh, e3_voiExp_prod, e3_voiExp_q, e3_expect_harm_scan n μ hμ hh,
    zero_add]
  rw [show 1 - ((n : ℝ) + 1)⁻¹ - (1 - δ) * (1 - ((n : ℝ) + 1)⁻¹) = δ * (1 - ((n : ℝ) + 1)⁻¹) by ring]

/-- **S2's headline, exact: in the E3 family, J3 against asking first holds at every number of
plans iff `δ ≤ μh`** (for `0 < μh`; the degenerate cells `δ = 0` and one plan are in range).
`(⇐)`: `δ(1 − 1/(n+1)) ≤ δ` with strictness from `δ < μh` or from `1/(n+1) > 0` when
`δ = μh > 0`. `(⇒)`: if `δ > μh`, a large `n` makes `δ(1 − 1/(n+1)) ≥ μh` (Archimedes).
Source: power-wisdom-final.md S2 (l. 103, "J3 holds at **every** `n` iff `δ ≤ μh`"); P2 (l. 159)
Kind: P
Fidelity: exact (the `n`-independent sufficient form, both directions; indexed by `n+1` plans;
over the plan set, see `e3_j3Given_iff_cont` for `plans ∪ {∅, s}`; `0 < μh` named — at `μh = 0`
J3 fails already at one plan with `δ = 0`)
Hyps: (a) `0 ≤ h`, `0 < μh` -/
theorem e3_j3Given_all_iff (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) {h : ℝ} (hh : 0 ≤ h)
    (hμh : 0 < μ * h) (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    (∀ n : ℕ, J3Given (e3P n μ hμ) (e3V n h) (e3Q n δ hδ) (ofMap Prod.fst) (e3Scan n) (e3Nul n)
      (e3Plans n) (e3Plans_nonempty n)) ↔ δ ≤ μ * h := by
  simp only [e3_j3Given_iff _ μ hμ hh δ hδ]
  constructor
  · intro H
    by_contra hlt
    push Not at hlt
    have hd : 0 < δ - μ * h := by linarith
    obtain ⟨n, hn⟩ := exists_nat_gt (δ / (δ - μ * h))
    rw [div_lt_iff₀ hd] at hn
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have H' := H n
    have hcn : ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) = 1 := inv_mul_cancel₀ hn1.ne'
    have e : δ * (1 - ((n : ℝ) + 1)⁻¹) * ((n : ℝ) + 1) = δ * ((n : ℝ) + 1) - δ := by
      rw [mul_sub, mul_one, sub_mul, mul_assoc, hcn, mul_one]
    have := mul_lt_mul_of_pos_right H' hn1
    rw [e] at this
    nlinarith
  · intro H n
    have hc : 0 < ((n : ℝ) + 1)⁻¹ := by positivity
    have hc1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rcases lt_or_eq_of_le H with hlt | heq
    · nlinarith [hδ.1]
    · rw [← heq]
      have hδpos : 0 < δ := by rw [heq]; exact hμh
      nlinarith

/-- **The `μh = 0` cell: J3 never holds**, whatever `δ` and `n` (the harm side is `0`, the gain
side is `≥ 0`). Recorded so that the hypothesis `0 < μh` of `e3_j3Given_all_iff` is seen to be
necessary, not a convenience.
Source: power-wisdom-final.md S2 (l. 103); [[corr-power-channel-mandate]] T4(a) ("`δ = 0` and
`n = 1` are the degenerate cells and must be in range")
Kind: L
Fidelity: exact -/
theorem e3_j3Given_fails_of_zero (n : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) {h : ℝ} (hh : 0 ≤ h)
    (hμh : μ * h = 0) (δ : ℝ) (hδ : δ ∈ Set.Icc (0 : ℝ) 1) :
    ¬ J3Given (e3P n μ hμ) (e3V n h) (e3Q n δ hδ) (ofMap Prod.fst) (e3Scan n) (e3Nul n)
      (e3Plans n) (e3Plans_nonempty n) := by
  rw [e3_j3Given_iff n μ hμ hh δ hδ, hμh]
  have hc1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  nlinarith [hδ.1]

end

end Cleanroom.Corrigibility.CorrPowerChannel
