import Cleanroom.Info.InfoVoiLatents.Voi
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# info-voi-latents — witnesses for the VOI bound chain (Target 3)

* **Weak binary signal** (N+): `W = S = Fin 2`, uniform prior, kernel `[[½+η, ½−η], [½−η, ½+η]]`,
  menu `u a w = M·𝟙[a = w]`, `0 ≤ η ≤ ½`, `0 ≤ M`: `voi = M·η` exactly (`weakSignal_voi`), the
  TV bound is attained (`weakSignal_tv_bound`), and the expected finite KL is exactly
  `log 2 − h₂(½ + η)` (`weakSignal_klFin`), bounded below by `2η²` by binary Pinsker
  (`weakSignal_klFin_ge`), so the last step of the chain sits at or above `voi`
  (`weakSignal_mi_bound_ge_voi`). The numeric claim "ratio → 1" is recorded only.
* **Rare state** (N+): `W = {right, wrong}`, prior `(1−ε, ε)`, a press with false rate `α` and true
  rate `β`, stakes `c` (stop when right) and `h` (continue when wrong): the exact formula
  `voi = max 0 (εβh − (1−ε)αc)` under the two orderings that make "continue" prior-optimal and
  posterior-optimal after no press (`rareState_voi`); at `(ε, α, β, c, h) = (1/100, 1/100, 9/10,
  1, 10)`: `voi = 801/10000` (**not** `2/25 = 0.08`, the three-decimal value the sources quote —
  see findings), regret-mass bound `1/10 = εh`, TV bound `8811/50000`.

Mandate: `run/wp/info-voi-latents/info-voi-latents-mandate.md`, Target 3 witnesses.
-/

namespace Cleanroom.Info.InfoVoiLatents.Voi

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell

noncomputable section

/-- `sup'` over `Fin 2` is the `max` of the two values.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sup'_fin_two (f : Fin 2 → ℝ) :
    (univ : Finset (Fin 2)).sup' univ_nonempty f = max (f 0) (f 1) := by
  apply le_antisymm
  · rw [Finset.sup'_le_iff]
    intro b _
    fin_cases b
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (Finset.le_sup' f (mem_univ 0)) (Finset.le_sup' f (mem_univ 1))

/-! ### The weak binary signal -/

/-- The uniform prior on two states.
Source: none: infrastructure (witness)
Kind: D
Fidelity: exact -/
def half : Fin 2 → ℝ := fun _ => 1 / 2

/-- `half ∈ stdSimplex`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem half_mem : half ∈ stdSimplex ℝ (Fin 2) :=
  ⟨fun _ => by norm_num [half], by norm_num [half, Fin.sum_univ_two]⟩

/-- The **weak binary signal**: reports the state with probability `½ + η`, `0 ≤ η ≤ ½`.
Source: [[generalization-final]] P2 l. 107 (`voi_bound.py` ll. 35–42: "EVSI = eta exactly")
Kind: D
Fidelity: exact -/
def weakSignal (η : ℝ) (hη : η ∈ Set.Icc (0 : ℝ) (1 / 2)) : Experiment (Fin 2) (Fin 2) where
  k := fun w s => if w = s then 1 / 2 + η else 1 / 2 - η
  k_mem := fun w => ⟨fun s => by dsimp only; split_ifs <;> linarith [hη.1, hη.2], by
    fin_cases w <;> simp [Fin.sum_univ_two] <;> norm_num⟩

/-- The kernel of the weak signal, unfolded.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem weakSignal_k {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) (1 / 2)) (w s : Fin 2) :
    (weakSignal η hη).k w s = if w = s then 1 / 2 + η else 1 / 2 - η := rfl

/-- The **matching menu** `u a w = M · 𝟙[a = w]` (guess the state, prize `M`).
Source: [[generalization-final]] P2 l. 107 (`voi_bound.py`: `u(a,l) = M·1[a==l]`)
Kind: D
Fidelity: exact -/
def matchMenu (M : ℝ) : Fin 2 → Fin 2 → ℝ := fun a w => if a = w then M else 0

/-- The posterior scores of the weak signal: `postScore s a = ½ · k a s · M`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem weakSignal_postScore {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) (1 / 2)) (M : ℝ) (s a : Fin 2) :
    postScore half (weakSignal η hη) (matchMenu M) s a
      = 1 / 2 * (if a = s then 1 / 2 + η else 1 / 2 - η) * M := by
  unfold postScore half weakSignal matchMenu
  fin_cases s <;> fin_cases a <;> simp [Fin.sum_univ_two]

/-- **`voi = M·η` exactly** for the weak binary signal with the matching menu (`0 ≤ M`).
Source: [[generalization-final]] S2 l. 61 ("sharp in the weak-signal limit"), P2 l. 107;
`voi_bound.py` ll. 35–42
Kind: N+
Fidelity: exact (the numeric "ratio → 1" of the MI bound is recorded only)
Hyps: (a) all -/
theorem weakSignal_voi {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) (1 / 2)) {M : ℝ} (hM : 0 ≤ M) :
    voi half (weakSignal η hη) (matchMenu M) = M * η := by
  unfold voi
  rw [bayesValue_eq_sum_sup']
  simp_rw [weakSignal_postScore hη M]
  have hprior : priorValue half (matchMenu M) = M / 2 := by
    unfold priorValue
    rw [sup'_fin_two]
    simp [E, half, matchMenu]
    ring
  rw [hprior, Fin.sum_univ_two, sup'_fin_two, sup'_fin_two]
  have h1 : 0 ≤ η := hη.1
  simp only [Fin.isValue, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, ↓reduceIte,
    Fin.one_eq_zero_iff, one_ne_zero]
  rw [max_eq_left (by nlinarith), max_eq_right (by nlinarith)]
  ring

/-- The signal mass of the weak signal is `½` for both signals.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem weakSignal_sigMass {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) (1 / 2)) (s : Fin 2) :
    sigMass half (weakSignal η hη) s = 1 / 2 := by
  unfold sigMass half weakSignal
  fin_cases s <;> simp [Fin.sum_univ_two] <;> ring

/-- The posterior of the weak signal is its likelihood row: `post s w = ½ + η` iff `w = s`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem weakSignal_post {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) (1 / 2)) (s w : Fin 2) :
    post half (weakSignal η hη) s w = if w = s then 1 / 2 + η else 1 / 2 - η := by
  unfold post
  rw [weakSignal_sigMass, weakSignal_k]
  unfold half
  by_cases h : w = s
  · rw [if_pos h]
    ring
  · rw [if_neg h]
    ring

/-- **The TV bound is attained** by the weak binary signal: `M · ∑ s, P(s) · tv (post s) half = M·η`.
Source: [[generalization-final]] P2 l. 107 (`voi_bound.py`: `bound_TV/M` column equals `eta`)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem weakSignal_tv_bound {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) (1 / 2)) (M : ℝ) :
    M * ∑ s, sigMass half (weakSignal η hη) s * tv (post half (weakSignal η hη) s) half
      = M * η := by
  have h1 : 0 ≤ η := hη.1
  have hpos : ∀ s w, post half (weakSignal η hη) s w
      = if w = s then 1 / 2 + η else 1 / 2 - η := weakSignal_post hη
  have htv : ∀ s, tv (post half (weakSignal η hη) s) half = η := by
    intro s
    unfold tv
    rw [Fin.sum_univ_two, hpos, hpos]
    unfold half
    fin_cases s
    · simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte, Fin.one_eq_zero_iff, one_ne_zero]
      rw [show (1 / 2 + η - 1 / 2 : ℝ) = η by ring, show (1 / 2 - η - 1 / 2 : ℝ) = -η by ring,
        abs_neg, abs_of_nonneg h1]
      ring
    · simp only [Fin.isValue, Fin.mk_one, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, ↓reduceIte]
      rw [show (1 / 2 + η - 1 / 2 : ℝ) = η by ring, show (1 / 2 - η - 1 / 2 : ℝ) = -η by ring,
        abs_neg, abs_of_nonneg h1]
      ring
  simp_rw [weakSignal_sigMass hη, htv, Fin.sum_univ_two]
  ring

/-- **The expected finite KL of the weak signal is exactly `log 2 − h₂(½ + η)`** (with
`Real.binEntropy`): both signals have the same divergence from the uniform prior.
Source: [[generalization-final]] P2 l. 107 (the `I(nats)` column of `voi_bound.py`); Target 3
witness ("record the exact `I = log 2 − h₂(½+η)`")
Kind: N+
Fidelity: exact (finite-sum form; the identification with PFR's `I[· : ·]` is `Bridge.lean`)
Hyps: (a) all -/
theorem weakSignal_klFin {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    ∑ s, sigMass half (weakSignal η hη) s * klFin (post half (weakSignal η hη) s) half
      = Real.log 2 - Real.binEntropy (1 / 2 + η) := by
  have hpos : ∀ s w, post half (weakSignal η hη) s w
      = if w = s then 1 / 2 + η else 1 / 2 - η := weakSignal_post hη
  have e1 := mul_log_div_eq (a := 1 / 2 + η) (b := 1 / 2) (by linarith [hη.1]) (by norm_num)
  have e2 := mul_log_div_eq (a := 1 / 2 - η) (b := 1 / 2) (by linarith [hη.2]) (by norm_num)
  have hb : Real.binEntropy (1 / 2 + η)
      = Real.negMulLog (1 / 2 + η) + Real.negMulLog (1 / 2 - η) := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
    congr 2
    ring
  have hlog : Real.log (1 / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hkl : ∀ s, klFin (post half (weakSignal η hη) s) half
      = Real.log 2 - Real.binEntropy (1 / 2 + η) := by
    intro s
    unfold klFin
    rw [Fin.sum_univ_two, hpos, hpos]
    unfold half
    fin_cases s
    · simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte, Fin.one_eq_zero_iff, one_ne_zero]
      rw [e1, e2, hb, hlog]
      ring
    · simp only [Fin.isValue, Fin.mk_one, Fin.zero_eq_one_iff, OfNat.ofNat_ne_one, ↓reduceIte]
      rw [e1, e2, hb, hlog]
      ring
  simp_rw [weakSignal_sigMass hη, hkl, Fin.sum_univ_two]
  ring

/-- **Binary Pinsker at the weak signal**: the expected finite KL is at least `2η²`.
Source: Target 3 witness (stretch: "`I ≥ 2η²` from binary Pinsker")
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem weakSignal_klFin_ge {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    2 * η ^ 2 ≤ ∑ s, sigMass half (weakSignal η hη) s * klFin (post half (weakSignal η hη) s) half := by
  rw [weakSignal_klFin hη]
  have hb : (1 / 2 : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by norm_num
  have ha : (1 / 2 + η : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hη.1], by linarith [hη.2]⟩
  have h := binary_pinsker hb ha
  have e1 := mul_log_div_eq (a := 1 / 2 + η) (b := 1 / 2) (by linarith [hη.1]) (by norm_num)
  have e2 := mul_log_div_eq (a := 1 - (1 / 2 + η)) (b := 1 - 1 / 2) (by linarith [hη.2]) (by norm_num)
  rw [e1, e2] at h
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  have hlog : Real.log (1 / 2) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have h12 : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  rw [h12, hlog] at h
  have hsq : (1 / 2 + η - 1 / 2 : ℝ) ^ 2 = η ^ 2 := by ring
  rw [hsq] at h
  linarith

/-- **The last step of the chain at the weak signal**: `voi = M·η ≤ M · √(E[klFin]/2)`. Together
with `weakSignal_tv_bound` this shows the TV bound is attained and the finite-KL bound sits
above it; the ratio's convergence to `1` as `η → 0` is the numeric claim, recorded only.
Source: [[generalization-final]] S2 l. 61 ("sharp in the weak-signal limit (ratio → 1; P2)")
Kind: N+
Fidelity: weaker: the inequality at the witness, not the asymptotic ratio
Hyps: (a) all -/
theorem weakSignal_mi_bound_ge_voi {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) (1 / 2)) {M : ℝ}
    (hM : 0 ≤ M) :
    voi half (weakSignal η hη) (matchMenu M)
      ≤ M * Real.sqrt ((∑ s, sigMass half (weakSignal η hη) s
          * klFin (post half (weakSignal η hη) s) half) / 2) := by
  rw [weakSignal_voi hη hM]
  refine mul_le_mul_of_nonneg_left ?_ hM
  have h := weakSignal_klFin_ge hη
  apply Real.le_sqrt_of_sq_le
  linarith

/-! ### The rare state -/

/-- The **rare-state prior** `(1 − ε, ε)` on `{right = 0, wrong = 1}`.
Source: [[generalization-final]] P2 l. 107 (rare state); `voi_bound.py` ll. 44–52
Kind: D
Fidelity: exact -/
def rarePrior (ε : ℝ) : Fin 2 → ℝ := fun w => if w = 0 then 1 - ε else ε

/-- `rarePrior ε ∈ stdSimplex` for `ε ∈ [0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rarePrior_mem {ε : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1) : rarePrior ε ∈ stdSimplex ℝ (Fin 2) :=
  ⟨fun w => by unfold rarePrior; split_ifs <;> linarith [hε.1, hε.2],
    by simp [rarePrior, Fin.sum_univ_two]⟩

/-- The **press experiment**: fires with rate `α` when right (false alarm) and `β` when wrong.
Signals `{no press = 0, press = 1}`.
Source: [[generalization-final]] P2 l. 107; `voi_bound.py` ll. 44–52
Kind: D
Fidelity: exact -/
def pressExp (α β : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    Experiment (Fin 2) (Fin 2) where
  k := fun w s => if w = 0 then (if s = 0 then 1 - α else α) else (if s = 0 then 1 - β else β)
  k_mem := fun w => ⟨fun s => by
      dsimp only; split_ifs <;> linarith [hα.1, hα.2, hβ.1, hβ.2],
    by fin_cases w <;> simp [Fin.sum_univ_two]⟩

/-- The **stop/continue menu**: continue (`0`) costs `h` when wrong, stop (`1`) costs `c` when
right; utilities `continue = (0, −h)`, `stop = (−c, 0)`.
Source: [[generalization-final]] P2 l. 107; `voi_bound.py` l. 48
Kind: D
Fidelity: exact (unshifted: `voi` and the bounds are shift-invariant, the ranges are `h` and `c`)
-/
def stopMenu (c h : ℝ) : Fin 2 → Fin 2 → ℝ :=
  fun a w => if a = 0 then (if w = 0 then 0 else -h) else (if w = 0 then -c else 0)

/-- **The rare-state VOI formula**: under the orderings `εh ≤ (1−ε)c` (continue is
prior-optimal) and `ε(1−β)h ≤ (1−ε)(1−α)c` (continue stays optimal after no press),
`voi = max 0 (εβh − (1−ε)αc)` as a formula in the parameters.
Source: [[generalization-final]] P2 l. 107 ("exact VOI = εβh − (1−ε)αc"); `voi_bound.py` l. 50
Kind: N+
Fidelity: exact (under the two stated orderings, which the note leaves implicit)
Hyps: (a) all — the orderings are the case distinction the note's formula silently assumes -/
theorem rareState_voi {ε α β c h : ℝ} (hε : ε ∈ Set.Icc (0 : ℝ) 1) (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) (hc : 0 ≤ c) (hh : 0 ≤ h)
    (hO1 : ε * h ≤ (1 - ε) * c) (hO2 : ε * (1 - β) * h ≤ (1 - ε) * (1 - α) * c) :
    voi (rarePrior ε) (pressExp α β hα hβ) (stopMenu c h)
      = max 0 (ε * β * h - (1 - ε) * α * c) := by
  unfold voi
  rw [bayesValue_eq_sum_sup']
  have hps : ∀ s a, postScore (rarePrior ε) (pressExp α β hα hβ) (stopMenu c h) s a
      = if s = 0 then (if a = 0 then -(ε * (1 - β) * h) else -((1 - ε) * (1 - α) * c))
        else (if a = 0 then -(ε * β * h) else -((1 - ε) * α * c)) := by
    intro s a
    unfold postScore rarePrior pressExp stopMenu
    fin_cases s <;> fin_cases a <;> simp [Fin.sum_univ_two]
  simp_rw [hps]
  have hprior : priorValue (rarePrior ε) (stopMenu c h) = -(ε * h) := by
    unfold priorValue
    rw [sup'_fin_two]
    have h0 : E (rarePrior ε) (stopMenu c h 0) = -(ε * h) := by
      simp [E, rarePrior, stopMenu, Fin.sum_univ_two]
    have h1 : E (rarePrior ε) (stopMenu c h 1) = -((1 - ε) * c) := by
      simp [E, rarePrior, stopMenu, Fin.sum_univ_two]
    rw [h0, h1, max_eq_left (by linarith)]
  rw [hprior, Fin.sum_univ_two, sup'_fin_two, sup'_fin_two]
  simp only [Fin.isValue, ↓reduceIte, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one, one_ne_zero]
  rw [max_eq_left (by linarith)]
  rw [show -(ε * (1 - β) * h) + max (-(ε * β * h)) (-((1 - ε) * α * c)) - -(ε * h)
      = max (-(ε * β * h)) (-((1 - ε) * α * c)) + ε * β * h by ring]
  rw [← max_add_add_right]
  congr 1 <;> ring

/-- **The rare-state instance** `(ε, α, β, c, h) = (1/100, 1/100, 9/10, 1, 10)`: `voi = 801/10000`
(exactly; the sources' `0.080` is a three-decimal rounding and the mandate's `2/25` is wrong),
the regret-mass bound `M · μ(B) = 10 · 1/100 = 1/10 = ε h` (`B = {wrong}`, `M = 10` the
cross-action range), and the TV bound `M · ∑ s, P(s) · tv = 8811/50000` (`M = 10` the
within-action range; `≈ 0.176`, the sources' `0.18`).
Source: [[generalization-final]] P2 l. 107; `voi_bound.py` ll. 44–52; [[generalization-adversary]]
D5 l. 19
Kind: N+
Fidelity: exact rationals
Hyps: (a) all -/
theorem rareState_instance :
    voi (rarePrior (1 / 100)) (pressExp (1 / 100) (9 / 10) (by norm_num) (by norm_num))
        (stopMenu 1 10) = 801 / 10000 ∧
    (10 : ℝ) * ∑ w ∈ univ.filter (fun w => ∃ a, stopMenu 1 10 0 w < stopMenu 1 10 a w),
        rarePrior (1 / 100) w = 1 / 10 ∧
    (10 : ℝ) * ∑ s, sigMass (rarePrior (1 / 100)) (pressExp (1 / 100) (9 / 10) (by norm_num)
        (by norm_num)) s * tv (post (rarePrior (1 / 100)) (pressExp (1 / 100) (9 / 10)
        (by norm_num) (by norm_num)) s) (rarePrior (1 / 100)) = 8811 / 50000 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rareState_voi (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)]
    rw [max_eq_right (by norm_num)]
    norm_num
  · have hB : univ.filter (fun w : Fin 2 => ∃ a, stopMenu 1 10 0 w < stopMenu 1 10 a w) = {1} := by
      ext w
      fin_cases w <;> simp [stopMenu]
    rw [hB]
    simp [rarePrior]
    norm_num
  · have hsig : ∀ s, sigMass (rarePrior (1 / 100)) (pressExp (1 / 100) (9 / 10) (by norm_num)
        (by norm_num)) s = if s = 0 then 9811 / 10000 else 189 / 10000 := by
      intro s
      unfold sigMass rarePrior pressExp
      fin_cases s <;> simp [Fin.sum_univ_two] <;> norm_num
    have hpost : ∀ s w, post (rarePrior (1 / 100)) (pressExp (1 / 100) (9 / 10) (by norm_num)
        (by norm_num)) s w = if s = 0 then (if w = 0 then 9801 / 9811 else 10 / 9811)
          else (if w = 0 then 11 / 21 else 10 / 21) := by
      intro s w
      unfold post
      rw [hsig]
      unfold rarePrior pressExp
      fin_cases s <;> fin_cases w <;> simp <;> norm_num
    simp_rw [hsig, Fin.sum_univ_two]
    unfold tv
    simp_rw [hpost]
    unfold rarePrior
    simp [Fin.sum_univ_two]
    norm_num [abs_of_nonneg, abs_of_nonpos]

end

end Cleanroom.Info.InfoVoiLatents.Voi
