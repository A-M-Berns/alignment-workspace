import Cleanroom.Info.InfoVoiLatents.VoiWitness
import Cleanroom.Info.InfoVoiLatents.Bridge

/-!
# info-voi-latents — harm mass versus regret mass; the rare-state bound applied; the bridge at the
weak signal (Target 3; repair round 1)

Audit r1 (fidelity item 3, adversarial items 3, 4, 9):

* [[generalization-final]] D5 l. 35 *does* define the harm mass — `m_t(A) := sup_{a ∈ A} P_t(a is
  harmful)`, harm relative to the null action (D11 l. 47). Under that definition S2 l. 61's "the
  direct bound `VOI ≤ M·m_t(A)` … is the one to quote" is **false**: `harmMass_zero_voi_pos` — two
  equiprobable states, null action `≡ 0`, actions `(2, 0)` and `(0, 2)`; no action is ever below
  the null action, so `harmMass = 0`, while the perfect signal has `voi = 1`. The package's
  `voi_le_mul_regretMass` is therefore a *repair* of S2's last sentence (findings F6, severity
  raised to local error), with `regretMass` now a definition of record.
* `rareState_voi_le_regretMass`: the regret-mass bound *applied* at the rare-state instance,
  `voi ≤ 1/10` (the instance previously only evaluated the right-hand side).
* `weakSignal_mutualInfo`: PFR's `I[fst : snd ; joint half (weakSignal η)] = log 2 − h₂(½ + η)`,
  an exact mutual information on record through the bridge.

Repair round 2 (audit r2, fidelity item 2, adversarial item 3; probes `HarmMassBinary.lean` and
`Vacuity.lean` P1, promoted):

* **Where S2's sentence is true**: on the binary execute-or-null menu `{a, ∅}` with `a`
  prior-optimal, D5's harm mass *is* the regret mass of `a` (`harmMass_binary_eq_regretMass`) and
  `voi ≤ M · harmMass` (`voi_le_mul_harmMass_binary`) — the case the rare-state instance
  illustrates, which is why the note's `εh = 0.10` is right there and wrong in general (D11's
  decision set for J3 is the future option set, not `{a, ∅}`).
* **The refutation with the null action in the menu** (`nullMenu`: `(2, 0)`, `(0, 2)`, `(0, 0)`):
  `harmMass = 0`, `1 ≤ voi` (`nullMenu_no_M`); and in the *rare-state* regime S2 names
  (`rarePrior ε`, `ε ≤ 1/3`, menu `(1, 0)`, `(0, 2)`, `(0, 0)`): `harmMass = 0 < 2ε ≤ voi`
  (`rareNull_no_M`). So the sentence is false even in the regime it names, and the absence of
  the null action from `matchMenu 2` in `harmMass_zero_voi_pos` is immaterial.
-/

namespace Cleanroom.Info.InfoVoiLatents.Voi

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Blackwell
open MeasureTheory ProbabilityTheory

noncomputable section

variable {W S : Type} [Fintype W] [Fintype S]

/-! ### Harm mass (D5, as stated) and regret mass (the bound's reading) -/

open scoped Classical in
/-- **D5's harm mass**: `m(A) := max_{a ∈ A} μ{w | u a w < v₀ w}`, the largest prior mass on which
an action of the menu falls below the null action `v₀` (D11: harm is relative to the null action;
"`a` is harmful at `w`" read pointwise as `u a w < v₀ w` — ATTRIBUTION-UNVETTED that this is the
note's intended event; D11's own `harm` is an expectation, under which the counterexample below
is unchanged).
Source: [[generalization-final]] D5 l. 35, D11 l. 47
Kind: D
Fidelity: exact (pointwise reading of "`a` is harmful") -/
def harmMass (μ : W → ℝ) (v₀ : W → ℝ) {n : ℕ} (u : Fin (n + 1) → W → ℝ) : ℝ :=
  (univ : Finset (Fin (n + 1))).sup' univ_nonempty
    (fun a => ∑ w ∈ univ.filter (fun w => u a w < v₀ w), μ w)

open scoped Classical in
/-- **Regret mass**: `μ{w | ∃ a, u a⋆ w < u a w}`, the prior mass of the states where some action
beats the prior-optimal `a⋆` — the reading under which `voi_le_mul_regretMass` holds.
Source: [[generalization-final]] S2 l. 61 (last sentence), D5 l. 35; findings F6
Kind: D
Fidelity: variant: regret-mass reading of "harm mass" -/
def regretMass (μ : W → ℝ) {n : ℕ} (u : Fin (n + 1) → W → ℝ) (aStar : Fin (n + 1)) : ℝ :=
  ∑ w ∈ univ.filter (fun w => ∃ a, u aStar w < u a w), μ w

open scoped Classical in
/-- `voi_le_mul_regretMass` restated with the definition of record.
Source: [[generalization-final]] S2 l. 61, D5 l. 35; findings F6
Kind: C
Fidelity: variant: regret-mass reading of "harm mass"
Hyps: (a) all -/
theorem voi_le_mul_regretMass' [DecidableEq S] {μ : W → ℝ} (hμ : μ ∈ stdSimplex ℝ W)
    (k : Experiment W S) {n : ℕ} {u : Fin (n + 1) → W → ℝ} {M : ℝ}
    (hM : ∀ a a' w, u a w - u a' w ≤ M) {aStar : Fin (n + 1)}
    (hstar : E μ (u aStar) = priorValue μ u) : voi μ k u ≤ M * regretMass μ u aStar := by
  unfold regretMass
  convert voi_le_mul_regretMass hμ k hM hstar

/-- The perfect binary signal (`weakSignal` at `η = ½`).
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def perfectSignal : Experiment (Fin 2) (Fin 2) := weakSignal (1 / 2) (by norm_num)

/-- **S2's harm-mass bound is false under D5's definition**: two equiprobable states, null action
`≡ 0`, menu `(2, 0)`, `(0, 2)` (`matchMenu 2`): no action is ever below the null action, so
`harmMass = 0`, while the perfect signal has `voi = 1` — no `M` makes `voi ≤ M · harmMass`.
Source: [[generalization-final]] S2 l. 61 ("the direct bound `VOI ≤ M·m_t(A)` (harm mass, D5) is
the one to quote"), D5 l. 35; audit r1 (fidelity item 3); findings F6
Kind: N+
Fidelity: exact (a refutation of S2's last sentence for D5's `m_t`)
Hyps: (a) all -/
theorem harmMass_zero_voi_pos :
    harmMass half (fun _ => 0) (matchMenu 2) = 0 ∧ voi half perfectSignal (matchMenu 2) = 1 := by
  refine ⟨?_, ?_⟩
  · unfold harmMass
    rw [Finset.sup'_congr univ_nonempty rfl (g := fun _ => (0 : ℝ)) (fun a _ => ?_),
      Finset.sup'_const]
    refine Finset.sum_eq_zero fun w hw => ?_
    exfalso
    simp only [mem_filter, mem_univ, true_and, matchMenu] at hw
    split_ifs at hw <;> linarith
  · unfold perfectSignal
    rw [weakSignal_voi (by norm_num) (by norm_num)]
    norm_num

/-! ### The refutation with the null action in the menu (audit r2, adversarial item 3) -/

/-- Menu `(2, 0)`, `(0, 2)`, `(0, 0)` on two states: the null action is the third action.
Source: none: infrastructure (audit r2 probe `Vacuity.lean` P1, promoted)
Kind: D
Fidelity: exact -/
def nullMenu : Fin 3 → Fin 2 → ℝ := fun a w =>
  if a = 0 then (if w = 0 then 2 else 0) else if a = 1 then (if w = 1 then 2 else 0) else 0

/-- `nullMenu_nonneg`: no action is ever below the null action `≡ 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem nullMenu_nonneg (a : Fin 3) (w : Fin 2) : 0 ≤ nullMenu a w := by
  unfold nullMenu
  split_ifs <;> norm_num

/-- D5's harm mass of `nullMenu` is `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem nullMenu_harmMass_zero : harmMass half (fun _ => 0) nullMenu = 0 := by
  unfold harmMass
  rw [Finset.sup'_congr univ_nonempty rfl (g := fun _ => (0 : ℝ)) (fun a _ => ?_),
    Finset.sup'_const]
  refine Finset.sum_eq_zero fun w hw => ?_
  exfalso
  simp only [mem_filter, mem_univ, true_and] at hw
  linarith [nullMenu_nonneg a w]

/-- The perfect signal has `voi ≥ 1` on `nullMenu`: "match the state" earns `2`, the prior value
is `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem nullMenu_voi_ge_one : 1 ≤ voi half perfectSignal nullMenu := by
  unfold voi
  have hprior : priorValue half nullMenu ≤ 1 := by
    unfold priorValue
    rw [Finset.sup'_le_iff]
    intro a _
    fin_cases a <;> simp [E, half, nullMenu, Fin.sum_univ_two] <;> norm_num
  have hbayes : 2 ≤ bayesValue half perfectSignal nullMenu := by
    unfold bayesValue
    refine le_trans (le_of_eq ?_)
      (Finset.le_sup' _ (mem_univ (fun s : Fin 2 => if s = 0 then (0 : Fin 3) else 1)))
    unfold perfectSignal
    simp [half, nullMenu, Fin.sum_univ_two]
    norm_num
  linarith

/-- **S2's harm-mass bound is false with the null action in the menu**: no `M` makes
`voi ≤ M · harmMass` on `nullMenu` (`harmMass = 0`, `voi ≥ 1`).
Source: [[generalization-final]] S2 l. 61 (last sentence), D5 l. 35, D11 l. 47; audit r2
(adversarial item 3)
Kind: N+
Fidelity: exact (refutation, with D11's null action available)
Hyps: (a) all -/
theorem nullMenu_no_M (M : ℝ) :
    ¬ voi half perfectSignal nullMenu ≤ M * harmMass half (fun _ => 0) nullMenu := by
  rw [nullMenu_harmMass_zero, mul_zero]
  linarith [nullMenu_voi_ge_one]

/-- The rare-state variant: prior `(1 − ε, ε)`, menu `(1, 0)`, `(0, 2)`, `(0, 0)`.
Source: none: infrastructure (audit r2 probe P1)
Kind: D
Fidelity: exact -/
def rareNullMenu : Fin 3 → Fin 2 → ℝ := fun a w =>
  if a = 0 then (if w = 0 then 1 else 0) else if a = 1 then (if w = 1 then 2 else 0) else 0

/-- `rareNullMenu_nonneg`: no action is ever below the null action.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rareNullMenu_nonneg (a : Fin 3) (w : Fin 2) : 0 ≤ rareNullMenu a w := by
  unfold rareNullMenu
  split_ifs <;> norm_num

/-- D5's harm mass of `rareNullMenu` is `0` at every prior.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rareNull_harmMass_zero (ε : ℝ) :
    harmMass (rarePrior ε) (fun _ => 0) rareNullMenu = 0 := by
  unfold harmMass
  rw [Finset.sup'_congr univ_nonempty rfl (g := fun _ => (0 : ℝ)) (fun a _ => ?_),
    Finset.sup'_const]
  refine Finset.sum_eq_zero fun w hw => ?_
  exfalso
  simp only [mem_filter, mem_univ, true_and] at hw
  linarith [rareNullMenu_nonneg a w]

/-- With the rare state of mass `ε ≤ 1/3`, the perfect signal still has `voi ≥ 2ε > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rareNull_voi_ge {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 3) :
    2 * ε ≤ voi (rarePrior ε) perfectSignal rareNullMenu := by
  unfold voi
  have hprior : priorValue (rarePrior ε) rareNullMenu ≤ 1 - ε := by
    unfold priorValue
    rw [Finset.sup'_le_iff]
    intro a _
    fin_cases a <;> simp [E, rarePrior, rareNullMenu, Fin.sum_univ_two] <;> linarith
  have hbayes : 1 + ε ≤ bayesValue (rarePrior ε) perfectSignal rareNullMenu := by
    unfold bayesValue
    refine le_trans (le_of_eq ?_)
      (Finset.le_sup' _ (mem_univ (fun s : Fin 2 => if s = 0 then (0 : Fin 3) else 1)))
    unfold perfectSignal
    simp [rarePrior, rareNullMenu, Fin.sum_univ_two]
    ring
  linarith

/-- **S2's harm-mass bound is false in the rare-state regime it names**, with the null action in
the menu: for `0 < ε ≤ 1/3`, no `M` makes `voi ≤ M · harmMass` (`harmMass = 0 < 2ε ≤ voi`).
Source: [[generalization-final]] S2 l. 61 ("rare-state uncertainty"; last sentence), D5 l. 35;
audit r2 (adversarial item 3)
Kind: N+
Fidelity: exact (refutation in the regime the sentence names)
Hyps: (a) all -/
theorem rareNull_no_M {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 3) (M : ℝ) :
    ¬ voi (rarePrior ε) perfectSignal rareNullMenu
        ≤ M * harmMass (rarePrior ε) (fun _ => 0) rareNullMenu := by
  rw [rareNull_harmMass_zero, mul_zero]
  linarith [rareNull_voi_ge hε hε']

/-! ### Where S2's harm-mass bound is true: the binary execute-or-null menu (audit r2) -/

open scoped Classical in
/-- On the binary menu `![a, v₀]` (execute `a`, or the null action `v₀`) with `a` prior-optimal,
D5's harm mass equals the regret mass of `a`: the only action that can be below the null action
is `a`, and the only action that can beat `a` is the null action.
Source: [[generalization-final]] D5 l. 35, D11 l. 47; audit r2 (fidelity item 2, probe
`HarmMassBinary.lean`, promoted)
Kind: P
Fidelity: exact -/
theorem harmMass_binary_eq_regretMass (μ : W → ℝ) (hμ : ∀ w, 0 ≤ μ w) (a v₀ : W → ℝ) :
    harmMass μ v₀ ![a, v₀] = regretMass μ ![a, v₀] 0 := by
  unfold harmMass regretMass
  rw [sup'_fin_two]
  have h1 : (univ.filter fun w => (![a, v₀] : Fin 2 → W → ℝ) 1 w < v₀ w) = ∅ := by
    ext w
    simp
  have h0 : (univ.filter fun w => ∃ b : Fin 2, (![a, v₀] : Fin 2 → W → ℝ) 0 w < ![a, v₀] b w)
      = univ.filter fun w => (![a, v₀] : Fin 2 → W → ℝ) 0 w < v₀ w := by
    ext w
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨b, hb⟩
      fin_cases b
      · simp at hb
      · simpa using hb
    · intro h
      exact ⟨1, by simpa using h⟩
  rw [h1, h0, Finset.sum_empty]
  exact max_eq_left (Finset.sum_nonneg fun w _ => hμ w)

open scoped Classical in
/-- **S2's harm-mass bound holds for the binary execute-or-null menu with the action
prior-optimal**: `voi ≤ M · harmMass`, `M` the range `|a − v₀|`. This is the case the rare-state
instance illustrates (`stopMenu`, `continue` prior-optimal, harm set `{wrong}`), which is why the
note's `εh = 0.10` is right there; for a general menu the sentence is false
(`harmMass_zero_voi_pos`, `nullMenu_no_M`, `rareNull_no_M`).
Source: [[generalization-final]] S2 l. 61 (last sentence), D5 l. 35; audit r2 (fidelity item 2)
Kind: C
Fidelity: weaker: the binary menu `{a, ∅}` with `a` prior-optimal (the general sentence is false)
Hyps: (a) all -/
theorem voi_le_mul_harmMass_binary [DecidableEq S] {μ : W → ℝ} (hμ : μ ∈ stdSimplex ℝ W)
    (k : Experiment W S) (a v₀ : W → ℝ) {M : ℝ} (hM : ∀ w, |a w - v₀ w| ≤ M)
    (hstar : E μ a = priorValue μ ![a, v₀]) :
    voi μ k ![a, v₀] ≤ M * harmMass μ v₀ ![a, v₀] := by
  rw [harmMass_binary_eq_regretMass μ hμ.1 a v₀]
  refine voi_le_mul_regretMass' hμ k ?_ hstar
  intro b b' w
  have h := abs_le.1 (hM w)
  fin_cases b <;> fin_cases b' <;> simp <;> linarith [h.1, h.2]

/-! ### The regret-mass bound applied at the rare-state instance -/

/-- **The regret-mass bound applied at the rare-state instance**: `voi ≤ 10 · μ{wrong}`, with its
hypothesis package discharged (`M = 10` the cross-action range; `continue` prior-optimal).
Source: [[generalization-final]] P2 l. 109; [[generalization-adversary]] D5 l. 19; audit r1
(adversarial item 4, probe P6)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem rareState_regret_bound :
    voi (rarePrior (1 / 100)) (pressExp (1 / 100) (9 / 10) (by norm_num) (by norm_num))
        (stopMenu 1 10)
      ≤ 10 * ∑ w ∈ univ.filter (fun w => ∃ a, stopMenu 1 10 0 w < stopMenu 1 10 a w),
          rarePrior (1 / 100) w := by
  refine voi_le_mul_regretMass (rarePrior_mem (by norm_num)) _ ?_ ?_
  · intro a a' w
    unfold stopMenu
    fin_cases a <;> fin_cases a' <;> fin_cases w <;> simp <;> norm_num
  · unfold priorValue
    rw [sup'_fin_two]
    have h0 : E (rarePrior (1 / 100)) (stopMenu 1 10 0) = -(1 / 10) := by
      simp [E, rarePrior, stopMenu, Fin.sum_univ_two]
      norm_num
    have h1 : E (rarePrior (1 / 100)) (stopMenu 1 10 1) = -(99 / 100) := by
      simp [E, rarePrior, stopMenu]
      norm_num
    rw [h0, h1, max_eq_left (by norm_num)]

/-- **`voi ≤ 1/10` at the rare-state instance**, as a theorem (the bound, not an evaluation of its
right-hand side); with `voi = 801/10000` this is the bound's slack `199/10000`.
Source: [[generalization-final]] P2 l. 109; findings F6, F8
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem rareState_voi_le_regretMass :
    voi (rarePrior (1 / 100)) (pressExp (1 / 100) (9 / 10) (by norm_num) (by norm_num))
        (stopMenu 1 10) ≤ 1 / 10 := by
  have h := rareState_regret_bound
  rw [rareState_instance.2.1] at h
  exact h

/-! ### The bridge instantiated on PFR's side -/

/-- **The weak signal's mutual information over PFR**: `I[fst : snd ; joint half (weakSignal η)]
= log 2 − h₂(½ + η)` exactly, through the bridge — an exact PFR mutual information on record.
Source: [[generalization-final]] P2 l. 109 (the `I(nats)` column of `voi_bound.py`); audit r1
(adversarial item 3)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem weakSignal_mutualInfo {η : ℝ} (hη : η ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    I[(Prod.fst : Fin 2 × Fin 2 → Fin 2) : (Prod.snd : Fin 2 × Fin 2 → Fin 2) ;
        Bridge.joint half (weakSignal η hη) half_mem]
      = Real.log 2 - Real.binEntropy (1 / 2 + η) := by
  rw [← Bridge.sum_klFin_eq_mutualInfo, weakSignal_klFin hη]

end

end Cleanroom.Info.InfoVoiLatents.Voi
