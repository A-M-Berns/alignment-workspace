import Cleanroom.Corrigibility.CorrReflectFrames.Viability
import Cleanroom.Corrigibility.CorrReflectFrames.Compose
import Cleanroom.Corrigibility.CorrReflectFrames.Twist
import Cleanroom.Corrigibility.CorrReflectFrames.Accuracy
import Cleanroom.Corrigibility.CorrReflectFrames.WitnessesA
import Mathlib.Data.Fin.VecNotation

/-!
# corr-reflect-frames — witnesses D (repair round 1)

Built for audit r1 (fidelity B2, N2; adversarial 1, 9, 10):

* **T8(b)**: the two-observation witness of finding F3 (`twoObs_legit_not_condIndep`: `L` is
  legitimizing for the agent's own refinement while `L ⊥ φ | O` fails on a fibre), adopted from
  the adversarial probe; the "sensor reported correctly" event on the 4-atom joint
  `P(W) = 1/10`, `P(Pr | R) = 1/10`, `P(Pr | W) = 3/5` is *not* viable
  (`sensorCorrect_not_legitimizingVal`: `P(W | Pr, L) = 1 ≠ 2/5`).
* **T8(c)**: two general Blackwell facts — a constant experiment is a garbling of every
  experiment (`blackwellLE_of_const`), every experiment is a garbling of the perfect one
  (`blackwellLE_ofMap_id`) — and the two instances: the coin arm (forced press on tails) is
  strictly delegitimizing, "the programmers acquire evidence" (perfect sensor given `E`) is
  strictly legitimizing.
* **T16(b)**: E3′ — a successor `ρ` and the builder's conditional `b` given `(ρ, L)` agree on
  `E[X]` (value form on `{X}` holds) and disagree on `E[X · 𝟙_Pr]` (value form on `{Z}` fails);
  the builder complies (`60/109 ≥ 1/5`), the successor overrides (`6/55 < 1/5`).
* Positive witnesses: the twist family instantiated (`twist4_instance`), `flat` introspective
  (`flat_candsIntrospective`, the N− of `collapse`), `legitimizingTT_iff_forall_legitimizingVal`
  and `totalTrust_of_partition` inhabited on `frame4` with proper events, and a strict Brier
  improvement under value form (`frame4_brier_strict`).
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames.Witnesses

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames

noncomputable section

/-! ## Finite-evaluation helpers -/

/-- Mass of an intersection as a filtered sum over the first factor.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_inter_eq {W : Type} [Fintype W] [DecidableEq W] (π : W → ℝ) (A B : Finset W) :
    mass π (A ∩ B) = ∑ v ∈ A, if v ∈ B then π v else 0 := by
  rw [mass, ← filter_mem_eq_inter, sum_filter]

/-- Mass of a fibre as a full sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_fibre_eq {W S : Type} [Fintype W] [DecidableEq W] [DecidableEq S] (π : W → ℝ)
    (f : W → S) (w : W) : mass π (fibre f w) = ∑ v, if f v = f w then π v else 0 := by
  rw [mass, fibre, sum_filter]

/-- Mass of an event inside a fibre as a filtered sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_inter_fibre_eq {W S : Type} [Fintype W] [DecidableEq W] [DecidableEq S] (π : W → ℝ)
    (A : Finset W) (f : W → S) (w : W) :
    mass π (A ∩ fibre f w) = ∑ v ∈ A, if f v = f w then π v else 0 := by
  rw [mass_inter_eq]
  simp only [mem_fibre]

/-- The announced value of a positive conditional row, as a ratio.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condRow_mass_eq {W S : Type} [Fintype W] [DecidableEq W] [DecidableEq S] {π : W → ℝ}
    {f : W → S} {w : W} (h : 0 < mass π (fibre f w)) (φ : Finset W) :
    mass (condRow π f w) φ = mass π (φ ∩ fibre f w) / mass π (fibre f w) := by
  rw [eq_div_iff h.ne']
  exact condRow_mass_mul h φ

/-! ## T8(b): the two-observation witness (finding F3) -/

/-- The uniform prior on four atoms `(φ,o₁), (¬φ,o₁), (φ,o₂), (¬φ,o₂)`.
Source: [[miri]] I5.2 l. 143 (finding F3, corr-wf13-2-007); audit r1 adversarial probe
Kind: D
Fidelity: exact -/
def πTwoObs : Fin 4 → ℝ := fun _ => 1 / 4

/-- `πTwoObs` is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πTwoObs_nonneg (w : Fin 4) : 0 ≤ πTwoObs w := by norm_num [πTwoObs]

/-- The observation map: atoms `0, 1` see `o₁`, atoms `2, 3` see `o₂`.
Source: [[miri]] I5.2 l. 143
Kind: D
Fidelity: exact -/
def obsTwo : Fin 4 → Fin 2 := ![0, 0, 1, 1]

/-- `φ = {0, 2}`: the hits, one in each observation.
Source: [[miri]] I5.2 l. 143
Kind: D
Fidelity: exact -/
abbrev φTwoObs : Finset (Fin 4) := {0, 2}

/-- `L = {0, 3}`: all hits inside `o₁`, all misses inside `o₂`.
Source: [[miri]] I5.2 l. 143 (finding F3)
Kind: D
Fidelity: exact -/
abbrev LTwoObs : Finset (Fin 4) := {0, 3}

/-- The agent's own refinement along the observation.
Source: [[miri]] I5.2 l. 143
Kind: D
Fidelity: exact -/
def FTwoObs : Frame (Fin 4) := refineFrame πTwoObs πTwoObs_nonneg obsTwo

/-- Each observation fibre has mass `1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_fibre_obsTwo (w : Fin 4) : mass πTwoObs (fibre obsTwo w) = 1 / 2 := by
  fin_cases w <;>
    (rw [mass, fibre, sum_filter]; simp [Fin.sum_univ_four, obsTwo, πTwoObs]; norm_num)

/-- Each observation fibre carries hits of mass `1/4`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_φ_fibre_obsTwo (w : Fin 4) : mass πTwoObs (φTwoObs ∩ fibre obsTwo w) = 1 / 4 := by
  fin_cases w <;>
    (rw [mass_inter_eq, sum_pair (show (0 : Fin 4) ≠ 2 by decide)];
      simp [mem_fibre, obsTwo, πTwoObs])

/-- Both observations announce `P(φ | o) = 1/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem FTwoObs_row_φ (w : Fin 4) : mass (FTwoObs.P w) φTwoObs = 1 / 2 := by
  have h : 0 < mass πTwoObs (fibre obsTwo w) := by rw [mass_fibre_obsTwo]; norm_num
  have := condRow_mass_mul (π := πTwoObs) h φTwoObs
  rw [mass_fibre_obsTwo, mass_φ_fibre_obsTwo] at this
  show mass (condRow πTwoObs obsTwo w) φTwoObs = 1 / 2
  linarith

/-- `L = {0, 3}` is legitimizing for `φ` toward the agent's own refinement.
Source: [[miri]] I5.2 l. 143 (finding F3)
Kind: L
Fidelity: n/a -/
theorem LTwoObs_legit : LegitimizingVal πTwoObs FTwoObs φTwoObs LTwoObs := by
  intro c
  rw [mass_inter_valCell, mass_inter_valCell]
  have e : φTwoObs ∩ LTwoObs = {0} := by decide
  rw [e, sum_singleton, sum_pair (show (0 : Fin 4) ≠ 3 by decide)]
  simp only [FTwoObs_row_φ, πTwoObs]
  split_ifs <;> (try subst_vars) <;> norm_num at *

/-- `L ⊥ φ | O` fails on the `o₁` fibre: `1/4 · 1/2 ≠ 1/4 · 1/4`.
Source: [[miri]] I5.2 l. 143 (finding F3)
Kind: L
Fidelity: n/a -/
theorem twoObs_not_condIndep_o1 :
    ¬ (mass πTwoObs (φTwoObs ∩ LTwoObs ∩ fibre obsTwo 0) * mass πTwoObs (fibre obsTwo 0) =
        mass πTwoObs (φTwoObs ∩ fibre obsTwo 0) * mass πTwoObs (LTwoObs ∩ fibre obsTwo 0)) := by
  rw [mass_fibre_obsTwo, mass_φ_fibre_obsTwo, mass_inter_eq, mass_inter_eq]
  have e : φTwoObs ∩ LTwoObs = {0} := by decide
  rw [e, sum_singleton, sum_pair (show (0 : Fin 4) ≠ 3 by decide)]
  simp [mem_fibre, obsTwo, πTwoObs]

/-- **F3 witness (T8(b), N+)**: with two observations announcing the same value, `L` is
legitimizing for `φ` toward the agent's own refinement while `L ⊥ φ | O` fails — the
hypothesis of `legitimizingVal_of_condIndep_fibres` fails while its conclusion holds, so miri
I5.2's `L ⊥ φ | O` is sufficient, not necessary. Both observations announce `1/2`, so the value
cell is `univ` and legitimacy is the single identity `π(φ ∩ L) = 1/2 · π(L)` (`1/4 = 1/2 · 1/2`)
— the balancing across the two fibres is the content.
Source: [[miri]] I5.2 l. 143; corr-wf13-2-007; audit r1 adversarial probe `TwoObsViability`
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem twoObs_legit_not_condIndep : LegitimizingVal πTwoObs FTwoObs φTwoObs LTwoObs ∧
    ¬ ∀ w, mass πTwoObs (φTwoObs ∩ LTwoObs ∩ fibre obsTwo w) * mass πTwoObs (fibre obsTwo w) =
        mass πTwoObs (φTwoObs ∩ fibre obsTwo w) * mass πTwoObs (LTwoObs ∩ fibre obsTwo w) :=
  ⟨LTwoObs_legit, fun h => twoObs_not_condIndep_o1 (h 0)⟩

/-! ## T8(b): "the sensor reported correctly" is not viable -/

/-- The 4-atom joint `P(W) = 1/10`, `P(Pr | R) = 1/10`, `P(Pr | W) = 3/5`: atoms `(W,Pr) = 6/100`,
`(W,¬Pr) = 4/100`, `(R,Pr) = 9/100`, `(R,¬Pr) = 81/100` (indices `0, 1, 2, 3`). A witness, not
a definition of record (`corr-three-step` owns Setting S).
Source: [[miri]] I5.2 l. 143; mandate T8(b)
Kind: D
Fidelity: exact -/
def πSC : Fin 4 → ℝ := ![6 / 100, 4 / 100, 9 / 100, 81 / 100]

/-- `πSC` is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πSC_nonneg (w : Fin 4) : 0 ≤ πSC w := by fin_cases w <;> norm_num [πSC]

/-- The press observation: atoms `0, 2` are pressed (`1`), atoms `1, 3` are not (`0`).
Source: [[miri]] I5.2 l. 143
Kind: D
Fidelity: exact -/
def pressSC : Fin 4 → Fin 2 := ![1, 0, 1, 0]

/-- `W = {0, 1}`: the wrong-state atoms.
Source: [[miri]] I5.2 l. 143
Kind: D
Fidelity: exact -/
abbrev φSC : Finset (Fin 4) := {0, 1}

/-- "The sensor reported correctly": `(Pr ∩ W) ∪ (¬Pr ∩ R) = {0, 3}`.
Source: [[miri]] I5.2 l. 143 ("the sensor reported correctly … is not viable")
Kind: D
Fidelity: exact -/
abbrev LSC : Finset (Fin 4) := {0, 3}

/-- The press fibre has mass `15/100`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_fibre_pressSC_0 : mass πSC (fibre pressSC 0) = 15 / 100 := by
  rw [mass_fibre_eq]; simp [Fin.sum_univ_four, pressSC, πSC]; norm_num

/-- The no-press fibre has mass `85/100`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_fibre_pressSC_3 : mass πSC (fibre pressSC 3) = 85 / 100 := by
  rw [mass_fibre_eq]; simp [Fin.sum_univ_four, pressSC, πSC]; norm_num

/-- The pressed row announces `P(W | Pr) = 2/5`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rowSC_0 : mass ((refineFrame πSC πSC_nonneg pressSC).P 0) φSC = 2 / 5 := by
  have h : 0 < mass πSC (fibre pressSC 0) := by rw [mass_fibre_pressSC_0]; norm_num
  show mass (condRow πSC pressSC 0) φSC = 2 / 5
  rw [condRow_mass_eq h, mass_fibre_pressSC_0, mass_inter_fibre_eq,
    sum_pair (show (0 : Fin 4) ≠ 1 by decide)]
  simp [pressSC, πSC]; norm_num

/-- The unpressed row announces `P(W | ¬Pr) = 4/85`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem rowSC_3 : mass ((refineFrame πSC πSC_nonneg pressSC).P 3) φSC = 4 / 85 := by
  have h : 0 < mass πSC (fibre pressSC 3) := by rw [mass_fibre_pressSC_3]; norm_num
  show mass (condRow πSC pressSC 3) φSC = 4 / 85
  rw [condRow_mass_eq h, mass_fibre_pressSC_3, mass_inter_fibre_eq,
    sum_pair (show (0 : Fin 4) ≠ 1 by decide)]
  simp [pressSC, πSC]; norm_num

/-- **"The sensor reported correctly" is not minimally viable (T8(b), N+)**: on the pressed cell
`P(W | Pr) = 2/5`, but conditional on `L` the pressed worlds are all wrong, `P(W | Pr, L) = 1`.
Source: [[miri]] I5.2 l. 143 (non-viability of the correctness event); mandate T8(b)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem sensorCorrect_not_legitimizingVal :
    ¬ LegitimizingVal πSC (refineFrame πSC πSC_nonneg pressSC) φSC LSC := by
  intro h
  have := h (2 / 5)
  rw [mass_inter_valCell, mass_inter_valCell] at this
  have e : φSC ∩ LSC = {0} := by decide
  rw [e, sum_singleton, sum_pair (show (0 : Fin 4) ≠ 3 by decide), rowSC_0, rowSC_3] at this
  simp [πSC] at this
  norm_num at this

/-! ## T8(c): legitimizing and delegitimizing world events (Blackwell instances) -/

/-- **A constant experiment is a garbling of every experiment**: if every row of `kc` is the
same distribution `r`, then `kc` is Blackwell-below any `k` (garble every signal to `r`).
Source: none: infrastructure (Blackwell 1953); mandate T8(c)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem blackwellLE_of_const {Ω S T : Type} [Fintype S] [Fintype T]
    (k : Blackwell.Experiment Ω S) (kc : Blackwell.Experiment Ω T) {r : T → ℝ}
    (hr : r ∈ stdSimplex ℝ T) (hk : ∀ w, kc.k w = r) : Blackwell.BlackwellLE kc k := by
  refine ⟨fun _ => r, fun _ => hr, fun w t => ?_⟩
  rw [hk w, ← sum_mul, (k.k_mem w).2, one_mul]

/-- **Every experiment is a garbling of the perfect experiment** `ofMap id` (signal = state):
garble the state `w` to the signal distribution `k.k w`.
Source: none: infrastructure (Blackwell 1953); mandate T8(c)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem blackwellLE_ofMap_id {Ω S : Type} [Fintype Ω] [DecidableEq Ω] [Fintype S]
    (k : Blackwell.Experiment Ω S) : Blackwell.BlackwellLE k (Blackwell.ofMap (id : Ω → Ω)) := by
  refine ⟨k.k, k.k_mem, fun w t => ?_⟩
  simp only [Blackwell.ofMap, id_eq, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, if_true]

/-- The press sensor `(α, β) = (1/10, 3/5)`: state `0 = R` presses (signal `1`) with probability
`1/10`, state `1 = W` with probability `3/5`.
Source: [[miri]] I6.3 l. 157; [[joint]] running parameters l. 170
Kind: D
Fidelity: exact -/
def kSensor : Blackwell.Experiment (Fin 2) (Fin 2) where
  k := ![![9 / 10, 1 / 10], ![2 / 5, 3 / 5]]
  k_mem := by
    intro w
    refine ⟨fun s => ?_, ?_⟩
    · fin_cases w <;> fin_cases s <;> simp <;> norm_num
    · fin_cases w <;> simp [Fin.sum_univ_two] <;> norm_num

/-- The forced press (the coin arm on tails): the press happens whatever the state.
Source: [[miri]] I6.3 l. 157 ("the coin arm")
Kind: D
Fidelity: exact -/
def kForced : Blackwell.Experiment (Fin 2) (Fin 2) where
  k := fun _ => ![0, 1]
  k_mem := fun _ => ⟨fun s => by fin_cases s <;> simp, by simp [Fin.sum_univ_two]⟩

/-- **The coin arm is strictly delegitimizing (T8(c), N+)**: given the tails event the sensor
is the forced press, a garbling of the sensor given heads; and not conversely (the sensor's
rows differ, a constant's cannot).
Source: [[miri]] I6.3 l. 157, I6.1 l. 153; mandate T8(c)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem coinArm_strictlyDelegitimizing : StrictlyDelegitimizingEvent kForced kSensor := by
  refine ⟨blackwellLE_of_const kSensor kForced (r := ![0, 1]) ?_ (fun _ => rfl), ?_⟩
  · exact ⟨fun s => by fin_cases s <;> simp, by simp [Fin.sum_univ_two]⟩
  · rintro ⟨g, _, hg⟩
    have h0 := hg 0 1
    have h1 := hg 1 1
    simp [kSensor, kForced, Fin.sum_univ_two] at h0 h1
    linarith

/-- **"The programmers acquire evidence" is strictly legitimizing (T8(c), N+)**: given the
evidence event the sensor is perfect (`ofMap id`), of which the press sensor is a garbling; and
not conversely (a garbling of the sensor cannot separate the states with certainty).
Source: [[miri]] I6.3 l. 157, I6.1 l. 153; mandate T8(c)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem evidence_strictlyLegitimizing :
    StrictlyLegitimizingEvent (Blackwell.ofMap (id : Fin 2 → Fin 2)) kSensor := by
  refine ⟨blackwellLE_ofMap_id kSensor, ?_⟩
  rintro ⟨g, hgs, hg⟩
  have h00 := hg 0 0
  have h10 := hg 1 0
  simp [Blackwell.ofMap, kSensor, Fin.sum_univ_two] at h00 h10
  have a := (hgs 0).1 0
  have b := (hgs 1).1 0
  linarith

/-! ## T16(b): E3′ — value form on `{X}` holds, on `{Z}` fails -/

/-- The successor `ρ` of E3′: `ε = 1/50`, sensor `(1/10, 3/5)`; atoms `(R,¬Pr) = 441/500`,
`(R,Pr) = 49/500`, `(W,¬Pr) = 4/500`, `(W,Pr) = 6/500` (indices `0, 1, 2, 3`).
Source: [[joint]] P.7 E3′ l. 211 (script (k))
Kind: D
Fidelity: exact -/
def ρE3 : Fin 4 → ℝ := ![441 / 500, 49 / 500, 4 / 500, 6 / 500]

/-- The builder's conditional `b` given `(ρ, L)` of E3′: `ε = 1/50`, sensor `(1/100, 3/5)`;
atoms `4851/5000`, `49/5000`, `40/5000`, `60/5000`.
Source: [[joint]] P.7 E3′ l. 211
Kind: D
Fidelity: exact -/
def bE3 : Fin 4 → ℝ := ![4851 / 5000, 49 / 5000, 40 / 5000, 60 / 5000]

/-- `ρE3` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem ρE3_mem : ρE3 ∈ stdSimplex ℝ (Fin 4) :=
  ⟨fun w => by fin_cases w <;> norm_num [ρE3], by simp [Fin.sum_univ_four, ρE3]; norm_num⟩

/-- The decision variable `X` of E3′: `1` on `R`, `−4` on `W` (`c = 1`, `h = 4`).
Source: [[joint]] running parameters l. 170; P.7 E3′ l. 211
Kind: D
Fidelity: exact (reconstructed from the printed expectations: `E_ρ X = 9/10`, `E_ρ Z = 1/20`,
`E_b Z = −191/5000` determine it uniquely) -/
def XE3 : Fin 4 → ℝ := ![1, 1, -4, -4]

/-- The press cell `Pr = {1, 3}`.
Source: [[joint]] P.7 E3′ l. 211
Kind: D
Fidelity: exact -/
abbrev PrE3 : Finset (Fin 4) := {1, 3}

/-- The wrong-state event `W = {2, 3}`.
Source: [[joint]] P.7 E3′ l. 211
Kind: D
Fidelity: exact -/
abbrev WE3 : Finset (Fin 4) := {2, 3}

/-- The press-cell-weighted variable `Z = X · 𝟙_Pr`.
Source: [[joint]] P.7 E3′ l. 211
Kind: D
Fidelity: exact -/
def ZE3 : Fin 4 → ℝ := fun w => XE3 w * ind PrE3 w

/-- The constant frame with every row `ρ` (a single announced successor).
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def constFrame {W : Type} [Fintype W] {ρ : W → ℝ} (hρ : ρ ∈ stdSimplex ℝ W) : Frame W where
  P := fun _ => ρ
  P_mem := fun _ => hρ

/-- Every estimate cell of the constant frame at the announced estimate is `univ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem estCell_constFrame {W : Type} [Fintype W] [DecidableEq W] {ρ : W → ℝ}
    (hρ : ρ ∈ stdSimplex ℝ W) (X : W → ℝ) : estCell (constFrame hρ) X (E ρ X) = univ := by
  ext w; simp [mem_estCell, constFrame]

/-- **E3′ (T16(b), N+)**: with the successor `ρ` as the only announced row and the builder's
conditional `b` as the deferrer, the variable-form identity holds at the announced estimate of
`X` (`E_b X = E_ρ X = 9/10`) and fails for `Z = X · 𝟙_Pr` (`E_b Z = −191/5000 ≠ 1/20 = E_ρ Z`);
the builder complies on the press cell (`b(W ∩ Pr) ≥ 1/5 · b(Pr)`, i.e. `60/109 ≥ 1/5`) while
the successor overrides (`ρ(W ∩ Pr) < 1/5 · ρ(Pr)`, i.e. `6/55 < 1/5`). So refined anticipation
plus value form on the unconditional decision variable does not transport compliance; the
reflection family must contain the press-cell-weighted variables.
Source: [[joint]] P.7 E3′ l. 211; [[joint-final]] Theorem B sharpness (a) l. 133; mandate T16(b)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem e3prime_witness :
    (∑ w ∈ estCell (constFrame ρE3_mem) XE3 (E ρE3 XE3), bE3 w * XE3 w =
        E ρE3 XE3 * mass bE3 (estCell (constFrame ρE3_mem) XE3 (E ρE3 XE3))) ∧
      ¬ (∑ w ∈ estCell (constFrame ρE3_mem) ZE3 (E ρE3 ZE3), bE3 w * ZE3 w =
        E ρE3 ZE3 * mass bE3 (estCell (constFrame ρE3_mem) ZE3 (E ρE3 ZE3))) ∧
      E ρE3 XE3 = 9 / 10 ∧ E bE3 XE3 = 9 / 10 ∧ E ρE3 ZE3 = 1 / 20 ∧
      E bE3 ZE3 = -191 / 5000 ∧
      1 / 5 * mass bE3 PrE3 ≤ mass bE3 (WE3 ∩ PrE3) ∧
      mass ρE3 (WE3 ∩ PrE3) < 1 / 5 * mass ρE3 PrE3 := by
  have hX : E ρE3 XE3 = 9 / 10 := by simp [E, Fin.sum_univ_four, ρE3, XE3]; norm_num
  have hbX : E bE3 XE3 = 9 / 10 := by simp [E, Fin.sum_univ_four, bE3, XE3]; norm_num
  have hZ : E ρE3 ZE3 = 1 / 20 := by
    simp [E, Fin.sum_univ_four, ρE3, XE3, ZE3, ind]; norm_num
  have hbZ : E bE3 ZE3 = -191 / 5000 := by
    simp [E, Fin.sum_univ_four, bE3, XE3, ZE3, ind]; norm_num
  have hm : mass bE3 univ = 1 := by simp [mass, Fin.sum_univ_four, bE3]; norm_num
  refine ⟨?_, ?_, hX, hbX, hZ, hbZ, ?_, ?_⟩
  · rw [estCell_constFrame, hm, mul_one, hX, ← hbX]
    rfl
  · rw [estCell_constFrame, hm, mul_one, hZ]
    show ¬ (E bE3 ZE3 = 1 / 20)
    rw [hbZ]; norm_num
  · have e : WE3 ∩ PrE3 = {3} := by decide
    rw [e, mass, mass, sum_singleton, sum_pair (show (1 : Fin 4) ≠ 3 by decide)]
    simp [bE3]; norm_num
  · have e : WE3 ∩ PrE3 = {3} := by decide
    rw [e, mass, mass, sum_singleton, sum_pair (show (1 : Fin 4) ≠ 3 by decide)]
    simp [ρE3]; norm_num

/-! ## Positive witnesses -/

/-- **The twist family instantiated (N+)**: `twist π4 branch (1/2)` is estimate-matching, not
introspective at candidates, not reflected.
Source: [[armstrong]] I2.2 l. 95; mandate T2(b)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem twist4_instance :
    EstimateMatching π4 (twist π4 π4_mem branch (1 / 2) (by norm_num) (by norm_num)) ∧
      ¬ CandsIntrospective π4 (twist π4 π4_mem branch (1 / 2) (by norm_num) (by norm_num)) ∧
      ¬ Reflects π4 (twist π4 π4_mem branch (1 / 2) (by norm_num) (by norm_num)) := by
  have h0 : 0 < π4 0 := by rw [show π4 0 = 1 / 3 from rfl]; norm_num
  have h2 : 0 < π4 2 := by rw [show π4 2 = 1 / 8 from rfl]; norm_num
  have hne : branch 0 ≠ branch 2 := by simp [branch]
  exact ⟨twist_estimateMatching π4 π4_mem branch (1 / 2) (by norm_num) (by norm_num),
    twist_not_candsIntrospective π4 π4_mem branch (by norm_num) (by norm_num) h0 h2 hne,
    twist_not_reflects π4 π4_mem branch (by norm_num) (by norm_num) h0 h2 hne⟩

open Cleanroom.Found.LitDdbFrames.Examples in
/-- **`flat` is introspective at the candidates of `half`** (the N− of `collapse`): its single
candidate row `half` has cell `univ`, self-mass `1`.
Source: mandate T1 (N− `flat`)
Kind: N−
Fidelity: exact (degenerate: all rows equal the deferrer)
Hyps: (a) none -/
theorem flat_candsIntrospective : CandsIntrospective half flat := by
  intro ρ hρ
  obtain ⟨w, _, rfl⟩ := Frame.mem_cands.1 hρ
  have hcell : flat.cell (flat.P w) = univ := by
    ext v
    simp only [Frame.mem_cell, mem_univ, iff_true]
    fin_cases v <;> fin_cases w <;> rfl
  unfold Frame.selfMass
  rw [hcell]
  fin_cases w <;> simp [flat_P, half, mass, Fin.sum_univ_two] <;> norm_num

/-- The branch-`A` fibre of `frame4` is `{0, 1}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fibre_branch_A (w : Fin 4) (hw : w ∈ ({0, 1} : Finset (Fin 4))) :
    fibre branch w = {0, 1} := by
  ext v
  fin_cases w <;> simp at hw <;> fin_cases v <;> simp [mem_fibre, branch]

/-- The branch-`B` fibre of `frame4` is `{2, 3}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fibre_branch_B (w : Fin 4) (hw : w ∈ ({2, 3} : Finset (Fin 4))) :
    fibre branch w = {2, 3} := by
  ext v
  fin_cases w <;> simp at hw <;> fin_cases v <;> simp [mem_fibre, branch]

/-- The cells of `frame4` at branch `A` lie in `{0, 1}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem frame4_cells_A : ∀ w ∈ ({0, 1} : Finset (Fin 4)), frame4.cell (frame4.P w) ⊆ {0, 1} := by
  intro w hw
  have hpos : 0 < mass π4 (fibre branch w) := by
    rw [fibre_branch_A w hw, mass, sum_pair (show (0 : Fin 4) ≠ 1 by decide)]
    simp [π4]; norm_num
  rw [show frame4.P w = condRow π4 branch w from rfl, frame4, cell_condRow π4_mem.1 hpos,
    fibre_branch_A w hw]

/-- The cells of `frame4` at branch `B` lie in `{2, 3}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem frame4_cells_B : ∀ w ∈ ({2, 3} : Finset (Fin 4)), frame4.cell (frame4.P w) ⊆ {2, 3} := by
  intro w hw
  have hpos : 0 < mass π4 (fibre branch w) := by
    rw [fibre_branch_B w hw, mass, sum_pair (show (2 : Fin 4) ≠ 3 by decide)]
    simp [π4]; norm_num
  rw [show frame4.P w = condRow π4 branch w from rfl, frame4, cell_condRow π4_mem.1 hpos,
    fibre_branch_B w hw]

/-- **Conditional Total Trust on each branch (N+)**: `frame4` is totally trusted by `π4`
restricted to branch `A` and by `π4` restricted to branch `B` — the hypothesis package of
`totalTrust_of_partition` with two proper events, and of `legitimizingTT_iff_forall_legitimizingVal`
(under INT at the restricted candidates) with a proper `L`.
Source: [[ddb]] L-C l. 49; mandate T11(a), T11(c)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem frame4_conditional_totalTrust :
    LegitimizingTT π4 frame4 {0, 1} ∧ LegitimizingTT π4 frame4 {2, 3} ∧
      CandsIntrospective (restrict π4 {0, 1}) frame4 ∧
      (LegitimizingTT π4 frame4 {0, 1} ↔ ∀ φ, LegitimizingVal π4 frame4 φ {0, 1}) ∧
      TotalTrust π4 frame4 := by
  have hI : frame4.Immodest := refineFrame_immodest _ _
  have hA : Reflects (restrict π4 {0, 1}) frame4 :=
    reflects_restrict_of_cells_subset π4_mem.1 (refineFrame_reflects _ _) frame4_cells_A
  have hB : Reflects (restrict π4 {2, 3}) frame4 :=
    reflects_restrict_of_cells_subset π4_mem.1 (refineFrame_reflects _ _) frame4_cells_B
  have hTA : LegitimizingTT π4 frame4 {0, 1} :=
    totalTrust_of_varReflects (restrict_nonneg π4_mem.1 _) (varReflects_of_reflects (restrict_nonneg π4_mem.1 _) hA)
  have hTB : LegitimizingTT π4 frame4 {2, 3} :=
    totalTrust_of_varReflects (restrict_nonneg π4_mem.1 _) (varReflects_of_reflects (restrict_nonneg π4_mem.1 _) hB)
  refine ⟨hTA, hTB, candsIntrospective_of_immodest hI _,
    legitimizingTT_iff_forall_legitimizingVal π4_mem.1 _ (candsIntrospective_of_immodest hI _), ?_⟩
  refine totalTrust_of_partition (L := ![{0, 1}, {2, 3}]) ?_ ?_
  · intro w
    fin_cases w <;> simp [Fin.sum_univ_two, ind]
  · intro j
    fin_cases j
    · exact hTA
    · exact hTB

/-- The rows of `frame4` at worlds `1` and `3` equal those at `0` and `2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem frame4_rows' : frame4.P 1 = frame4.P 0 ∧ frame4.P 3 = frame4.P 2 := by
  constructor
  · have hpos : 0 < mass π4 (fibre branch 0) := by rw [mass_fibre_branch0]; norm_num
    exact condRow_eq_of_mem hpos (by simp [mem_fibre, branch])
  · have hpos : 0 < mass π4 (fibre branch 2) := by rw [mass_fibre_branch2]; norm_num
    exact condRow_eq_of_mem hpos (by simp [mem_fibre, branch])

/-- **Strict Brier improvement under value form (N+ for `brier_expLoss_le_constLoss`)**: on
`frame4` with `φ = {0, 1}` (branch `A`), value-form reflection holds and the expert's expected
Brier loss is `0` against the constant forecast's `1/4`.
Source: [[radical]] Theorem I4.2(a) l. 134; mandate T5(a)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem frame4_brier_strict :
    ValueReflectsOn π4 frame4 {0, 1} ∧ expLoss π4 frame4 {0, 1} brier = 0 ∧
      constLoss π4 {0, 1} brier = 1 / 4 := by
  obtain ⟨hr0, hr2⟩ := frame4_rows
  obtain ⟨hr1, hr3⟩ := frame4_rows'
  refine ⟨valueReflects_iff_forall_on.1 (refineFrame_valueReflects _ _) _, ?_, ?_⟩
  · simp only [expLoss, Fin.sum_univ_four, hr1, hr3, hr0, hr2, brier, ind, mass,
      sum_pair (show (0 : Fin 4) ≠ 1 by decide)]
    simp [π4]
    norm_num
  · simp only [constLoss, Fin.sum_univ_four, brier, ind, mass,
      sum_pair (show (0 : Fin 4) ≠ 1 by decide)]
    simp [π4]; norm_num

end

end Cleanroom.Corrigibility.CorrReflectFrames.Witnesses
