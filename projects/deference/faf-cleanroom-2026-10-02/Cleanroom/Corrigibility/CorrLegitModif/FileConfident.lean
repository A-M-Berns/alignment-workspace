import Cleanroom.Corrigibility.CorrLegitModif.Plumbing
import Cleanroom.Corrigibility.CorrReflectFrames.Collapse
import Cleanroom.Corrigibility.CorrLegitGeneral.Locality
import Cleanroom.Lit.LitDdbFacts.Examples

/-!
# corr-legit-modif — T7, T13: filing the confident case in `¬L`; a learned `L̂`

[[yudkowsky]] C5 l. 84: "'Reflection conditional on `L`' is satisfiable by an agent that puts the
press-when-I-am-confident case in `¬L`". Formalized: for every deferrer `π ≥ 0` and event `B`
(the confident case) with `0 < π(Bᶜ)`, take `L := Bᶜ` and the Bayesian refinement of `π` along the
partition `{B, Bᶜ}` as the successor frame. Then the `L`-conditioned criterion holds in every form
— Total Trust, the equality form (Reflection of `restrict π L`), the local equality form for every
question — while `restrict π L` gives `B` mass `0`: the criterion constrains nothing on `B`, and the
per-`Q` rule at `π(L ∩ B) = 0` (`PerQ.perQ_threshold`, cited) does not comply there. The companion
`legitTotalTrustWrt_congr_off_L` is the formal content of "legitimacy's content lies in the prior
over `L`": the criterion sees `π` and `F` only on `L`. Finding: §2.11's criterion needs a constraint
on `P(L)`; the surviving neighbour is the per-`Q` threshold.

T13 (stretch): with a detector `L̂` in place of `L`, `legitimizingTT_certain_of_legit` applies
verbatim — the successor is certain of `L̂`, not of the true `L` (`certain_of_detector`,
`detector_witness`: `P_w(L̂) = 1`, `P_w(L) = 1/2`).
-/

namespace Cleanroom.Corrigibility.CorrLegitModif

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Corrigibility.CorrLegitGeneral Cleanroom.Lit.LitDdbFacts.Examples

noncomputable section

set_option linter.unusedSectionVars false

variable {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

/-- **The confident-case frame**: the Bayesian refinement of `π` along the partition `{B, Bᶜ}` —
rows on `Bᶜ` are `π(· | Bᶜ)`, rows on `B` are `π(· | B)` (a point mass if `B` is null).
Source: [[yudkowsky]] C5 l. 84; mandate T7 ("rows on `L` = the conditionals of `restrict π L` on a
partition of `L`; rows on `B` arbitrary")
Kind: D
Fidelity: exact (the one-cell partition of `L`) -/
def fileFrame (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (B : Finset W) : Frame W :=
  refineFrame π hπ (fun w => decide (w ∈ B))

/-- `Bᶜ` is a union of fibres of the partition `{B, Bᶜ}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem compl_fibre_closed (B : Finset W) :
    ∀ w ∈ Bᶜ, ∀ v, decide (v ∈ B) = decide (w ∈ B) → v ∈ Bᶜ := by
  intro w hw v hv
  rw [mem_compl] at hw ⊢
  simpa [hw] using hv

/-- **T7, `file_confident_case`**: for every `π ≥ 0` and event `B` with `0 < π(Bᶜ)`, the event
`L := Bᶜ` and the frame `fileFrame π B` satisfy `LegitimizingTT π F L`, `Reflects (restrict π L) F`
(the equality form) and `LegitReflectsWrt Q π F L` for every `Q`, while
`mass (restrict π L) B = 0`. The criterion constrains nothing on the confident case. The
partition of `L` is the coarsest one, so the successor has one candidate on `L` (the restricted
deferrer is proportional to its only row there) — which is yudkowsky C5's point that the criterion
is satisfiable vacuously; the same proof works for any `f` refining `{B, Bᶜ}`
(`reflects_restrict_refineFrame` with `A = Bᶜ`).
Source: [[yudkowsky]] C5 l. 84; corr-wf13-2-076; [[legitimacy]] §2.11 (the criterion)
Kind: C (`reflects_restrict_refineFrame`, `varReflects_of_reflects`, `totalTrust_of_varReflects`;
regraded at audit round 1)
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, `0 < mass π Bᶜ` -/
theorem file_confident_case {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) (B : Finset W)
    (hB : 0 < mass π Bᶜ) :
    Bᶜ ∩ B = ∅ ∧ 0 < mass π Bᶜ ∧
    LegitimizingTT π (fileFrame π hπ B) Bᶜ ∧ Reflects (restrict π Bᶜ) (fileFrame π hπ B) ∧
    (∀ (Q : W → C), LegitReflectsWrt Q π (fileFrame π hπ B) Bᶜ) ∧
    mass (restrict π Bᶜ) B = 0 := by
  have hR : Reflects (restrict π Bᶜ) (fileFrame π hπ B) :=
    reflects_restrict_refineFrame hπ _ Bᶜ (compl_fibre_closed B)
  have hπ' := restrict_nonneg hπ Bᶜ
  refine ⟨by ext w; simp, hB, ?_, hR, fun Q => reflectsWrt_of_reflects hR Q, ?_⟩
  · unfold LegitimizingTT
    exact totalTrust_of_varReflects hπ' (varReflects_of_reflects hπ' hR)
  · rw [mass_restrict, show B ∩ Bᶜ = ∅ by ext w; simp]; rfl

/-- The existential packaging of `file_confident_case`.
Source: [[yudkowsky]] C5 l. 84; corr-wf13-2-076
Kind: P
Fidelity: exact
Hyps: (a) as `file_confident_case` -/
theorem file_confident_case_exists {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) (B : Finset W)
    (hB : 0 < mass π Bᶜ) :
    ∃ (L : Finset W) (F : Frame W), L ∩ B = ∅ ∧ 0 < mass π L ∧ LegitimizingTT π F L ∧
      Reflects (restrict π L) F ∧ (∀ (Q : W → C), LegitReflectsWrt Q π F L) ∧
      mass (restrict π L) B = 0 :=
  ⟨Bᶜ, fileFrame π hπ B, file_confident_case hπ B hB⟩

/-- **Legitimacy's content lies in `L`** (`legitTotalTrustWrt_congr_off_L`): if two deferrers agree
on `L` and two frames have the same rows on `L`, the `L`-conditioned local criteria agree — the
criterion sees nothing off `L`.
Source: [[yudkowsky]] C5 l. 84 ("Nothing in it constrains `P_{t₁}(L | Pr, confident)`"); mandate T7
Kind: L
Fidelity: exact
Hyps: (a) `π' = π` on `L`, `F'.P = F.P` on `L` -/
theorem legitTotalTrustWrt_congr_off_L {Q : W → C} {π π' : W → ℝ} {F F' : Frame W} {L : Finset W}
    (hπ : ∀ w ∈ L, π' w = π w) (hF : ∀ w ∈ L, F'.P w = F.P w) :
    LegitTotalTrustWrt Q π' F' L ↔ LegitTotalTrustWrt Q π F L := by
  unfold LegitTotalTrustWrt TotalTrustWrt
  have key : ∀ (X : W → ℝ) (s : ℝ),
      ∑ w, restrict π' L w * (X w - s) * (if s ≤ E (F'.P w) X then 1 else 0) =
        ∑ w, restrict π L w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) := by
    intro X s
    apply sum_congr rfl
    intro w _
    rw [restrict_apply, restrict_apply]
    by_cases hw : w ∈ L
    · rw [if_pos hw, if_pos hw, hπ w hw, hF w hw]
    · rw [if_neg hw, if_neg hw]; ring
  simp only [key]

/-! ## T13: the learned detector -/

/-- **Locality-forcing with a learned `L̂`** (`certain_of_detector`): under the criterion with the
agent's detector `L̂` in place of `L`, every positive-mass `L̂`-world's successor is certain of `L̂` —
`legitimizingTT_certain_of_legit` verbatim; nothing is said about the true `L`.
Source: [[corr-legit-general-handoff]] item 7; `legitimizingTT_certain_of_legit`
Kind: L (cited)
Fidelity: exact
Hyps: (a) as the cited theorem, with `L̂` for `L` -/
theorem certain_of_detector {π : W → ℝ} (hπ : ∀ v, 0 ≤ π v) {F : Frame W} {Lhat : Finset W}
    (h : LegitimizingTT π F Lhat) {w : W} (hw : w ∈ Lhat) (hπw : 0 < π w) :
    mass (F.P w) Lhat = 1 :=
  legitimizingTT_certain_of_legit hπ h hw hπw

/-! ## Witnesses on three worlds -/

/-- The third coordinate of a three-vector (`fin_cases` leaves `2` as a literal).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem vec3_two (a b c : ℝ) : (![a, b, c] : Fin 3 → ℝ) 2 = c := rfl

/-- The deferrer `(1/2, 1/4, 1/4)` on three worlds.
Source: mandate T7 (witness)
Kind: D
Fidelity: exact -/
def πfc : Fin 3 → ℝ := ![1 / 2, 1 / 4, 1 / 4]

/-- The confident case `B = {0}` (mass `1/2`) with `Bᶜ = {1, 2}` (mass `1/2`).
Source: mandate T7 (witness)
Kind: D
Fidelity: exact -/
def Bfc : Finset (Fin 3) := {0}

/-- Nonnegativity of the witness deferrer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem πfc_nonneg : ∀ w, 0 ≤ πfc w := by
  intro w; fin_cases w <;> norm_num [πfc, vec3_two]

/-- **T7's witness**: both `B` and `Bᶜ` have positive mass (`1/2` each); the confident-case frame
has `LegitimizingTT`, the equality form and every local form on `L = Bᶜ`, and gives `B` restricted
mass `0`; its rows are `π(· | {1, 2}) = (0, 1/2, 1/2)` on `L` and `δ₀` on `B`, and the `L`-rows are
certain of `L` (`legitimizingTT_certain_of_legit`'s conclusion, `P_1(L) = 1`).
Source: mandate T7 (witness); [[yudkowsky]] C5 l. 84
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem file_confident_witness :
    0 < mass πfc Bfc ∧ 0 < mass πfc Bfcᶜ ∧
    LegitimizingTT πfc (fileFrame πfc πfc_nonneg Bfc) Bfcᶜ ∧
    Reflects (restrict πfc Bfcᶜ) (fileFrame πfc πfc_nonneg Bfc) ∧
    mass (restrict πfc Bfcᶜ) Bfc = 0 ∧
    (fileFrame πfc πfc_nonneg Bfc).P 1 = ![0, 1 / 2, 1 / 2] ∧
    (fileFrame πfc πfc_nonneg Bfc).P 0 = ![1, 0, 0] ∧
    mass ((fileFrame πfc πfc_nonneg Bfc).P 1) Bfcᶜ = 1 := by
  have hcompl : (Bfcᶜ : Finset (Fin 3)) = {1, 2} := by decide
  have hBc : 0 < mass πfc Bfcᶜ := by
    rw [hcompl]; simp [mass, πfc, vec3_two] <;> norm_num
  obtain ⟨-, -, h1, h2, -, h3⟩ := file_confident_case (C := Fin 1) πfc_nonneg Bfc hBc
  have hfib1 : fibre (fun w : Fin 3 => decide (w ∈ Bfc)) 1 = {1, 2} := by
    ext w; fin_cases w <;> simp [mem_fibre, Bfc]
  have hfib0 : fibre (fun w : Fin 3 => decide (w ∈ Bfc)) 0 = {0} := by
    ext w; fin_cases w <;> simp [mem_fibre, Bfc]
  have hm1 : mass πfc (fibre (fun w : Fin 3 => decide (w ∈ Bfc)) 1) = 1 / 2 := by
    rw [hfib1]; simp [mass, πfc, vec3_two] <;> norm_num
  have hm0 : mass πfc (fibre (fun w : Fin 3 => decide (w ∈ Bfc)) 0) = 1 / 2 := by
    rw [hfib0]; simp [mass, πfc] <;> norm_num
  have hrow1 : (fileFrame πfc πfc_nonneg Bfc).P 1 = ![0, 1 / 2, 1 / 2] := by
    simp only [fileFrame, refineFrame_P]
    rw [condRow_of_pos (by rw [hm1]; norm_num)]
    simp only [hm1]
    simp only [hfib1]
    funext w; fin_cases w <;> simp [ind, πfc, vec3_two] <;> norm_num
  have hrow0 : (fileFrame πfc πfc_nonneg Bfc).P 0 = ![1, 0, 0] := by
    simp only [fileFrame, refineFrame_P]
    rw [condRow_of_pos (by rw [hm0]; norm_num)]
    simp only [hm0]
    simp only [hfib0]
    funext w; fin_cases w <;> simp [ind, πfc, vec3_two] <;> norm_num
  refine ⟨by simp [mass, Bfc, πfc], hBc, h1, h2, h3, hrow1, hrow0, ?_⟩
  rw [hrow1, hcompl]
  simp [mass, vec3_two] <;> norm_num

/-- **T13's witness**: with the detector `L̂ = {1, 2}` and the true legitimacy event `L = {1}`, the
successor at the positive-mass world `1` is certain of `L̂` (`1`) but not of `L` (`1/2`).
Source: [[corr-legit-general-handoff]] item 7 (what a modified-`L` criterion forces)
Kind: N− (one row; the detector/truth gap is the content, the frame is T7's)
Fidelity: exact
Hyps: (a) none -/
theorem detector_witness :
    mass ((fileFrame πfc πfc_nonneg Bfc).P 1) Bfcᶜ = 1 ∧
    mass ((fileFrame πfc πfc_nonneg Bfc).P 1) {1} = 1 / 2 ∧ ((1 / 2 : ℝ) < 1) := by
  obtain ⟨-, -, -, -, -, hrow1, -, hL⟩ := file_confident_witness
  refine ⟨hL, ?_, by norm_num⟩
  rw [hrow1]; simp [mass] <;> norm_num

end

end Cleanroom.Corrigibility.CorrLegitModif
