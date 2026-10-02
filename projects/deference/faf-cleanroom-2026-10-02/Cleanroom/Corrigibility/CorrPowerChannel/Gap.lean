import Cleanroom.Corrigibility.CorrPowerChannel.J3
import Cleanroom.Corrigibility.CorrPowerChannel.SelfCap
import Cleanroom.Corrigibility.CorrPowerChannel.Separable

/-!
# `corr-power-channel` — T4(b),(c): the structural gap and the direct-gain identity

* **(c) `takeover_j3_iff`** (106(d)/2-062): for a takeover `T` with gain `g` everywhere and harm
  `h_T` only under the self-reliability latent `Z`, with no information (`trivialExp`),
  J3 holds iff `P(Z) h_T > g` — under the positive-part convention on the net value (`harmOf`,
  `gainOf`), and (`takeover_components_iff`) under the convention that books harm `h_T` and gain
  `g` as separate components. Equality cell `P(Z) = 1/5` at `g = 1/10`, `h_T = 1/2`
  (`takeover_equality_cell`).
* **(b) The structural gap is not a theorem without separability — a finding.** The source's
  "general case" asserts `VOI(s | q) ≥ VOI(ρ-component) > 0` for every `δ` whenever `q` is
  uninformative about `ρ` and `s` reveals it. `gap_counterexample` refutes the unrestricted
  claim: `Ω = Bool × Bool` (`π`, `ρ`) uniform, four options `𝟙[π = 0], 𝟙[π = 1], 𝟙[ρ = 0], 𝟙[ρ = 1]`,
  `q` revealing `π` exactly (`δ = 0`), `s` perfect: `VOI(s | q) = 0` while `VOI(ρ) = 1/2`. Once
  `π` is known, a `π`-option is worth `1` and `ρ` is decision-irrelevant. The separable instance
  of the mandate (`δ(1 − 1/(n+1)) + σ(1 − 1/(m+1))`) and the general separable theorem are
  `Separable.lean` (`e3rho_marginal`, `voiExp_marginal_sep_eq`, `voiExp_marginal_ge_rho_sep`).
  Register (repair round 1): D16's displayed inequality `VOI(s | q) ≥ VOI(s | q, π)` is *true* for
  every `q`, `π` when `a = s` is the perfect scan (`marginal_perfect_antitone`, by Blackwell) and
  reads `0 ≥ 0` here; what the counterexample refutes is S2's general-case sentence and P2's
  identification of `VOI(s | q, π)` with the unconditional `ρ`-residual `EVPI^ρ`.
* **(b′) D16's display itself fails for an `a` that reveals `ρ` alone — a finding (F-19, repair
  round 2).** `d16_display_fails_for_rho_only_a`: XOR bets on `(π, ρ)`, `q = ∅`, `π = ofMap fst`,
  `a = ofMap snd`: `VOI(a) = 0 = VOI(π)` but `VOI(a, π) = 1/2`, so `VOI(a | ∅) = 0 < 1/2 =
  VOI(a | ∅, π)` — information is complementary, not submodular; the display needs `a`
  decision-sufficient (the perfect scan), which is what the package proves.

Sources: power-wisdom-final.md S2 (l. 103, "General case"), S4(d) (l. 107), D16 (l. 73),
P2 (l. 159); power-wisdom-adversary.md S2.2 (l. 45), S4.4; corr-wf14-106(d), 2-060(b), 2-062;
[[corr-power-channel-audit-r2-fidelity]] N1 (probe `D16GeneralA.lean`, lifted).
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Corrigibility.CorrChannelVoi (expProd expProd_k trivialExp perfectExp
  blackwellLE_right_prod blackwellLE_left_prod experiment_ext)
open Cleanroom.Corrigibility.CorrCautionPower (harmOf harmOf_nonneg harmOf_nul)
open Finset hiding expect expect_const

noncomputable section

set_option linter.unusedSectionVars false

/-! ## (c) The takeover: J3 ⟺ `P(Z) h_T > g` -/

/-- The takeover option: `Ω = Bool` (`Z = true`), `A = Fin 2` (`∅ = 0`, `T = 1`), gain `g`
everywhere, harm `h_T` only under `Z` (net value `g − h_T` there).
Source: power-wisdom-final.md S4(d) (l. 107); P2 (l. 159, "Direct-gain variant")
Kind: D
Fidelity: exact -/
def takeoverVg (g hT : ℝ) : Bool → Fin 2 → ℝ := fun z => if z then ![0, g - hT] else ![0, g]

/-- **106(d)/2-062, net convention: `J3(T) ⟺ P(Z) h_T > g`** with `VOI(T) = 0`, for every
`g, h_T ≥ 0`, under the positive-part convention on the *net* value (`harmOf`/`gainOf` of
`V_ω(T) − V_ω(∅)`): if `h_T ≥ g` the harm under `Z` is `h_T − g` and the gain `g` off `Z`; if
`h_T < g` the harm is `0` and the gain is `g − h_T` under `Z`, `g` off it — both read
`P(Z) h_T > g`.
Source: power-wisdom-final.md S4(d) (l. 107, "`J3_t(T) ⟺ P_t(Z) h_T > g` under either
positive-part convention"); P2 (l. 159)
Kind: L
Fidelity: exact
Hyps: (a) `0 ≤ g`, `0 ≤ h_T` -/
theorem takeover_j3_iff {g hT z : ℝ} (hg : 0 ≤ g) (hhT : 0 ≤ hT) (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    J3 (boolPt z h0 h1) (takeoverVg g hT) trivialExp 1 0 univ univ_nonempty ↔ g < z * hT := by
  unfold J3
  rw [voiExp_trivial, add_zero]
  simp only [expect_bool, boolPt, takeoverVg, gainOf, harmOf, if_true, if_false,
    Matrix.cons_val_one, Matrix.cons_val_zero, Bool.false_eq_true, sub_zero, zero_sub]
  rcases le_or_gt g hT with hle | hlt
  · rw [max_eq_right (by linarith), max_eq_left hg, max_eq_left (by linarith),
      max_eq_right (by linarith)]
    constructor <;> intro H <;> nlinarith
  · rw [max_eq_left (by linarith), max_eq_left hg, max_eq_right (by linarith),
      max_eq_right (by linarith)]
    constructor <;> intro H <;> nlinarith

/-- The component convention's harm: `h_T` under `Z`, `0` otherwise.
Source: power-wisdom-final.md S4(d) (l. 107). Kind: D. Fidelity: exact -/
def takeoverHarmComp (hT : ℝ) : Bool → ℝ := fun z => if z then hT else 0

/-- The component convention's gain: `g` everywhere.
Source: power-wisdom-final.md S4(d) (l. 107). Kind: D. Fidelity: exact -/
def takeoverGainComp (g : ℝ) : Bool → ℝ := fun _ => g

/-- **106(d)/2-062, component convention**: booking harm and gain as separate components,
`E[g] + 0 < E[harm] ⟺ g < P(Z) h_T`.
Source: power-wisdom-final.md S4(d) (l. 107, "under either positive-part convention")
Kind: L
Fidelity: exact -/
theorem takeover_components_iff (g hT z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1) :
    expect (boolPt z h0 h1) (takeoverGainComp g) + 0 < expect (boolPt z h0 h1) (takeoverHarmComp hT)
      ↔ g < z * hT := by
  simp only [expect_bool, boolPt, takeoverGainComp, takeoverHarmComp, if_true, if_false,
    Bool.false_eq_true, add_zero]
  constructor <;> intro H <;> nlinarith

/-- **The equality cell**: at `g = 1/10`, `h_T = 1/2`, `P(Z) = 1/5` the takeover is exactly
indifferent — J3 fails and `g = P(Z) h_T`.
Source: power-wisdom-final.md S4(d) (l. 107, "`P_t(Z) > 1/5`"); P2 (l. 159, "equality at
`P_t(Z) = 1/5`")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem takeover_equality_cell :
    ¬ J3 (boolPt (1 / 5) (by norm_num) (by norm_num)) (takeoverVg (1 / 10) (1 / 2)) trivialExp 1 0
        univ univ_nonempty ∧
      (1 / 10 : ℝ) = 1 / 5 * (1 / 2) := by
  refine ⟨fun h => ?_, by norm_num⟩
  have := (takeover_j3_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1 h
  norm_num at this

/-! ## (b) The structural gap: counterexample to the unrestricted inequality -/

/-- `sup'` over a four-element set. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sup'_quad {A : Type} [DecidableEq A] {a b c d : A} (f : A → ℝ)
    (h : ({a, b, c, d} : Finset A).Nonempty) :
    ({a, b, c, d} : Finset A).sup' h f = max (f a) (max (f b) (max (f c) (f d))) := by
  apply le_antisymm
  · rw [sup'_le_iff]
    intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact le_max_left _ _
    · exact le_trans (le_max_left _ _) (le_max_right _ _)
    · exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
    · exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
  · exact max_le (le_sup' f (by simp)) (max_le (le_sup' f (by simp))
      (max_le (le_sup' f (by simp)) (le_sup' f (by simp))))

/-- The counterexample's hypotheses: `(π, ρ)`, both binary.
Source: power-wisdom-final.md D16 (l. 73, "`ω = (π, ρ)`"). Kind: D. Fidelity: exact -/
abbrev GapΩ : Type := Bool × Bool

/-- The counterexample's value table: options `0, 1` bet on `π`, options `2, 3` bet on `ρ`.
Source: none: this package's refutation of power-wisdom-final.md S2 "General case" (l. 103)
Kind: D
Fidelity: n/a (witness) -/
def gapV : GapΩ → Fin 4 → ℝ := fun ω =>
  ![if ω.1 then 0 else 1, if ω.1 then 1 else 0, if ω.2 then 0 else 1, if ω.2 then 1 else 0]

/-- The uniform mass on `Bool × Bool`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem uniform_mass_gap (ω : GapΩ) : (Distr.uniform : Distr GapΩ).mass ω = 1 / 4 := by
  norm_num [Distr.uniform, Fintype.card_prod, Fintype.card_bool]

/-- Expectation over `Bool × Bool`, expanded. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sum_gap (f : GapΩ → ℝ) :
    ∑ ω, f ω = f (true, true) + f (true, false) + f (false, true) + f (false, false) := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  ring

/-- Index `3` of a four-vector. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem vec4_three (a b c d : ℝ) : (![a, b, c, d] : Fin 4 → ℝ) 3 = d := rfl

/-- Index `2` of a four-vector. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem vec4_two (a b c d : ℝ) : (![a, b, c, d] : Fin 4 → ℝ) 2 = c := rfl

/-- **Finding: the unrestricted structural-gap inequality is false.** With `q` revealing `π`
exactly and `s` perfect, `VOI(s, q) = VOI(q) = EVPI = 1/2` so the marginal `VOI(s | q) = 0`,
while the value of learning `ρ` alone is `VOI(ρ) = 1/2`: `VOI(s | q) < VOI(ρ-component)`, at
`δ = 0`. The source's "`VOI_t(s | q) ≥ VOI_t(ρ) > 0` for every `δ`" needs separability of the
option set across `π` and `ρ`; here a `π`-option is worth `1` once `π` is known and `ρ` becomes
decision-irrelevant. **What is refuted**: S2's general-case sentence and P2's "`VOI(s | q) ≥
EVPI^ρ`" (the *unconditional* `ρ`-residual). **What stands**: D16's display
`VOI(s | q) ≥ VOI(s | q, π)` holds for every `q`, `π` (`marginal_perfect_antitone`, `Separable.lean`)
and reads `0 ≥ 0` here; under separability the inequality against `VOI(ρ)` is a theorem
(`voiExp_marginal_ge_rho_sep`).
Source: power-wisdom-final.md S2 (l. 103, "General case"), D16 (l. 73, "Structural gap");
power-wisdom-adversary.md S2.2 (l. 45)
Kind: N+
Fidelity: exact (refutation of the unrestricted claim; the separable form is proved in
`Separable.lean`)
Hyps: none -/
theorem gap_counterexample :
    evpi (Distr.uniform : Distr GapΩ) gapV univ univ_nonempty = 1 / 2 ∧
      voiExp (Distr.uniform : Distr GapΩ) gapV (ofMap Prod.fst) univ univ_nonempty = 1 / 2 ∧
      voiExp (Distr.uniform : Distr GapΩ) gapV (expProd (ofMap Prod.fst) perfectExp) univ
        univ_nonempty = 1 / 2 ∧
      voiExp (Distr.uniform : Distr GapΩ) gapV (ofMap Prod.snd) univ univ_nonempty = 1 / 2 ∧
      voiExp (Distr.uniform : Distr GapΩ) gapV (expProd (ofMap Prod.fst) perfectExp) univ
          univ_nonempty -
        voiExp (Distr.uniform : Distr GapΩ) gapV (ofMap Prod.fst) univ univ_nonempty <
        voiExp (Distr.uniform : Distr GapΩ) gapV (ofMap Prod.snd) univ univ_nonempty := by
  have hu4 : (univ : Finset (Fin 4)) = {0, 1, 2, 3} := by decide
  have he : evpi (Distr.uniform : Distr GapΩ) gapV univ univ_nonempty = 1 / 2 := by
    simp only [evpi, power, bestMix, attainable, mixValue, expect, sum_gap, uniform_mass_gap, hu4,
      sup'_quad, gapV, Matrix.cons_val_zero, Matrix.cons_val_one, vec4_two, vec4_three, if_true,
      if_false, Bool.false_eq_true]
    norm_num
  have hq : voiExp (Distr.uniform : Distr GapΩ) gapV (ofMap Prod.fst) univ univ_nonempty = 1 / 2 := by
    simp only [voiExp, bestMix, mixValue, expect, sum_gap, uniform_mass_gap, hu4, sup'_quad, gapV,
      ofMap, Matrix.cons_val_zero, Matrix.cons_val_one, vec4_two, vec4_three, if_true, if_false,
      Bool.false_eq_true, Fintype.sum_bool]
    norm_num
  have hρ : voiExp (Distr.uniform : Distr GapΩ) gapV (ofMap Prod.snd) univ univ_nonempty = 1 / 2 := by
    simp only [voiExp, bestMix, mixValue, expect, sum_gap, uniform_mass_gap, hu4, sup'_quad, gapV,
      ofMap, Matrix.cons_val_zero, Matrix.cons_val_one, vec4_two, vec4_three, if_true, if_false,
      Bool.false_eq_true, Fintype.sum_bool]
    norm_num
  have hprod : voiExp (Distr.uniform : Distr GapΩ) gapV (expProd (ofMap Prod.fst) perfectExp) univ
      univ_nonempty = 1 / 2 := by
    apply le_antisymm
    · rw [← he]; exact voiExp_le_evpi _ _ _ _
    · rw [← he, ← voiExp_perfect_eq_evpi]
      exact voiExp_mono_blackwell _ _ (blackwellLE_right_prod _ _) _
  refine ⟨he, hq, hprod, hρ, ?_⟩
  rw [hprod, hq, hρ]
  norm_num

/-! ## (b′) D16's display fails for a `ρ`-only `a` (F-19; repair round 2, fidelity N1) -/

/-- The product of two deterministic experiments is the deterministic experiment of the pair map.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem expProd_ofMap_ofMap {Ω S T : Type} [Fintype Ω] [Fintype S] [Fintype T] [DecidableEq S]
    [DecidableEq T] (f : Ω → S) (g : Ω → T) :
    expProd (ofMap f) (ofMap g) = ofMap (fun ω => (f ω, g ω)) := by
  apply experiment_ext
  funext ω p
  obtain ⟨s, t⟩ := p
  simp only [expProd_k, ofMap, Prod.mk.injEq]
  by_cases hf : f ω = s <;> by_cases hg : g ω = t <;> simp [hf, hg]

/-- XOR bets on `(π, ρ)`: option `0` pays `1` iff `π = ρ`, option `1` pays `1` iff `π ≠ ρ`.
Source: none: this package's refutation of power-wisdom-final.md D16's display (l. 73) for a
`ρ`-only `a`. Kind: D. Fidelity: n/a (witness) -/
def xorV : GapΩ → Fin 2 → ℝ := fun ω =>
  ![if ω.1 = ω.2 then 1 else 0, if ω.1 = ω.2 then 0 else 1]

/-- **F-19: D16's displayed inequality `VOI_t(a | q) ≥ VOI_t(a | q, π)` is false for an `a` that
reveals `ρ` alone.** Uniform `(π, ρ) ∈ Bool × Bool`, XOR bets, `q = ∅` (so `VOI(· | q) = VOI(·)`;
the source's `δ = 1`), `π = ofMap Prod.fst`, `a = ofMap Prod.snd`: `VOI(a) = 0` (knowing `ρ` alone
is worthless for an XOR bet), `VOI(π) = 0`, but `VOI(a, π) = EVPI = 1/2` (the pair reveals the
world; `expProd_ofMap_ofMap` and `voiExp_ofMap_eq_evpi_of_factors`), so
`VOI(a | ∅) = 0 < 1/2 = VOI(a, π) − VOI(π) = VOI(a | ∅, π)`. Information is complementary, not
submodular: the display's "for every channel error `δ`" fails at `δ = 1`, and it needs `a`
decision-sufficient — e.g. the perfect scan, which is the case the package proves
(`marginal_perfect_antitone`, `Separable.lean`).
Source: power-wisdom-final.md D16 (l. 73, "`VOI_t(a | q) ≥ VOI_t(a | q, π)` — the value of what
`a` reveals about `ρ` — for every channel error `δ`"); [[corr-power-channel-audit-r2-fidelity]]
N1 (probe `D16GeneralA.lean`, lifted with the literal `(a, π)` product in place of `perfectExp`)
Kind: N+
Fidelity: exact (refutation of the display for a `ρ`-revealing `a`; the perfect-scan case stands)
Hyps: none -/
theorem d16_display_fails_for_rho_only_a :
    voiExp (Distr.uniform : Distr GapΩ) xorV (ofMap Prod.snd) univ univ_nonempty = 0 ∧
      voiExp (Distr.uniform : Distr GapΩ) xorV (ofMap Prod.fst) univ univ_nonempty = 0 ∧
      voiExp (Distr.uniform : Distr GapΩ) xorV (expProd (ofMap Prod.snd) (ofMap Prod.fst)) univ
        univ_nonempty = 1 / 2 ∧
      voiExp (Distr.uniform : Distr GapΩ) xorV (ofMap Prod.snd) univ univ_nonempty <
        voiExp (Distr.uniform : Distr GapΩ) xorV (expProd (ofMap Prod.snd) (ofMap Prod.fst)) univ
            univ_nonempty -
          voiExp (Distr.uniform : Distr GapΩ) xorV (ofMap Prod.fst) univ univ_nonempty := by
  have hu2 : (univ : Finset (Fin 2)) = {0, 1} := by decide
  have hρ : voiExp (Distr.uniform : Distr GapΩ) xorV (ofMap Prod.snd) univ univ_nonempty = 0 := by
    simp only [voiExp, bestMix, mixValue, expect, sum_gap, uniform_mass_gap, hu2, sup'_pair', xorV,
      ofMap, Matrix.cons_val_zero, Matrix.cons_val_one, Fintype.sum_bool]
    norm_num
  have hπ : voiExp (Distr.uniform : Distr GapΩ) xorV (ofMap Prod.fst) univ univ_nonempty = 0 := by
    simp only [voiExp, bestMix, mixValue, expect, sum_gap, uniform_mass_gap, hu2, sup'_pair', xorV,
      ofMap, Matrix.cons_val_zero, Matrix.cons_val_one, Fintype.sum_bool]
    norm_num
  have hp : voiExp (Distr.uniform : Distr GapΩ) xorV (expProd (ofMap Prod.snd) (ofMap Prod.fst))
      univ univ_nonempty = 1 / 2 := by
    rw [expProd_ofMap_ofMap, voiExp_ofMap_eq_evpi_of_factors _ _ _ _ (fun a _ ω ω' h => by
      have h' : (ω.2, ω.1) = (ω'.2, ω'.1) := h
      obtain ⟨h2, h1⟩ := Prod.mk.inj h'
      rw [Prod.ext h1 h2])]
    simp only [evpi, power, bestMix, attainable, mixValue, expect, sum_gap, uniform_mass_gap, hu2,
      sup'_pair', xorV, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  refine ⟨hρ, hπ, hp, ?_⟩
  rw [hρ, hπ, hp]
  norm_num

end

end Cleanroom.Corrigibility.CorrPowerChannel
