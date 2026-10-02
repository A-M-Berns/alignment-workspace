import Cleanroom.Corrigibility.CorrPowerChannel.Evpi

/-!
# `corr-power-channel` — T3: the inert self-cap, the support veto, low regret ⇒ non-obstruction

* **(a)** `evpi_pair_null_eq_zero`: an option dominated by the null option under every hypothesis
  has per-option residual `EVPI{a, ∅} = 0` for every posterior — this is what killed the develop
  file's S11 (the per-option self-cap is inert against every pure experiment). Corollary
  `evpi_insert_dominated`: inserting an option dominated by a member of `B` leaves `EVPI(B)`
  unchanged (the D17 unlock increment of a pure experiment is `0`). Witness A2 (`e1n_pair`): E1's
  fully contested pair has per-option residuals `0, 0` and set residual `1/2`. (The E3 instances
  are in `Witnesses.lean`, built on the E3 family of `J3.lean`.)
* **(b)** `SupportVeto`: `a` is available only if its harm under every *live* hypothesis
  (`P ω > η`) is at most `τ`. Witness R2's takeover cell (`takeover_veto`): harm `h_T − g = 2/5`
  under `Z`, vetoed iff `P(Z) > η`. Witness R3 (`e1n_veto_passes_coverage_blocks`): E1's pair
  passes the veto at `τ = 0` while the coverage form of D18 blocks the unlock.
* **(c)** `nonObstructive_of_low_regret`: `∅ ∈ B` and `Reg*(B)(a) ≤ θ` give the `θ`-slack
  non-obstruction inequality `V*(∅) − θ ≤ V*(a)`; the converse is refuted
  (`nonObstructive_not_low_regret`): the agent picks `∅` with regret `1`.

Sources: power-wisdom-final.md S11′ (l. 135), S12 (l. 137), P8 (l. 181–183);
power-wisdom-adversary.md S11.1–S11.3 (l. 155–159), S12.2–S12.3 (l. 106–108); scripts A1, A2, R2, R3.
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Corrigibility.CorrCautionPower (harmOf harmOf_nonneg harmOf_nul)
open Finset hiding expect expect_const

noncomputable section

set_option linter.unusedSectionVars false

variable {A Ω : Type} [Fintype A] [DecidableEq A] [Fintype Ω]

/-! ## (a) The per-option self-cap is inert -/

/-- Inserting an element whose value is at most that of some member leaves `sup'` unchanged.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sup'_insert_of_le (f : A → ℝ) {B : Finset A} (hB : B.Nonempty) {a b : A} (hb : b ∈ B)
    (h : f a ≤ f b) : (insert a B).sup' (insert_nonempty a B) f = B.sup' hB f := by
  apply le_antisymm
  · rw [sup'_le_iff]
    intro x hx
    rw [mem_insert] at hx
    rcases hx with rfl | hx
    · exact le_trans h (le_sup' f hb)
    · exact le_sup' f hx
  · exact sup'_mono f (subset_insert a B) hB

/-- **S11.1 / A1: the per-option residual against the null is identically zero for every option
dominated by `∅` under every hypothesis** — hence for every pure experiment (`g ≡ 0`,
`harm ≥ 0`). Both terms of `EVPI{a, ∅}` equal `V̄(∅)`. This kills the develop file's S11
self-cap: no threshold `τ ≥ 0` ever excludes a scan. Kind L (two `max` evaluations), but it is a
refutation of a develop headline and is listed as such.
Source: power-wisdom-final.md S11′ (l. 135, "inert"); power-wisdom-adversary.md S11.1 (l. 155);
script A1
Kind: L
Fidelity: exact
Hyps: (a) the pointwise domination `V_ω(a) ≤ V_ω(∅)` is the content of "pure experiment" -/
theorem evpi_pair_null_eq_zero (P : Distr Ω) (V : Ω → A → ℝ) (a nul : A)
    (h : ∀ ω, V ω a ≤ V ω nul) : evpi P V {a, nul} (by simp) = 0 := by
  unfold evpi power bestMix attainable
  have hatt : (fun ω => ({a, nul} : Finset A).sup' (by simp) (V ω)) = fun ω => V ω nul := by
    funext ω
    rw [sup'_pair']
    exact max_eq_right (h ω)
  rw [hatt, sup'_pair']
  have hm : max (mixValue P V a) (mixValue P V nul) = mixValue P V nul :=
    max_eq_right (expect_mono P h)
  rw [hm]
  exact sub_self _

/-- **S11.2 / A1, set form: inserting an option dominated (under every hypothesis) by some member
of `B` leaves `EVPI(B)` unchanged** — the D17 unlock increment of a pure experiment is `0`, so the
set-level subjective cap never sees it either.
Source: power-wisdom-adversary.md S11.2 (l. 157); power-wisdom-final.md D17 (l. 79, "by A1 the
`Π^subj` unlock increment for a pure experiment is `0`")
Kind: L
Fidelity: exact
Hyps: (a) pointwise domination by a member of `B` -/
theorem evpi_insert_dominated (P : Distr Ω) (V : Ω → A → ℝ) {B : Finset A} (hB : B.Nonempty)
    {a b : A} (hb : b ∈ B) (h : ∀ ω, V ω a ≤ V ω b) :
    evpi P V (insert a B) (insert_nonempty a B) = evpi P V B hB := by
  unfold evpi power bestMix attainable
  have hatt : (fun ω => (insert a B).sup' (insert_nonempty a B) (V ω)) =
      fun ω => B.sup' hB (V ω) := by
    funext ω
    exact sup'_insert_of_le (V ω) hB hb (h ω)
  rw [hatt, sup'_insert_of_le (mixValue P V) hB hb (expect_mono P h)]

/-- **`voiExp` form of `evpi_insert_dominated`: inserting an option dominated (under every
hypothesis) by some member of `B` leaves the VOI of every experiment unchanged** — on every signal
the dominated option's signal gain is at most the dominating member's (the weights `P ω · k ω s`
are nonnegative), and the baseline is `evpi_insert_dominated`'s `bestMix` half. This is the lemma
that lets J3 be stated over D18's full continuation set `A_{t+1} ⊇ {∅, s}` rather than over the
plans alone (`e3_j3_iff_cont`, `Witnesses.lean`).
Source: power-wisdom-final.md D18 (l. 83, "`A_{t+1} ⊇ {∅, s}`"); power-wisdom-adversary.md S11.2
(l. 92)
Kind: L
Fidelity: exact
Hyps: (a) pointwise domination by a member of `B` -/
theorem voiExp_insert_dominated {S : Type} [Fintype S] (P : Distr Ω) (V : Ω → A → ℝ)
    (k : Experiment Ω S) {B : Finset A} (hB : B.Nonempty) {a b : A} (hb : b ∈ B)
    (h : ∀ ω, V ω a ≤ V ω b) :
    voiExp P V k (insert a B) (insert_nonempty a B) = voiExp P V k B hB := by
  unfold voiExp bestMix
  rw [sup'_insert_of_le (mixValue P V) hB hb (expect_mono P h)]
  congr 1
  refine sum_congr rfl fun s _ => ?_
  apply sup'_insert_of_le _ hB hb
  exact sum_le_sum fun ω _ =>
    mul_le_mul_of_nonneg_left (h ω) (mul_nonneg (P.nonneg ω) (experiment_nonneg k ω s))

/-- E1's pair with a null option: `Ω = Fin 2`, `A = Fin 3`, `b₁ = 0 ↦ (1, 0)`, `b₂ = 1 ↦ (0, 1)`,
`∅ = 2 ↦ (0, 0)`.
Source: power-wisdom-adversary.md S11.3 (l. 159); script A2
Kind: D
Fidelity: n/a (witness) -/
def e1nV : Fin 2 → Fin 3 → ℝ := ![![1, 0, 0], ![0, 1, 0]]

/-- **A2 (N+): per-option coverage against the null does not control set-level coverage.** E1's
fully contested pair has `EVPI{b₁, ∅} = EVPI{b₂, ∅} = 0` while `EVPI{b₁, b₂} = 1/2`: both
options enter the self-cap's effective set at any `τ ≥ 0`, and the residual on that set is `1/2`.
Source: power-wisdom-adversary.md S11.3 (l. 159); power-wisdom-final.md S11′ (l. 135); script A2
Kind: N+
Fidelity: exact
Hyps: none -/
theorem e1n_pair :
    evpi (Distr.uniform : Distr (Fin 2)) e1nV {0, 2} (by simp) = 0 ∧
      evpi (Distr.uniform : Distr (Fin 2)) e1nV {1, 2} (by simp) = 0 ∧
      evpi (Distr.uniform : Distr (Fin 2)) e1nV {0, 1} (by simp) = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [evpi, power, bestMix, attainable, mixValue, expect_fin2, uniform_mass_fin,
      sup'_pair', e1nV]
    norm_num

/-! ## (b) The support veto -/

/-- **The support veto** (S11′(b)): `a` is available only if its harm under every *live*
hypothesis — every `ω` with `P(ω) > η` — is at most `τ`. DRL's veto transposed from traps to harm;
`η` is the external knob.
Source: power-wisdom-final.md S11′ (l. 135, "(b) Per-option support veto")
Kind: D
Fidelity: exact -/
def SupportVeto (P : Distr Ω) (V : Ω → A → ℝ) (nul : A) (η τ : ℝ) (a : A) : Prop :=
  ∀ ω, η < P.mass ω → harmOf nul (V ω) a ≤ τ

/-- The two-point distribution on `Bool` with mass `z` on `true`.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def boolPt (z : ℝ) (h0 : 0 ≤ z) (h1 : z ≤ 1) : Distr Bool where
  mass := fun b => if b then z else 1 - z
  nonneg := fun b => by cases b <;> simp <;> linarith
  sum_eq_one := by simp [Fintype.sum_bool]

/-- Expectation on `Bool`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem expect_bool (μ : Distr Bool) (X : Bool → ℝ) :
    expect μ X = μ.mass true * X true + μ.mass false * X false := by
  simp [expect, Fintype.sum_bool]

/-- The takeover option `T` of S4(d)/R2: `Ω = Bool` (`Z = true`), `A = Fin 2` (`∅ = 0`, `T = 1`),
gain `g = 1/10` everywhere, harm `h_T = 1/2` only under `Z` (net value `1/10 − 1/2 = −2/5`).
Source: power-wisdom-final.md P8 (l. 183, R2 "takeover T"); S4(d) (l. 107)
Kind: D
Fidelity: n/a (witness) -/
def takeoverV : Bool → Fin 2 → ℝ := fun z => if z then ![0, 1 / 10 - 1 / 2] else ![0, 1 / 10]

/-- **R2's takeover cell (N+): the support veto blocks the takeover iff `Z` is live.** At
`η = 1/100`, `τ = 0`: with `P(Z) = 1/20 > η` the veto fails (`harm = 2/5` under `Z`); with
`P(Z) = 1/200 < η` it passes (only `¬Z` is live, where the takeover is harmless). `η` is the
external knob.
Source: power-wisdom-final.md P8 (l. 183, R2); script R2
Kind: N+
Fidelity: exact
Hyps: none -/
theorem takeover_veto :
    ¬ SupportVeto (boolPt (1 / 20) (by norm_num) (by norm_num)) takeoverV 0 (1 / 100) 0 1 ∧
      SupportVeto (boolPt (1 / 200) (by norm_num) (by norm_num)) takeoverV 0 (1 / 100) 0 1 := by
  constructor
  · intro h
    have := h true (by simp [boolPt]; norm_num)
    simp [takeoverV, harmOf] at this
    norm_num at this
  · intro ω hω
    cases ω
    · simp [takeoverV, harmOf]
    · simp [boolPt] at hω
      norm_num at hω

/-- **R3 (N+): E1's contested pair passes the support veto while the coverage form blocks its
unlock.** Every harm is `0` (both options pass at `τ = 0` for every `η`), and with
`N = {b₁, b₂}`, `B = {b₁, b₂, ∅}` the coverage form `EVPI(B) < min_{a∈N}(E[harm] − E[g])` reads
`1/2 < −1/2` and fails.
Source: power-wisdom-final.md P8 (l. 183, R3); S11′ (l. 135); script R3
Kind: N+
Fidelity: exact
Hyps: none -/
theorem e1n_veto_passes_coverage_blocks :
    (∀ η : ℝ, SupportVeto (Distr.uniform : Distr (Fin 2)) e1nV 2 η 0 0 ∧
      SupportVeto (Distr.uniform : Distr (Fin 2)) e1nV 2 η 0 1) ∧
      ¬ J3Coverage (Distr.uniform : Distr (Fin 2)) e1nV 2 {0, 1} (by simp) {0, 1, 2} (by simp) := by
  constructor
  · intro η
    constructor <;> intro ω _ <;> fin_cases ω <;> simp [e1nV, harmOf]
  · intro h
    unfold J3Coverage at h
    have hinf : ({0, 1} : Finset (Fin 3)).inf' (by simp)
        (fun a => expect (Distr.uniform : Distr (Fin 2)) (fun ω => harmOf 2 (e1nV ω) a) -
          expect (Distr.uniform : Distr (Fin 2)) (fun ω => gainOf 2 (e1nV ω) a)) ≤ -(1 / 2) := by
      refine le_trans (inf'_le _ (show (0 : Fin 3) ∈ ({0, 1} : Finset (Fin 3)) by simp)) ?_
      simp only [expect_fin2, uniform_mass_fin, harmOf, gainOf, e1nV]
      norm_num
    have he : evpi (Distr.uniform : Distr (Fin 2)) e1nV {0, 1, 2} (by simp) = 1 / 2 := by
      simp only [evpi, power, bestMix, attainable, mixValue, expect_fin2, uniform_mass_fin,
        sup'_triple, e1nV]
      norm_num
    rw [he] at h
    linarith

/-! ## (c) Low regret implies non-obstruction, not conversely -/

/-- **S12: low regret implies `θ`-slack non-obstruction.** If `∅ ∈ B` and `Reg*(B)(a) ≤ θ` then
`V*(∅) − θ ≤ V*(a)` — Turner's Definition 1 with slack `θ`, against the actual valuation `V*`.
Source: power-wisdom-final.md S12 (l. 137, "Low regret implies non-obstruction");
power-wisdom-adversary.md S12.2 (l. 171)
Kind: L
Fidelity: exact
Hyps: (a) `∅ ∈ B` -/
theorem nonObstructive_of_low_regret (Vstar : A → ℝ) {B : Finset A} (hB : B.Nonempty) {nul a : A}
    (hnul : nul ∈ B) {θ : ℝ} (h : regret Vstar B hB a ≤ θ) : Vstar nul - θ ≤ Vstar a := by
  unfold regret at h
  have := le_sup' Vstar hnul
  linarith

/-- At `θ = 0`, low regret gives exact non-obstruction with respect to `{V*}`.
Source: power-wisdom-final.md S12 (l. 137)
Kind: L
Fidelity: exact
Hyps: (a) `∅ ∈ B` -/
theorem nonObstructive_of_zero_regret (Vstar : A → ℝ) {B : Finset A} (hB : B.Nonempty) {nul a : A}
    (hnul : nul ∈ B) (h : regret Vstar B hB a ≤ 0) : NonObstructive {Vstar} nul a := by
  intro v hv
  rw [Set.mem_singleton_iff] at hv
  rw [hv]
  have := nonObstructive_of_low_regret Vstar hB hnul h
  linarith

/-- **The converse fails (N+): non-obstructive with regret `1`.** Two options `{∅ = 0, a = 1}`
with `V* = (0, 1)`: picking `∅` is non-obstructive (trivially) and has regret `1`.
Source: power-wisdom-final.md S12 (l. 137, "but not conversely"); power-wisdom-adversary.md
S12.2 (l. 171)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem nonObstructive_not_low_regret :
    NonObstructive {(![0, 1] : Fin 2 → ℝ)} 0 0 ∧
      regret (![0, 1] : Fin 2 → ℝ) univ univ_nonempty 0 = 1 := by
  constructor
  · intro v _
    exact le_rfl
  · have hu : (univ : Finset (Fin 2)) = {0, 1} := by decide
    norm_num [regret, hu, sup'_pair']

end

end Cleanroom.Corrigibility.CorrPowerChannel
