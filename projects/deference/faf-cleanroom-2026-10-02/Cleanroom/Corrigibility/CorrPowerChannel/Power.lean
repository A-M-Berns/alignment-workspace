import Cleanroom.Corrigibility.CorrCautionPower.Setting
import Cleanroom.Corrigibility.CorrReflectFrames.Good
import Cleanroom.Found.LitDdbFrames.Blackwell

/-!
# `corr-power-channel` — T1: definitions of record (POWER, EVPI, reach, regret, VOI, J3)

The carrier is `corr-caution-power`'s: a finite option type `A` with a null option `nul`, a finite
hypothesis type `Ω`, a value table `V : Ω → A → ℝ` and a FAF `Distr Ω` posterior `P`. Option sets
are `Finset A` with a nonemptiness proof wherever a maximum is taken (`Finset.sup'`), so nothing
here takes a junk `max` over an empty set.

* `mixValue P V a` — `V̄_t(a) = E_{ω∼P}[V_ω(a)]` (power-wisdom-final D4).
* `bestMix P V B hB` — `max_{a∈B} V̄_t(a)`.
* `attainable V B hB ω` — `AV_B(ω) = max_{a∈B} V_ω(a)` (D6).
* `power D V B hB` — `POWER_D(B) = E_{ω∼D}[max_{a∈B} V_ω(a)]` (D7; Turner et al. Def. 5.1,
  one-shot). The reference distribution `D` is a separate argument from the posterior `P`.
* `evpi P V B hB` — `EVPI_t(B) = POWER_{P}(B) − max_{a∈B} V̄_t(a)` (D12); `evpi_nonneg`
  (Jensen), `evpi_eq_expect_regret` (S1's second display), the bridge to
  `corr-reflect-frames`' `voi` (`evpi_univ_eq_voi`).
* `gainOf`, `reach`, `NonObstructive`, `regret`, `realizedHarm`, the caps `CapSubj`/`CapObj`/
  `CapHarm` (D9, D7′, D10, D13, D17). Harm is `corr-caution-power`'s `harmOf` (not redefined).
* `voiExp P V k B hB` — `VOI_t` of an experiment `k` (D16) in product form, `j3` (D18) and its
  coverage form `J3Coverage` with the implication `j3_of_coverage`.

Sources: `research/corrigibility/workflow-2026-09-14/dynamics/power-wisdom-final.md` (cited as
power-wisdom-final.md with the definition labels D1–D20, l. 25–93), `power-wisdom-adversary.md`
D.1 (realizability is a hypothesis, never a field), 2-068(c) (non-obstruction over a set of payoff
functions).
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Corrigibility.CorrCautionPower (harmOf harmOf_nonneg harmOf_nul CautionState)
open Finset hiding expect expect_const

noncomputable section

set_option linter.unusedSectionVars false

variable {A Ω : Type} [Fintype A] [DecidableEq A] [Fintype Ω]

/-! ## Finite Jensen for `sup'` over an option set -/

/-- **Finite Jensen for `max` over a `Finset`**: for nonnegative weights `p` on a finite index and
a nonempty option set `B`, `max_{a∈B} ∑ᵢ pᵢ v i a ≤ ∑ᵢ pᵢ max_{a∈B} v i a`. The `Finset` form of
`corr-reflect-frames`' `sup'_sum_le_sum_sup'` (which is over `univ`).
Source: none: infrastructure (power-wisdom-final.md P1 "VOI bound")
Kind: L
Fidelity: n/a -/
theorem sup'_sum_le_sum_sup'_finset {ι : Type} [Fintype ι] {B : Finset A} (hB : B.Nonempty)
    {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) (v : ι → A → ℝ) :
    B.sup' hB (fun a => ∑ i, p i * v i a) ≤ ∑ i, p i * B.sup' hB (fun a => v i a) := by
  rw [sup'_le_iff]
  intro a ha
  apply sum_le_sum
  intro i _
  exact mul_le_mul_of_nonneg_left (le_sup' (fun a => v i a) ha) (hp i)

/-! ## D4, D6, D7, D12 — mixture value, attainable value, POWER, EVPI -/

/-- **Mixture value** `V̄_t(a) = E_{ω∼P}[V_ω(a)]` of an option under the posterior.
Source: power-wisdom-final.md D4 (l. 31)
Kind: D
Fidelity: exact -/
def mixValue (P : Distr Ω) (V : Ω → A → ℝ) (a : A) : ℝ := expect P (fun ω => V ω a)

/-- **Best mixture value** `max_{a∈B} V̄_t(a)` over a nonempty option set.
Source: power-wisdom-final.md D4, D12 (l. 31, 61)
Kind: D
Fidelity: exact -/
def bestMix (P : Distr Ω) (V : Ω → A → ℝ) (B : Finset A) (hB : B.Nonempty) : ℝ :=
  B.sup' hB (mixValue P V)

/-- **Attainable value** `AV_B(ω) = max_{a∈B} V_ω(a)` — the one-shot attainable-utility profile.
Source: power-wisdom-final.md D6 (l. 39)
Kind: D
Fidelity: exact -/
def attainable (V : Ω → A → ℝ) (B : Finset A) (hB : B.Nonempty) (ω : Ω) : ℝ := B.sup' hB (V ω)

/-- **POWER, one-shot form**: `POWER_D(B) = E_{ω∼D}[max_{a∈B} V_ω(a)]` for a reference
distribution `D` (Turner et al. 2021 Definition 5.1, average optimal value, with no discount and
no `R(s)` subtraction). `D` is a separate argument from the posterior so that S1's identity reads
`evpi P V B = power P V B − bestMix` with `D := P` visible.
Source: power-wisdom-final.md D7 (l. 41); Turner et al. 2021 Def. 5.1
Kind: D
Fidelity: variant: one-shot (option set, no MDP, no discount) -/
def power (D : Distr Ω) (V : Ω → A → ℝ) (B : Finset A) (hB : B.Nonempty) : ℝ :=
  expect D (attainable V B hB)

/-- **Residual decision-relevant uncertainty** `EVPI_t(B) = POWER_{P_t}(B) − max_{a∈B} V̄_t(a)`,
the expected value of perfect information about `ω` for the choice in `B`. Nonnegative by
`evpi_nonneg` (a theorem, not part of the definition).
Source: power-wisdom-final.md D12 (l. 61); S1 (l. 99)
Kind: D
Fidelity: exact -/
def evpi (P : Distr Ω) (V : Ω → A → ℝ) (B : Finset A) (hB : B.Nonempty) : ℝ :=
  power P V B hB - bestMix P V B hB

/-- The mixture value of a member of `B` is at most `POWER_P(B)` (pointwise `V_ω(a) ≤ AV_B(ω)`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mixValue_le_power (P : Distr Ω) (V : Ω → A → ℝ) {B : Finset A} (hB : B.Nonempty) {a : A}
    (ha : a ∈ B) : mixValue P V a ≤ power P V B hB :=
  expect_mono P fun ω => le_sup' (V ω) ha

/-- `max_{a∈B} V̄(a) ≤ POWER_P(B)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem bestMix_le_power (P : Distr Ω) (V : Ω → A → ℝ) {B : Finset A} (hB : B.Nonempty) :
    bestMix P V B hB ≤ power P V B hB := by
  unfold bestMix
  rw [sup'_le_iff]
  intro a ha
  exact mixValue_le_power P V hB ha

/-- **`EVPI ≥ 0`** (finite Jensen for `max`): the best mixture act is feasible under every
hypothesis, so the expected attainable value is at least the best mixture value.
Source: power-wisdom-final.md D12 (l. 61, "`≥ 0`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem evpi_nonneg (P : Distr Ω) (V : Ω → A → ℝ) {B : Finset A} (hB : B.Nonempty) :
    0 ≤ evpi P V B hB :=
  sub_nonneg.2 (bestMix_le_power P V hB)

/-- `AV` is monotone in the option set (pointwise in `ω`).
Source: power-wisdom-final.md D7 (l. 41, "monotone in the option set")
Kind: L
Fidelity: n/a -/
theorem attainable_mono (V : Ω → A → ℝ) {B B' : Finset A} (hB : B.Nonempty) (hB' : B'.Nonempty)
    (h : B ⊆ B') (ω : Ω) : attainable V B hB ω ≤ attainable V B' hB' ω :=
  sup'_mono (V ω) h hB

/-- **S1(i): POWER is monotone in the option set for every reference distribution.**
Source: power-wisdom-final.md S1(i) (l. 99); D7 (l. 41)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem power_mono (D : Distr Ω) (V : Ω → A → ℝ) {B B' : Finset A} (hB : B.Nonempty)
    (hB' : B'.Nonempty) (h : B ⊆ B') : power D V B hB ≤ power D V B' hB' :=
  expect_mono D (attainable_mono V hB hB' h)

/-- Some member of `B` attains the best mixture value (the Bayes act `a*_t(B)` exists).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem exists_bestMix_attained (P : Distr Ω) (V : Ω → A → ℝ) {B : Finset A} (hB : B.Nonempty) :
    ∃ a ∈ B, mixValue P V a = bestMix P V B hB := by
  obtain ⟨a, ha, h⟩ := exists_mem_eq_sup' hB (mixValue P V)
  exact ⟨a, ha, h.symm⟩

/-- **S1, second display: EVPI is the posterior-expected regret of the Bayes act.** For any
`a* ∈ B` attaining the best mixture value, `EVPI_t(B) = E_{ω∼P}[max_{a∈B} V_ω(a) − V_ω(a*)]`.
Source: power-wisdom-final.md S1 (l. 99, second equality); D13 (l. 65, "P1")
Kind: L
Fidelity: exact
Hyps: (a) `a*` attains `bestMix` (named, satisfiable by `exists_bestMix_attained`) -/
theorem evpi_eq_expect_regret (P : Distr Ω) (V : Ω → A → ℝ) {B : Finset A} (hB : B.Nonempty)
    {a : A} (hopt : mixValue P V a = bestMix P V B hB) :
    evpi P V B hB = expect P (fun ω => attainable V B hB ω - V ω a) := by
  rw [expect_sub, evpi, ← hopt]
  rfl

/-- **Bridge to `corr-reflect-frames`**: on the full option set, `evpi` *is* `voi` with the
option type as the menu index (`voi hK π V = ∑ θ, π θ · max_k V k θ − max_k ∑ θ, π θ · V k θ`).
Source: power-wisdom-final.md D12 (l. 61); [[corr-power-channel-mandate]] §Carrier
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem evpi_univ_eq_voi [Nonempty A] (P : Distr Ω) (V : Ω → A → ℝ) :
    evpi P V univ univ_nonempty =
      CorrReflectFrames.voi univ_nonempty P.mass (fun a ω => V ω a) := by
  unfold evpi power bestMix attainable mixValue expect CorrReflectFrames.voi
  rfl

/-- **The caution state's proxy is the mixture value**: `corr-caution-power`'s `S.proxy a` is
`mixValue S.P S.V a`.
Source: [[corr-power-channel-mandate]] §Carrier; caution-final.md D2
Kind: L
Fidelity: exact -/
theorem mixValue_eq_proxy (S : CautionState A Ω) (a : A) : mixValue S.P S.V a = S.proxy a := rfl

/-! ## D9, D7′, D10, D13, D17 — gain, reach, non-obstruction, regret, the caps -/

/-- **Direct gain** `g_ω(a) = (V_ω(a) − V_ω(∅))⁺` of an option over the null option. Harm is
`corr-caution-power`'s `harmOf nul v a = (v ∅ − v a)⁺` (not redefined).
Source: power-wisdom-final.md D9 (l. 51)
Kind: D
Fidelity: exact -/
def gainOf (nul : A) (v : A → ℝ) (a : A) : ℝ := max (v a - v nul) 0

/-- `g_ω(∅) = 0`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem gainOf_nul (nul : A) (v : A → ℝ) : gainOf nul v nul = 0 := by simp [gainOf]

/-- `0 ≤ g_ω(a)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem gainOf_nonneg (nul : A) (v : A → ℝ) (a : A) : 0 ≤ gainOf nul v a := le_max_right _ _

/-- An option dominated by the null option under `v` has zero gain.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem gainOf_eq_zero_of_le (nul : A) (v : A → ℝ) {a : A} (h : v a ≤ v nul) :
    gainOf nul v a = 0 := by
  unfold gainOf
  exact max_eq_right (by linarith)

/-- **Reach** `Reach = max_{a∈B} max_{ω∈S} harm_ω(a)`: the worst harm any available option can
do to any plausible human goal in the oversight-side set `S` (a `Finset Ω` of hypotheses read as
goals).
Source: power-wisdom-final.md D7′ (l. 45)
Kind: D
Fidelity: exact -/
def reach (V : Ω → A → ℝ) (nul : A) (S : Finset Ω) (hS : S.Nonempty) (B : Finset A)
    (hB : B.Nonempty) : ℝ :=
  B.sup' hB (fun a => S.sup' hS (fun ω => harmOf nul (V ω) a))

/-- **Reach is monotone in the option set** (and in the goal set).
Source: power-wisdom-final.md D7′ (l. 45, "Monotone in `A_t`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem reach_mono (V : Ω → A → ℝ) (nul : A) {S S' : Finset Ω} (hS : S.Nonempty)
    (hS' : S'.Nonempty) (hSS : S ⊆ S') {B B' : Finset A} (hB : B.Nonempty) (hB' : B'.Nonempty)
    (hBB : B ⊆ B') : reach V nul S hS B hB ≤ reach V nul S' hS' B' hB' := by
  unfold reach
  rw [sup'_le_iff]
  intro a ha
  refine le_trans ?_ (le_sup' (fun a => S'.sup' hS' (fun ω => harmOf nul (V ω) a)) (hBB ha))
  exact sup'_mono (fun ω => harmOf nul (V ω) a) hSS hS

/-- `0 ≤ Reach`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem reach_nonneg (V : Ω → A → ℝ) (nul : A) {S : Finset Ω} (hS : S.Nonempty) {B : Finset A}
    (hB : B.Nonempty) : 0 ≤ reach V nul S hS B hB := by
  unfold reach
  obtain ⟨a, ha⟩ := hB
  obtain ⟨ω, hω⟩ := hS
  exact le_trans (harmOf_nonneg nul (V ω) a)
    (le_trans (le_sup' (fun ω => harmOf nul (V ω) a) hω)
      (le_sup' (fun a => S.sup' ⟨ω, hω⟩ (fun ω => harmOf nul (V ω) a)) ha))

/-- **Non-obstruction (Turner 2020, Definition 1)** of an option `a` with respect to a *set* `Vs`
of payoff functions the humans might have: `v ∅ ≤ v a` for every `v ∈ Vs`. Over payoff
functions, not over `Ω` — the set need not sit inside the agent's hypothesis space (2-068(c)).
Source: power-wisdom-final.md D10 (l. 53); power-wisdom-adversary.md S12.3; Turner 2020 Def. 1
Kind: D
Fidelity: exact (the `ε`-slack form is `nonObstructive_of_low_regret`'s conclusion) -/
def NonObstructive (Vs : Set (A → ℝ)) (nul a : A) : Prop := ∀ v ∈ Vs, v nul ≤ v a

/-- **Realized regret** `Reg*(B) = max_{a∈B} V*(a) − V*(a)` of an option against the humans'
actual valuation `Vstar : A → ℝ` — **not** indexed by an `ω* ∈ Ω`: realizability `Vstar = V ω*`
is a hypothesis where it is used, never a field (D.1).
Source: power-wisdom-final.md D13 (l. 65); power-wisdom-adversary.md D.1 (l. 15)
Kind: D
Fidelity: exact (against `V*`, realizability-free) -/
def regret (Vstar : A → ℝ) (B : Finset A) (hB : B.Nonempty) (a : A) : ℝ := B.sup' hB Vstar - Vstar a

/-- `0 ≤ Reg*(B)(a)` for `a ∈ B`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem regret_nonneg (Vstar : A → ℝ) {B : Finset A} (hB : B.Nonempty) {a : A} (ha : a ∈ B) :
    0 ≤ regret Vstar B hB a :=
  sub_nonneg.2 (le_sup' Vstar ha)

/-- **Realized harm** `Harm* = (V*(∅) − V*(a))⁺` against the humans' actual valuation.
Source: power-wisdom-final.md D9, D13 (l. 51, 65)
Kind: D
Fidelity: exact -/
def realizedHarm (Vstar : A → ℝ) (nul a : A) : ℝ := harmOf nul Vstar a

/-- **The subjective cap** `Π^subj_t(θ): EVPI_t(A_t) ≤ θ`.
Source: power-wisdom-final.md D17 (l. 79)
Kind: D
Fidelity: exact -/
def CapSubj (P : Distr Ω) (V : Ω → A → ℝ) (B : Finset A) (hB : B.Nonempty) (θ : ℝ) : Prop :=
  evpi P V B hB ≤ θ

/-- **The objective cap, per step** `Π^obj_t(θ): Reg*_t(A_t) ≤ θ` for the chosen option `a`.
Source: power-wisdom-final.md D17 (l. 79)
Kind: D
Fidelity: exact (per step; the trajectory form is `CapObjTraj` in `Evpi.lean`) -/
def CapObj (Vstar : A → ℝ) (B : Finset A) (hB : B.Nonempty) (a : A) (θ : ℝ) : Prop :=
  regret Vstar B hB a ≤ θ

/-- **The harm cap** `Π^harm_t`: the chosen option is non-obstructive with respect to the
oversight-side set of payoff functions.
Source: power-wisdom-final.md D17 (l. 79); S12 (l. 137)
Kind: D
Fidelity: exact -/
def CapHarm (Vs : Set (A → ℝ)) (nul a : A) : Prop := NonObstructive Vs nul a

/-- **The two-sided form** (D17, `[conjectured]` in the source; O8): `Reach · κ ≤ θ` — the worst
harm available times the agent's miscalibration `κ` about its own coverage. A definition of
record only; no theorem about it is claimed (O8 hands it to `joint`).
Source: power-wisdom-final.md D17 (l. 79, "Two-sided form"), O8 (l. 266)
Kind: D
Fidelity: exact (as a predicate on two reals; `κ` is not computed here) -/
def CapTwoSided (reach κ θ : ℝ) : Prop := reach * κ ≤ θ

/-! ## D16, D18 — the value of information of an experiment, J3 and its coverage form -/

/-- **VOI of an experiment** `k : Experiment Ω S` for the choice in `B`, in product form (no
division by signal mass): `∑_s max_{b∈B} ∑_ω P ω · k ω s · V_ω(b) − max_{b∈B} V̄(b)`.
Source: power-wisdom-final.md D16 (l. 73)
Kind: D
Fidelity: exact (product form of `E_{o}[max_b E_{P^o}[V_ω(b)]] − max_b E_P[V_ω(b)]`) -/
def voiExp {S : Type} [Fintype S] (P : Distr Ω) (V : Ω → A → ℝ) (k : Experiment Ω S)
    (B : Finset A) (hB : B.Nonempty) : ℝ :=
  (∑ s, B.sup' hB (fun b => ∑ ω, P.mass ω * k.k ω s * V ω b)) - bestMix P V B hB

/-- **J3, formal** (D18): the linear-expectation agent declines `a` —
`E_P[g_ω(a)] + VOI(a) < E_P[harm_ω(a)]`, where the observation `a` yields is the experiment `k`
and the continuation set is `B`. The direct-gain term is kept so that a pure experiment
(`g ≡ 0`) and a takeover (`g` the point) are one inequality. **S3 residue (2-061):** there is no
separate stakes knob in this inequality; harm magnitude enters only through `harmOf`.
Source: power-wisdom-final.md D18 (l. 83); 2-061 (S3 ill-posed: no stakes parameter in the
linear rule)
Kind: D
Fidelity: exact -/
def J3 {S : Type} [Fintype S] (P : Distr Ω) (V : Ω → A → ℝ) (k : Experiment Ω S) (a nul : A)
    (B : Finset A) (hB : B.Nonempty) : Prop :=
  expect P (fun ω => gainOf nul (V ω) a) + voiExp P V k B hB <
    expect P (fun ω => harmOf nul (V ω) a)

/-- **J3, coverage form** (D18): `EVPI_t(A_{t+1}) < min_{a∈N} (E_P[harm_ω(a)] − E_P[g_ω(a)])` —
the residual on the enlarged set against the recognized net harm of the cheapest new option.
Source: power-wisdom-final.md D18 (l. 83, "Coverage form")
Kind: D
Fidelity: exact -/
def J3Coverage (P : Distr Ω) (V : Ω → A → ℝ) (nul : A) (N : Finset A) (hN : N.Nonempty)
    (B : Finset A) (hB : B.Nonempty) : Prop :=
  evpi P V B hB <
    N.inf' hN (fun a => expect P (fun ω => harmOf nul (V ω) a) - expect P (fun ω => gainOf nul (V ω) a))

end

end Cleanroom.Corrigibility.CorrPowerChannel
