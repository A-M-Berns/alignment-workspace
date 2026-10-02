import Cleanroom.Decision.DpDevicesCatalog.Grid

set_option autoImplicit false

/-!
# `dp-devices-catalog` — T9, the remaining cells of the Told-You-So and miniature rows

Completes the three rows of `Grid.lean` whose masked / per-run / per-occurrence cells were
left out: `Told-You-So, C₀` `(T*, T*, T, T*, T*, T, T)`, `Told-You-So, C*` `(T*, F, T, F, F, F, F)`,
`Remark 4.3 miniature, q = 2/3` `(T, T, T, T, T, T, F)` — now exactly as ZO-19 prints them.
Tools: the SSC clauses collapse to prior calibration where `#_d` is constant on the tree
(`perOccClausesAt_of_priorCalibrated_of_count_const`, `k = 1` on `B_P` at `d₅`, `k = 2` on the
miniature), and on `B_P` the `d₁₀`-occurrence is the `O₁₀`-event.
-/

namespace Cleanroom.Decision.DpDevicesCatalog

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpLocalOpt

section general

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] [DecidableEq ι] {acts : ι → Type}
  [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  (s : ι → State Ω ℚ) (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (d : ι)

/-- Where `#_d ≡ k` on the tree, `𝔼[#_d 1_X] = k ν(X)` and `𝔼[#_d r 1_X] = k 𝔼[r 1_X]`.
Source: none: infrastructure
Kind: L -/
theorem countMass_countPay_of_count_const (k : ℕ) (hcount : ∀ ℓ, count d B ℓ = k) (X : Finset Ω) :
    countMass C B d X = (k : ℚ) * nu C B X ∧ countPay C B d X = (k : ℚ) * paySum C B X := by
  unfold countMass countPay nu mass paySum
  rw [Finset.mul_sum, Finset.mul_sum]
  constructor <;> refine Finset.sum_congr rfl fun ℓ _ => ?_ <;> rw [hcount ℓ] <;> ring

/-- **Per-occurrence SSC from prior calibration where `#_d` is a positive constant** (the
per-occurrence clauses collapse to Definition 11).
Source: [[decision-problems-v2]] §3.1 Definition 13 (with constant `#_d`); the mirror of
`perRunClausesAt_of_priorCalibrated_of_occ_univ`
Kind: L -/
theorem perOccClausesAt_of_priorCalibrated_of_count_const (k : ℕ) (hk : 0 < k)
    (hcount : ∀ ℓ, count d B ℓ = k) (hprior : PriorCalibrated C B (s d)) :
    PerOccClausesAt s C B d := by
  have hk' : (0 : ℚ) < k := by exact_mod_cast hk
  refine ⟨fun X => ?_, fun X hX hXm => ?_⟩
  · rw [(countMass_countPay_of_count_const C B d k hcount X).1,
      (countMass_countPay_of_count_const C B d k hcount Finset.univ).1, nu_univ, hprior.1 X]
    ring
  · rw [(countMass_countPay_of_count_const C B d k hcount X).1] at hXm ⊢
    rw [(countMass_countPay_of_count_const C B d k hcount X).2]
    have hν : 0 < nu C B X := by
      by_contra hc
      have := mul_nonpos_of_nonneg_of_nonpos hk'.le (not_lt.mp hc)
      linarith
    rw [← mul_assoc, mul_comm ((s d).V X) (k : ℚ), mul_assoc, hprior.2 X hν]

end general

/-! ## Told-You-So: the missing cells -/

/-- `#_{d₅} ≡ 1` on `B_P`. Source: none: infrastructure. Kind: L -/
theorem tys_count_five (ℓ : toldYouSo.Leaves) : count .five toldYouSo ℓ = 1 := by
  unfold toldYouSo at ℓ ⊢
  rcases ℓ with ⟨a, ℓ⟩
  cases a
  · rfl
  · rcases ℓ with ⟨b, _⟩; cases b <;> rfl

/-- `𝔼[#_{d₁₀} 1_X] = ν(X ∩ O₁₀)` on `B_P` (the `d₁₀`-node is met exactly on the `O₁₀`-runs).
Source: none: infrastructure. Kind: L -/
theorem tys_countMass_ten (C : Proc Five10 (fun _ => Five10) ℚ) (X : Finset TysW) :
    countMass C toldYouSo .ten X = nu C toldYouSo (X ∩ tysObs .ten) := by
  have e : countMass C toldYouSo .ten X =
      ∑ ℓ, if world toldYouSo ℓ ∈ X then leafLaw C toldYouSo ℓ * (count .ten toldYouSo ℓ : ℚ)
        else 0 := by
    unfold countMass worldEv; rw [Finset.sum_filter]
  rw [e, tys_sum, tys_nu]
  simp [toldYouSo, leafLaw_decision, world_decision, count_decision, tysObs]

/-- `μ_{C₀}(occ(d₁₀)) = 0` and `μ_{C*}(occ(d₁₀)) = 1`.
Source: none: infrastructure. Kind: L -/
theorem tys_mass_occ_ten :
    mass procFiveTen toldYouSo (occ .ten toldYouSo) = 0 ∧
    mass procTake10 toldYouSo (occ .ten toldYouSo) = 1 := by
  have e : ∀ C : Proc Five10 (fun _ => Five10) ℚ, mass C toldYouSo (occ .ten toldYouSo) =
      ∑ ℓ, if 0 < count .ten toldYouSo ℓ then leafLaw C toldYouSo ℓ else 0 := by
    intro C; unfold mass occ; rw [Finset.sum_filter]
  constructor <;> rw [e, tys_sum] <;>
    simp [toldYouSo, leafLaw_decision, count_decision, procFiveTen, procTake10]

/-- `C₀` is prior-calibrated with the stipulated `s₅` (`ν_{C₀} = δ_{(5,5)}`, payoff `5`).
Source: v2 Proposition 8 proof. Kind: L -/
theorem procFiveTen_priorCalibrated_five : PriorCalibrated procFiveTen toldYouSo (tysState .five) := by
  refine ⟨fun X => ?_, fun X _ => ?_⟩
  · rw [tys_nu]; simp [tysState, State.dirac_pr, procFiveTen]
  · rw [tys_nu, tys_paySum]; simp [tysState, procFiveTen, Five10.val]

/-- **Grid row `Told-You-So, C₀`: masked `T*`, per-run `T*`, per-occurrence `T*`** (at `d₁₀`
no self-model realizes `O₁₀`, `occ(d₁₀)` and `𝔼[#_{d₁₀}]` are null; at `d₅` everything is
substantive and the clauses are Definition 11's).
Source: `zoo.md` ZO-19 (row "Told-You-So, C0": `T* T* T T* T* T T`)
Kind: T -/
theorem grid_tys_fiveTen_rest :
    GridVerdict (queried toldYouSo) (MaskedOCAt tysState tysObs procFiveTen toldYouSo)
      (fun d => ∀ C', Admissible .LF procFiveTen d C' → nu C' toldYouSo (tysObs d) = 0) .Tstar ∧
    GridVerdict (queried toldYouSo) (PerRunSSCAt tysState procFiveTen toldYouSo)
      (fun d => mass procFiveTen toldYouSo (occ d toldYouSo) = 0) .Tstar ∧
    GridVerdict (queried toldYouSo) (PerOccSSCAt tysState procFiveTen toldYouSo)
      (fun d => countMass procFiveTen toldYouSo d Finset.univ = 0) .Tstar := by
  obtain ⟨m0, -⟩ := tys_mass_occ_ten
  have hc5 : countMass procFiveTen toldYouSo .five Finset.univ = 1 := by
    rw [(countMass_countPay_of_count_const procFiveTen toldYouSo .five 1 tys_count_five _).1,
      nu_univ]; simp
  have hc10 : countMass procFiveTen toldYouSo .ten Finset.univ = 0 := by
    rw [tys_countMass_ten, Finset.univ_inter, tys_nu_obs_values.2.1]
  refine ⟨⟨fun d hd => tys_fiveTen_maskedOC d hd, ⟨.ten, tys_queried .ten, ?_⟩,
      ⟨.five, tys_queried .five, ?_⟩⟩,
    ⟨fun d hd => ?_, ⟨.ten, tys_queried .ten, m0⟩, ⟨.five, tys_queried .five, ?_⟩⟩,
    ⟨fun d hd => ?_, ⟨.ten, tys_queried .ten, hc10⟩, ⟨.five, tys_queried .five, ?_⟩⟩⟩
  · rintro C' ⟨m, -, rfl⟩
    rw [tys_nu]; simp [tysObs, Proc.deviate, procFiveTen]
  · intro h
    have := h (procFiveTen.deviate .five FinDistr.uniform)
      ⟨FinDistr.uniform, fun a => FinDistr.uniform_w_pos a, rfl⟩
    rw [tys_nu_obs_five, Proc.deviate_same] at this
    exact (FinDistr.uniform_w_pos (K := ℚ) (α := Five10) .five).ne' this
  · cases d
    · intro _
      exact perRunClausesAt_of_priorCalibrated_of_occ_univ procFiveTen toldYouSo tysState
        tys_occ_five procFiveTen_priorCalibrated_five
    · intro hpos; rw [m0] at hpos; exact absurd hpos (lt_irrefl 0)
  · dsimp only; rw [tys_occ_five, mass_univ]; norm_num
  · cases d
    · intro _
      exact perOccClausesAt_of_priorCalibrated_of_count_const tysState procFiveTen toldYouSo
        .five 1 one_pos tys_count_five procFiveTen_priorCalibrated_five
    · intro hpos; rw [hc10] at hpos; exact absurd hpos (lt_irrefl 0)
  · dsimp only; rw [hc5]; norm_num

/-- **Grid row `Told-You-So, C*`: masked `F`, per-run `F`, per-occurrence `F`** (masked fails
at `d₁₀`, dp-calibration's F2; both SSC senses fail at `d₅`, where `s₅` is certain of `(5,5)`
but `C*` never reaches it).
Source: `zoo.md` ZO-19 (row "Told-You-So, C*": `T* F T F F F F`)
Kind: T -/
theorem grid_tys_take10_rest :
    GridVerdict (queried toldYouSo) (MaskedOCAt tysState tysObs procTake10 toldYouSo)
      (fun d => ∀ C', Admissible .LF procTake10 d C' → nu C' toldYouSo (tysObs d) = 0) .F ∧
    GridVerdict (queried toldYouSo) (PerRunSSCAt tysState procTake10 toldYouSo)
      (fun d => mass procTake10 toldYouSo (occ d toldYouSo) = 0) .F ∧
    GridVerdict (queried toldYouSo) (PerOccSSCAt tysState procTake10 toldYouSo)
      (fun d => countMass procTake10 toldYouSo d Finset.univ = 0) .F := by
  refine ⟨⟨.ten, tys_queried .ten, tys_take10_not_masked_LF .vacuity⟩,
    ⟨.five, tys_queried .five, fun h => ?_⟩, ⟨.five, tys_queried .five, fun h => ?_⟩⟩
  · have hpos : 0 < mass procTake10 toldYouSo (occ .five toldYouSo) := by
      rw [tys_occ_five, mass_univ]; norm_num
    have := (h hpos).1 {(.five, .five)}
    rw [tys_occ_five, Finset.inter_univ, mass_univ, mul_one] at this
    change (tysState .five).pr {(Five10.five, Five10.five)} = nu procTake10 toldYouSo _ at this
    simp only [tysState, State.dirac_pr] at this
    rw [tys_nu] at this
    simp [procTake10] at this
  · have hc5 : countMass procTake10 toldYouSo .five Finset.univ = 1 := by
      rw [(countMass_countPay_of_count_const procTake10 toldYouSo .five 1 tys_count_five _).1,
        nu_univ]; simp
    have hpos : 0 < countMass procTake10 toldYouSo .five Finset.univ := by rw [hc5]; norm_num
    have := (h hpos).1 {(.five, .five)}
    rw [hc5, (countMass_countPay_of_count_const procTake10 toldYouSo .five 1 tys_count_five _).1,
      tys_nu] at this
    simp only [tysState, State.dirac_pr] at this
    simp [procTake10] at this

/-! ## The miniature: the missing cells -/

/-- `occ(d)` on the miniature is every run. Source: none: infrastructure. Kind: L -/
theorem miniature_occ : occ () miniature = Finset.univ := by
  ext ℓ; simp [miniature_count]

/-- **Grid row `Remark 4.3 miniature, q = 2/3`: masked `T`, per-run `T`, per-occurrence `T`**
(self-model `C(d)` itself, full support; `occ = Leaves` and `#_d ≡ 2`, so both SSC senses are
prior calibration, which the strict state at `⊤` satisfies).
Source: `zoo.md` ZO-19 (row "Remark 4.3 miniature, q=2/3": `T T T T T T F`)
Kind: T -/
theorem grid_miniature_tie_rest :
    GridVerdict (queried miniature)
      (MaskedOCAt (fun _ => miniState (2/3) (by norm_num) (by norm_num)) miniObs
        (procQ (2/3) (by norm_num) (by norm_num)) miniature)
      (fun d => ∀ C', Admissible .LF (procQ (2/3) (by norm_num) (by norm_num)) d C' →
        nu C' miniature (miniObs d) = 0) .T ∧
    GridVerdict (queried miniature)
      (PerRunSSCAt (fun _ => miniState (2/3) (by norm_num) (by norm_num))
        (procQ (2/3) (by norm_num) (by norm_num)) miniature)
      (fun d => mass (procQ (2/3) (by norm_num) (by norm_num)) miniature (occ d miniature) = 0) .T ∧
    GridVerdict (queried miniature)
      (PerOccSSCAt (fun _ => miniState (2/3) (by norm_num) (by norm_num))
        (procQ (2/3) (by norm_num) (by norm_num)) miniature)
      (fun d => countMass (procQ (2/3) (by norm_num) (by norm_num)) miniature d Finset.univ = 0)
      .T := by
  have hself : (procQ (2/3) (by norm_num) (by norm_num)).deviate ()
      (procQ (2/3) (by norm_num) (by norm_num) ()) = procQ (2/3) (by norm_num) (by norm_num) := by
    funext d; cases d; simp
  have hprior : PriorCalibrated (procQ (2/3) (by norm_num) (by norm_num)) miniature
      (miniState (2/3) (by norm_num) (by norm_num)) :=
    priorCalibrated_calibratedState_univ _ _ _
  refine ⟨fun d _ => ⟨?_, ?_⟩, fun d _ => ⟨?_, ?_⟩, fun d _ => ⟨?_, ?_⟩⟩
  · cases d
    refine Or.inl ⟨_, ⟨procQ (2/3) (by norm_num) (by norm_num) (), ?_, rfl⟩, ?_, ?_⟩
    · intro a; cases a <;> simp [procQ] <;> norm_num
    · rw [hself, miniObs, nu_univ]; norm_num
    · rw [hself]
      exact strictClausesAt_calibratedState miniObs _ miniature _ () _ rfl
  · cases d
    intro h
    have := h _ ⟨procQ (2/3) (by norm_num) (by norm_num) (),
      fun a => by cases a <;> simp [procQ] <;> norm_num, rfl⟩
    rw [hself, miniObs, nu_univ] at this
    norm_num at this
  · cases d
    intro _
    exact perRunClausesAt_of_priorCalibrated_of_occ_univ _ miniature _ miniature_occ hprior
  · cases d; dsimp only; rw [miniature_occ, mass_univ]; norm_num
  · cases d
    intro _
    exact perOccClausesAt_of_priorCalibrated_of_count_const _ _ miniature () 2 (by norm_num)
      miniature_count hprior
  · cases d; dsimp only
    rw [(countMass_countPay_of_count_const _ miniature () 2 miniature_count _).1, nu_univ]
    norm_num

/-! ## An `N+` for the vacuity criterion with non-empty action events

Audit round 1 (adversarial §3.6) noted that the only in-package instance of `d2VacuousAt_iff`
was the empty-event rendering of the AMD, which is tree-free. Here is a point with non-empty
action events at which the escape clause fires under every procedure and tremble, in a tree
with a second point at which it does not: Told-You-So with `O₁₀` replaced by the non-leaf
world `(5,10)`. -/

/-- Told-You-So's observations with `O₁₀` replaced by `{(5,10)}` ("announced five, took ten"),
a world no leaf carries; `O₅` unchanged.
Source: none: infrastructure (the witness audit round 1 asked for; `zoo.md` ZO-19 (i) names
rows of this shape — CX1 at `d'`, Claim-B at `d`, AMD+e at `d`)
Kind: D -/
def tysObsAlt : Five10 → Finset TysW
  | .five => tysObs .five
  | .ten => {(.five, .ten)}

/-- Every Told-You-So action event is non-empty. Source: none: infrastructure. Kind: L -/
theorem tysActEv_nonempty (d a : Five10) : (tysActEv d a).Nonempty :=
  ⟨(.five, a), by simp [tysActEv]⟩

/-- **The escape clause fires at `d₁₀` for every procedure and tremble**, with non-empty
action events: `a ∧ O'₁₀ ⊆ {(5,10)}` carries no leaf-world, so `ν_{C^ε}(a ∧ O'₁₀) = 0` for
every `a` (`d2VacuousAt_iff`'s criterion, read off the tree).
Source: mandate extension; `zoo.md` ZO-19 (i)
Kind: N+ -/
theorem tysObsAlt_d2Vacuous_ten (C : Proc Five10 (fun _ => Five10) ℚ) (ε : ℚ) (h0 : 0 < ε)
    (h1 : ε ≤ 1) : D2VacuousAt tysObsAlt tysActEv toldYouSo C ε h0 h1 .ten := by
  intro b
  rw [tys_nu]; simp [tysActEv, tysObsAlt]

/-- **…and does not fire at `d₅`**: `five ∧ O₅` carries the leaf `(5,5)` with mass
`C^ε(d₅)(five) > 0`, so the same tree has a substantive point next to the vacuous one.
Source: mandate extension
Kind: N+ -/
theorem tysObsAlt_not_d2Vacuous_five (C : Proc Five10 (fun _ => Five10) ℚ) (ε : ℚ)
    (h0 : 0 < ε) (h1 : ε ≤ 1) : ¬ D2VacuousAt tysObsAlt tysActEv toldYouSo C ε h0 h1 .five := by
  intro h
  have := h .five
  change nu _ _ (tysActEv .five .five ∩ tysObs .five) = 0 at this
  rw [(tys_tremble_nu_five C ε h0.le h1).1] at this
  exact (tys_tremble_w_pos C ε h0 h1 .five .five).ne' this

/-- The criterion's tree-level side at `d₁₀`: no chance-positive leaf has its world in any
`a ∧ O'₁₀` (the `d2VacuousAt_iff` reading of the above).
Source: mandate extension
Kind: L -/
theorem tysObsAlt_unrealised_ten :
    ∀ a, ∀ ℓ, Positive toldYouSo ℓ → world toldYouSo ℓ ∉ tysActEv .ten a ∩ tysObsAlt .ten :=
  (d2VacuousAt_iff tysObsAlt tysActEv toldYouSo procFiveTen 1 one_pos le_rfl .ten).1
    (tysObsAlt_d2Vacuous_ten procFiveTen 1 one_pos le_rfl)

end Cleanroom.Decision.DpDevicesCatalog
