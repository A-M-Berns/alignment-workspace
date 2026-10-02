import Cleanroom.Udt.UdtHarmonyBargain.Translation
import Cleanroom.Found.DpCoreTree.Catalogue
import Cleanroom.Found.DpCoreTree.Witnesses
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# `udt-harmony-bargain` — tree witnesses: TN-V2 (T8(d)) and the miniature (T11)

**T8(d), updating breaks harmony off the fair class, without disagreement.** On TN-V2
(`tnV2 (3/4) _ _ 4 1`, two queried points `d_F`, `d_E`, actions `Box`), the tree gives
`V(l,l) = 3, V(l,b) = 7/4, V(b,l) = 5/4, V(b,b) = 2` (so the optimum is `(large, large)`) and the
*updated* point-specific utilities `U_F(O) = 𝔼_{μ_{B,O}}[r ∣ λ ⊨ O_F] = (4, 4, 5, 5)`,
`U_E(O) = 𝔼_{μ_{B,O}}[r ∣ λ ⊨ O_E] = (0, 1, 0, 1)` (conditioning masses `q, 1 − q ∈ {1/4, 3/4}`
positive). In the updated bargaining game `σ* = ((both, {bb}), (both, {bb}))` is harmonious for
every singleton-faithful `sel` (each `s*ᵢ` yields its player's maximum against every opponent
proposal: `thpe_of_dominant`), its outcome `(both, both)` is Pareto-optimal for the updated
utilities, yet `V(both, both) = 2 < 3`, and in the homogeneous game `(both, both)` is not a
harmonious outcome (Proposition S(a)). Both updated points *agree* on `(both, both)`: the
mechanism is event-conditioning (HA-12′(d)), not Remark 13.2's "disagreement" (finding F6).

**T11, Remark 4.3's miniature cannot be embedded.** The miniature has one queried point and two
pure outcomes, both worth `0`; every mixed profile of its action game is worth `0`; every profile
of its homogeneous bargaining game is harmonious (constant payoffs); yet the independent-redraw
value at `q = 1/2` is `3/4`.

The player set of the tree games here is `TnPt` (resp. `Unit`), which is `queried B` on the nose;
the homogeneous utilities are `V_B` of the pure profile (`sum_chanceLaw_payoff`), the translation's
`treeValue` with `queried B` written as the ambient point type.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtHarmonyBargain

open Finset SafeParetoImprovements StrategicGame
open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree Cleanroom.Found.DpCoreTree.Catalogue

instance : Nonempty TnPt := ⟨.F⟩

/-- Sums over `Box`. Source: none: infrastructure. Kind: L -/
theorem Box.sum_univ {M : Type} [AddCommMonoid M] (f : Box → M) : ∑ x, f x = f .large + f .both := by
  have : (Finset.univ : Finset Box) = {.large, .both} := by ext x; cases x <;> simp
  rw [this, Finset.sum_pair (by decide)]

section TreeRecursion

variable {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)] [DecidableEq Ω]

/-- Box constructor disequalities (for `simp`). Source: none: infrastructure. Kind: L -/
theorem Box.large_ne_both : Box.large ≠ Box.both := by decide
theorem Box.both_ne_large : Box.both ≠ Box.large := by decide

/-- The payoff mass on a world event, `∑_{ℓ : λ(ℓ) ⊨ X} μ(ℓ) r(ℓ)` (the numerator of a conditional
expectation).
Source: none: infrastructure
Kind: D -/
def condSum (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (X : Finset Ω) : ℚ :=
  ∑ ℓ, if world B ℓ ∈ X then leafLaw C B ℓ * payoff B ℓ else 0

/-- Conditional expectation of the payoff given a world event, `𝔼_{μ_{B,C}}[r ∣ λ ⊨ X] =
condSum / ν(X)` (`0/0 = 0` when the event has mass zero — every use below proves `ν(X) > 0`).
Source: `repair/harmony.md` HA-2′(i) (the updated point-specific utilities); mandate T8(d)
Kind: D -/
def condExp (C : Proc ι acts ℚ) (B : Tree Ω ι acts ℚ) (X : Finset Ω) : ℚ :=
  condSum C B X / nu C B X

theorem nu_leaf' (C : Proc ι acts ℚ) (ω : Ω) (r : ℚ) (X : Finset Ω) :
    nu C (.leaf ω r) X = if ω ∈ X then 1 else 0 := by
  rw [nu_eq_sum, Tree.sum_leaves_leaf]
  simp

theorem nu_chance' (C : Proc ι acts ℚ) (n : ℕ) (β : FinDistr ℚ (Fin n))
    (child : Fin n → Tree Ω ι acts ℚ) (X : Finset Ω) :
    nu C (.chance n β child) X = ∑ i, β.w i * nu C (child i) X := by
  rw [nu_eq_sum, sum_leaves_chance]
  refine sum_congr rfl fun i _ => ?_
  rw [nu_eq_sum, mul_sum]
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [leafLaw_chance, world_chance]
  split_ifs <;> ring

theorem nu_decision' (C : Proc ι acts ℚ) (d : ι) (child : acts d → Tree Ω ι acts ℚ)
    (X : Finset Ω) : nu C (.decision d child) X = ∑ a, (C d).w a * nu C (child a) X := by
  rw [nu_eq_sum, sum_leaves_decision]
  refine sum_congr rfl fun a _ => ?_
  rw [nu_eq_sum, mul_sum]
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [leafLaw_decision, world_decision]
  split_ifs <;> ring

theorem condSum_leaf' (C : Proc ι acts ℚ) (ω : Ω) (r : ℚ) (X : Finset Ω) :
    condSum C (.leaf ω r) X = if ω ∈ X then r else 0 := by
  unfold condSum
  rw [Tree.sum_leaves_leaf]
  simp

theorem condSum_chance' (C : Proc ι acts ℚ) (n : ℕ) (β : FinDistr ℚ (Fin n))
    (child : Fin n → Tree Ω ι acts ℚ) (X : Finset Ω) :
    condSum C (.chance n β child) X = ∑ i, β.w i * condSum C (child i) X := by
  unfold condSum
  rw [sum_leaves_chance]
  refine sum_congr rfl fun i _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [leafLaw_chance, world_chance, payoff_chance]
  split_ifs <;> ring

theorem condSum_decision' (C : Proc ι acts ℚ) (d : ι) (child : acts d → Tree Ω ι acts ℚ)
    (X : Finset Ω) : condSum C (.decision d child) X = ∑ a, (C d).w a * condSum C (child a) X := by
  unfold condSum
  rw [sum_leaves_decision]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun ℓ _ => ?_
  simp only [leafLaw_decision, world_decision, payoff_decision]
  split_ifs <;> ring

end TreeRecursion

/-! ### TN-V2 -/

/-- Pure profiles on the two Newcomb points. Source: mandate T8(d). Kind: D -/
abbrev TnOut : Type := TnPt → Box

/-- The profile `(x at d_F, y at d_E)`. Source: none: infrastructure. Kind: D -/
def tnO (f e : Box) : TnOut := fun d => match d with | .F => f | .E => e

@[simp] theorem tnO_F (f e : Box) : tnO f e .F = f := rfl
@[simp] theorem tnO_E (f e : Box) : tnO f e .E = e := rfl

theorem tnOut_cases (O : TnOut) :
    O = tnO .large .large ∨ O = tnO .large .both ∨ O = tnO .both .large ∨ O = tnO .both .both := by
  have h : O = tnO (O .F) (O .E) := by funext d; cases d <;> rfl
  rw [h]
  cases O .F <;> cases O .E <;> simp

/-- TN-V2 at `p = 3/4`, `L = 4`, `S = 1`. Source: [[decision-problems-v2]] §7.2 via the catalogue;
mandate T8(d). Kind: D -/
def tnB : Tree TnW TnPt (fun _ => Box) ℚ := tnV2 (3/4) (by norm_num) (by norm_num) 4 1

/-- `V_B(O)` on TN-V2. Source: mandate T8(d). Kind: D -/
def tnV (O : TnOut) : ℚ := value (Proc.ofFun O) tnB

/-- The updated utility of `d_F`: `𝔼_{μ_{B,O}}[r ∣ λ ⊨ O_F]`. Source: HA-2′(i); mandate T8(d).
Kind: D -/
def tnUF (O : TnOut) : ℚ := condExp (Proc.ofFun O) tnB (tnObs .F)

/-- The updated utility of `d_E`: `𝔼_{μ_{B,O}}[r ∣ λ ⊨ O_E]`. Source: HA-2′(i); mandate T8(d).
Kind: D -/
def tnUE (O : TnOut) : ℚ := condExp (Proc.ofFun O) tnB (tnObs .E)

/-- **The tree values** `V(l,l) = 3, V(l,b) = 7/4, V(b,l) = 5/4, V(b,b) = 2` — so the optimum is
`(large, large)`.
Source: `repair/harmony.md` HA-12′(d) (thread `tn_bg.py`); mandate T8(d)
Kind: N+ -/
theorem tnV_values :
    tnV (tnO .large .large) = 3 ∧ tnV (tnO .large .both) = 7/4 ∧
      tnV (tnO .both .large) = 5/4 ∧ tnV (tnO .both .both) = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [tnV, tnB, tnV2, tnReal, value_decision', value_chance', value_leaf', Box.sum_univ,
      Fin.sum_univ_two, Proc.ofFun_w, tnO_F, tnO_E, FinDistr.coin, tnPay]
    norm_num [Box.large_ne_both, Box.both_ne_large]

/-- The conditioning masses are positive: `μ_{B,O}{fill = 1} ∈ {3/4, 1/4}` and
`μ_{B,O}{fill = 0} ∈ {1/4, 3/4}` (no junk division in `tnUF`, `tnUE`).
Source: mandate T8(d) ("prove it, no junk division")
Kind: L -/
theorem tn_mass_pos (O : TnOut) :
    0 < nu (Proc.ofFun O) tnB (tnObs .F) ∧ 0 < nu (Proc.ofFun O) tnB (tnObs .E) := by
  rcases tnOut_cases O with rfl | rfl | rfl | rfl <;>
  · simp only [tnB, tnV2, tnReal, nu_decision', nu_chance', nu_leaf', Box.sum_univ,
      Fin.sum_univ_two, Proc.ofFun_w, tnO_F, tnO_E, FinDistr.coin, tnObs, Finset.mem_filter,
      Finset.mem_univ]
    norm_num [Box.large_ne_both, Box.both_ne_large]

/-- **The updated utilities**: `U_F = (4, 4, 5, 5)`, `U_E = (0, 1, 0, 1)` over
`((l,l), (l,b), (b,l), (b,b))`.
Source: `repair/harmony.md` HA-12′(d) (`U_F = (4,4,5,5)`, `U_E = (0,1,0,1)`); mandate T8(d)
Kind: N+ -/
theorem tnU_values :
    (tnUF (tnO .large .large) = 4 ∧ tnUF (tnO .large .both) = 4 ∧
      tnUF (tnO .both .large) = 5 ∧ tnUF (tnO .both .both) = 5) ∧
    (tnUE (tnO .large .large) = 0 ∧ tnUE (tnO .large .both) = 1 ∧
      tnUE (tnO .both .large) = 0 ∧ tnUE (tnO .both .both) = 1) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩ <;>
  · simp only [tnUF, tnUE, condExp, tnB, tnV2, tnReal, nu_decision', nu_chance', nu_leaf',
      condSum_decision', condSum_chance', condSum_leaf', Box.sum_univ, Fin.sum_univ_two,
      Proc.ofFun_w, tnO_F, tnO_E, FinDistr.coin, tnObs, tnPay, Finset.mem_filter,
      Finset.mem_univ]
    norm_num [Box.large_ne_both, Box.both_ne_large]

/-- The updated (point-specific-utility) collection on TN-V2 as a game over FAF's `Game`.
Source: `repair/harmony.md` HA-2′(i); mandate T8(d)
Kind: D -/
noncomputable def tnUpd : Game TnPt (fun _ => Box) :=
  utilGame fun d => match d with
    | .F => fun O => (tnUF O : ℝ)
    | .E => fun O => (tnUE O : ℝ)

@[simp] theorem tnUpd_u_F (O : TnOut) : tnUpd.u O .F = (tnUF O : ℝ) := rfl
@[simp] theorem tnUpd_u_E (O : TnOut) : tnUpd.u O .E = (tnUE O : ℝ) := rfl

theorem tnUF_le (O : TnOut) : tnUF O ≤ 5 := by
  obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := tnU_values
  rcases tnOut_cases O with rfl | rfl | rfl | rfl <;> linarith

theorem tnUF_of_both (O : TnOut) (h : O .F = .both) : tnUF O = 5 := by
  obtain ⟨⟨h1, h2, h3, h4⟩, -⟩ := tnU_values
  rcases tnOut_cases O with rfl | rfl | rfl | rfl <;> simp_all

theorem tnUE_le (O : TnOut) : tnUE O ≤ 1 := by
  obtain ⟨-, ⟨h1, h2, h3, h4⟩⟩ := tnU_values
  rcases tnOut_cases O with rfl | rfl | rfl | rfl <;> linarith

theorem tnUE_of_both (O : TnOut) (h : O .E = .both) : tnUE O = 1 := by
  obtain ⟨-, ⟨h1, h2, h3, h4⟩⟩ := tnU_values
  rcases tnOut_cases O with rfl | rfl | rfl | rfl <;> simp_all

/-- A player whose acceptable set is `{O₀}` with `O₀` agreeing with its batna realises its own
batna coordinate, for every singleton-faithful `sel`.
Source: none: infrastructure
Kind: L -/
theorem outcome_coord_of_singleton {N : Type} [Fintype N] [DecidableEq N] {A : N → Type}
    [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]
    {sel : Finset (Outcome A) → Outcome A}
    (hsel : ∀ S : Finset (Outcome A), S.Nonempty → sel S ∈ S) (σ : ∀ i, Proposal A i) (j : N)
    {O₀ : Outcome A} (h : (σ j).2 = {O₀}) (hb : O₀ j = (σ j).1) :
    outcome sel σ j = (σ j).1 := by
  rcases outcome_eq_sel_or_batna sel σ with ⟨hne, hout⟩ | ⟨-, hout⟩
  · rw [hout]
    have hmem := hsel _ hne
    rw [mem_inter] at hmem
    have := hmem j
    rw [h, mem_singleton] at this
    rw [this, hb]
  · rw [hout]
    rfl

/-- `σ* = ((both, {bb}), (both, {bb}))`. Source: HA-12′(d); mandate T8(d). Kind: D -/
def tnSigma : ∀ i : TnPt, Proposal (fun _ => Box) i :=
  fun _ => (.both, {tnO .both .both})

/-- **`σ*` is harmonious in the updated game** for every singleton-faithful `sel` (a fortiori
every welfare rule): each `s*ᵢ` yields its player's maximum (`5`, resp. `1`) against every
opponent proposal, so `thpe_of_dominant` applies.
Source: `repair/harmony.md` HA-12′(d); mandate T8(d)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem tnSigma_harmonious (sel : Finset TnOut → TnOut)
    (hsel : ∀ S : Finset TnOut, S.Nonempty → sel S ∈ S) : HarmoniousPure tnUpd sel tnSigma := by
  apply thpe_of_dominant
  intro i s τ
  rw [bargain_payoff, bargain_payoff, ofStrategicProfile_update, ofStrategicProfile_update]
  cases i
  · rw [tnUpd_u_F, tnUpd_u_F]
    set σ' := Function.update ((bargain tnUpd sel).ofStrategicProfile τ) .F
      (toStrat tnUpd sel tnSigma .F : Proposal (fun _ => Box) .F) with hσ'
    have h5 : tnUF (outcome sel σ') = 5 :=
      tnUF_of_both _ (outcome_coord_of_singleton hsel σ' .F (O₀ := tnO .both .both)
        (by simp [hσ', tnSigma]) (by simp [hσ', tnSigma]))
    rw [h5]
    exact_mod_cast tnUF_le _
  · rw [tnUpd_u_E, tnUpd_u_E]
    set σ' := Function.update ((bargain tnUpd sel).ofStrategicProfile τ) .E
      (toStrat tnUpd sel tnSigma .E : Proposal (fun _ => Box) .E) with hσ'
    have h1 : tnUE (outcome sel σ') = 1 :=
      tnUE_of_both _ (outcome_coord_of_singleton hsel σ' .E (O₀ := tnO .both .both)
        (by simp [hσ', tnSigma]) (by simp [hσ', tnSigma]))
    rw [h1]
    exact_mod_cast tnUE_le _

/-- The outcome of `σ*` is `(both, both)` for every singleton-faithful `sel`.
Source: mandate T8(d)
Kind: L -/
theorem tnSigma_outcome (sel : Finset TnOut → TnOut)
    (hsel : ∀ S : Finset TnOut, S.Nonempty → sel S ∈ S) :
    outcome sel tnSigma = tnO .both .both := by
  funext d
  cases d
  · exact outcome_coord_of_singleton hsel tnSigma .F rfl rfl
  · exact outcome_coord_of_singleton hsel tnSigma .E rfl rfl

/-- **`(both, both)` is Pareto-optimal for the updated utilities**: both updated points attain
their maxima there — they agree; no disagreement is involved (finding F6).
Source: `repair/harmony.md` HA-12′(d) ("both updated TN-V2 points agree on `(2,2)`"); mandate T8(d)
Kind: N+ -/
theorem tn_bb_paretoOptimal :
    Game.ParetoOptimalIn (tnUpd.u (tnO .both .both)) (tnUpd.u '' Set.univ) := by
  rw [paretoOptimalIn_iff]
  intro O' h
  rw [paretoDom_iff] at h
  obtain ⟨-, i, hi⟩ := h
  cases i
  · rw [tnUpd_u_F, tnUpd_u_F, tnUF_of_both _ rfl] at hi
    have := tnUF_le O'
    exact absurd hi (not_lt.mpr (by exact_mod_cast this))
  · rw [tnUpd_u_E, tnUpd_u_E, tnUE_of_both _ rfl] at hi
    have := tnUE_le O'
    exact absurd hi (not_lt.mpr (by exact_mod_cast this))

/-- `V(both, both) = 2 < 3 = V(large, large)`: the harmonious outcome of the updated game is
prior-suboptimal.
Source: `repair/harmony.md` HA-12′(d); mandate T8(d)
Kind: N+ -/
theorem tn_bb_suboptimal : tnV (tnO .both .both) < tnV (tnO .large .large) := by
  obtain ⟨h1, -, -, h4⟩ := tnV_values
  rw [h1, h4]; norm_num

/-- The homogeneous (not updating) TN-V2 game: every point values outcomes by `V_B`.
Source: `repair/harmony.md` HA-1′; mandate T8(d)
Kind: D -/
noncomputable def tnHom : Game TnPt (fun _ => Box) := commonGame fun O => (tnV O : ℝ)

/-- **In the homogeneous game `(both, both)` is not a harmonious outcome** (Proposition S(a)):
updating breaks harmony on TN-V2, off the fair class, by event-conditioning.
Source: `repair/harmony.md` HA-12′(d); mandate T8(d) (load-bearing 5)
Kind: C
Fidelity: exact (pure grade)
Hyps: (a) all -/
theorem tn_bb_not_harmonious_homogeneous (sel : Finset TnOut → TnOut) (W : TnOut → ℝ)
    (hW : IsWelfareSel tnHom sel W) (σ : ∀ i : TnPt, Proposal (fun _ => Box) i)
    (h : HarmoniousPure tnHom sel σ) : outcome sel σ ≠ tnO .both .both := by
  intro heq
  have hopt := harmoniousPure_isOpt hW h
  rw [heq] at hopt
  have := hopt (tnO .large .large)
  have h2 := tn_bb_suboptimal
  have : (tnV (tnO .large .large) : ℝ) ≤ tnV (tnO .both .both) := this
  exact absurd (by exact_mod_cast this) (not_le.mpr h2)

/-- The homogeneous TN-V2 utilities are the translation's: `V_B` of the pure profile, equivalently
the chance-law expectation of `r` at the realised leaf (`sum_chanceLaw_payoff`).
Source: `repair/harmony.md` HA-1′; mandate T9(ii)
Kind: L -/
theorem tnV_eq_sum_chanceLaw (O : TnOut) :
    tnV O = ∑ e, chanceLaw tnB e * payoff tnB (leafOf O tnB e) :=
  (sum_chanceLaw_payoff O tnB).symm

/-! ### The miniature (T11) -/

/-- The value of every deterministic procedure on the miniature is `0` (both pure outcomes are
worth `0`).
Source: `repair/harmony.md` HA-13′; [[decision-problems-v2]] Remark 4.3; mandate T11
Kind: N- -/
theorem value_ofFun_miniature (π : Unit → Act2) : value (Proc.ofFun π) miniature = 0 := by
  unfold miniature
  rw [value_decision', Act2.sum_univ, value_decision', value_decision', Act2.sum_univ,
    Act2.sum_univ]
  simp only [value_leaf', Proc.ofFun_w, miniPay]
  cases π () <;> simp

/-- Every pure profile of the miniature's homogeneous game is worth `0`.
Source: mandate T11
Kind: N- -/
theorem treeValue_miniature (O : (d : ↥(queried miniature)) → Act2) : treeValue miniature O = 0 := by
  unfold treeValue
  rw [value_ofFun_miniature]
  simp

/-- **Every mixed profile of the miniature's action game is worth `0`**, while the
independent-redraw value at `q = 1/2` is `3/4`: the miniature cannot be embedded in the
translation (HA-13′), which is exact at the pure / shared-seed grade only.
Source: `repair/harmony.md` HA-13′; [[decision-problems-v2]] Remark 4.3; mandate T11
Kind: N-
Fidelity: exact
Hyps: (a) all -/
theorem miniature_not_embeddable :
    (∀ (p : MixedProfile (actionGame miniature)) (d : ↥(queried miniature)),
      expectedPayoff (actionGame miniature) p d = 0) ∧
      value (procQ (1/2) (by norm_num) (by norm_num)) miniature = 3/4 := by
  refine ⟨fun p d => ?_, ?_⟩
  · unfold expectedPayoff
    refine sum_eq_zero fun σ _ => ?_
    rw [Game.toStrategic_payoff, commonGame_u, treeValue_miniature, mul_zero]
  · rw [miniature_value]; norm_num

/-- **Every profile of the miniature's homogeneous bargaining game is harmonious** (constant
payoffs), for every `sel`.
Source: mandate T11
Kind: N- -/
theorem miniature_all_harmonious (sel : Finset ((d : ↥(queried miniature)) → Act2) →
    ((d : ↥(queried miniature)) → Act2)) (σ : ∀ d : ↥(queried miniature), Proposal (fun _ => Act2) d) :
    HarmoniousPure (homogeneousGame miniature) sel σ := by
  apply thpe_of_dominant
  intro i s τ
  rw [bargain_payoff, bargain_payoff, homogeneousGame_eq_commonGame, commonGame_u, commonGame_u,
    treeValue_miniature, treeValue_miniature]

end Cleanroom.Udt.UdtHarmonyBargain
