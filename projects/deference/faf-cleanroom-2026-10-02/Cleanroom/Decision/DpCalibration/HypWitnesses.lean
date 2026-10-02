import Cleanroom.Decision.DpCalibration.Chain
import Cleanroom.Decision.DpCalibration.ToldYouSo
import Cleanroom.Decision.DpCalibration.Witnesses
import Cleanroom.Decision.DpCalibration.Recording
import Cleanroom.Decision.DpCalibration.FiveTen
import Cleanroom.Found.DpCoreTree.ScreeningWitness

/-!
# The hypothesis packages inhabited (repair round 1)

Audit round 1 (fidelity B3; adversarial B1, B2, B4) found that the load-bearing hypothesis
packages — `H_d = Covers ∧ ∀ q, SubtreeVeridicalAS` (Proposition 3, LB 3), `H_d ∧ AlmostFair`
(ZO-2's chain, LB 1) and `RecordsForAll` (CA-12′) — were inhabited nowhere in Lean; that
Proposition 7's `coinQuery` instance had `C = C'`; and that D2 was shown empty on the miniature
without an instance on which it holds. This file ships the witnesses (the auditors' probes,
adopted):

* **`coinQuery`** — `H_d`, almost-fairness and `RecordsForAll` for every procedure (`O = ⊤`).
  The Proposition-3 / ZO-2 instance there is **N−**: with `O = ⊤` subtree-veridicality is
  trivial and both senses are prior calibration. The `RecordsForAll` instance is N+ (the action
  event is a proper event, recorded for every procedure).
* **`toldYouSo` at `d₁₀`** — `H_d`, almost-fairness and `RecordsForAll` for every procedure,
  with the proper observation `O₁₀ = {n = 10}` realized iff the root gives ten positive weight
  (`tys_nu_obs_ten`); Proposition 3 and ZO-2's chain instantiated there (**N+**); Proposition 7
  instantiated with two *different* procedures (`½` and `¼` on ten at the root, ten at `d₁₀`),
  `prop7_nondegenerate_instance` (**N+**).
* **`fiveTen`** — take-10 is event-tremble-EDT-consistent (`fiveTen_take10_eventTremble`): D2 is
  inhabited, so its emptiness on the miniature (`miniature_not_eventTremble`) is a fact about the
  miniature, not about the definition ([[STANDARDS]] §3's artifact check for an impossibility).
-/

set_option linter.unusedSectionVars false
set_option linter.constructorNameAsVariable false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-! ## `coinQuery`: the packages for every procedure (`O = ⊤`) -/

section coinQueryPackages

/-- CA-12′'s hypothesis `RecordsForAll` is inhabited on `coinQuery` (`dp-core-tree`'s
`coinQuery_recordsFor` takes an arbitrary procedure).
Source: mandate T15(d) (CA-12′'s repaired hypothesis); audit round 1
Kind: N+ -/
theorem coinQuery_recordsForAll : RecordsForAll cqObs cqActEv coinQuery () :=
  fun C => coinQuery_recordsFor C

/-- Coverage at `d` on `coinQuery` for every procedure. Source: none: infrastructure. Kind: L -/
theorem coinQuery_covers (C : Proc Unit (fun _ => Act2) ℚ) : Covers cqObs C coinQuery () :=
  (coinQuery_recordsFor C).covers

/-- A.s. subtree-veridicality at every `d`-node of `coinQuery` (`O = ⊤`, so trivially).
Source: none: infrastructure. Kind: L -/
theorem coinQuery_svAS (C : Proc Unit (fun _ => Act2) ℚ) (q : coinQuery.DecNode)
    (_ : pt coinQuery q = ()) : SubtreeVeridicalAS cqObs C coinQuery q :=
  fun _ _ _ => by simp [cqObs]

/-- `coinQuery` is almost fair (`#_d = 1` on every leaf). Source: none: infrastructure. Kind: L -/
theorem coinQuery_almostFair : AlmostFair coinQuery := by
  intro d ℓ
  cases d
  rw [coinQuery_count]

/-- The full hypothesis package of `zo2_chain_at` (LB 1) and `perRunSSCAt_iff_strictOCAt`
(LB 3) is inhabited on `coinQuery` for every procedure — **N−** as a Proposition-3 witness:
`O = ⊤` makes subtree-veridicality trivial and both senses collapse to prior calibration; the
N+ instance is `tys_zo2_instance`.
Source: mandate T5/T7 ("`coinQuery`"); audit round 1
Kind: N− -/
theorem coinQuery_Hd_almostFair (C : Proc Unit (fun _ => Act2) ℚ) :
    (Covers cqObs C coinQuery () ∧
      ∀ q, pt coinQuery q = () → SubtreeVeridicalAS cqObs C coinQuery q) ∧
    AlmostFair coinQuery :=
  ⟨⟨coinQuery_covers C, coinQuery_svAS C⟩, coinQuery_almostFair⟩

/-- ZO-2's chain instantiated on `coinQuery` for every procedure and state assignment (guards
`ν(O_d) = 1`, `μ(occ) = 1`); N− for the reason given on `coinQuery_Hd_almostFair`.
Source: ZO-2; mandate T10; audit round 1
Kind: N− -/
theorem coinQuery_zo2_instance (C : Proc Unit (fun _ => Act2) ℚ)
    (s : Unit → State CoinQueryW ℚ) :
    (LimitOCAt s cqObs C coinQuery () → StrictOCAt s cqObs C coinQuery ()) ∧
    (StrictOCAt s cqObs C coinQuery () ↔ PerRunSSCAt s C coinQuery ()) ∧
    (PerRunSSCAt s C coinQuery () ↔ PerOccSSCAt s C coinQuery ()) :=
  zo2_chain_at C coinQuery cqObs s (coinQuery_covers C) (coinQuery_svAS C) coinQuery_almostFair

end coinQueryPackages

/-! ## `toldYouSo` at `d₁₀`: the packages for every procedure, a proper observation -/

section toldYouSoPackages

/-- Coverage at `d₁₀`: every positive `O₁₀`-leaf passes the inner `d₁₀`-node.
Source: none: infrastructure. Kind: L -/
theorem tys_covers_ten (C : Proc Five10 (fun _ => Five10) ℚ) :
    Covers tysObs C toldYouSo .ten := by
  intro ℓ _ hobs
  unfold toldYouSo at ℓ hobs ⊢
  rcases ℓ with ⟨k, ℓ⟩
  cases k
  · simp [tysObs] at hobs
  · rcases ℓ with ⟨k', ℓ'⟩
    cases k' <;> simp [count_decision]

/-- Every `d₁₀`-node (there is one) is subtree-veridical: both leaves below it have `n = 10`.
Source: none: infrastructure. Kind: L -/
theorem tys_sv_ten (C : Proc Five10 (fun _ => Five10) ℚ) :
    ∀ q, pt toldYouSo q = .ten → SubtreeVeridicalAS tysObs C toldYouSo q := by
  unfold toldYouSo
  rintro (_ | ⟨k, q⟩) hq ℓ hℓ _
  · exact absurd hq (by decide)
  · cases k
    · exact q.elim
    · rcases q with _ | ⟨k', q'⟩
      · rw [mem_leavesBelow] at hℓ
        rcases ℓ with ⟨k, ℓ⟩
        cases k
        · simp at hℓ
        · rcases ℓ with ⟨k', ℓ'⟩
          cases k' <;> simp [tysObs]
      · cases k' <;> exact Empty.elim q'

/-- `toldYouSo` is almost fair (no path meets two nodes of one point).
Source: none: infrastructure. Kind: L -/
theorem tys_almostFair : AlmostFair toldYouSo := by
  intro d ℓ
  unfold toldYouSo at ℓ ⊢
  rcases ℓ with ⟨k, ℓ⟩
  cases k
  · cases d <;> simp [count_decision]
  · rcases ℓ with ⟨k', ℓ'⟩
    cases k' <;> cases d <;> simp [count_decision]

/-- `ν_C(O₁₀) = C(d₅)(ten)`: the observation is a proper event, realized exactly when the root
plays ten with positive weight. Source: none: infrastructure. Kind: L -/
theorem tys_nu_obs_ten (C : Proc Five10 (fun _ => Five10) ℚ) :
    nu C toldYouSo (tysObs .ten) = (C .five).w .ten := by
  rw [tys_nu]
  have := (C .ten).sum_one
  rw [Five10.sum_univ] at this
  simp [tysObs]
  linear_combination (C .five).w .ten * this

/-- `μ(occ(d₁₀)) = C(d₅)(ten)` on `toldYouSo`. Source: none: infrastructure. Kind: L -/
theorem tys_mass_occ_ten (C : Proc Five10 (fun _ => Five10) ℚ) :
    mass C toldYouSo (occ .ten toldYouSo) = (C .five).w .ten := by
  rw [mass_occ_eq_nu_obs tysObs C toldYouSo (tys_covers_ten C) (tys_sv_ten C), tys_nu_obs_ten]

/-- **Proposition 3 instantiated at `d₁₀` on `toldYouSo`** for every procedure and every state
assignment: per-run SSC at `d₁₀` ⟺ strict OC at `d₁₀`, with the proper observation
`O₁₀ = {n = 10}` (both guards equal `C(d₅)(ten)`).
Source: [[decision-problems-v2]] §3.1 Proposition 3 (LB 3); audit round 1
Kind: N+ -/
theorem tys_perRun_iff_strict_ten (C : Proc Five10 (fun _ => Five10) ℚ)
    (s : Five10 → State TysW ℚ) :
    PerRunSSCAt s C toldYouSo .ten ↔ StrictOCAt s tysObs C toldYouSo .ten :=
  perRunSSCAt_iff_strictOCAt tysObs C toldYouSo s (tys_covers_ten C) (tys_sv_ten C)

/-- **ZO-2's chain instantiated at `d₁₀` on `toldYouSo`** (LB 1's hypothesis package inhabited
on a tree with a proper observation, for every procedure and state assignment).
Source: `zoo.md` ZO-2 (LB 1); audit round 1
Kind: N+ -/
theorem tys_zo2_instance (C : Proc Five10 (fun _ => Five10) ℚ) (s : Five10 → State TysW ℚ) :
    (LimitOCAt s tysObs C toldYouSo .ten → StrictOCAt s tysObs C toldYouSo .ten) ∧
    (StrictOCAt s tysObs C toldYouSo .ten ↔ PerRunSSCAt s C toldYouSo .ten) ∧
    (PerRunSSCAt s C toldYouSo .ten ↔ PerOccSSCAt s C toldYouSo .ten) :=
  zo2_chain_at C toldYouSo tysObs s (tys_covers_ten C) (tys_sv_ten C) tys_almostFair

/-- **`toldYouSo` records at `d₁₀` for every procedure**: every positive `O₁₀`-leaf passes the
inner node exactly once, that node is subtree-veridical, its instance is action-veridical, and
the leaf-world satisfies only the drawn action's event.
Source: none: infrastructure (v2 Definition 7 on `B_P`). Kind: L -/
theorem tys_recordsFor_ten (C : Proc Five10 (fun _ => Five10) ℚ) :
    RecordsFor tysObs tysActEv C toldYouSo .ten := by
  intro ℓ _ hobs
  unfold toldYouSo at ℓ hobs ⊢
  rcases ℓ with ⟨k, ℓ⟩
  cases k
  · simp [tysObs] at hobs
  · rcases ℓ with ⟨k', _⟩
    refine ⟨by cases k' <;> simp [count_decision], ?_⟩
    rintro (_ | ⟨k'', q⟩) hq a ha
    · exact absurd hq (by decide)
    · cases k''
      · exact Empty.elim q
      · rcases q with _ | ⟨k3, q3⟩
        · simp only [edgeOf_decision_some, dite_true, edgeOf_decision_none,
            Option.some.injEq] at ha
          subst ha
          refine ⟨?_, ?_, ?_⟩
          · intro ℓ' hℓ'
            rw [mem_leavesBelow] at hℓ'
            rcases ℓ' with ⟨k4, ℓ4⟩
            cases k4
            · simp at hℓ'
            · rcases ℓ4 with ⟨k5, _⟩
              cases k5 <;> simp [tysObs]
          · cases k' <;> simp [tysActEv]
          · intro a' ha'
            cases k' <;> simp [tysActEv] at ha' <;> exact ha'.symm
        · cases k3 <;> exact Empty.elim q3

/-- CA-12′'s hypothesis `RecordsForAll` is inhabited on `toldYouSo` at `d₁₀`.
Source: mandate T15(d); audit round 1
Kind: N+ -/
theorem tys_recordsForAll_ten : RecordsForAll tysObs tysActEv toldYouSo .ten :=
  fun C => tys_recordsFor_ten C

/-- A procedure playing ten at `d₁₀` is strictly calibrated at `d₁₀` with the stipulated
state `δ_{(10,10)}` (whatever it plays at the root). Source: none: infrastructure. Kind: L -/
theorem tys_strictOCAt_ten_of_pure (C : Proc Five10 (fun _ => Five10) ℚ)
    (hC : C .ten = FinDistr.pure .ten) : StrictOCAt tysState tysObs C toldYouSo .ten := by
  intro _
  refine ⟨fun X => ?_, fun X _ _ => ?_⟩
  · rw [tys_nu, tys_nu]
    simp [tysObs, tysState, State.dirac_pr, hC]
  · rw [tys_nu, tys_paySum]
    simp [tysObs, tysState, hC, Five10.val]
    split_ifs <;> ring

/-- A mixture on `Five10` with weight `q` on ten. Source: none: infrastructure. Kind: D -/
def mixRoot (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : FinDistr ℚ Five10 where
  w := fun | .five => 1 - q | .ten => q
  nonneg := by intro x; cases x <;> simp <;> linarith
  sum_one := by rw [Five10.sum_univ]; simp

/-- The procedure playing `mixRoot q` at `d₅` and ten at `d₁₀`. Source: none: infrastructure.
Kind: D -/
def procMixTen (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Proc Five10 (fun _ => Five10) ℚ :=
  fun | .five => mixRoot q h0 h1 | .ten => FinDistr.pure .ten

/-- `ν(O₁₀) = q` under `procMixTen q`. Source: none: infrastructure. Kind: L -/
theorem procMixTen_nu_obs (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    nu (procMixTen q h0 h1) toldYouSo (tysObs .ten) = q := by
  rw [tys_nu]; simp [tysObs, procMixTen, mixRoot]

/-- **Proposition 7's hypothesis package, non-degenerately inhabited**: `C = (½ on ten; ten)` and
`C' = (¼ on ten; ten)` differ, both record at `d₁₀`, both realize `O₁₀`, both are strictly
calibrated at `d₁₀` with `tysState`, and Proposition 7 yields `C d₁₀ = C' d₁₀`. (The `coinQuery`
instance `coinQuery_prop7_instance` has `C = C'` and is N−.)
Source: [[decision-problems-v2]] §3.1 Proposition 7 (LB 5); audit round 1
Kind: N+ -/
theorem prop7_nondegenerate_instance :
    procMixTen (1/2) (by norm_num) (by norm_num) ≠ procMixTen (1/4) (by norm_num) (by norm_num) ∧
    RecordsFor tysObs tysActEv (procMixTen (1/2) (by norm_num) (by norm_num)) toldYouSo .ten ∧
    RecordsFor tysObs tysActEv (procMixTen (1/4) (by norm_num) (by norm_num)) toldYouSo .ten ∧
    0 < nu (procMixTen (1/2) (by norm_num) (by norm_num)) toldYouSo (tysObs .ten) ∧
    0 < nu (procMixTen (1/4) (by norm_num) (by norm_num)) toldYouSo (tysObs .ten) ∧
    StrictOCAt tysState tysObs (procMixTen (1/2) (by norm_num) (by norm_num)) toldYouSo .ten ∧
    StrictOCAt tysState tysObs (procMixTen (1/4) (by norm_num) (by norm_num)) toldYouSo .ten ∧
    procMixTen (1/2) (by norm_num) (by norm_num) .ten =
      procMixTen (1/4) (by norm_num) (by norm_num) .ten := by
  have hne : procMixTen (1/2) (by norm_num) (by norm_num) ≠
      procMixTen (1/4) (by norm_num) (by norm_num) := by
    intro h
    have := congrArg (fun P => (P .five).w .ten) h
    simp [procMixTen, mixRoot] at this
  have hr := tys_recordsFor_ten (procMixTen (1/2) (by norm_num) (by norm_num))
  have hr' := tys_recordsFor_ten (procMixTen (1/4) (by norm_num) (by norm_num))
  have hpos : 0 < nu (procMixTen (1/2) (by norm_num) (by norm_num)) toldYouSo (tysObs .ten) := by
    rw [procMixTen_nu_obs]; norm_num
  have hpos' : 0 < nu (procMixTen (1/4) (by norm_num) (by norm_num)) toldYouSo (tysObs .ten) := by
    rw [procMixTen_nu_obs]; norm_num
  have hs := tys_strictOCAt_ten_of_pure (procMixTen (1/2) (by norm_num) (by norm_num)) rfl
  have hs' := tys_strictOCAt_ten_of_pure (procMixTen (1/4) (by norm_num) (by norm_num)) rfl
  exact ⟨hne, hr, hr', hpos, hpos', hs, hs',
    prop7_rigidity tysObs tysActEv _ toldYouSo tysState _ hr hr' hpos hpos' hs hs'⟩

end toldYouSoPackages

/-! ## D2 is inhabited: take-10 on five-and-ten -/

section d2Inhabited

/-- `condExp` of the two act events on `fiveTen` under an interior mixture: `5` and `10`.
Source: none: infrastructure. Kind: L -/
theorem fiveTen_condExp (r : ℚ) (h0 : 0 < r) (h1 : r < 1) :
    condExp (procQ r h0.le h1.le) fiveTen (ftActEv () .a ∩ ftObs ()) = 5 ∧
    condExp (procQ r h0.le h1.le) fiveTen (ftActEv () .b ∩ ftObs ()) = 10 := by
  simp only [condExp, ftObs, Finset.inter_univ, fiveTen_nu, fiveTen_paySum, ftActEv, procQ,
    FinDistr.act2_a, FinDistr.act2_b]
  have hr : r ≠ 0 := h0.ne'
  have hr' : (1 - r) ≠ 0 := by linarith
  constructor <;> simp <;> field_simp

/-- **D2 is inhabited**: take-10 (`procQ 0`) is event-tremble-EDT-consistent on `fiveTen` — at
every `ε ∈ (0,1)` the trembled act values are `5` and `10`, the argmax is `{b}`, and
`supp (procQ 0) = {b}`. The artifact check for `miniature_not_eventTremble` (findings F5).
Source: [[decision-problems-v2]] §3.2 Remark 3.12 (take-10 tremble-consistent); `calibration.md`
D2; audit round 1
Kind: N+ -/
theorem fiveTen_take10_eventTremble :
    EventTrembleEdtConsistent ftObs ftActEv (procQ 0 le_rfl zero_le_one) fiveTen := by
  refine ⟨1, one_pos, fun ε h0 h1 hlt d _ _ _ a ha => ?_⟩
  cases d
  have hr0 := (qeps_mem 0 ε le_rfl zero_le_one h0.le h1).1
  have hr1 := (qeps_mem 0 ε le_rfl zero_le_one h0.le h1).2
  obtain ⟨hi0, hi1⟩ := qeps_interior 0 ε le_rfl zero_le_one h0 hlt
  rw [tremble_procQ]
  obtain ⟨hva, hvb⟩ := fiveTen_condExp _ hi0 hi1
  have hnu : ∀ b, nu (procQ ((1 - ε) * 0 + ε / 2) hr0 hr1) fiveTen (ftActEv () b ∩ ftObs ()) =
      (procQ ((1 - ε) * 0 + ε / 2) hr0 hr1 ()).w b := by
    intro b; rw [ftObs, Finset.inter_univ, fiveTen_nu]; cases b <;> simp [ftActEv]
  cases a
  · simp [procQ] at ha
  · refine ⟨?_, fun b _ => ?_⟩
    · rw [hnu]; simp only [procQ, FinDistr.act2_b]; linarith
    · cases b
      · rw [hva, hvb]; norm_num
      · exact le_rfl

end d2Inhabited

/-! ## Repair round 2: Proposition 7 with a properly mixed label; the empty Witness cells

The auditors' probes `Prop7Mixed` (adversarial N2) and `FidelityCoinQueryInstances` (fidelity N4),
adopted. -/

section prop7Mixed

/-- `q` on ten at the root, the mixture `m` at `d₁₀`.
Source: none: infrastructure. Kind: D -/
def procMixBoth (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (m : FinDistr ℚ Five10) :
    Proc Five10 (fun _ => Five10) ℚ :=
  fun | .five => mixRoot q h0 h1 | .ten => m

/-- `C = (½ on ten; ½/½ at d₁₀)`. Source: none: infrastructure. Kind: D -/
def procHalfHalf : Proc Five10 (fun _ => Five10) ℚ :=
  procMixBoth (1/2) (by norm_num) (by norm_num) (mixRoot (1/2) (by norm_num) (by norm_num))

/-- `C' = (¼ on ten; ½/½ at d₁₀)`. Source: none: infrastructure. Kind: D -/
def procQuarterHalf : Proc Five10 (fun _ => Five10) ℚ :=
  procMixBoth (1/4) (by norm_num) (by norm_num) (mixRoot (1/2) (by norm_num) (by norm_num))

/-- `C` realizes `O₁₀`. Source: none: infrastructure. Kind: L -/
theorem procHalfHalf_pos : 0 < nu procHalfHalf toldYouSo (tysObs .ten) := by
  rw [tys_nu_obs_ten]; norm_num [procHalfHalf, procMixBoth, mixRoot]

/-- `C'` realizes `O₁₀`. Source: none: infrastructure. Kind: L -/
theorem procQuarterHalf_pos : 0 < nu procQuarterHalf toldYouSo (tysObs .ten) := by
  rw [tys_nu_obs_ten]; norm_num [procQuarterHalf, procMixBoth, mixRoot]

/-- The strict state of `C` at `d₁₀`: the mixed conditional `½ δ_{(10,10)} + ½ δ_{(10,5)}`.
Source: none: infrastructure. Kind: D -/
noncomputable def tysMixState : State TysW ℚ :=
  calibratedState procHalfHalf toldYouSo (tysObs .ten) procHalfHalf_pos

/-- The state's act-credences are the mixture: `P(m = 10) = ½`, `P(m = 5) = ½`.
Source: none: infrastructure. Kind: L -/
theorem tysMixState_pr :
    tysMixState.pr (tysActEv .ten .ten) = 1/2 ∧ tysMixState.pr (tysActEv .ten .five) = 1/2 := by
  constructor <;> rw [tysMixState, calibratedState_pr, tys_nu, tys_nu] <;>
    simp [tysObs, tysActEv, procHalfHalf, procMixBoth, mixRoot] <;> norm_num

/-- `C'` is strictly calibrated at `d₁₀` with `C`'s state: the conditional on `O₁₀` does not
depend on the root's mixture.
Source: none: infrastructure. Kind: L -/
theorem tysMixState_strict_quarter :
    StrictOCAt (fun _ => tysMixState) tysObs procQuarterHalf toldYouSo .ten := by
  intro _
  refine ⟨fun X => ?_, fun X _ hXO => ?_⟩
  · simp only [tysMixState]
    rw [calibratedState_pr, tys_nu, tys_nu, tys_nu, tys_nu]
    simp [tysObs, procHalfHalf, procQuarterHalf, procMixBoth, mixRoot]
    split_ifs <;> norm_num
  · rw [tys_nu] at hXO
    simp only [tysMixState]
    rw [calibratedState_V, tys_nu, tys_paySum, tys_nu, tys_paySum]
    simp [tysObs, procHalfHalf, procQuarterHalf, procMixBoth, mixRoot] at hXO ⊢
    split_ifs at hXO ⊢ <;> (try norm_num at hXO) <;> norm_num

/-- **Proposition 7's package inhabited with a properly mixed label at `d₁₀`** (N+): `C ≠ C'`,
`C(d₁₀)` puts weight `½` on each action, recording for both, both positivities, strict OC at
`d₁₀` for both with the one state `tysMixState`, and rigidity returns `C(d₁₀) = C'(d₁₀)`. The
mixed label is pinned by the state, not by self-certainty (`prop7_nondegenerate_instance` is
deterministic at `d₁₀` and exercises only Remark 3.6's collapse).
Source: [[decision-problems-v2]] Proposition 7; audit round 2 adversarial N2 (probe adopted)
Kind: N+
Fidelity: exact -/
theorem prop7_mixed_instance :
    procHalfHalf ≠ procQuarterHalf ∧
    (0 < (procHalfHalf .ten).w .ten ∧ 0 < (procHalfHalf .ten).w .five) ∧
    RecordsFor tysObs tysActEv procHalfHalf toldYouSo .ten ∧
    RecordsFor tysObs tysActEv procQuarterHalf toldYouSo .ten ∧
    0 < nu procHalfHalf toldYouSo (tysObs .ten) ∧
    0 < nu procQuarterHalf toldYouSo (tysObs .ten) ∧
    StrictOCAt (fun _ => tysMixState) tysObs procHalfHalf toldYouSo .ten ∧
    StrictOCAt (fun _ => tysMixState) tysObs procQuarterHalf toldYouSo .ten ∧
    procHalfHalf .ten = procQuarterHalf .ten := by
  have hne : procHalfHalf ≠ procQuarterHalf := by
    intro h
    have := congrArg (fun P => (P .five).w .ten) h
    norm_num [procHalfHalf, procQuarterHalf, procMixBoth, mixRoot] at this
  have hmix : 0 < (procHalfHalf .ten).w .ten ∧ 0 < (procHalfHalf .ten).w .five := by
    constructor <;> norm_num [procHalfHalf, procMixBoth, mixRoot]
  have hr := tys_recordsFor_ten procHalfHalf
  have hr' := tys_recordsFor_ten procQuarterHalf
  have hs : StrictOCAt (fun _ => tysMixState) tysObs procHalfHalf toldYouSo .ten :=
    strictOCAt_calibratedState tysObs procHalfHalf toldYouSo _ .ten procHalfHalf_pos rfl
  have hs' := tysMixState_strict_quarter
  exact ⟨hne, hmix, hr, hr', procHalfHalf_pos, procQuarterHalf_pos, hs, hs',
    prop7_rigidity tysObs tysActEv _ toldYouSo _ _ hr hr' procHalfHalf_pos procQuarterHalf_pos
      hs hs'⟩

end prop7Mixed

section coinQueryInstances

/-- Every payoff on `coinQuery` is `0`. Source: none: infrastructure. Kind: L -/
theorem coinQuery_payoff (ℓ : coinQuery.Leaves) : payoff coinQuery ℓ = 0 := by
  unfold coinQuery at ℓ ⊢
  rcases ℓ with ⟨i, act, _⟩
  simp [payoff_chance, payoff_decision, payoff_leaf]

/-- The strict state's desirability on `coinQuery` is identically `0`.
Source: none: infrastructure. Kind: L -/
theorem cqStrictState_V (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (X : Finset CoinQueryW) :
    (cqStrictState r hr0 hr1).V X = 0 := by
  rw [cqStrictState, calibratedState_V]
  have : paySum (procQ r hr0 hr1) coinQuery (X ∩ cqObs ()) = 0 :=
    Finset.sum_eq_zero fun ℓ _ => by rw [coinQuery_payoff, mul_zero]
  rw [this, zero_div]

/-- Self-transparency of the strict state of `procQ r` on `coinQuery`.
Source: none: infrastructure. Kind: L -/
theorem cqStrictState_selfTransparent (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    SelfTransparent (fun _ => cqStrictState r hr0 hr1) cqActEv (procQ r hr0 hr1) () :=
  selfTransparent_of_recordsFor_strict cqObs cqActEv (procQ r hr0 hr1) coinQuery
    (fun _ => cqStrictState r hr0 hr1) (coinQuery_recordsFor _)
    (by rw [coinQuery_nu_obs]; exact one_pos)
    (strictOCAt_calibratedState cqObs (procQ r hr0 hr1) coinQuery _ () _ rfl)

/-- The strict state's action credences on `coinQuery` are the procedure's weights.
Source: none: infrastructure. Kind: L -/
theorem cqStrictState_pr_act (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (a : Act2) :
    (cqStrictState r hr0 hr1).pr (cqActEv () a) = (procQ r hr0 hr1 ()).w a := by
  have h := cqStrictState_selfTransparent r hr0 hr1 a
  dsimp only at h
  exact h

/-- **Instance of `maskedOCAt_of_strict_fullSupport`** (T10's "strict ⟹ masked" arrow) on
`coinQuery` with `procQ ½`: every hypothesis (recording, positivity, strict OC, full-support
strict action credences) and the conclusion. N+: interior mixture, a proper action event.
Source: [[decision-problems-v2]] Remark 3.7; audit round 2 fidelity N4 (probe adopted)
Kind: N+
Fidelity: exact -/
theorem coinQuery_strict_imp_masked_instance :
    RecordsFor cqObs cqActEv (procQ (1/2) (by norm_num) (by norm_num)) coinQuery () ∧
    0 < nu (procQ (1/2) (by norm_num) (by norm_num)) coinQuery (cqObs ()) ∧
    StrictOCAt (fun _ => cqStrictState (1/2) (by norm_num) (by norm_num)) cqObs
      (procQ (1/2) (by norm_num) (by norm_num)) coinQuery () ∧
    (∀ a, 0 < (cqStrictState (1/2) (by norm_num) (by norm_num)).pr (cqActEv () a)) ∧
    MaskedOCAt (fun _ => cqStrictState (1/2) (by norm_num) (by norm_num)) cqObs
      (procQ (1/2) (by norm_num) (by norm_num)) coinQuery () := by
  obtain ⟨hr, hpos, hs⟩ := coinQuery_prop7_instance (1/2) (by norm_num) (by norm_num)
  have hfull : ∀ a, 0 < (cqStrictState (1/2) (by norm_num) (by norm_num)).pr (cqActEv () a) := by
    intro a
    rw [cqStrictState_pr_act]
    cases a <;> norm_num [procQ]
  exact ⟨hr, hpos, hs, hfull,
    maskedOCAt_of_strict_fullSupport cqObs cqActEv _ coinQuery _ hr hpos hs hfull⟩

/-- **Instance of Remark 3.9's theorem-let** (`tEdtAt_of_deterministic_recorded`,
`aPlus_eq_singleton_of_deterministic`) on `coinQuery` with `procQ 1 = δ_a`: `A^+ = {a}` and the
`T_EDT` clause. N+ (a proper action event at a recorded positive point).
Source: [[decision-problems-v2]] Remark 3.9; audit round 2 fidelity N4 (probe adopted)
Kind: N+
Fidelity: exact -/
theorem coinQuery_deterministic_instance :
    APlus (fun _ => cqStrictState 1 zero_le_one le_rfl) cqActEv () = {Act2.a} ∧
    TEdtAt (fun _ => cqStrictState 1 zero_le_one le_rfl) cqActEv (procQ 1 zero_le_one le_rfl) () := by
  obtain ⟨hr, hpos, hs⟩ := coinQuery_prop7_instance 1 zero_le_one le_rfl
  have hC : procQ 1 zero_le_one le_rfl () = FinDistr.pure Act2.a := by
    apply FinDistr.ext'
    intro a
    cases a <;> simp [procQ, FinDistr.pure_w]
  exact tEdtAt_of_deterministic_recorded (fun _ => cqStrictState 1 zero_le_one le_rfl) cqActEv
    cqObs (procQ 1 zero_le_one le_rfl) coinQuery Act2.a hC hr hpos hs

/-- `T_EDT` at `d` holds for every `procQ r` with its strict state on `coinQuery` (all act values
are `0`, so every subjectively possible act is a maximiser).
Source: none: infrastructure. Kind: L -/
theorem cqStrictState_tEdtAt (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    TEdtAt (fun _ => cqStrictState r hr0 hr1) cqActEv (procQ r hr0 hr1) () := by
  intro _ a ha
  rw [mem_argmaxPlus]
  refine ⟨?_, fun b _ => ?_⟩
  · simp only [APlus, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [cqStrictState_pr_act]
    exact ha
  · simp [cqStrictState_V]

end coinQueryInstances

end Cleanroom.Decision.DpCalibration
