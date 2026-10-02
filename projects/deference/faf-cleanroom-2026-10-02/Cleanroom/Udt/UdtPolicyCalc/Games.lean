import Cleanroom.Udt.UdtPolicyCalc.LocalGlobal
import EconCSLib.GameTheory.StrategicGame.NashEquilibrium
import SafeParetoImprovements.Game

/-!
# The instance game and the Nash reading of local optimality (T12(b), §5's tautology)

Post 1: "if we consider the version of you in a situation as a player in a game, then you're
basically in a single-shot really large game against the yous in different situations, and all
players have the same utility function … even if all players in a game have the same utility
function, there can be Nash equilibria that aren't globally optimal."

* `instanceGame U : SafeParetoImprovements.Game S (fun _ => A)` — the **definition of record**
  (FAF's object, §1 of [[STANDARDS]]): one player per situation, action set `univ`, common payoff
  `U`. Nash is EconCSLib's `IsNashEquilibrium` on `(instanceGame U).toStrategic`.
* `directGame U : StrategicGame S ℝ` — the direct form we compute with; the two Nash predicates
  are equivalent (`isNashEquilibrium_instanceGame_iff_directGame`).
* `isNashEquilibrium_directGame_iff` / `isNashEquilibrium_instanceGame_iff`: a policy is a pure
  Nash equilibrium iff it is a local optimum (a UDT1.0 fixed point); `isNashEquilibrium_of_isOptimal`
  (the UDT1.1 optimum is Nash, via T2); `coordButtons_nash_not_optimal` (a non-optimal Nash
  equilibrium exists).
* `localGlobal_iff_nash_optimal`: §5's exact characterization, recorded as the tautology it is.

Package `udt-policy-calc` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtPolicyCalc

noncomputable section

open StrategicGame

section Games

variable {S A : Type} [DecidableEq S] [Fintype A]

/-- **The instance game (definition of record).** One player per situation `s : S`, every player's
action set is all of `A` (`Finset.univ`), and every player's payoff at the profile `π` is the
common policy utility `U π`. FAF's `SafeParetoImprovements.Game` over the action universe
`fun _ => A`.
Source: `references/udt101/01-story-so-far.md` lines 65–77 (udt-rep-2-018); FAF `Game.lean:43`
Kind: D
Fidelity: exact
Hyps: n/a -/
def instanceGame [Nonempty A] (U : Policy S A → ℝ) : SafeParetoImprovements.Game S (fun _ => A) where
  S _ := Finset.univ
  nonempty _ := Finset.univ_nonempty
  u a _ := U a

omit [DecidableEq S] in
/-- Every policy is a profile of the instance game.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_profiles_instanceGame [Nonempty A] (U : Policy S A → ℝ) (π : Policy S A) :
    π ∈ (instanceGame U).profiles := fun _ => Finset.mem_univ _

/-- The instance game in direct form: `strategy _ := A`, `payoff σ _ := U σ` (an EconCSLib
`StrategicGame` without the subtype coercion of FAF's `toStrategic`).
Source: mandate §3 ("the direct form … over which the equivalence is `Iff.rfl`")
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev directGame (U : Policy S A → ℝ) : StrategicGame S ℝ where
  strategy _ := A
  payoff σ _ := U σ

omit [Fintype A] in
/-- **T12(b), direct form.** `π` is a pure Nash equilibrium of the direct instance game iff it is a
local optimum of `U` (a UDT1.0 fixed point): unilateral deviation *is* one-situation modification.
Source: `references/udt101/01-story-so-far.md` lines 65–77 (udt-rep-2-018)
Kind: P
Fidelity: exact (the content is that `deviate` is `Function.update`)
Hyps: (a) none -/
theorem isNashEquilibrium_directGame_iff (U : Policy S A → ℝ) (π : Policy S A) :
    IsNashEquilibrium (directGame U) π ↔ IsLocalOptimum U π := by
  rw [isLocalOptimum_iff]
  simp only [IsNashEquilibrium, IsBestResponse, StrategicGame.deviate]

/-- **T12(b), FAF form.** `π`, as a profile of FAF's `(instanceGame U).toStrategic`, is a pure
Nash equilibrium (EconCSLib's `IsNashEquilibrium`) iff it is a local optimum of `U`. The
subtype coercion is pushed through `Function.update` by FAF's `ofStrategicProfile_deviate`.
Source: `references/udt101/01-story-so-far.md` lines 65–77 (udt-rep-2-018); FAF `Game.lean:156–200`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem isNashEquilibrium_instanceGame_iff [Nonempty A] (U : Policy S A → ℝ) (π : Policy S A) :
    IsNashEquilibrium (instanceGame U).toStrategic
        ((instanceGame U).toStrategicProfile π (mem_profiles_instanceGame U π)) ↔
      IsLocalOptimum U π := by
  rw [isLocalOptimum_iff]
  constructor
  · intro h s a
    have := h s ⟨a, Finset.mem_univ a⟩
    rw [SafeParetoImprovements.Game.toStrategic_payoff,
      SafeParetoImprovements.Game.toStrategic_payoff,
      SafeParetoImprovements.Game.ofStrategicProfile_deviate,
      SafeParetoImprovements.Game.ofStrategicProfile_toStrategicProfile] at this
    exact this
  · intro h i s'
    show (instanceGame U).toStrategic.payoff _ i ≤ (instanceGame U).toStrategic.payoff _ i
    rw [SafeParetoImprovements.Game.toStrategic_payoff,
      SafeParetoImprovements.Game.toStrategic_payoff,
      SafeParetoImprovements.Game.ofStrategicProfile_deviate,
      SafeParetoImprovements.Game.ofStrategicProfile_toStrategicProfile]
    exact h i s'

/-- The FAF-form and direct-form Nash predicates agree.
Source: mandate §3 (the ledger cites the FAF form, proofs compute with the direct one)
Kind: L
Fidelity: exact
Hyps: none -/
theorem isNashEquilibrium_instanceGame_iff_directGame [Nonempty A] (U : Policy S A → ℝ)
    (π : Policy S A) :
    IsNashEquilibrium (instanceGame U).toStrategic
        ((instanceGame U).toStrategicProfile π (mem_profiles_instanceGame U π)) ↔
      IsNashEquilibrium (directGame U) π := by
  rw [isNashEquilibrium_instanceGame_iff, isNashEquilibrium_directGame_iff]

/-- **T12(b).** The UDT1.1 optimum is a pure Nash equilibrium of the instance game (T2 read
through the bridge).
Source: `references/udt101/01-story-so-far.md` lines 65–77 (udt-rep-2-018)
Kind: L
Fidelity: exact
Hyps: (a) none beyond `IsOptimal U π` -/
theorem isNashEquilibrium_of_isOptimal [Nonempty A] {U : Policy S A → ℝ} {π : Policy S A}
    (h : IsOptimal U π) :
    IsNashEquilibrium (instanceGame U).toStrategic
      ((instanceGame U).toStrategicProfile π (mem_profiles_instanceGame U π)) :=
  (isNashEquilibrium_instanceGame_iff U π).mpr (isLocalOptimum_of_isOptimal h)

/-- **§5's exact characterization, recorded as the tautology it is.** `LocalGlobal U` says exactly
that every pure Nash equilibrium of the instance game is a welfare (common-payoff) optimum.
Source: [[udt-policy-calc-mandate]] §5
Kind: L
Fidelity: exact
Hyps: none -/
theorem localGlobal_iff_nash_optimal (U : Policy S A → ℝ) :
    LocalGlobal U ↔ ∀ π, IsNashEquilibrium (directGame U) π → IsOptimal U π := by
  simp only [LocalGlobal, isNashEquilibrium_directGame_iff]

end Games

/-- **T12(b), non-optimal Nash equilibria exist.** Coordinated Buttons: `const 0` is a pure Nash
equilibrium of the instance game (FAF form) and not optimal.
Source: `references/udt101/01-story-so-far.md` lines 71–73 ("there can be Nash equilibria that aren't globally optimal") (udt-rep-2-018, 003(a))
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem coordButtons_nash_not_optimal :
    IsNashEquilibrium (instanceGame coordButtons).toStrategic
        ((instanceGame coordButtons).toStrategicProfile ![0, 0]
          (mem_profiles_instanceGame coordButtons ![0, 0])) ∧
      ¬ IsOptimal coordButtons ![0, 0] :=
  ⟨(isNashEquilibrium_instanceGame_iff coordButtons ![0, 0]).mpr coordButtons_localOptimum,
    coordButtons_not_optimal⟩

end

end Cleanroom.Udt.UdtPolicyCalc
