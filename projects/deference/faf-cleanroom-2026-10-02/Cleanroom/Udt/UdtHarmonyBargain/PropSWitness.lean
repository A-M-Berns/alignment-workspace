import Cleanroom.Udt.UdtHarmonyBargain.PropS
import Cleanroom.Udt.UdtHarmonyBargain.Existence
import Cleanroom.Udt.UdtHarmonyBargain.Translation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# `udt-harmony-bargain` — Proposition S: existence (T7(b)), the Stag Hunt (N+), the constant game
(N−), and Theorem H′(b′) on trees (T8(b′))

* `exists_harmonious_optimum`: some optimum is the outcome of a support profile of a
  trembling-hand equilibrium (T6 + Proposition S(a)) — Thm 13.1(2)'s existence clause, in the only
  form available (the limit may be mixed).
* **Stag Hunt** (`V(S,S) = 2`, `V(H,H) = 1`, else `0`; no safe batna): every support outcome of every
  trembling-hand equilibrium is `(S,S)` (`stag_outcome_eq_SS`), trembling-hand equilibria exist,
  while `(H,H)` is a pure Nash equilibrium of the *action* game (`HH_nash_actionGame`) and never a
  harmonious outcome of the bargaining game (HA-6′: Definition 22 ≠ harmony).
* **Constant game** (`V ≡ 0`): every pure profile is harmonious and every outcome optimal — the
  optimality theorem is not an artifact of an over-strong `THPE`.
* **Trees** (T8(b′)): in the homogeneous game of any tree every harmonious outcome is
  `V_B`-optimal, and a `V_B`-optimal pure profile exists (`dp-core-tree`'s `exists_pure_max_value'`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtHarmonyBargain

open Finset SafeParetoImprovements StrategicGame
open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree

section General

variable {N : Type} [Fintype N] [DecidableEq N] [Nonempty N]
variable {A : N → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)] [∀ i, Nonempty (A i)]

/-- The strategy types of a bridged FAF game are nonempty (its action sets are).
Source: none: infrastructure
Kind: D -/
instance instNonemptyToStrategicStrategy (Γ : Game N A) (i : N) :
    Nonempty (Γ.toStrategic.strategy i) :=
  ⟨⟨(Γ.nonempty i).choose, (Γ.nonempty i).choose_spec⟩⟩

variable {V : Outcome A → ℝ} {sel : Finset (Outcome A) → Outcome A} {W : Outcome A → ℝ}

/-- **Proposition S(b)**: some `V`-optimal outcome is realised by a support profile of a
trembling-hand equilibrium of the homogeneous bargaining game (Thm 13.1(2)'s existence clause, in
the support form; the equilibrium may be mixed).
Source: [[superconditioning-mismatched-ontologies]] §13.1 Thm 13.1(2) ("`O*` is itself harmonious");
HA-5′; mandate T7(b)
Kind: C
Fidelity: weaker: support form (no pure trembling-hand equilibrium is claimed to exist)
Hyps: (a) all -/
theorem exists_harmonious_optimum (hW : IsWelfareSel (commonGame V) sel W) :
    ∃ (p : MixedProfile (BG V sel)) (τ : (BG V sel).Profile), THPE p ∧ 0 < profWeight p τ ∧
      IsOpt V (outcome sel ((bargain (commonGame V) sel).ofStrategicProfile τ)) := by
  obtain ⟨p, hp⟩ := exists_thpe (G := BG V sel)
  -- some profile has positive weight (the weights sum to one)
  have hex : ∃ τ : (BG V sel).Profile, 0 < profWeight p τ := by
    by_contra h
    push_neg at h
    have h0 : ∑ τ : (BG V sel).Profile, profWeight p τ = 0 :=
      sum_eq_zero fun τ _ => le_antisymm (h τ) (profWeight_nonneg p τ)
    rw [sum_profWeight] at h0
    exact one_ne_zero h0
  obtain ⟨τ, hτ⟩ := hex
  exact ⟨p, τ, hp, hτ, harmonious_subset_optimal hW hp τ hτ⟩

/-- **Encoding check (N−)**: in the constant game every pure profile is harmonious and every
outcome is optimal — Proposition S(a) is not an artifact of an over-strong `THPE`.
Source: mandate T7 ("N−/encoding check for (a)")
Kind: N-
Fidelity: n/a -/
theorem constant_game_all_harmonious (sel : Finset (Outcome A) → Outcome A)
    (σ : ∀ i, Proposal A i) :
    HarmoniousPure (commonGame (fun _ => (0 : ℝ))) sel σ ∧ IsOpt (fun _ => (0 : ℝ)) (outcome sel σ) := by
  refine ⟨?_, fun _ => le_refl _⟩
  apply thpe_of_dominant
  intro i s τ
  rw [bargain_payoff, bargain_payoff, commonGame_u, commonGame_u]

end General

/-! ### The Stag Hunt -/

namespace StagHunt

/-- Two players, actions `Bool` (`true` = stag `S`, `false` = hare `H`).
Source: mandate T7 (N+ witness); HA-6′
Kind: D -/
abbrev Act : Fin 2 → Type := fun _ => Bool

/-- `(S, S)`. Source: mandate T7. Kind: D -/
def SS : Outcome Act := ![true, true]
/-- `(H, H)`. Source: mandate T7. Kind: D -/
def HH : Outcome Act := ![false, false]

theorem out_cases (O : Outcome Act) :
    O = SS ∨ O = HH ∨ O = ![true, false] ∨ O = ![false, true] := by revert O; decide

/-- The Stag Hunt payoff: `2` at `(S,S)`, `1` at `(H,H)`, else `0`.
Source: mandate T7; HA-6′
Kind: D -/
noncomputable def V (O : Outcome Act) : ℝ := if O = SS then 2 else if O = HH then 1 else 0

theorem V_SS : V SS = 2 := by unfold V; simp
theorem V_HH : V HH = 1 := by unfold V; simp [HH, SS]
theorem V_le (O : Outcome Act) : V O ≤ 2 := by unfold V; split_ifs <;> norm_num
theorem V_le_one_of_ne {O : Outcome Act} (h : O ≠ SS) : V O ≤ 1 := by
  unfold V; rw [if_neg h]; split_ifs <;> norm_num

/-- The unique optimum is `(S,S)`. Source: mandate T7. Kind: L -/
theorem isOpt_iff (O : Outcome Act) : IsOpt V O ↔ O = SS := by
  constructor
  · intro h
    by_contra hne
    have := h SS
    rw [V_SS] at this
    linarith [V_le_one_of_ne hne]
  · rintro rfl O'
    rw [V_SS]; exact V_le O'

/-- No batna is safe in the Stag Hunt.
Source: mandate T7 ("no safe batna")
Kind: L -/
theorem no_safe_batna : ∀ (j : Fin 2) (b : Bool), ¬ Safe V j b := by
  intro j b h
  unfold Safe at h
  fin_cases j <;> cases b
  · have := (isOpt_iff _).mp (h ![false, true] rfl); exact absurd this (by decide)
  · have := (isOpt_iff _).mp (h ![true, false] rfl); exact absurd this (by decide)
  · have := (isOpt_iff _).mp (h ![true, false] rfl); exact absurd this (by decide)
  · have := (isOpt_iff _).mp (h ![false, true] rfl); exact absurd this (by decide)

/-- **The unique harmonious outcome of the Stag Hunt is `(S,S)`**: every support profile of every
trembling-hand equilibrium of the bargaining game, under every welfare rule, realises `(S,S)`
(Proposition S(c)); such equilibria exist (`exists_thpe`).
Source: mandate T7 (N+ witness for (a)/(c)); HA-5′, HA-6′
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem stag_outcome_eq_SS (sel : Finset (Outcome Act) → Outcome Act) (W : Outcome Act → ℝ)
    (hW : IsWelfareSel (commonGame V) sel W) {p : MixedProfile (BG V sel)} (hp : THPE p)
    (τ : (BG V sel).Profile) (hτ : 0 < profWeight p τ) :
    outcome sel ((bargain (commonGame V) sel).ofStrategicProfile τ) = SS :=
  (isOpt_iff _).mp (unique_without_safe_batna hW no_safe_batna hp τ hτ).2.1

/-- Trembling-hand equilibria of the Stag Hunt bargaining game exist (so the uniqueness claim is not
vacuous).
Source: mandate T7; T6
Kind: N+ -/
theorem stag_exists_thpe (sel : Finset (Outcome Act) → Outcome Act) :
    ∃ p : MixedProfile (BG V sel), THPE p :=
  exists_thpe

/-- `(H,H)` as a profile of the strategic action game.
Source: mandate T7 (HA-6′)
Kind: D -/
def HHstrat : (commonGame V).toStrategic.Profile := fun _ => ⟨false, mem_univ _⟩

/-- **`(H,H)` is a pure Nash equilibrium of the action game** (Definition 22's notion) …
Source: mandate T7; HA-6′ ("Definition 22 ≠ harmony")
Kind: L -/
theorem HH_nash_actionGame : IsNashEquilibrium (commonGame V).toStrategic HHstrat := by
  intro i s'
  show V (fun j => ((Function.update HHstrat i s') j : Bool)) ≤ V (fun j => (HHstrat j : Bool))
  have hHH : (fun j => (HHstrat j : Bool)) = HH := by funext j; fin_cases j <;> rfl
  rw [hHH, V_HH]
  apply V_le_one_of_ne
  intro h
  obtain ⟨j0, hj0⟩ : ∃ j0 : Fin 2, j0 ≠ i := by
    fin_cases i
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
  have := congrFun h j0
  simp only [Function.update_of_ne hj0] at this
  have h1 : (HHstrat j0 : Bool) = false := rfl
  have h2 : SS j0 = true := by fin_cases j0 <;> rfl
  rw [h1, h2] at this
  exact Bool.false_ne_true this

/-- … but never a harmonious outcome of the bargaining game (HA-6′: Definition 22 ≠ harmony).
Source: mandate T7; HA-6′
Kind: C -/
theorem HH_not_harmonious (sel : Finset (Outcome Act) → Outcome Act) (W : Outcome Act → ℝ)
    (hW : IsWelfareSel (commonGame V) sel W) {p : MixedProfile (BG V sel)} (hp : THPE p)
    (τ : (BG V sel).Profile) (hτ : 0 < profWeight p τ) :
    outcome sel ((bargain (commonGame V) sel).ofStrategicProfile τ) ≠ HH := by
  rw [stag_outcome_eq_SS sel W hW hp τ hτ]
  decide

end StagHunt

/-! ### Theorem H′(b′): trees -/

section Trees

variable {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
  [DecidableEq ι] [∀ d, Nonempty (acts d)]

/-- **Theorem H′(b′), pure grade**: in the homogeneous game of a tree with at least one queried
point, every support outcome of every trembling-hand equilibrium (under any welfare rule) is
`V_B`-optimal among pure profiles.
Source: `repair/harmony.md` HA-12′(a),(b) (pure grade); [[superconditioning-mismatched-ontologies]]
§13.2 Remark 13.2 (first half); mandate T8(a),(b′)
Kind: C
Fidelity: exact (pure / shared-seed grade)
Hyps: (a) all -/
theorem homogeneousGame_harmonious_isOpt (B : Tree Ω ι acts ℚ) [Nonempty ↥(queried B)]
    (sel : Finset ((d : ↥(queried B)) → acts d) → ((d : ↥(queried B)) → acts d))
    (W : ((d : ↥(queried B)) → acts d) → ℝ) :
    ∀ (_hW : IsWelfareSel (homogeneousGame B) sel W)
      (p : MixedProfile (bargain (homogeneousGame B) sel).toStrategic) (_hp : THPE p)
      (τ : (bargain (homogeneousGame B) sel).toStrategic.Profile) (_hτ : 0 < profWeight p τ),
      IsOpt (treeValue B) (outcome sel ((bargain (homogeneousGame B) sel).ofStrategicProfile τ)) := by
  rw [homogeneousGame_eq_commonGame]
  intro hW p hp τ hτ
  exact harmonious_subset_optimal hW hp τ hτ

/-- A `V_B`-optimal pure profile exists (Remark 13.2's "not updating attains it", pure grade), from
`dp-core-tree`'s `exists_pure_max_value'`.
Source: `repair/harmony.md` HA-12′(b); mandate T8(b′)
Kind: C -/
theorem exists_isOpt_treeValue (B : Tree Ω ι acts ℚ) :
    ∃ O : (d : ↥(queried B)) → acts d, IsOpt (treeValue B) O := by
  obtain ⟨π, -, hπ, -⟩ := exists_pure_max_value' B
  refine ⟨fun d => π d, fun O => ?_⟩
  unfold treeValue
  rw [Rat.cast_le]
  have h1 : value (Proc.ofFun (extendQ B fun d => π d)) B = value (Proc.ofFun π) B := by
    refine value_congr_queried B fun d hd => ?_
    show FinDistr.pure (extendQ B (fun d => π d) d) = FinDistr.pure (π d)
    rw [extendQ_of_mem B _ hd]
  rw [h1]
  exact hπ _

end Trees

end Cleanroom.Udt.UdtHarmonyBargain
