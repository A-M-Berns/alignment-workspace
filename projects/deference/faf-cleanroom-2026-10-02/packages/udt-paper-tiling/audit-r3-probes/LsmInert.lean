import Cleanroom.Udt.UdtPaperTiling.Vingean

/-!
Audit round 3, adversarial lens — probe for `thm3_vingean_tiling` and `thm4_appendixA_tiling`
(T5, load-bearing 2): the `LimitedSelfMod` hypothesis is inert.

Both theorems take `L : LimitedSelfMod S` but use only the *data* `L.ob` and `L.ac`; none of
`mod_eq` ("exactly one policy-point"), `ac_nonMod` ("the forced action is non-modifying") or
`not_self` ("an action can't modify its own policy-point") is used. The two theorems below are the
same statements with `ob : Act → ↥𝒟` and `ac : Act → Act` arbitrary functions and Fine-Grained
Fairness restated over them; the proofs are the library's, verbatim. In the paper, `not_self` is
what makes `o ≠ ob aₘ`, which the quantified forms of Faith in Joint Argmax and Action
Coordination (`∀ o ≠ o'`) need before they can be instantiated at `(o, ob aₘ)`; the package takes
the instances directly, so nothing of LSM is load-bearing in the Lean. Not imported by the
library.
-/

namespace Cleanroom.Udt.UdtPaperTiling.AuditR3Adv

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
  [DecidableEq Act] {P : FiniteBLIPrior 𝒮 m 𝒟 Act}

/-- Theorem 3 with `ob`/`ac` arbitrary functions: the body of `thm3_vingean_tiling` verbatim. -/
theorem thm3_raw (S : PaperStructure 𝒟 Act) (ob : Act → ↥𝒟) (ac : Act → Act) (V : ArgmaxVars P)
    (hFGF : ∀ o, ∀ aₘ ∈ S.Aof o, aₘ ∈ S.selfMod → 0 < P.ppMass o aₘ →
      0 < P.pairMass o (ob aₘ) (S.twin aₘ) (ac aₘ) →
      P.EU o aₘ = cellEU P o (ob aₘ) (S.twin aₘ) (ac aₘ))
    (o : ↥𝒟) (aₘ : Act) (haₘ : aₘ ∈ S.Aof o) (hm : aₘ ∈ S.selfMod) (hpos : 0 < P.ppMass o aₘ)
    (hcell : 0 < P.pairMass o (ob aₘ) (S.twin aₘ) (ac aₘ))
    (hFJA : FaithInJointArgmaxAt V (S.nonModAt o) o (ob aₘ))
    (hAC : ActionCoordination V (S.nonModAt o) o (ob aₘ))
    (hKDP : KnowledgeOfDecisionProcedure V (ob aₘ)) :
    ∃ a ∈ S.Aof o, a ∉ S.selfMod ∧ 0 < P.ppMass o a ∧ P.EU o aₘ ≤ P.EU o a := by
  have h1 : P.EU o aₘ = cellEU P o (ob aₘ) (S.twin aₘ) (ac aₘ) := hFGF o aₘ haₘ hm hpos hcell
  have htwin : S.twin aₘ ∈ S.nonModAt o := by
    rw [S.mem_nonModAt]
    exact ⟨S.twin_typed aₘ o haₘ, S.twin_nonMod aₘ⟩
  obtain ⟨b, hb, hbpos, hble⟩ := hFJA (ac aₘ) (S.twin aₘ) htwin hcell
  obtain ⟨hmass₁, hval₁⟩ := ac_step V hAC b
  obtain ⟨hmass₂, hval₂⟩ := kdp_step V hKDP o b
  rw [S.mem_nonModAt] at hb
  refine ⟨b, hb.1, hb.2, ?_, ?_⟩
  · rw [← hmass₂, ← hmass₁]; exact hbpos
  · rw [h1, ← hval₂, ← hval₁]; exact hble

/-- Theorem 4 with `ob`/`ac` arbitrary functions: the body of `thm4_appendixA_tiling` verbatim. -/
theorem thm4_raw (S : PaperStructure 𝒟 Act) (ob : Act → ↥𝒟) (ac : Act → Act) (V : ArgmaxVars P)
    (hFGF : ∀ o, ∀ aₘ ∈ S.Aof o, aₘ ∈ S.selfMod → 0 < P.ppMass o aₘ →
      0 < P.pairMass o (ob aₘ) (S.twin aₘ) (ac aₘ) →
      P.EU o aₘ = cellEU P o (ob aₘ) (S.twin aₘ) (ac aₘ))
    (o : ↥𝒟) (aₘ : Act) (haₘ : aₘ ∈ S.Aof o) (hm : aₘ ∈ S.selfMod) (hpos : 0 < P.ppMass o aₘ)
    (hcell : 0 < P.pairMass o (ob aₘ) (S.twin aₘ) (ac aₘ))
    (hFA : FaithInArgmax V (ob aₘ) o (S.twin aₘ))
    (hNAC : NaiveActionCoordination S V (ob aₘ) o (S.twin aₘ))
    (hKDP : KnowledgeOfDecisionProcedure V (ob aₘ)) :
    0 < P.ppMass o (S.twin aₘ) ∧ P.EU o aₘ ≤ P.EU o (S.twin aₘ) := by
  have h1 : P.EU o aₘ = cellEU P o (ob aₘ) (S.twin aₘ) (ac aₘ) := hFGF o aₘ haₘ hm hpos hcell
  obtain ⟨hCpos, hCle⟩ := hFA (ac aₘ) hcell
  obtain ⟨hmass₁, hval₁⟩ := nac_step S V (S.twin_nonMod aₘ) hNAC
  obtain ⟨hmass₂, hval₂⟩ := kdp_step V hKDP o (S.twin aₘ)
  refine ⟨?_, ?_⟩
  · rw [← hmass₂, ← hmass₁]; exact hCpos
  · rw [h1, ← hval₂, ← hval₁]; exact hCle

end Cleanroom.Udt.UdtPaperTiling.AuditR3Adv
