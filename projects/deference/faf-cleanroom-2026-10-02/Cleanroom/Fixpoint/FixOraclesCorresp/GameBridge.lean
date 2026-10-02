import Cleanroom.Fixpoint.FixOraclesCorresp.NashReflective

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.GameBridge`: the FAF-form bridge for mixed Nash

The definition of record for a finite two-action game is FAF's `twoActionFAF u :
SafeParetoImprovements.Game N (fun _ => Fin 2)` with every action set `univ`; the proofs compute with
the direct `twoActionGame u`. This file is the `L` bridge for *mixed* profiles (the `udt-policy-calc`
pattern, which bridged pure Nash): `toFAFProfile` transports a mixed profile of the direct game to one
of `(twoActionFAF u).toStrategic` (whose strategy types are the subtypes `↥(univ : Finset (Fin 2))`),
expected payoffs and deviations agree, and `IsMixedNashEq` agrees (`isMixedNashEq_twoActionFAF_iff`).
So every headline stated over `twoActionGame u` holds verbatim for the FAF-form game.
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set StrategicGame

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- A mixed profile of the direct game, as a mixed profile of the FAF-form game's `toStrategic`.
Source: FAF `SafeParetoImprovements/Game.lean:156` (`toStrategic`); mandate target 13 (definition of
record)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def toFAFProfile (u : (N → Fin 2) → N → ℝ) (σ : MixedProfile (twoActionGame u)) :
    MixedProfile (twoActionFAF u).toStrategic := fun i =>
  ⟨fun s => (σ i).val s.1, ⟨fun s => (σ i).2.1 s.1, by
    show ∑ s : ↥(Finset.univ : Finset (Fin 2)), (σ i).val ↑s = 1
    rw [Finset.sum_coe_sort (Finset.univ : Finset (Fin 2)) (fun s => (σ i).val s)]
    exact (σ i).2.2⟩⟩

/-- The equivalence between FAF-form pure profiles and direct pure profiles.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def profileEquiv (u : (N → Fin 2) → N → ℝ) : (twoActionFAF u).toStrategic.Profile ≃ (N → Fin 2) :=
  Equiv.piCongrRight fun _ => Equiv.subtypeUnivEquiv fun _ => Finset.mem_univ _

/-- Expected payoffs agree across the bridge.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem expectedPayoff_toFAFProfile (u : (N → Fin 2) → N → ℝ) (σ : MixedProfile (twoActionGame u))
    (j : N) :
    expectedPayoff (twoActionFAF u).toStrategic (toFAFProfile u σ) j =
      expectedPayoff (twoActionGame u) σ j := by
  unfold expectedPayoff
  exact Fintype.sum_equiv (profileEquiv u) _ _ fun τ => rfl

omit [Fintype N] in
/-- Deviations agree across the bridge.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem toFAFProfile_deviateMixed (u : (N → Fin 2) → N → ℝ) (σ : MixedProfile (twoActionGame u))
    (i : N) (s : (twoActionFAF u).toStrategic.strategy i) :
    deviateMixed (twoActionFAF u).toStrategic (toFAFProfile u σ) i s =
      toFAFProfile u (deviateMixed (twoActionGame u) σ i s.1) := by
  funext j
  by_cases h : j = i
  · subst h
    apply Subtype.ext
    funext t
    simp only [deviateMixed, Function.update_self, toFAFProfile]
    show (if t = s then (1 : ℝ) else 0) = if t.1 = s.1 then 1 else 0
    by_cases ht : t = s
    · subst ht; simp
    · rw [if_neg ht, if_neg (fun h => ht (Subtype.ext h))]
  · simp [deviateMixed, Function.update_of_ne h, toFAFProfile]

/-- **The bridge**: a mixed profile of the direct two-action game is a mixed Nash equilibrium iff its
transport is a mixed Nash equilibrium of FAF's `(twoActionFAF u).toStrategic`. Every headline of
`NashReflective.lean`, `PenniesGadget.lean` and `GameR.lean` therefore holds for the FAF-form game of
record.
Source: mandate target 13 ("the FAF form … the ledger cites the FAF form, proofs compute with the
direct one")
Kind: L
Fidelity: exact
Hyps: none -/
theorem isMixedNashEq_twoActionFAF_iff (u : (N → Fin 2) → N → ℝ)
    (σ : MixedProfile (twoActionGame u)) :
    IsMixedNashEq (twoActionFAF u).toStrategic (toFAFProfile u σ) ↔
      IsMixedNashEq (twoActionGame u) σ := by
  unfold IsMixedNashEq
  constructor
  · intro h who s
    have := h who ⟨s, Finset.mem_univ _⟩
    rwa [toFAFProfile_deviateMixed, expectedPayoff_toFAFProfile, expectedPayoff_toFAFProfile] at this
  · intro h who s
    rw [toFAFProfile_deviateMixed, expectedPayoff_toFAFProfile, expectedPayoff_toFAFProfile]
    exact h who s.1

end Cleanroom.Fixpoint.FixOraclesCorresp
