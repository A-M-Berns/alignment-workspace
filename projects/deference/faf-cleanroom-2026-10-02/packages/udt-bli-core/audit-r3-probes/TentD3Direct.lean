import Cleanroom.Bli.UdtBliCore

/-!
# `udt-bli-core` · audit round 3, adversarial lens · probe: what `Tent.d3_on_tent` adds

Not part of the library (never imported by it). Elaborated with `scripts/lean-check`.

Repair round 2 ships `Tent.d3_on_tent` (ledger: N+, "`CoordinationFreeExp` inhabited
non-degenerately on the tent skeleton, and Desideratum 3 is a real statement there"). Its
inhabitant is `tentEntangledExp := entangledExpOfPolicyLevel hR hL`, the empty-map structure that
*every* `ReflectivePolicy ∧ LocalUtility` prior carries, and its coordination-freeness is
`∀ T, ∅ ⊆ {T} ∧ ∅ = ∅`. This probe records that

1. the coordination-freeness clause is closed by the same two-token term for every prior
   (`cf_is_trivial`), and
2. the middle conjunct (one-step = updateful at every tent table) is one line from
   `tentPrior_structure` and `oneStep_iff_updateful`, without any entanglement structure
   (`d3_direct`).

So the N+ content of the row is `tentPrior_structure`'s `ReflectivePolicy ∧ LocalUtility` plus
`tentPrior_varying`, already in the ledger; `EntangledExp` adds a name, not a check.
-/

namespace AuditR3

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.FiniteBLIPrior
  Cleanroom.Bli.UdtBliCore.Tent Finset

namespace TentD3

/-- Coordination-freeness of the empty-map structure is the same closed term on every prior. -/
theorem cf_is_trivial {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {A : Type}
    [DecidableEq A] [Fintype A] (P : FiniteBLIPrior 𝒮 m 𝒟 A) (hR : P.ReflectivePolicy)
    (hL : P.LocalUtility) : P.CoordinationFreeExp (P.entangledExpOfPolicyLevel hR hL) :=
  fun _ => ⟨Finset.empty_subset _, rfl⟩

/-- `Tent.d3_on_tent`'s middle conjunct without any entanglement structure. -/
theorem d3_direct :
    ∀ (T : ↥(grid witIndex witMesh.d 1)) (a : Bool),
      (tentPrior.IsOneStepChoice T a ↔ tentPrior.IsUpdatefulChoice T a) := by
  obtain ⟨hR, hN, _, _, _, _, _, hpol, _, _⟩ := tentPrior_structure
  intro T a
  exact tentPrior.oneStep_iff_updateful hpol hR hN T (by rw [stateMass_tentPrior]; norm_num) a

/-- The whole of `d3_on_tent` from the package's earlier rows and `cf_is_trivial`. -/
theorem d3_on_tent_again :
    tentPrior.CoordinationFreeExp tentEntangledExp ∧
      (∀ (T : ↥(grid witIndex witMesh.d 1)) (a : Bool),
        (tentPrior.IsOneStepChoice T a ↔ tentPrior.IsUpdatefulChoice T a)) ∧
      tentPrior.IsOneStepChoice Tone true ∧ ¬ tentPrior.IsOneStepChoice Tone false ∧
      tentPrior.IsOneStepChoice Tzero false ∧ ¬ tentPrior.IsOneStepChoice Tzero true := by
  obtain ⟨h1, h2, h3, h4, _⟩ := tentPrior_varying
  exact ⟨cf_is_trivial _ _ _, d3_direct, (d3_direct _ _).mpr h1, fun h => h2 ((d3_direct _ _).mp h),
    (d3_direct _ _).mpr h3, fun h => h4 ((d3_direct _ _).mp h)⟩

end TentD3

end AuditR3
