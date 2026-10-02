import Cleanroom.Found.LiAsympCalc.Ramp

/-!
# D2, legality half: the doubly-soft gate is a `PGenerableWeighting`

The certificate that `dsFeature` is a ℙ-generable feature progression (FAF
`PGenerableWeighting`, `Properties/Calibration.lean`), built exactly as FAF's
`calibrationIndicator_pgenerable`: machine-metered price features (`MachineSpliceStream.serialize_price`
from `MachineSentenceCodes`), constant leaves, `add`, `mul`, `clip01`. Together with
`dsFeature_denote` (`Ramp.lean`) this closes, **in one market**, the "continuous ⟹ legal
trader" step that [[AUDIT]] §3.2 recorded as a modelling substitution: legality is
`EF`-expressibility plus generability, both now theorems about the construction; joint
continuity (`continuous_dsWeight`) is a *consequence* (`EF.continuous_denote`), not the
property itself. The cross-market residue — the corpus's `Ind_δ(a_n > t) · Ind_δ(E^H_n(X) < t-ε)`
mixes `A`'s quote with `H`'s expectation — is `li-quote-lane` target (4).

This file is allowed to import `Construction.*` (plan §0.5) but does not need to: every splice
lemma it uses is reachable through `Properties/Calibration.lean`.
-/

namespace Cleanroom.Found.LiAsympCalc

open LogicalInduction Filter Topology

/-- **`dsFeature` is ℙ-generable** (D2, legality): for machine-coded sentence sequences `φ ψ`
and constant rational parameters, `n ↦ dsFeature (φ n) (ψ n) t ε δ n` is a `PGenerableWeighting`
(FAF `def:ece` data: machine-metered serialization, rank `≤ n`, closed denotation). A
certificate assembled from FAF's `MachineSpliceStream.serialize_*` combinators along the same
spine as `calibrationIndicator_pgenerable`; graded `C` (composition of FAF's cited facts).
Source: [[faithful-acceleration]] §9; [[AUDIT]] §3.2; FAF `calibrationIndicator_pgenerable`
Kind: C
Fidelity: exact (one-market form)
Hyps: (a) none -/
theorem dsFeature_pgenerable (φ ψ : ℕ → Sentence) (hφ : MachineSentenceCodes φ)
    (hψ : MachineSentenceCodes ψ) (t ε δ : ℚ) :
    PGenerableWeighting (fun n => dsFeature (φ n) (ψ n) t ε δ n) := by
  have hpriceφ := MachineSpliceStream.serialize_price hφ UnaryRuler.id
    (MachineDigits.ofUnaryRuler UnaryRuler.id)
  have hpriceψ := MachineSpliceStream.serialize_price hψ UnaryRuler.id
    (MachineDigits.ofUnaryRuler UnaryRuler.id)
  have hinv := MachineSpliceStream.serialize_const (1 / δ)
  have hramp1 := MachineSpliceStream.serialize_clip01
    (MachineSpliceStream.serialize_mul
      (MachineSpliceStream.serialize_add hpriceφ
        (MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const (-1))
          (MachineSpliceStream.serialize_const t)))
      hinv)
  have hramp2 := MachineSpliceStream.serialize_clip01
    (MachineSpliceStream.serialize_mul
      (MachineSpliceStream.serialize_add (MachineSpliceStream.serialize_const (t - ε))
        (MachineSpliceStream.serialize_mul (MachineSpliceStream.serialize_const (-1)) hpriceψ))
      hinv)
  refine
    { polySeg := MachineSpliceStream.serialize_mul hramp1 hramp2
      rank_le := ?_
      closed := ?_ }
  · intro n
    simp [dsFeature, rampFeature]
  · intro n ρ V
    simp [dsFeature, rampFeature, clip01, efMin, EF.denoteWith, EF.denote]

/-- `dsFeature` is a `DivergentWeighting` in market `P` iff the doubly-soft weights of the
realized prices have divergent mass — the range half is a theorem (`dsFeature_mem_Icc`), the
divergence half is a genuine hypothesis about the market.
Source: [[li-asymp-calc-mandate]] D2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem dsFeature_divergentWeighting_iff (φ ψ : ℕ → Sentence) {t ε δ : ℚ} (hδ : 0 < δ)
    (P : History) :
    DivergentWeighting (fun n => dsFeature (φ n) (ψ n) t ε δ n) P ↔
      Tendsto (prefixSum (fun n => dsWeight t ε δ (P n (φ n)) (P n (ψ n)))) atTop atTop := by
  unfold DivergentWeighting
  simp only [dsFeature_denote _ _ hδ]
  exact ⟨fun h => h.2,
    fun h => ⟨fun n => ⟨dsWeight_nonneg _ _ _ _ _, dsWeight_le_one _ _ _ _ _⟩, h⟩⟩

end Cleanroom.Found.LiAsympCalc
