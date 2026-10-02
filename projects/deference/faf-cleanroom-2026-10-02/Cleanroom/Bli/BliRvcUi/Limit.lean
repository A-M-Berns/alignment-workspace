import LogicalInduction.Properties.LimitCoherence
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Properties.NonDogmatism

/-!
# `bli-rvc-ui` · Limit: semantic monotonicity of the limiting belief

**The lemma every limit statement of this package rests on.** FAF's `GaifmanCoherent.mono` gives
`P∞ φ ≤ P∞ ψ` only for a *tautological* implication (every world). The universal-instantiation and
threshold-monotonicity facts of this package hold only in **completed-theory** worlds
(`ConsistentWithTheory DP`), so what is needed is:

* `limitingBelief_le_of_theory_imp`: if every completed-theory world holding `φ` holds `ψ`, then
  `P∞ φ ≤ P∞ ψ`. Route: `P∞(φ ⋏ ∼ψ) = 0` by `lic_provind_false` on the constant family (the
  conjunction is refuted in every completed world), then the Gaifman split
  `P∞ φ = P∞(φ ⋏ ψ) + P∞(φ ⋏ ∼ψ)` and `P∞(φ ⋏ ψ) ≤ P∞ ψ` (tautological).
* `limitingBelief_eq_one_of_theory` / `_eq_zero_of_theory`: semantic versions of FAF's
  `lic_limitingBelief_theorem` / `_refutable` (which ask for stage membership).
* `limitingBelief_le_of_eventually_le` / `_ge_of_eventually_ge`: read an eventual price bound at the
  limit.

No hypothesis beyond `[IsLogicalInductor P DP]` and FAF's `hworld` (every stage has a consistent
world); the e.c. certificate is `MachineSentenceCodes.const`.
-/

namespace Cleanroom.Bli.BliRvcUi

open LogicalInduction LO.Propositional Filter Topology

variable {P : History} {DP : DeductiveProcess} [IsLogicalInductor P DP]
  (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n))
include hworld

/-- A sentence holding in every completed-theory world has limiting belief `1` (semantic form of
FAF's `lic_limitingBelief_theorem`, which asks for stage membership).
Source: FAF `lic_provind_true` (constant family), `lic_limitingBelief_tendsto`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem limitingBelief_eq_one_of_theory {φ : Sentence}
    (h : ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds φ) : limitingBelief P φ = 1 := by
  have hone := lic_provind_true P DP (fun _ => φ) (MachineSentenceCodes.const φ)
    (fun _ v hv => h v hv) hworld
  have ht : ConvergesTo (fun n => P n φ) 1 := convergesTo_iff_asympEq_const.mpr hone
  exact tendsto_nhds_unique (lic_limitingBelief_tendsto P DP hworld φ) ht

/-- A sentence failing in every completed-theory world has limiting belief `0`.
Source: FAF `lic_provind_false` (constant family), `lic_limitingBelief_tendsto`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem limitingBelief_eq_zero_of_theory {φ : Sentence}
    (h : ∀ v : PCWorld, v.ConsistentWithTheory DP → ¬ v.Holds φ) : limitingBelief P φ = 0 := by
  have hzero := lic_provind_false P DP (fun _ => φ) (MachineSentenceCodes.const φ)
    (fun _ v hv => (PCWorld.holds_neg v φ).mpr (h v hv)) hworld
  have ht : ConvergesTo (fun n => P n φ) 0 := convergesTo_iff_asympEq_const.mpr hzero
  exact tendsto_nhds_unique (lic_limitingBelief_tendsto P DP hworld φ) ht

/-- **Semantic monotonicity of the limiting belief**: if every completed-theory world holding `φ`
holds `ψ`, then `P∞ φ ≤ P∞ ψ`. (FAF's `GaifmanCoherent.mono` needs the implication in *every*
world; this is the completed-theory form.)
Source: none: infrastructure (FAF `lic_limitingBelief_gaifman`, `lic_provind_false`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem limitingBelief_le_of_theory_imp {φ ψ : Sentence}
    (h : ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds φ → v.Holds ψ) :
    limitingBelief P φ ≤ limitingBelief P ψ := by
  have hG := lic_limitingBelief_gaifman P DP hworld
  have hzero : limitingBelief P (φ ⋏ ∼ψ) = 0 :=
    limitingBelief_eq_zero_of_theory hworld fun v hv hh =>
      ((PCWorld.holds_neg v ψ).mp hh.2) (h v hv hh.1)
  have hsplit : limitingBelief P ((φ ⋏ ψ) ⋎ (φ ⋏ ∼ψ)) =
      limitingBelief P (φ ⋏ ψ) + limitingBelief P (φ ⋏ ∼ψ) :=
    hG.disjoint_add fun v hv => ((PCWorld.holds_neg v ψ).mp hv.2.2) hv.1.2
  have hcongr : limitingBelief P ((φ ⋏ ψ) ⋎ (φ ⋏ ∼ψ)) = limitingBelief P φ :=
    hG.congr fun v => by
      rw [PCWorld.holds_or, PCWorld.holds_and, PCWorld.holds_and, PCWorld.holds_neg]
      constructor
      · rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> exact h1
      · intro h1
        by_cases hψ : v.Holds ψ
        · exact Or.inl ⟨h1, hψ⟩
        · exact Or.inr ⟨h1, hψ⟩
  have hmono : limitingBelief P (φ ⋏ ψ) ≤ limitingBelief P ψ :=
    hG.mono fun v hv => hv.2
  linarith

/-- An eventual upper bound on the prices bounds the limiting belief.
Source: FAF `lic_limitingBelief_tendsto`
Kind: L
Fidelity: n/a -/
theorem limitingBelief_le_of_eventually_le {φ : Sentence} {c : ℝ}
    (h : ∀ᶠ n in atTop, P n φ ≤ c) : limitingBelief P φ ≤ c :=
  le_of_tendsto (lic_limitingBelief_tendsto P DP hworld φ) h

/-- An eventual lower bound on the prices bounds the limiting belief from below.
Source: FAF `lic_limitingBelief_tendsto`
Kind: L
Fidelity: n/a -/
theorem limitingBelief_ge_of_eventually_ge {φ : Sentence} {c : ℝ}
    (h : ∀ᶠ n in atTop, c ≤ P n φ) : c ≤ limitingBelief P φ :=
  ge_of_tendsto (lic_limitingBelief_tendsto P DP hworld φ) h

/-- The limiting belief lies in `[0,1]`.
Source: FAF `lic_limitingBelief_gaifman` (`mem_Icc`)
Kind: L
Fidelity: n/a -/
theorem limitingBelief_mem_Icc (φ : Sentence) :
    0 ≤ limitingBelief P φ ∧ limitingBelief P φ ≤ 1 :=
  (lic_limitingBelief_gaifman P DP hworld).mem_Icc φ

/-- **Non-dogmatism at the limit, dual direction**: if every stage admits a consistent world
failing `φ`, the limiting belief of `φ` is strictly below `1`.
Source: FAF `lic_nonDogmatism_dual`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem limitingBelief_lt_one_of_nonDogmatism {φ : Sentence}
    (hφ : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds φ) :
    limitingBelief P φ < 1 := by
  obtain ⟨ε, hε, hev⟩ := lic_nonDogmatism_dual P DP φ hφ
  have := limitingBelief_le_of_eventually_le hworld hev
  linarith

/-- **Non-dogmatism at the limit, positive direction**: if every stage admits a consistent world
holding `φ`, the limiting belief of `φ` is strictly positive.
Source: FAF `lic_nonDogmatism`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem limitingBelief_pos_of_nonDogmatism {φ : Sentence}
    (hφ : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds φ) :
    0 < limitingBelief P φ := by
  obtain ⟨ε, hε, hev⟩ := lic_nonDogmatism P DP φ hφ
  have := limitingBelief_ge_of_eventually_ge hworld hev
  linarith

/-- **Strict semantic monotonicity**: if every completed-theory world holding `φ` holds `ψ`, and
every stage admits a consistent world holding `ψ` but not `φ`, then `P∞ φ < P∞ ψ`. The gap is
`P∞(ψ ⋏ ∼φ) > 0` (non-dogmatism); the schema half is `P∞(φ ⋏ ∼ψ) = 0` (inside
`limitingBelief_le_of_theory_imp`). Added in repair round 1 for the free-instance UI witness.
Source: none: infrastructure (FAF `lic_limitingBelief_gaifman`, `lic_nonDogmatism`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem limitingBelief_lt_of_theory_imp {φ ψ : Sentence}
    (h : ∀ v : PCWorld, v.ConsistentWithTheory DP → v.Holds φ → v.Holds ψ)
    (hsep : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds (ψ ⋏ ∼φ)) :
    limitingBelief P φ < limitingBelief P ψ := by
  have hG := lic_limitingBelief_gaifman P DP hworld
  have hle : limitingBelief P φ ≤ limitingBelief P (ψ ⋏ φ) :=
    limitingBelief_le_of_theory_imp hworld fun v hv hφ =>
      (PCWorld.holds_and v ψ φ).mpr ⟨h v hv hφ, hφ⟩
  have hpos : 0 < limitingBelief P (ψ ⋏ ∼φ) := limitingBelief_pos_of_nonDogmatism hworld hsep
  have hsplit : limitingBelief P ((ψ ⋏ φ) ⋎ (ψ ⋏ ∼φ)) =
      limitingBelief P (ψ ⋏ φ) + limitingBelief P (ψ ⋏ ∼φ) :=
    hG.disjoint_add fun v hv => ((PCWorld.holds_neg v φ).mp hv.2.2) hv.1.2
  have hcongr : limitingBelief P ((ψ ⋏ φ) ⋎ (ψ ⋏ ∼φ)) = limitingBelief P ψ :=
    hG.congr fun v => by
      rw [PCWorld.holds_or, PCWorld.holds_and, PCWorld.holds_and, PCWorld.holds_neg]
      constructor
      · rintro (⟨h1, -⟩ | ⟨h1, -⟩) <;> exact h1
      · intro h1
        by_cases hφ : v.Holds φ
        · exact Or.inl ⟨h1, hφ⟩
        · exact Or.inr ⟨h1, hφ⟩
  linarith

/-- **Believed in the limit means decided by the process**: if `P∞ φ = 1`, some stage already
forces `φ` (every world consistent with that stage holds it) — the contrapositive of
non-dogmatism. This is the observation behind finding F-19: any family whose instances all have
limiting belief `1` has instances that hold in every completed world, so a schema `u 🡒 inst c` is
inert in the limit.
Source: none: infrastructure (FAF `lic_nonDogmatism_dual`); [[bli-rvc-ui-findings]] F-19
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem stage_forces_of_limitingBelief_eq_one {φ : Sentence} (h : limitingBelief P φ = 1) :
    ∃ n, ∀ v : PCWorld, v.ConsistentWith (DP.D n) → v.Holds φ := by
  by_contra hcon
  refine absurd h (ne_of_lt (limitingBelief_lt_one_of_nonDogmatism hworld fun n => ?_))
  exact Classical.byContradiction fun hn => hcon ⟨n, fun v hv =>
    Classical.byContradiction fun hφ => hn ⟨v, hv, hφ⟩⟩

/-- A sentence with limiting belief `1` holds in every completed-theory world.
Source: none: infrastructure; [[bli-rvc-ui-findings]] F-19
Kind: L
Fidelity: n/a -/
theorem holds_of_limitingBelief_eq_one {φ : Sentence} (h : limitingBelief P φ = 1)
    (v : PCWorld) (hv : v.ConsistentWithTheory DP) : v.Holds φ :=
  let ⟨n, hn⟩ := stage_forces_of_limitingBelief_eq_one hworld h
  hn v (hv n)

end Cleanroom.Bli.BliRvcUi
