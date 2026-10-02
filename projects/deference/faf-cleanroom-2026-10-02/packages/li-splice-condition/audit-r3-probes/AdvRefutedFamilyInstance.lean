import Cleanroom.Li.LiSpliceCondition.DayIndexedWitness

/-!
# Audit r3 (adversarial) probe — the "candidates refuted by the next stage" class is inhabited by
a genuine inductor with a varying family

Companion to `AdvCandidateRefutedFloor.lean`, whose lemma `summable_price_of_nextStage_refuted`
(and its corollaries: no uniform floor; any decaying floor summable) quantifies over an inductor
`P` over a stage-consistent `DP`, an e.c. family `ψ`, and the refutation of each `ψ n` by stage
`n + 1`. This file inhabits that hypothesis package non-degenerately: FAF's LIA over the prefix
process of the **negated** atoms (stage `n` = `{∼a₀, …, ∼aₙ}`, computable by FAF's
`prefixProcessComputation` at `machineSentenceCodes_atom.neg`; the all-false world at every stage)
with the injective family `n ↦ aₙ` — day `n`'s candidate, which the process refutes on day `n + 1`.
This is exactly the shape of an unchosen candidate learned the next day, so the companion's
"no floor" conclusion is a statement about a real class, not an empty one. Evidence only; not
imported by the library.
-/

namespace Cleanroom.Li.LiSpliceCondition.AuditR3Adv

open LogicalInduction LO.Propositional Cleanroom.Li.LiProjection

/-- The negated-atom prefix process: stage `n` = `{∼a₀, …, ∼aₙ}`. -/
abbrev negAtomDP : DeductiveProcess := prefixProcess (fun i => ∼ (Formula.atom i : Sentence))

/-- It is computable (FAF's `prefixProcessComputation` at the negated atom certificate). -/
theorem negAtomDP_computable : ComputableDeductiveProcess negAtomDP :=
  (prefixProcessComputation _ machineSentenceCodes_atom.neg).toComputable

/-- The all-false world is consistent with every stage. -/
theorem negAtomDP_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (negAtomDP.D n) := by
  intro n
  refine ⟨fun _ => False, fun φ hφ => ?_⟩
  simp only [negAtomDP, prefixProcess, List.mem_toFinset, List.mem_map, List.mem_range] at hφ
  obtain ⟨i, _, rfl⟩ := hφ
  simp [PCWorld.holds_neg, PCWorld.holds_atom]

/-- Day `n`'s candidate `aₙ` is refuted by stage `n + 1`. -/
theorem negAtom_refuted (n : ℕ) (v : PCWorld) (hv : v.ConsistentWith (negAtomDP.D (n + 1))) :
    ¬ v.Holds (Formula.atom n) := by
  have hmem : (∼ (Formula.atom n : Sentence)) ∈ negAtomDP.D (n + 1) := by
    simp only [negAtomDP, prefixProcess, List.mem_toFinset, List.mem_map, List.mem_range]
    exact ⟨n, by omega, rfl⟩
  exact (PCWorld.holds_neg v _).mp (hv _ hmem)

/-- **The hypothesis package of `summable_price_of_nextStage_refuted` is inhabited** by FAF's LIA
of `negAtomDP` with the injective atom family: an inductor, a stage-consistent process, an e.c.
family, each member refuted by the next stage. -/
theorem refutedFamily_package_inhabited :
    IsLogicalInductor (liaHistory negAtomDP) negAtomDP ∧
    (∀ n, ∃ v : PCWorld, v.ConsistentWith (negAtomDP.D n)) ∧
    MachineSentenceCodes (fun n => (Formula.atom n : Sentence)) ∧
    (∀ n (v : PCWorld), v.ConsistentWith (negAtomDP.D (n + 1)) → ¬ v.Holds (Formula.atom n)) ∧
    Function.Injective (fun n => (Formula.atom n : Sentence)) :=
  ⟨LIA_is_logical_inductor _ negAtomDP_computable, negAtomDP_hworld, machineSentenceCodes_atom,
    negAtom_refuted, fun _ _ h => Formula.atom.inj h⟩

end Cleanroom.Li.LiSpliceCondition.AuditR3Adv
