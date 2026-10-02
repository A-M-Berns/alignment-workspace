import Cleanroom.Li.LiSpliceCondition.DayIndexed
import Cleanroom.Li.LiSpliceCondition.Candidate
import Cleanroom.Li.LiSpliceCondition.Witnesses
import LogicalInduction.Framework.Machine.Witnesses

/-!
# `li-splice-condition` · DayIndexedWitness: 063(a)'s readings instantiated

Package `Cleanroom.Li.LiSpliceCondition` ([[li-splice-condition-mandate]]), file 12 of the layout,
added in repair round 1 and extended in repair round 2. Instances of `DayIndexed.lean`'s and
`Candidate.lean`'s statements:

* over FAF's paper LIA `paperBase := liaHistory (paperDP 𝗜𝚺₁)` with the fresh atoms `spliceAtom 3`,
  `spliceAtom 4`: the (S) refutation with its explicit exploit (`paperAlternating_exploited`,
  `paperDayIndexed_floor_false`), the (G) instance in FAF's consistent branch
  (`paperPrefix_instance`, from the adversarial round-2 probe), the candidate reading's
  hypotheses inhabited (`paperCandidate_not_gatedExploits`), and the (L) N− at a constant family
  (`paperLearnedPast_const`);
* over FAF's LIA of the **atom prefix process** (stage `n` = `{a₀, …, aₙ}`, FAF's `prefixProcess`
  of FAF's atom family, computable by `prefixProcessComputation`): the (L) **varying** N+
  (`atomPrefix_learnedPast`) with the shifted family `n ↦ aₙ₊₁` — day `n`'s condition is not in
  day `n`'s stage and is asserted by the base process on day `n + 1`, the one-day lag that
  distinguishes (L) from FAF's fixed case. The e.c. certificate is FAF's
  `machineSentenceCodes_atom` reindexed by the ruler `n ↦ n + 1`. (A varying N+ over the *paper*
  process would need a machine for `spliceAtomCode`'s `Nat.pair` registry, not in hand.)

Kept in its own file so that a slice kill costs one file (the paper LIA and the conditioning
endpoints are both imported here).
-/

namespace Cleanroom.Li.LiSpliceCondition

open LogicalInduction LO.Propositional Cleanroom.Li.LiProjection Cleanroom.Bli.BliFound

/-- The two counterexample atoms are distinct (`freshAtomCode` is injective in its payload).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma spliceAtomCode_three_ne_four : spliceAtomCode 3 ≠ spliceAtomCode 4 := by
  intro h
  have h1 := (freshAtomCode_inj.mp h).2
  have h2 := (Nat.pair_eq_pair.mp h1).2
  have h3 := (Nat.pair_eq_pair.mp h2).2
  omega

/-- Both counterexample atoms are jointly plausible at every stage of `paperDP 𝗜𝚺₁`, with the
alternating family's prefixes: the joint-consistency hypothesis of `prefixUnion_hworld`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperAlt_joint (n : ℕ) :
    ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) ∧
      ∀ i, i ≤ n → v.Holds (altCondition (spliceAtomCode 3) (spliceAtomCode 4) i) := by
  obtain ⟨v, hv⟩ := paperDP_hworld 𝗜𝚺₁ n
  refine ⟨setAtom (setAtom v (spliceAtomCode 3) true) (spliceAtomCode 4) true,
    (consistentWith_setAtom_iff (paperDP_spliceAtomFree 4) _ true n).mp
      ((consistentWith_setAtom_iff (paperDP_spliceAtomFree 3) v true n).mp hv), fun i _ => ?_⟩
  unfold altCondition
  split_ifs <;> rw [PCWorld.holds_atom] <;> simp [setAtom, spliceAtomCode_three_ne_four]

/-- **The single-condition reading of 063(a) refuted over the paper LIA, with the explicit
exploit**: the odd-day seller of `∼spliceAtom 3` exploits `paperBase` conditioned day `n` on the
alternating family `spliceAtom 3, spliceAtom 4, …`, over the natural accumulating process
`paperDP 𝗜𝚺₁ ∪ prefixProcess (altCondition …)` (stage-consistent, `paperAlt_joint`), which is
therefore not an inductor. Sorry-free: nothing rests on (A) or (B1).
Source: [[corr-legit-neg-inventory]] 063(a) (E7 escape (ii)), single-condition reading; mandate T6.2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paperAlternating_exploited :
    (oddSeller (∼ Formula.atom (spliceAtomCode 3))).Exploits
      (conditionedHistory paperBase (altCondition (spliceAtomCode 3) (spliceAtomCode 4)))
      ((paperDP 𝗜𝚺₁).union (prefixProcess (altCondition (spliceAtomCode 3) (spliceAtomCode 4)))) ∧
    ¬ IsLogicalInductor
      (conditionedHistory paperBase (altCondition (spliceAtomCode 3) (spliceAtomCode 4)))
      ((paperDP 𝗜𝚺₁).union (prefixProcess (altCondition (spliceAtomCode 3) (spliceAtomCode 4)))) := by
  haveI := paperBase_isLogicalInductor
  have hcons' := prefixUnion_hworld (paperDP 𝗜𝚺₁)
    (altCondition (spliceAtomCode 3) (spliceAtomCode 4)) paperAlt_joint
  exact ⟨conditioned_alternating_exploited paperBase (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁) _ _
      spliceAtomCode_three_ne_four (paperDP_spliceAtomFree 3) (paperDP_spliceAtomFree 4) _
      (prefixUnion_mem _ _).2 hcons',
    conditioned_alternating_not_isLogicalInductor paperBase (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁) _ _
      spliceAtomCode_three_ne_four (paperDP_spliceAtomFree 3) (paperDP_spliceAtomFree 4) _
      (prefixUnion_mem _ _).2 hcons'⟩

/-- **The former OPEN (B6), with the audits' non-degeneracy clause, is false — refutation instance
over the paper LIA**: `conditioned_dayIndexed_floor_false` at `paperBase` over `paperDP 𝗜𝚺₁` with
the fresh atoms `spliceAtom 3`, `spliceAtom 4` (the floor-patched inductor and the alternating
family are built inside the proof). A refutation instance, not a witness of a hypothesis package
(the package's N+ for the refutation is `paperAlternating_exploited`; Kind corrected in repair
round 2). Sorry-free.
Source: [[corr-legit-neg-inventory]] 063(a); mandate T6.2
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem paperDayIndexed_floor_false :
    ¬ ∀ (Q : History) (DQ : DeductiveProcess) [IsLogicalInductor Q DQ] (ψ : ℕ → Sentence),
        MachineSentenceCodes ψ → ∀ ε : ℝ, 0 < ε → (∀ n, ε ≤ Q n (ψ n)) →
        (∀ n, ∃ v : PCWorld, v.ConsistentWith (DQ.D n) ∧ v.Holds (ψ n)) →
        ∃ DP' : DeductiveProcess, (∀ n, DQ.D n ⊆ DP'.D n) ∧ (∀ n, ψ n ∈ DP'.D n) ∧
          (∀ n, ∃ v : PCWorld, v.ConsistentWith (DP'.D n)) ∧
          IsLogicalInductor (conditionedHistory Q ψ) DP' := by
  haveI := paperBase_isLogicalInductor
  exact conditioned_dayIndexed_floor_false paperBase (paperDP 𝗜𝚺₁) (paperDP_hworld 𝗜𝚺₁)
    (spliceAtomCode 3) (spliceAtomCode 4) spliceAtomCode_three_ne_four
    (paperDP_spliceAtomFree 3) (paperDP_spliceAtomFree 4)

/-! ## The growing-conjunction reading (G): FAF's theorem in its consistent branch -/

/-- **(G) instantiated non-degenerately over the paper LIA** (from the adversarial round-2 probe
`AdvPrefixPaperInstance.lean`): FAF's `lic_conditioned_growing_ofSequence` at `paperBase` with the
alternating family, where the union process is stage-consistent (`paperAlt_joint`), so FAF's
theorem runs in its consistent branch, not the vacuous one. The prefix conjunctions are eventually
constant in content (`a ⋏ b ⋏ a ⋏ ⋯` holds iff `a ⋏ b` does from day `1`); a strictly growing
instance over the paper process needs the fresh-atom certificate named in the file header.
Source: [[corr-legit-neg-inventory]] 063(a), growing-conjunction reading (the inventory's covered case); adversarial audit r2 N2
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem paperPrefix_instance :
    IsLogicalInductor
      (conditionedHistory paperBase (fun n => sentenceConjunction
        ((List.range (n + 1)).map (altCondition (spliceAtomCode 3) (spliceAtomCode 4)))))
      ((paperDP 𝗜𝚺₁).union (prefixProcess (altCondition (spliceAtomCode 3) (spliceAtomCode 4)))) ∧
    ∀ n, ∃ v : PCWorld, v.ConsistentWith
      (((paperDP 𝗜𝚺₁).union
        (prefixProcess (altCondition (spliceAtomCode 3) (spliceAtomCode 4)))).D n) := by
  haveI := paperBase_isLogicalInductor
  exact ⟨(conditioned_prefix_isLogicalInductor paperBase (paperDP 𝗜𝚺₁) _
      (altCondition_codes _ _)).1,
    prefixUnion_hworld _ _ paperAlt_joint⟩

/-! ## The candidate reading (C): its hypotheses inhabited over the paper LIA -/

/-- **The candidate reading's hypothesis package inhabited over the paper LIA** (N+ for the
hypotheses): a genuine inductor over `paperDP 𝗜𝚺₁` (a finite patch of the LIA,
`exists_inductor_floor_two_atoms`) with a uniform rational floor on the *varying* alternating
family `spliceAtom 3, spliceAtom 4, …` — unchosen candidates held by no process — and the e.c.
odd-day seller of `∼spliceAtom 3`, the very trader that exploits the (S) reading
(`paperAlternating_exploited`): in the candidate reading its gated assessments over `paperDP` are
not bounded below and unbounded above. Disclosure: which disjunct holds for this trader is not
shown — on a `paperDP`-plausible world refuting `spliceAtom 3` and holding `spliceAtom 4` the seller
loses on every odd day, so its gated assessments may well be unbounded *below*. A witness in which
the bounded-above disjunct is the operative one needs a trader whose gated assessments are bounded
below on every plausible world, which no trader with infinitely many non-trivial trades has by
design (an odd-day pair trader's pair gains can be negative); it would need an argument specific
to the inductor, and was not built. Sorry-free.
Source: [[corr-legit-neg-inventory]] 063(a) (E7 escape (ii), the exploration reading); adversarial audit r2 B1
Kind: N+
Fidelity: exact (the hypotheses of `conditioned_candidate_not_gatedExploits`)
Hyps: (a) none -/
theorem paperCandidate_not_gatedExploits :
    ∃ P' : History, IsLogicalInductor P' (paperDP 𝗜𝚺₁) ∧ ∃ ε : ℚ, 0 < (ε : ℝ) ∧
      (∀ n, (ε : ℝ) ≤ P' n (altCondition (spliceAtomCode 3) (spliceAtomCode 4) n)) ∧
      ¬ GatedExploits (oddSeller (∼ Formula.atom (spliceAtomCode 3))) P'
        (altCondition (spliceAtomCode 3) (spliceAtomCode 4)) (paperDP 𝗜𝚺₁) := by
  haveI := paperBase_isLogicalInductor
  obtain ⟨P', hP', ε, hε, ha, hb⟩ := exists_inductor_floor_two_atoms paperBase (paperDP 𝗜𝚺₁)
    (paperDP_hworld 𝗜𝚺₁) (spliceAtomCode 3) (spliceAtomCode 4) (paperDP_spliceAtomFree 3)
    (paperDP_spliceAtomFree 4)
  obtain ⟨q, hq0, hqε⟩ := exists_rat_btwn hε
  have hfloor : ∀ n, (q : ℝ) ≤ P' n (altCondition (spliceAtomCode 3) (spliceAtomCode 4) n) := by
    intro n
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [altCondition_even h]
      exact hqε.le.trans (ha n)
    · rw [altCondition_odd h]
      exact hqε.le.trans (hb n)
  haveI := hP'
  exact ⟨P', hP', q, hq0, hfloor,
    conditioned_candidate_not_gatedExploits P' (paperDP 𝗜𝚺₁) _ (altCondition_codes _ _) q hq0
      hfloor _ (oddSeller_ec _)⟩

/-! ## The learned-past reading (L): an N− instance (constant family) over the paper process -/

/-- The base process of the learned-past N−: the paper process with the fresh atom `spliceAtom 5`
adjoined at every stage, so that the constant family `ψ ≡ spliceAtom 5` has its "past" learned from
day `0`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable abbrev paperLearnedDP : DeductiveProcess :=
  (paperDP 𝗜𝚺₁).adjoinSentence (spliceAtom 5)

/-- `paperLearnedDP` is computable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperLearnedDP_computable : ComputableDeductiveProcess paperLearnedDP :=
  computableDeductiveProcess_adjoinSentence _ (paperDP_computable _) _

/-- `paperLearnedDP` has a consistent world at every stage (the atom is fresh for the paper process).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperLearnedDP_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (paperLearnedDP.D n) :=
  adjoinSentence_hworld_of_atomFree _ _ (paperDP_spliceAtomFree 5) (paperDP_hworld 𝗜𝚺₁)

/-- `spliceAtom 5` is in stage `0` of `paperLearnedDP`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperLearnedDP_mem : spliceAtom 5 ∈ paperLearnedDP.D 0 := by
  simp [DeductiveProcess.adjoinSentence, DeductiveProcess.union_stage, fixedConditionProcess]

/-- **The learned-past reading's ε-form hypothesis package is inhabited (N−, constant family)**:
over `paperLearnedDP` there is an inductor (a finite patch of the LIA, whose price on
`spliceAtom 5` tends to `1` by obedience) with a uniform rational floor on the constant condition
family `ψ ≡ spliceAtom 5` — so it also inhabits the theorem of record's per-day positivity, with
`paperLearnedDP_hworld` — the union process is stage-consistent, and the day-wise conditioned
market is an inductor over `paperLearnedDP ∪ prefixProcess ψ`. N− twice over: the family is
constant, and the day's condition is already in the day's stage (`paperLearnedDP_mem` at stage
`0`), so neither the varying family nor the one-day lag that distinguishes (L) from FAF's
fixed-condition case is exercised; the conclusion is FAF's fixed case up to the process's shape.
The varying N+ is `atomPrefix_learnedPast` below. Sorry-free.
Source: [[corr-legit-neg-inventory]] 063(a), learned-past reading; mandate T6.2
Kind: N−
Fidelity: exact (the hypotheses of `conditioned_learnedPast_of_floor`, at a constant family)
Hyps: (a) none -/
theorem paperLearnedPast_const :
    ∃ P : History, IsLogicalInductor P paperLearnedDP ∧ ∃ ε : ℚ, 0 < (ε : ℝ) ∧
      (∀ n, (ε : ℝ) ≤ P n (spliceAtom 5)) ∧
      (∀ n, ∃ v : PCWorld, v.ConsistentWith
        ((paperLearnedDP.union (prefixProcess (fun _ => spliceAtom 5))).D n)) ∧
      IsLogicalInductor (conditionedHistory P (fun _ => spliceAtom 5))
        (paperLearnedDP.union (prefixProcess (fun _ => spliceAtom 5))) := by
  haveI hLI : IsLogicalInductor (liaHistory paperLearnedDP) paperLearnedDP :=
    LIA_is_logical_inductor _ paperLearnedDP_computable
  have hsum := obedience_summable (liaHistory paperLearnedDP) paperLearnedDP paperLearnedDP_hworld
    paperLearnedDP_mem
  have hT : Filter.Tendsto (fun n => liaHistory paperLearnedDP n (spliceAtom 5)) Filter.atTop
      (nhds 1) := by
    have h0 := hsum.tendsto_atTop_zero
    have h1 := h0.const_sub 1
    simpa using h1
  obtain ⟨P', hP', ε, hε, hfloor⟩ :=
    exists_patch_floor_of_tendsto _ paperLearnedDP (spliceAtom 5) 1 one_pos hT
  haveI := hP'
  have hpast : ∀ m n, m < n → (fun _ => spliceAtom 5) m ∈ paperLearnedDP.D n :=
    fun _ n _ => paperLearnedDP.mono_le (Nat.zero_le n) paperLearnedDP_mem
  refine ⟨P', hP', ε, hε, hfloor, learnedPast_hworld paperLearnedDP _ hpast fun n => ?_, ?_⟩
  · obtain ⟨v, hv⟩ := paperLearnedDP_hworld n
    exact ⟨v, hv, hv _ (paperLearnedDP.mono_le (Nat.zero_le n) paperLearnedDP_mem)⟩
  · exact conditioned_learnedPast_of_floor P' paperLearnedDP (fun _ => spliceAtom 5)
      (MachineSentenceCodes.const _) hpast ε hε hfloor

/-! ## The learned-past reading (L): the varying N+ over the atom prefix process -/

/-- The atom prefix process: stage `n` = `{a₀, …, aₙ}`, FAF's `prefixProcess` of FAF's atom family.
Source: none: infrastructure (FAF `prefixProcess`, `machineSentenceCodes_atom`)
Kind: D
Fidelity: n/a -/
abbrev atomPrefixDP : DeductiveProcess := prefixProcess (fun i => (Formula.atom i : Sentence))

/-- The atom prefix process is computable (FAF's `prefixProcessComputation` at FAF's certificate).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem atomPrefixDP_computable : ComputableDeductiveProcess atomPrefixDP :=
  (prefixProcessComputation _ machineSentenceCodes_atom).toComputable

/-- The all-true world is consistent with every stage of the atom prefix process.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem atomPrefixDP_hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (atomPrefixDP.D n) := by
  intro n
  refine ⟨fun _ => True, fun φ hφ => ?_⟩
  simp only [atomPrefixDP, prefixProcess, List.mem_toFinset, List.mem_map, List.mem_range] at hφ
  obtain ⟨i, _, rfl⟩ := hφ
  exact (PCWorld.holds_atom (fun _ => True) i).mpr trivial

/-- The shifted atom family `n ↦ aₙ₊₁`: day `n`'s condition is the atom the base process asserts
on day `n + 1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def shiftedAtom (n : ℕ) : Sentence := Formula.atom (n + 1)

/-- The shifted atom family is e.c.: FAF's `machineSentenceCodes_atom` reindexed by the unary
ruler `n ↦ n + 1`.
Source: none: infrastructure (FAF `MachineSentenceCodes.comp`, `UnaryRuler.succ`)
Kind: L
Fidelity: n/a -/
theorem shiftedAtom_codes : MachineSentenceCodes shiftedAtom :=
  (machineSentenceCodes_atom.comp UnaryRuler.id.succ).of_eq (fun _ => rfl)

/-- Every earlier condition is in the base stage: `aₘ₊₁ ∈ {a₀, …, aₙ}` for `m < n` — (L)'s
`hpast`, exactly.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem shiftedAtom_past : ∀ m n, m < n → shiftedAtom m ∈ atomPrefixDP.D n := by
  intro m n hmn
  simp only [atomPrefixDP, prefixProcess, shiftedAtom, List.mem_toFinset, List.mem_map,
    List.mem_range]
  exact ⟨m + 1, by omega, rfl⟩

/-- The day's own condition is **not** in the day's stage: `aₙ₊₁ ∉ {a₀, …, aₙ}` — the one-day lag
that `paperLearnedPast_const` does not exercise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem shiftedAtom_not_mem (n : ℕ) : shiftedAtom n ∉ atomPrefixDP.D n := by
  intro h
  simp only [atomPrefixDP, prefixProcess, shiftedAtom, List.mem_toFinset, List.mem_map,
    List.mem_range] at h
  obtain ⟨i, hi, hiq⟩ := h
  have h' : i = n + 1 := Formula.atom.inj hiq
  omega

/-- The shifted atom family is injective: a genuinely varying family.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem shiftedAtom_injective : Function.Injective shiftedAtom := by
  intro m n h
  have h' : m + 1 = n + 1 := Formula.atom.inj h
  omega

/-- **The learned-past reading's varying N+**: over FAF's LIA of the atom prefix process there is
an inductor (a finite patch of the LIA, `conditioned_learnedPast_patch`) with a uniform floor `1/2`
on the shifted atom family `n ↦ aₙ₊₁` — injective (`shiftedAtom_injective`), each day's condition
outside the day's stage (`shiftedAtom_not_mem`) and inside every later stage (`shiftedAtom_past`)
— whose day-wise conditioned market is an inductor over `atomPrefixDP ∪ prefixProcess shiftedAtom`.
The family is e.c. by FAF's atom certificate reindexed (`shiftedAtom_codes`), the base process is
computable (`atomPrefixDP_computable`) and stage-consistent (`atomPrefixDP_hworld`): the full
hypothesis package of the theorem of record (with the floor supplied by the patch corollary). N+:
the one-day lag and the varying family are exactly what distinguishes (L) from FAF's fixed case.
Not over the paper process (see the file header). Sorry-free.
Source: [[corr-legit-neg-inventory]] 063(a), learned-past reading; adversarial audit r2 N4, fidelity audit r2 N1(ii)
Kind: N+
Fidelity: exact (the conclusion of `conditioned_learnedPast_patch` at FAF's LIA of `atomPrefixDP`)
Hyps: (a) none -/
theorem atomPrefix_learnedPast :
    ∃ P : History, IsLogicalInductor P atomPrefixDP ∧
      (∀ n, ((1 / 2 : ℚ) : ℝ) ≤ P n (shiftedAtom n)) ∧
      IsLogicalInductor (conditionedHistory P shiftedAtom)
        (atomPrefixDP.union (prefixProcess shiftedAtom)) := by
  haveI := LIA_is_logical_inductor _ atomPrefixDP_computable
  exact conditioned_learnedPast_patch (liaHistory atomPrefixDP) atomPrefixDP atomPrefixDP_hworld
    shiftedAtom shiftedAtom_codes shiftedAtom_past

end Cleanroom.Li.LiSpliceCondition
