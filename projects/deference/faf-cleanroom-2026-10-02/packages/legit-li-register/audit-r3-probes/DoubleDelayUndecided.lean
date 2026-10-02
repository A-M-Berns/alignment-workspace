import Cleanroom.Trust.LegitLiRegister.Schedule

/-!
# Audit r3 (adversarial) probe · the N+ really has the attack's timing, and the bridge ignores it

The package's N+ for Target 9 (iii), `truthProcess_bridge_alternating_lia_double`, is FAF's LIA over
`truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) doubleDelay`: true items decided at `n + 1`,
false ones at `2n + 2`. This probe checks that the schedule is **genuinely truth-correlated at the
feedback day**: for an odd `k` the item `f k = k + 1` is false, and at the feedback day
`f (k + 1) = k + 2` the process has decided it **neither way** (neither literal is in stage
`k + 2`; the negative literal arrives at stage `2k + 4`). So the scout's attack shape is present —
the truth of item `f k` is not available from the process by day `f (k + 1)` — and the bridge
exists anyway (`truthProcess_bridge_alternating_lia_double`), which is what "schedule-blind" means:
the `FeedbackTruthSequence` reads the completed theory and the computation certificate, never the
stage. Not imported by the library.
-/

namespace Cleanroom.Trust.LegitLiRegister.AuditR3

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-- At the successor deferral an odd `k` indexes a false item. -/
theorem altBoolSucc_odd_false (k : ℕ) (hk : k % 2 = 1) : altBoolSucc (k + 1) = false := by
  unfold altBoolSucc
  simp
  omega

/-- The false item `k + 1` (`k` odd) is not enumerated at the feedback day `k + 2 = f (k + 1)`. -/
theorem false_item_not_enum (k : ℕ) (hk : k % 2 = 1) :
    (schedFamily, k + 1, false) ∉ schedEnum altBoolSucc doubleDelay (k + 2) := by
  intro h
  unfold schedEnum at h
  rw [List.mem_filterMap] at h
  obtain ⟨n, -, hn⟩ := h
  by_cases hx : altBoolSucc n = true
  · rw [if_pos hx] at hn
    split_ifs at hn <;> simp at hn
  · rw [if_neg hx] at hn
    split_ifs at hn with hg
    simp only [Option.some.injEq, Prod.mk.injEq] at hn
    obtain ⟨-, rfl, -⟩ := hn
    unfold doubleDelay at hg
    omega

/-- Nor is its positive literal, at any stage (its truth value is `false`). -/
theorem true_lit_not_enum (k : ℕ) (hk : k % 2 = 1) (s : ℕ) :
    (schedFamily, k + 1, true) ∉ schedEnum altBoolSucc doubleDelay s := by
  intro h
  have := (mem_schedEnum_bool h).1
  rw [altBoolSucc_odd_false k hk] at this
  exact Bool.false_ne_true this

/-- The negative literal is enumerated at `2k + 4 = doubleDelay (k + 1)`. -/
theorem false_item_enum_late (k : ℕ) (hk : k % 2 = 1) :
    (schedFamily, k + 1, false) ∈ schedEnum altBoolSucc doubleDelay (2 * k + 4) := by
  unfold schedEnum
  rw [List.mem_filterMap]
  refine ⟨k + 1, List.mem_range.2 (by omega), ?_⟩
  rw [if_neg (by rw [altBoolSucc_odd_false k hk]; simp), if_pos (by unfold doubleDelay; omega)]

/-- No stage of `paperDP 𝗜𝚺₁` contains a schedule literal (tag-freeness of the base). -/
theorem schedLit_not_mem_paperDP (n p : ℕ) :
    schedAtom p ∉ (paperDP 𝗜𝚺₁).D n ∧ ∼schedAtom p ∉ (paperDP 𝗜𝚺₁).D n := by
  have hfree : TagFreeProcess (cleanroomBaseTag + schedFamily) (paperDP 𝗜𝚺₁) :=
    paperDP_tagFree 𝗜𝚺₁ (Nat.le_add_right _ _)
  constructor
  · intro h
    have := TagFreeSentence.freshAtomCode_notMem (hfree n _ h) p
    simp [schedAtom] at this
  · intro h
    have := TagFreeSentence.freshAtomCode_notMem (hfree n _ h) p
    simp [schedAtom] at this

/-- A negated fresh atom is never a fresh atom (`∼φ = φ ➝ ⊥`). -/
theorem neg_freshAtom_ne_freshAtom (f p f' p' : ℕ) : ∼freshAtom f p ≠ freshAtom f' p' := by
  intro h
  unfold freshAtom at h
  rw [Formula.neg_def] at h
  cases h

/-- Negated fresh atoms are injective. -/
theorem neg_freshAtom_inj {f p f' p' : ℕ} (h : ∼freshAtom f p = ∼freshAtom f' p') :
    f = f' ∧ p = p' := by
  rw [Formula.neg_def, Formula.neg_def] at h
  exact freshAtom_inj.1 (Formula.imp.inj h).1

/-- **The N+'s process has not decided the false item by the feedback day**: for odd `k`, neither
`schedAtom (k + 1)` nor its negation is in stage `k + 2 = succDeferral.f (k + 1)` of
`truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) doubleDelay`, while the negation is in stage
`2k + 4`. The bridge `truthProcess_bridge_alternating_lia_double` exists regardless. -/
theorem false_item_undecided_at_feedback_day (k : ℕ) (hk : k % 2 = 1) :
    (schedAtom (k + 1) ∉
        (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) doubleDelay).D (k + 2) ∧
      ∼schedAtom (k + 1) ∉
        (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) doubleDelay).D (k + 2)) ∧
    ∼schedAtom (k + 1) ∈
      (truthProcess (paperDP 𝗜𝚺₁) (altBool succDeferral) doubleDelay).D (2 * k + 4) := by
  rw [altBool_succDeferral]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro h
    unfold truthProcess at h
    rw [extendBy_D, Finset.mem_union] at h
    rcases h with h | h
    · exact (schedLit_not_mem_paperDP _ _).1 h
    · obtain ⟨⟨f, p, b⟩, he, hl⟩ := Finset.mem_image.1 h
      unfold truthSched at he
      rw [LiteralSchedule.ofList_lits, List.mem_toFinset] at he
      obtain ⟨hxb, rfl⟩ := mem_schedEnum_bool he
      cases b
      · rw [literalOf_false] at hl
        exact neg_freshAtom_ne_freshAtom _ _ _ _ hl
      · rw [literalOf_true] at hl
        obtain ⟨-, rfl⟩ := freshAtom_inj.1 hl
        exact true_lit_not_enum k hk _ he
  · intro h
    unfold truthProcess at h
    rw [extendBy_D, Finset.mem_union] at h
    rcases h with h | h
    · exact (schedLit_not_mem_paperDP _ _).2 h
    · obtain ⟨⟨f, p, b⟩, he, hl⟩ := Finset.mem_image.1 h
      unfold truthSched at he
      rw [LiteralSchedule.ofList_lits, List.mem_toFinset] at he
      obtain ⟨hxb, rfl⟩ := mem_schedEnum_bool he
      cases b
      · rw [literalOf_false] at hl
        obtain ⟨-, rfl⟩ := neg_freshAtom_inj hl
        exact false_item_not_enum k hk he
      · rw [literalOf_true] at hl
        exact neg_freshAtom_ne_freshAtom _ _ _ _ hl.symm
  · have := neg_schedAtom_mem_of_false (paperDP 𝗜𝚺₁) altBoolSucc doubleDelay
      (altBoolSucc_odd_false k hk)
    have hmax : max (doubleDelay (k + 1)) (k + 1 + 1) = 2 * k + 4 := by
      unfold doubleDelay; omega
    rwa [hmax] at this

end Cleanroom.Trust.LegitLiRegister.AuditR3
