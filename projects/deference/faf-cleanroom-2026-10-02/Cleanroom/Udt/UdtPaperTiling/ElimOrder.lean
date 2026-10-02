import Cleanroom.Udt.UdtPaperTiling.Structure

/-!
# `udt-paper-tiling` · ElimOrder: iterated `elim` along a rank-compatible order equals
`effCausal` (T1(b); OPEN in round 1, proved in repair round 1)

The paper's `eff(π)` is "the limit of repeated applications of `elim`" (`main.tex` 95–97);
bli-slides-036 assumes the limit is well defined. `Structure.lean` gives the construction of
record `effCausal`, defined directly by the causal rank. The statement that connects the two —
running `elim` at every self-modifying point, in **any** enumeration of the observations sorted
by rank, yields `effCausal π` — is `elimSeq_eq_effCausal`. It was stated and left open in round 1
and is proved here (repair round 1) by the invariant the round-1 report named: after a prefix
`L₁` of the enumeration has been processed, the current policy agrees with `effCausal π` on `L₁`
and, off `L₁`, carries exactly the actions forced by the firing points of `L₁` and `π` elsewhere
(`ElimInv`). The step (`elimInv_step`) is the case analysis: a forced point carries a
non-modifying action and the step is a no-op; an unforced non-modifying point is a no-op; an
unforced self-modifying point fires (its firing is `fires π o`, since nothing of lower rank
forces it), is replaced by its twin, and forces its targets, which lie strictly later by
`rank_lt` (so no processed point is touched) and agree with any earlier forcing by `no_disagree`.
Same-rank observations never interact (`rank_lt` is strict), which is why any rank-sorted
enumeration works.

**What this does and does not say about the paper's limit** (repair round 2, from the adversarial
audit's B1 and the fidelity audit's N-9). The paper's `eff(π)` is "the limit of repeated
applications of `elim`" with no order stated, *assumed* "uniquely defined". The theorem gives
uniqueness **among rank-sorted orders** only: under a valid causal structure (all three
hypotheses, and Limited Self-Modification too) two complete eliminations in different orders can
end at different non-modifying policies — `Chain.limit_not_unique` in `StructureWitness.lean`,
where a modification whose target is itself a self-modifying point is overwritten before it can
fire in rank order and fires first in reverse order. So "elimination proceeds in causal order"
is a fourth clause the paper's assumption needs, not a consequence of the three; `effCausal` is
the rank-ordered result *by definition*, and this theorem shows that definition is insensitive
to which rank-compatible order is used. That a rank-sorted enumeration always exists, so the
limit is reached by some complete elimination with no side condition, is
`CausalStructure.effCausal_reached` (from the adversarial audit's probe `RankSortedExists`).

Package `udt-paper-tiling` (faf-cleanroom run, 2026-09-30; repair 2026-10-01).
-/

namespace Cleanroom.Udt.UdtPaperTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Finset

variable {𝒮 : SmallIndex} {m : ℕ} {𝒟 : Finset (Table 𝒮 m)} {Act : Type} [Fintype Act]
  [DecidableEq Act]

namespace PaperStructure

variable (S : PaperStructure 𝒟 Act)

/-- One elimination step at `o`: if the current policy's action at `o` is self-modifying, run
`elim` there; otherwise do nothing.
Source: `main.tex` 95 ("repeated applications of `elim`"); bli-slides-036
Kind: D
Fidelity: exact -/
def elimStep (π : Policy 𝒟 Act) (o : ↥𝒟) : Policy 𝒟 Act :=
  if π o ∈ S.selfMod then S.elim π o (π o) else π

/-- Iterated elimination along a list of observations.
Source: `main.tex` 95; bli-slides-036
Kind: D
Fidelity: exact (the order is the list) -/
def elimSeq (π : Policy 𝒟 Act) (L : List ↥𝒟) : Policy 𝒟 Act :=
  L.foldl S.elimStep π

namespace CausalStructure

variable {S}
variable (C : S.CausalStructure)

/-- **The traversal invariant**: after the observations of `L₁` have been processed, the current
policy `σ` agrees with `effCausal π` on `L₁`, and at every other observation `o` it carries the
action forced by any firing point of `L₁` (when one forces `o`) and `π o` otherwise.
Source: none: infrastructure (the invariant named in the round-1 report)
Kind: D
Fidelity: n/a -/
def ElimInv (π : Policy 𝒟 Act) (L₁ : List ↥𝒟) (σ : Policy 𝒟 Act) : Prop :=
  (∀ o ∈ L₁, σ o = C.effCausal π o) ∧
  ∀ o ∉ L₁,
    (∀ a' o₁, o₁ ∈ L₁ → C.fires π o₁ → S.mod (π o₁) o = some a' → σ o = a') ∧
    ((¬ ∃ a' o₁, o₁ ∈ L₁ ∧ C.fires π o₁ ∧ S.mod (π o₁) o = some a') → σ o = π o)

/-- **One step preserves the invariant** when `o` is unprocessed, every processed observation has
rank at most `rank o`, and every observation of strictly lower rank is processed.
Source: none: infrastructure
Kind: P
Fidelity: n/a
Hyps: (a) `π` well-typed (for `rank_lt`), the invariant, the rank conditions -/
lemma elimInv_step {π : Policy 𝒟 Act} (hπ : S.WellTyped π) {L₁ : List ↥𝒟} {σ : Policy 𝒟 Act}
    (hInv : C.ElimInv π L₁ σ) {o : ↥𝒟} (ho : o ∉ L₁)
    (hle : ∀ o' ∈ L₁, C.rank o' ≤ C.rank o) (hlow : ∀ o', C.rank o' < C.rank o → o' ∈ L₁) :
    C.ElimInv π (L₁ ++ [o]) (S.elimStep σ o) := by
  obtain ⟨hproc, hunproc⟩ := hInv
  -- the value of `σ` at `o`: the forced action if `o` is forced (the forcing point has lower
  -- rank, hence is processed), else `π o`
  have hσo : (∀ a' o₁, C.fires π o₁ → S.mod (π o₁) o = some a' → σ o = a') ∧
      (¬ C.Forced π o → σ o = π o) := by
    obtain ⟨h1, h2⟩ := hunproc o ho
    refine ⟨fun a' o₁ hf hm => h1 a' o₁ (hlow o₁ (C.rank_lt _ _ _ _ (hπ o₁) hm)) hf hm,
      fun hnf => h2 ?_⟩
    rintro ⟨a', o₁, _, hf, hm⟩
    exact hnf ⟨a', o₁, hf, hm⟩
  by_cases hF : C.Forced π o
  · -- Case A: `o` is forced; `σ o` is the forced, non-modifying action; the step is a no-op
    obtain ⟨a', o₁, hf, hm⟩ := hF
    have hσ : σ o = a' := hσo.1 a' o₁ hf hm
    have hnm : a' ∉ S.selfMod := C.mod_nonMod _ _ _ hm
    have hstep : S.elimStep σ o = σ := by
      unfold elimStep
      rw [hσ, if_neg hnm]
    rw [hstep]
    have hnfire : ¬ C.fires π o := by
      intro hfo
      have := ((C.fires_iff π o).mp hfo).2 o₁ (C.rank_lt _ _ _ _ (hπ o₁) hm) hf
      rw [hm] at this
      simp at this
    refine ⟨fun o' ho' => ?_, fun o' ho' => ?_⟩
    · rw [List.mem_append, List.mem_singleton] at ho'
      rcases ho' with h | rfl
      · exact hproc o' h
      · rw [hσ]
        exact (C.effCausal_of_forced hf hm).symm
    · rw [List.mem_append, List.mem_singleton, not_or] at ho'
      obtain ⟨h1, h2⟩ := hunproc o' ho'.1
      refine ⟨fun a'' o₂ ho₂ hf₂ hm₂ => ?_, fun hn => h2 ?_⟩
      · rw [List.mem_append, List.mem_singleton] at ho₂
        rcases ho₂ with h | rfl
        · exact h1 a'' o₂ h hf₂ hm₂
        · exact absurd hf₂ hnfire
      · rintro ⟨a'', o₂, ho₂, hf₂, hm₂⟩
        exact hn ⟨a'', o₂, List.mem_append_left _ ho₂, hf₂, hm₂⟩
  · -- Case B: `o` is not forced, so `σ o = π o`
    have hσ : σ o = π o := hσo.2 hF
    have heff : C.effCausal π o = if π o ∈ S.selfMod then S.twin (π o) else π o :=
      C.effCausal_of_not_forced hF
    by_cases hs : π o ∈ S.selfMod
    · -- B2: the step fires at `o`
      have hfire : C.fires π o := by
        rw [C.fires_iff]
        refine ⟨hs, fun o₁ _ hf₁ => ?_⟩
        cases hm : S.mod (π o₁) o with
        | none => rfl
        | some a' => exact absurd ⟨a', o₁, hf₁, hm⟩ hF
      have hstep : S.elimStep σ o = S.elim σ o (π o) := by
        unfold elimStep
        rw [hσ, if_pos hs]
      rw [hstep]
      refine ⟨fun o' ho' => ?_, fun o' ho' => ?_⟩
      · rw [List.mem_append, List.mem_singleton] at ho'
        rcases ho' with h | rfl
        · -- a processed point: not a target of `π o` (targets lie strictly later)
          have hne : o' ≠ o := fun e => ho (e ▸ h)
          have hnone : S.mod (π o) o' = none := by
            cases hm : S.mod (π o) o' with
            | none => rfl
            | some a' =>
              exfalso
              exact absurd (hle o' h) (not_le.mpr (C.rank_lt _ _ _ _ (hπ o) hm))
          rw [S.elim_other σ (π o) hne hnone]
          exact hproc o' h
        · rw [S.elim_self, heff, if_pos hs]
      · rw [List.mem_append, List.mem_singleton, not_or] at ho'
        have hne : o' ≠ o := ho'.2
        obtain ⟨h1, h2⟩ := hunproc o' ho'.1
        refine ⟨fun a'' o₂ ho₂ hf₂ hm₂ => ?_, fun hn => ?_⟩
        · rw [List.mem_append, List.mem_singleton] at ho₂
          rcases ho₂ with h | h
          · cases hm : S.mod (π o) o' with
            | none =>
              rw [S.elim_other σ (π o) hne hm]
              exact h1 a'' o₂ h hf₂ hm₂
            | some a₃ =>
              rw [S.elim_forced σ (π o) a₃ hne hm]
              exact C.no_disagree _ _ _ _ _ hm hm₂
          · rw [h] at hm₂
            exact S.elim_forced σ (π o) a'' hne hm₂
        · have hnone : S.mod (π o) o' = none := by
            cases hm : S.mod (π o) o' with
            | none => rfl
            | some a₃ =>
              exact absurd ⟨a₃, o, List.mem_append_right _ (by simp), hfire, hm⟩ hn
          rw [S.elim_other σ (π o) hne hnone]
          refine h2 ?_
          rintro ⟨a'', o₂, ho₂, hf₂, hm₂⟩
          exact hn ⟨a'', o₂, List.mem_append_left _ ho₂, hf₂, hm₂⟩
    · -- B1: `π o` is non-modifying; the step is a no-op
      have hstep : S.elimStep σ o = σ := by
        unfold elimStep
        rw [hσ, if_neg hs]
      rw [hstep]
      have hnfire : ¬ C.fires π o := fun hfo => hs (C.fires_selfMod hfo)
      refine ⟨fun o' ho' => ?_, fun o' ho' => ?_⟩
      · rw [List.mem_append, List.mem_singleton] at ho'
        rcases ho' with h | rfl
        · exact hproc o' h
        · rw [hσ, heff, if_neg hs]
      · rw [List.mem_append, List.mem_singleton, not_or] at ho'
        obtain ⟨h1, h2⟩ := hunproc o' ho'.1
        refine ⟨fun a'' o₂ ho₂ hf₂ hm₂ => ?_, fun hn => h2 ?_⟩
        · rw [List.mem_append, List.mem_singleton] at ho₂
          rcases ho₂ with h | rfl
          · exact h1 a'' o₂ h hf₂ hm₂
          · exact absurd hf₂ hnfire
        · rintro ⟨a'', o₂, ho₂, hf₂, hm₂⟩
          exact hn ⟨a'', o₂, List.mem_append_left _ ho₂, hf₂, hm₂⟩

/-- **The invariant is carried along the traversal** of a no-repeat, complete, rank-sorted
enumeration, split as a processed prefix `L₁` and a remainder `L₂`.
Source: none: infrastructure
Kind: P
Fidelity: n/a
Hyps: (a) `π` well-typed, the list conditions, the invariant at `L₁` -/
lemma elimInv_foldl {π : Policy 𝒟 Act} (hπ : S.WellTyped π) (L₂ : List ↥𝒟) :
    ∀ (L₁ : List ↥𝒟) (σ : Policy 𝒟 Act), (L₁ ++ L₂).Nodup →
      (L₁ ++ L₂).Pairwise (fun o₁ o₂ => C.rank o₁ ≤ C.rank o₂) → (∀ o, o ∈ L₁ ++ L₂) →
      C.ElimInv π L₁ σ → C.ElimInv π (L₁ ++ L₂) (L₂.foldl S.elimStep σ) := by
  induction L₂ with
  | nil =>
    intro L₁ σ _ _ _ hInv
    simpa using hInv
  | cons o L₂' ih =>
    intro L₁ σ hnd hsorted hall hInv
    have ho : o ∉ L₁ := by
      have hmid := List.nodup_middle.mp hnd
      exact fun h => (List.nodup_cons.mp hmid).1 (List.mem_append_left _ h)
    have hle : ∀ o' ∈ L₁, C.rank o' ≤ C.rank o := by
      intro o' ho'
      exact (List.pairwise_append.mp hsorted).2.2 o' ho' o (by simp)
    have hlow : ∀ o', C.rank o' < C.rank o → o' ∈ L₁ := by
      intro o' hlt
      rcases List.mem_append.mp (hall o') with h | h
      · exact h
      · exfalso
        rcases List.mem_cons.mp h with rfl | h'
        · exact lt_irrefl _ hlt
        · have := (List.pairwise_cons.mp (List.pairwise_append.mp hsorted).2.1).1 o' h'
          exact absurd hlt (not_lt.mpr this)
    have hstep := C.elimInv_step hπ hInv ho hle hlow
    have e : L₁ ++ o :: L₂' = (L₁ ++ [o]) ++ L₂' := by simp
    rw [e] at hnd hsorted hall
    rw [List.foldl_cons, e]
    exact ih (L₁ ++ [o]) (S.elimStep σ o) hnd hsorted hall hstep

end CausalStructure

/-- **Order-independence of iterated `elim` among rank-sorted orders**: for a well-typed policy
and any enumeration of the observations (no repeats, every observation listed) that is
non-decreasing in the causal rank, iterated elimination equals `effCausal π`. Proved (repair
round 1) by `ElimInv`: the invariant holds for the empty prefix with `σ = π` and is carried along
the list (`elimInv_foldl`); at the end every observation is processed, so the result agrees with
`effCausal π` everywhere. This is bli-slides-036's "well-defined limit" **restricted to
rank-compatible orders**: the limit along any such order exists, is reached in one pass, and is
the construction of record. It is *not* the uniqueness of the paper's unordered limit: under the
same causal structure, eliminations in a non-sorted order can end elsewhere
(`Chain.limit_not_unique`, `StructureWitness.lean`), so the order is part of the definition of
`eff` — which is what `effCausal` supplies.
Source: `main.tex` 95–97; bli-slides-036 ("a well-defined limit"); bli-paper-062
Kind: P
Fidelity: variant: the limit along rank-compatible orders only; the paper's unordered limit is
not unique even under the causal structure (the N− row `Chain.limit_not_unique`)
Hyps: (a) a causal structure, well-typedness, the list conditions (jointly satisfiable:
`CausalStructure.effCausal_reached`) -/
theorem elimSeq_eq_effCausal (C : S.CausalStructure) (π : Policy 𝒟 Act) (hπ : S.WellTyped π)
    (L : List ↥𝒟) (hnd : L.Nodup) (hall : ∀ o, o ∈ L)
    (hsorted : L.Pairwise (fun o₁ o₂ => C.rank o₁ ≤ C.rank o₂)) :
    S.elimSeq π L = C.effCausal π := by
  have hbase : C.ElimInv π [] π := by
    refine ⟨fun o ho => by simp at ho, fun o _ => ⟨fun a' o₁ ho₁ => by simp at ho₁, fun _ => rfl⟩⟩
  have h := C.elimInv_foldl hπ L [] π (by simpa using hnd) (by simpa using hsorted)
    (by simpa using hall) hbase
  funext o
  show List.foldl S.elimStep π L o = C.effCausal π o
  exact h.1 o (by simpa using hall o)

namespace CausalStructure

variable {S}

/-- **A repeat-free, complete, rank-sorted enumeration of the observations exists** (merge-sort
the universe by rank), so the list hypotheses of `elimSeq_eq_effCausal` are jointly satisfiable
for every causal structure.
Source: audit r2 adversarial probe `RankSortedExists` (N6); none: infrastructure
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem exists_rank_sorted_enum (C : S.CausalStructure) :
    ∃ L : List ↥𝒟, L.Nodup ∧ (∀ o, o ∈ L) ∧
      L.Pairwise (fun o₁ o₂ => C.rank o₁ ≤ C.rank o₂) := by
  classical
  let le : ↥𝒟 → ↥𝒟 → Bool := fun a b => decide (C.rank a ≤ C.rank b)
  let l : List ↥𝒟 := (Finset.univ : Finset ↥𝒟).toList
  have hperm := List.mergeSort_perm l le
  refine ⟨l.mergeSort le, hperm.nodup_iff.mpr (Finset.nodup_toList _),
    fun o => hperm.mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ o)), ?_⟩
  have hpw : (l.mergeSort le).Pairwise (fun a b => le a b) :=
    List.pairwise_mergeSort
      (fun a b c h1 h2 => by
        simp only [le, decide_eq_true_eq] at h1 h2 ⊢
        exact le_trans h1 h2)
      (fun a b => by
        simp only [le, Bool.or_eq_true, decide_eq_true_eq]
        exact le_total _ _)
      l
  exact hpw.imp (fun h => by simpa [le] using h)

/-- **`effCausal π` is reached by some complete elimination**, for every causal structure and
well-typed policy — "the limit is reached in one pass" as a theorem with no side condition.
Source: audit r2 adversarial probe `RankSortedExists` (N6); `main.tex` 95–97
Kind: C
Fidelity: n/a (the existence half of bli-slides-036's assumption; uniqueness holds only among
rank-sorted orders, `elimSeq_eq_effCausal`)
Hyps: (a) a causal structure, well-typedness -/
theorem effCausal_reached (C : S.CausalStructure) (π : Policy 𝒟 Act) (hπ : S.WellTyped π) :
    ∃ L : List ↥𝒟, L.Nodup ∧ (∀ o, o ∈ L) ∧ S.elimSeq π L = C.effCausal π := by
  obtain ⟨L, hnd, hall, hsorted⟩ := exists_rank_sorted_enum C
  exact ⟨L, hnd, hall, S.elimSeq_eq_effCausal C π hπ L hnd hall hsorted⟩

end CausalStructure

end PaperStructure

end Cleanroom.Udt.UdtPaperTiling
