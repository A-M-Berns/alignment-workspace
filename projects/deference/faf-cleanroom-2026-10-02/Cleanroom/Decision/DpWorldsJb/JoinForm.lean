import Cleanroom.Decision.DpWorldsJb.Defs
import Mathlib.Tactic.Ring

/-!
# The join form of the probability condition (T8(a)) and the finite-sup lemma

* `isGLB_compl_image_iff`: `IsGLB (compl '' D) mᶜ ↔ IsLUB D m` (De Morgan on bounds).
* `ContMeet`, `ContJoin`, **`contJoin_iff_contMeet_compl`**: continuity of `P` along a family in
  the join language (`P (⨆ D) = sup {P (⨆ F) | F ⊆ D finite}`, Appendix A "Typing the
  designation") is exactly continuity along the complemented family in the official meet
  language. So a package may designate in whichever language reads naturally.
* `Prob.isLUB_range_finset_sup`: for a designated complemented family `{ (g i)ᶜ }` with
  infimum `m`, `P mᶜ` is the least upper bound of `{P (⨆_{i ∈ s} g i) | s finite}` — the engine
  behind both countable additivity (`Sigma.lean`) and purely-atomic-ness (T8(b)).
-/

namespace Cleanroom.Decision.DpWorldsJb

noncomputable section

open Classical

variable {E : Type*} [BooleanAlgebra E]

/-- De Morgan on bounds: `mᶜ` is the infimum of the complemented family iff `m` is the supremum
of the family.
Source: [[decision-problems-v2]] Appendix A "Typing the designation" (line 329)
Kind: L
Fidelity: exact
Hyps: n/a -/
theorem isGLB_compl_image_iff (D : Set E) (m : E) : IsGLB (compl '' D) mᶜ ↔ IsLUB D m := by
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · intro A hA
      exact compl_le_compl_iff_le.1 (h1 ⟨A, hA, rfl⟩)
    · intro b hb
      have : bᶜ ∈ lowerBounds (compl '' D) := by
        rintro _ ⟨A, hA, rfl⟩
        exact compl_le_compl (hb hA)
      exact compl_le_compl_iff_le.1 (h2 this)
  · rintro ⟨h1, h2⟩
    constructor
    · rintro _ ⟨A, hA, rfl⟩
      exact compl_le_compl (h1 hA)
    · intro b hb
      have : bᶜ ∈ upperBounds D := by
        intro A hA
        exact le_compl_iff_le_compl.1 (hb ⟨A, hA, rfl⟩)
      exact le_compl_iff_le_compl.1 (h2 this)

/-- Continuity of `P` along one family in the official **meet** language.
Source: [[decision-problems-v2]] §1
Kind: D
Fidelity: exact
Hyps: n/a -/
def ContMeet {J : Designation E} (P : Prob J) (D : Set E) : Prop :=
  ∀ m, IsGLB D m → IsGLB {r | ∃ F : Finset E, ↑F ⊆ D ∧ r = P.P (F.inf id)} (P.P m)

/-- Continuity of `P` along one family in the **join** language:
`P (⨆ D) = sup {P (⨆ F) | F ⊆ D finite}` (no disjointness needed).
Source: [[decision-problems-v2]] Appendix A "Typing the designation" (line 329)
Kind: D
Fidelity: exact
Hyps: n/a -/
def ContJoin {J : Designation E} (P : Prob J) (D : Set E) : Prop :=
  ∀ m, IsLUB D m → IsLUB {r | ∃ F : Finset E, ↑F ⊆ D ∧ r = P.P (F.sup id)} (P.P m)

theorem isLUB_one_sub_image {S : Set ℝ} {a : ℝ} (h : IsGLB S a) :
    IsLUB ((fun r => 1 - r) '' S) (1 - a) := by
  constructor
  · rintro _ ⟨r, hr, rfl⟩
    have := h.1 hr
    linarith
  · intro c hc
    have : 1 - c ∈ lowerBounds S := by
      intro r hr
      have := hc ⟨r, hr, rfl⟩
      linarith
    have := h.2 this
    linarith

theorem isGLB_one_sub_image {S : Set ℝ} {a : ℝ} (h : IsLUB S a) :
    IsGLB ((fun r => 1 - r) '' S) (1 - a) := by
  constructor
  · rintro _ ⟨r, hr, rfl⟩
    have := h.1 hr
    linarith
  · intro c hc
    have : 1 - c ∈ upperBounds S := by
      intro r hr
      have := hc ⟨r, hr, rfl⟩
      linarith
    have := h.2 this
    linarith

/-- The finite sub-joins of `D` and the finite sub-meets of `compl '' D` have complementary
probabilities: `{P (⨆ F) | F ⊆ D} = (1 - ·) '' {P (⨅ G) | G ⊆ compl '' D}`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: n/a -/
theorem finset_sup_set_eq_one_sub_image {J : Designation E} (P : Prob J) (D : Set E) :
    {r | ∃ F : Finset E, ↑F ⊆ D ∧ r = P.P (F.sup id)} =
      (fun r => 1 - r) '' {r | ∃ G : Finset E, ↑G ⊆ compl '' D ∧ r = P.P (G.inf id)} := by
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨F, hF, rfl⟩
    refine ⟨P.P ((F.image compl).inf id), ⟨F.image compl, ?_, rfl⟩, ?_⟩
    · rw [Finset.coe_image]
      exact Set.image_mono hF
    · rw [Finset.inf_image]
      have : (F.inf (id ∘ compl)) = (F.sup id)ᶜ := by
        rw [Finset.compl_sup]
        rfl
      rw [this, P.compl]
      ring
  · rintro ⟨_, ⟨G, hG, rfl⟩, rfl⟩
    refine ⟨G.image compl, ?_, ?_⟩
    · rw [Finset.coe_image]
      intro A hA
      obtain ⟨B, hB, rfl⟩ := hA
      obtain ⟨C, hC, rfl⟩ := hG hB
      simpa using hC
    · rw [Finset.sup_image]
      have : (G.sup (id ∘ compl)) = (G.inf id)ᶜ := by
        rw [Finset.compl_inf]
        rfl
      rw [this, P.compl]

/-- **T8(a).** The join form of continuity along `D` is the meet form along the complemented
family `compl '' D`: designation may be typed in either language.
Source: [[decision-problems-v2]] Appendix A "Typing the designation" (line 329) | dp-core-2-060
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem contJoin_iff_contMeet_compl {J : Designation E} (P : Prob J) (D : Set E) :
    ContJoin P D ↔ ContMeet P (compl '' D) := by
  constructor
  · intro h m hm
    obtain ⟨m', rfl⟩ : ∃ m', m = m'ᶜ := ⟨mᶜ, (compl_compl m).symm⟩
    have hlub := (isGLB_compl_image_iff D m').1 hm
    have := h m' hlub
    rw [finset_sup_set_eq_one_sub_image] at this
    have h2 := isGLB_one_sub_image this
    rw [P.compl]
    have hS : ∀ S : Set ℝ, ((fun r : ℝ => 1 - r) '' ((fun r : ℝ => 1 - r) '' S)) = S := by
      intro S
      ext r
      constructor
      · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        simpa using ha
      · intro hr
        exact ⟨1 - r, ⟨r, hr, rfl⟩, by ring⟩
    rw [hS] at h2
    convert h2 using 1
  · intro h m hm
    have hglb := (isGLB_compl_image_iff D m).2 hm
    have := h mᶜ hglb
    rw [finset_sup_set_eq_one_sub_image]
    have h2 := isLUB_one_sub_image this
    rw [P.compl] at h2
    convert h2 using 1
    ring

/-- **The finite-sup lemma.** Let `g : ι → E` and suppose the complemented family
`{ (g i)ᶜ | i }` is designated with infimum `m`. Then `P mᶜ` is the least upper bound of
`{ P (⨆_{i ∈ s} g i) | s : Finset ι }`. (Countable additivity and purely-atomic-ness are both
instances.)
Source: [[decision-problems-v2]] §1 ("countable additivity in disguise", the downward step)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Prob.isLUB_range_finset_sup {ι : Type*} {J : Designation E} (P : Prob J) (g : ι → E)
    (hD : Set.range (fun i => (g i)ᶜ) ∈ J.1) (m : E) (hm : IsGLB (Set.range fun i => (g i)ᶜ) m) :
    IsLUB (Set.range fun s : Finset ι => P.P (s.sup g)) (P.P mᶜ) := by
  have hc := P.cont _ hD m hm
  constructor
  · rintro _ ⟨s, rfl⟩
    apply P.mono
    rw [le_compl_iff_le_compl, Finset.compl_sup]
    exact Finset.le_inf fun i _ => hm.1 ⟨i, rfl⟩
  · intro c hcU
    -- `1 - c` is a lower bound of the finite sub-meets of the complemented family
    have hlb : 1 - c ∈ lowerBounds {r | ∃ F : Finset E, ↑F ⊆ Set.range (fun i => (g i)ᶜ) ∧
        r = P.P (F.inf id)} := by
      rintro _ ⟨F, hF, rfl⟩
      -- pull `F` back to a finset of indices
      let idx : F → ι := fun A => Classical.choose (Set.mem_range.1 (hF (Finset.mem_coe.2 A.2)))
      have hidx : ∀ A : F, (g (idx A))ᶜ = A.1 :=
        fun A => Classical.choose_spec (Set.mem_range.1 (hF (Finset.mem_coe.2 A.2)))
      let s : Finset ι := F.attach.image idx
      have hle : F.sup (fun A : E => Aᶜ) ≤ s.sup g := by
        apply Finset.sup_le
        intro A hA
        have h1 : g (idx ⟨A, hA⟩) ≤ s.sup g :=
          Finset.le_sup (Finset.mem_image_of_mem idx (Finset.mem_attach F ⟨A, hA⟩))
        have h2 : (g (idx ⟨A, hA⟩))ᶜ = A := hidx ⟨A, hA⟩
        rw [← h2, compl_compl]
        exact h1
      have h1 : P.P (F.inf id) = 1 - P.P (F.sup (fun A : E => Aᶜ)) := by
        have := P.compl (F.inf id)
        rw [Finset.compl_inf] at this
        have h' : (F.sup fun A => (id A)ᶜ) = F.sup (fun A : E => Aᶜ) := rfl
        rw [h'] at this
        linarith
      have h2 : P.P (s.sup g) ≤ c := hcU ⟨s, rfl⟩
      have h3 := P.mono hle
      rw [h1]
      linarith
    have := hc.2 hlb
    rw [P.compl]
    linarith

end

end Cleanroom.Decision.DpWorldsJb
