import LogicalInduction.Framework.BooleanWorlds

/-!
# `bli-found` · Tags: the run's fresh-atom allocator and the tag-freeness predicates

Package `bli-found` (area `bli`), the FAF-facing root of both areas. This file is **D1** of the
mandate: the one allocator every package of the run uses when it adjoins decided atoms to a FAF
deductive process, and the freeness predicates its conservativity lemma (`Extend.lean`) and the
dependents' `hworld` transports take as hypotheses.

FAF's atom indices are `ℕ`. Every *public* atom FAF's processes emit has the form
`Nat.pair tag payload`, and the authoritative table at `ComputationClaimKind.godelCode`
(`Construction/Knowledge/Syntax.lean`) allocates tags `0`–`7`; `FinitePerturbationCounterexample`
uses `7` and `8` locally. This run allocates from `cleanroomBaseTag = 9` upward, family by family,
so nothing here can collide with a tag FAF already uses, and no two packages collide with each
other (they take distinct families from the registry on `freshAtom`).

Everything here is `D`/`L` by design (a foundation finishes on definitions). The FAF-facing
disjointness corollaries (`≠ quoteAtom`, `≠ paperPrimeSentence`, `≠ eventAtom`, …) and the process
facts about `paperDP`/`theoremDP` need the heavy `Construction.Paper` imports and live in
`PaperInstances.lean`; this file imports only `Framework.BooleanWorlds`.

Sources: [[plan]] §0.4 rule 10; [[anson-inventory]] 012; the mandate `bli-found-mandate` §D1.
-/

namespace Cleanroom.Bli.BliFound

open LogicalInduction LO.Propositional

/-! ## The tag space -/

/-- Base of the run's tag space: every atom this run allocates has
`(Nat.unpair a).1 ≥ cleanroomBaseTag`, so it is disjoint from FAF's public tags `0`–`7` and from
the two local tags `7`, `8` of `FinitePerturbationCounterexample`.
Source: [[plan]] §0.4 rule 10, [[anson-inventory]] 012
Kind: D
Fidelity: n/a -/
def cleanroomBaseTag : ℕ := 9

/-- The atom **index** of the fresh atom of family `family` with payload `payload`:
`Nat.pair (cleanroomBaseTag + family) payload`. Split out from `freshAtom` so that
computability lemmas can work on the `ℕ`-level code.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def freshAtomCode (family payload : ℕ) : ℕ := Nat.pair (cleanroomBaseTag + family) payload

/-- **The run's fresh-atom allocator.** The atom of family `family` with payload `payload`.

**Family registry** (add rows, never renumber; every family puts the *day* first in its payload,
`Nat.pair day rest`, so that `Size.atomDay` can read it):

| family | atoms | owner |
|---|---|---|
| `0` | state atoms `⌜𝑸_m = Q̂⌝`, payload `⟨m, q⟩` (`State.stateAtom`) | `bli-found` |
| `1` | policy points `⌜π(Q̂) = a⌝`, payload `⟨m, ⟨q, a⟩⟩` (`State.policyPoint`) | `bli-found` |
| `2` | realized actions `A_m = a`, payload `⟨m, a⟩` (`State.actionAt`) | `bli-found` |
| `3` | ledger atoms | `li-quote-lane` |
| `4` | projection / splice atoms | `li-projection`, `li-splice-condition` |
| `5` | obstruction atoms | `def-obstruction` |
| `6` | exogenous-trader atoms | `corr-exo-trader` |
| `7` | overlay-witness atoms (day-`0` re-pricing witness, payload `Nat.pair day rest`) | `bli-transfer` |
| `8`–`15` | reserved | — |

Source: [[plan]] §0.4 rule 10, [[anson-inventory]] 012
Kind: D
Fidelity: n/a -/
def freshAtom (family payload : ℕ) : Sentence := Formula.atom (freshAtomCode family payload)

/-- `Nat.unpair` of a fresh-atom code.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma freshAtomCode_unpair (family payload : ℕ) :
    (freshAtomCode family payload).unpair = (cleanroomBaseTag + family, payload) := by
  simp [freshAtomCode]

/-- The one atom index of a fresh atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma sentenceAtomCodes_freshAtom (family payload : ℕ) :
    sentenceAtomCodes (freshAtom family payload) = {freshAtomCode family payload} := rfl

/-- The fresh-atom code is injective in the pair `(family, payload)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshAtomCode_injective :
    Function.Injective (fun p : ℕ × ℕ => freshAtomCode p.1 p.2) := by
  rintro ⟨f, p⟩ ⟨f', p'⟩ h
  simp only [freshAtomCode, Nat.pair_eq_pair] at h
  ext <;> simp <;> omega

/-- The fresh atom is injective in the pair `(family, payload)`.
Source: mandate D1
Kind: L
Fidelity: exact -/
lemma freshAtom_injective :
    Function.Injective (fun p : ℕ × ℕ => freshAtom p.1 p.2) := by
  rintro ⟨f, p⟩ ⟨f', p'⟩ h
  exact freshAtomCode_injective (Formula.atom.inj h)

/-- `freshAtomCode_inj`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshAtomCode_inj {f p f' p' : ℕ} :
    freshAtomCode f p = freshAtomCode f' p' ↔ f = f' ∧ p = p' := by
  constructor
  · intro h
    have := freshAtomCode_injective (a₁ := (f, p)) (a₂ := (f', p')) h
    simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

/-- `freshAtom_inj`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshAtom_inj {f p f' p' : ℕ} :
    freshAtom f p = freshAtom f' p' ↔ f = f' ∧ p = p' := by
  constructor
  · intro h
    have := freshAtom_injective (a₁ := (f, p)) (a₂ := (f', p')) h
    simpa using this
  · rintro ⟨rfl, rfl⟩; rfl

/-- Every atom index of `freshAtom f p` carries the tag `cleanroomBaseTag + f`.
Source: mandate D1
Kind: L
Fidelity: exact -/
lemma freshAtom_tag (f p : ℕ) :
    ∀ a ∈ sentenceAtomCodes (freshAtom f p), a.unpair.1 = cleanroomBaseTag + f := by
  intro a ha
  rw [sentenceAtomCodes_freshAtom, Finset.mem_singleton] at ha
  subst ha
  simp

/-- Every atom index of a fresh atom has a tag above every tag FAF uses (`0`–`8`).
Source: mandate D1
Kind: L
Fidelity: exact -/
lemma freshAtom_ne_faf (f p : ℕ) :
    ∀ a ∈ sentenceAtomCodes (freshAtom f p), 8 < a.unpair.1 := by
  intro a ha
  rw [freshAtom_tag f p a ha]
  simp only [cleanroomBaseTag]
  omega

/-- The fresh-atom code itself has a tag above every tag FAF uses.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshAtomCode_tag_gt (f p : ℕ) : 8 < (freshAtomCode f p).unpair.1 := by
  simp only [freshAtomCode_unpair, cleanroomBaseTag]
  omega

/-! ## Tag-freeness predicates

`TagFreeSentence t φ` mirrors FAF's `SemanticPrimeFreshSentence` (`Construction/Knowledge/Syntax.lean`):
no atom of `φ` carries the tag `t`. These are the hypotheses a dependent takes on the *base*
process when it adjoins atoms of a family, and what `PaperInstances.lean` discharges for
`paperDP`/`theoremDP`. -/

/-- No atom of `φ` carries the tag `t`.
Source: mandate D1 (mirrors FAF's `SemanticPrimeFreshSentence`)
Kind: D
Fidelity: n/a -/
def TagFreeSentence (t : ℕ) (φ : Sentence) : Prop :=
  ∀ a ∈ sentenceAtomCodes φ, a.unpair.1 ≠ t

/-- No sentence of any stage of `DP` mentions an atom of tag `t`.
Source: mandate D1
Kind: D
Fidelity: n/a -/
def TagFreeProcess (t : ℕ) (DP : DeductiveProcess) : Prop :=
  ∀ k, ∀ φ ∈ DP.D k, TagFreeSentence t φ

/-- A sentence family (e.g. an abstract quote family `IntrospectionIntervalQuote.quote`) none of
whose members mentions an atom of tag `t`. This is the hypothesis consumers of an *abstract*
quote package take; it is provable for the concrete `quoteAtom`-built instances only
(`PaperInstances.lean`).
Source: mandate D1, Known issue 8
Kind: D
Fidelity: n/a -/
def TagFreeFamily (t : ℕ) (q : ℕ → Sentence) : Prop :=
  ∀ n, TagFreeSentence t (q n)

/-- Every atom of `φ` has a tag below `cleanroomBaseTag`: `φ` mentions no atom this run
allocates (it lives in FAF's own vocabulary).
Source: mandate D1
Kind: D
Fidelity: n/a -/
def CleanroomFreeSentence (φ : Sentence) : Prop :=
  ∀ a ∈ sentenceAtomCodes φ, a.unpair.1 < cleanroomBaseTag

/-- Every stage of `DP` consists of cleanroom-free sentences.
Source: mandate D1
Kind: D
Fidelity: n/a -/
def CleanroomFreeProcess (DP : DeductiveProcess) : Prop :=
  ∀ k, ∀ φ ∈ DP.D k, CleanroomFreeSentence φ

/-- A cleanroom-free sentence is tag-free for every tag at or above the base.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma CleanroomFreeSentence.tagFree {φ : Sentence} (h : CleanroomFreeSentence φ) {t : ℕ}
    (ht : cleanroomBaseTag ≤ t) : TagFreeSentence t φ := by
  intro a ha
  have := h a ha
  omega

/-- A cleanroom-free process is tag-free for every tag at or above the base.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma CleanroomFreeProcess.tagFree {DP : DeductiveProcess} (h : CleanroomFreeProcess DP) {t : ℕ}
    (ht : cleanroomBaseTag ≤ t) : TagFreeProcess t DP :=
  fun k φ hφ => (h k φ hφ).tagFree ht

/-- A fresh-atom code never occurs in a cleanroom-free sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma CleanroomFreeSentence.freshAtomCode_notMem {φ : Sentence} (h : CleanroomFreeSentence φ)
    (f p : ℕ) : freshAtomCode f p ∉ sentenceAtomCodes φ := by
  intro hmem
  have := h _ hmem
  simp [cleanroomBaseTag] at this

/-- A fresh-atom code of family `f` never occurs in a sentence tag-free for `f`'s tag.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma TagFreeSentence.freshAtomCode_notMem {f : ℕ} {φ : Sentence}
    (h : TagFreeSentence (cleanroomBaseTag + f) φ) (p : ℕ) :
    freshAtomCode f p ∉ sentenceAtomCodes φ := by
  intro hmem
  have := h _ hmem
  simp at this

/-- Tag-freeness is closed under the connectives (used to lift freeness from generators).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma TagFreeSentence.and {t : ℕ} {φ ψ : Sentence} (hφ : TagFreeSentence t φ)
    (hψ : TagFreeSentence t ψ) : TagFreeSentence t (φ ⋏ ψ) := by
  intro a ha
  rw [sentenceAtomCodes_and, Finset.mem_union] at ha
  exact ha.elim (hφ a) (hψ a)

/-- `TagFreeSentence.or`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma TagFreeSentence.or {t : ℕ} {φ ψ : Sentence} (hφ : TagFreeSentence t φ)
    (hψ : TagFreeSentence t ψ) : TagFreeSentence t (φ ⋎ ψ) := by
  intro a ha
  rw [sentenceAtomCodes_or, Finset.mem_union] at ha
  exact ha.elim (hφ a) (hψ a)

/-- `TagFreeSentence.imp`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma TagFreeSentence.imp {t : ℕ} {φ ψ : Sentence} (hφ : TagFreeSentence t φ)
    (hψ : TagFreeSentence t ψ) : TagFreeSentence t (φ 🡒 ψ) := by
  intro a ha
  rw [sentenceAtomCodes_imp, Finset.mem_union] at ha
  exact ha.elim (hφ a) (hψ a)

/-- `TagFreeSentence.neg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma TagFreeSentence.neg {t : ℕ} {φ : Sentence} (hφ : TagFreeSentence t φ) :
    TagFreeSentence t (∼φ) := by
  intro a ha
  rw [sentenceAtomCodes_neg] at ha
  exact hφ a ha

/-- `tagFreeSentence_falsum`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma tagFreeSentence_falsum (t : ℕ) : TagFreeSentence t (⊥ : Sentence) := by
  intro a ha
  simp at ha

/-- A fresh atom of family `f` is tag-free for every other family's tag.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshAtom_tagFree_of_ne {f p t : ℕ} (h : t ≠ cleanroomBaseTag + f) :
    TagFreeSentence t (freshAtom f p) := by
  intro a ha
  rw [freshAtom_tag f p a ha]
  exact h.symm

/-- Two fresh atoms of different families are different sentences.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma freshAtom_ne_of_family_ne {f p f' p' : ℕ} (h : f ≠ f') : freshAtom f p ≠ freshAtom f' p' := by
  intro heq
  exact h (freshAtom_inj.mp heq).1

end Cleanroom.Bli.BliFound
