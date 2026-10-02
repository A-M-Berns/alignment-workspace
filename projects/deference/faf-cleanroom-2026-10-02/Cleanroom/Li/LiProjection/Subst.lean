import LogicalInduction.Framework.Criterion
import LogicalInduction.Framework.BooleanWorlds
import Cleanroom.Bli.BliFound.Tags

/-!
# `li-projection` · Subst: atom substitution, the Shannon split and freshness

Package `Cleanroom.Li.LiProjection` ([[li-projection-mandate]]), file 1 of the layout. The
substitution `φ⟦u := ⊤⟧` / `φ⟦u := ⊥⟧` (Foundation's `Formula.subst` at the substitution
`substAtom u b`), the world operation `setAtom v u b` that fixes one atom, the Shannon split
`(setAtom v u b).Holds φ ↔ v.Holds (φ⟦substAtom u b⟧)` (T1.1), atom-freeness of sentences and
processes, and the **freshness lemma** (T1.2): over a process that never mentions `u`, a world
stays consistent with every stage when its `u`-bit is flipped, so both bits are plausible at every
day. The dose-response zip's Lean *defined* this ("`extPC`", its AUDIT §3.3); here it is a theorem.

Also here: the family-`4` fresh atoms `projAtom k` of the run's registry
(`Cleanroom.Bli.BliFound.Tags`), with the payload convention of record `Nat.pair 0 (Nat.pair 0 k)`
(day `0` first, then sub-family `0` — `li-splice-condition` takes sub-family `1` — then the index).

Scope: nothing here is about two inductors; the one-way tag applies from `Underdetermination.lean` on.
-/

namespace Cleanroom.Li.LiProjection

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## Substitution of one atom by a truth constant -/

/-- The substitution sending the atom `u` to `⊤` (`b = true`) or `⊥` (`b = false`) and every
other atom to itself. `φ⟦substAtom u true⟧` is the dose-response note's `α_φ`,
`φ⟦substAtom u false⟧` its `β_φ`.
Source: [[dose-response]] §6.1 Lemma A (the `α_φ`/`β_φ` of the extended market)
Kind: D
Fidelity: exact -/
def substAtom (u : ℕ) (b : Bool) : Substitution ℕ :=
  fun a => if a = u then (if b then ⊤ else ⊥) else Formula.atom a

/-- `substAtom_self`: the substitution at the atom it replaces.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma substAtom_self (u : ℕ) (b : Bool) : substAtom u b u = if b then ⊤ else ⊥ := by
  simp [substAtom]

/-- `substAtom_of_ne`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma substAtom_of_ne (u : ℕ) (b : Bool) {a : ℕ} (h : a ≠ u) :
    substAtom u b a = Formula.atom a := by
  simp [substAtom, h]

/-- A p.c. world with the atom `u` forced to `b` (and every other atom as in `v`).
This is the mandate's `PCWorld.set`, named `setAtom` because dot-notation on FAF's `PCWorld`
cannot reach a declaration of this package.
Source: [[dose-response]] §6.1 Lemma A (the extended world `(W, b)`)
Kind: D
Fidelity: exact -/
def setAtom (v : PCWorld) (u : ℕ) (b : Bool) : PCWorld :=
  fun a => if a = u then b = true else v a

/-- `setAtom_self`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma setAtom_self (v : PCWorld) (u : ℕ) (b : Bool) : setAtom v u b u ↔ b = true := by
  simp [setAtom]

/-- `setAtom_of_ne`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma setAtom_of_ne (v : PCWorld) (u : ℕ) (b : Bool) {a : ℕ} (h : a ≠ u) :
    (setAtom v u b a ↔ v a) := by
  simp [setAtom, h]

/-- The world with `u` set to `true` holds the atom `u`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma setAtom_holds_atom_true (v : PCWorld) (u : ℕ) :
    (setAtom v u true).Holds (Formula.atom u) := by
  rw [PCWorld.holds_atom]; simp [setAtom]

/-- The world with `u` set to `false` falsifies the atom `u`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma setAtom_not_holds_atom_false (v : PCWorld) (u : ℕ) :
    ¬ (setAtom v u false).Holds (Formula.atom u) := by
  rw [PCWorld.holds_atom]; simp [setAtom]

/-! ## T1.1 The Shannon split -/

/-- **Shannon split.** Forcing the atom `u` to `b` in the world is the same as substituting the
constant for `u` in the sentence: `(setAtom v u b).Holds φ ↔ v.Holds (φ⟦substAtom u b⟧)`.
Source: [[dose-response]] §6.1 Lemma A, `𝟙_{(W,1)}(φ) = 𝟙_W(α_φ)`, `𝟙_{(W,0)}(φ) = 𝟙_W(β_φ)`
Kind: P
Fidelity: exact -/
lemma holds_setAtom_iff (v : PCWorld) (u : ℕ) (b : Bool) :
    ∀ φ : Sentence, (setAtom v u b).Holds φ ↔ v.Holds (φ⟦substAtom u b⟧) := by
  intro φ
  induction φ using Formula.rec' with
  | hfalsum => exact Iff.rfl
  | hatom a =>
      show setAtom v u b a ↔ v.Holds (substAtom u b a)
      by_cases h : a = u
      · subst h
        simp only [setAtom, if_true, substAtom]
        cases b
        · simp [PCWorld.Holds, Formula.Boolean.val]
        · simp [PCWorld.Holds, Formula.Boolean.val, Formula.top_def]
      · rw [setAtom_of_ne v u b h, substAtom_of_ne u b h, PCWorld.holds_atom]
  | himp φ ψ ihφ ihψ =>
      show ((setAtom v u b).Holds φ → (setAtom v u b).Holds ψ) ↔
        (v.Holds (φ⟦substAtom u b⟧) → v.Holds (ψ⟦substAtom u b⟧))
      rw [ihφ, ihψ]
  | hand φ ψ ihφ ihψ =>
      show ((setAtom v u b).Holds φ ∧ (setAtom v u b).Holds ψ) ↔
        (v.Holds (φ⟦substAtom u b⟧) ∧ v.Holds (ψ⟦substAtom u b⟧))
      rw [ihφ, ihψ]
  | hor φ ψ ihφ ihψ =>
      show ((setAtom v u b).Holds φ ∨ (setAtom v u b).Holds ψ) ↔
        (v.Holds (φ⟦substAtom u b⟧) ∨ v.Holds (ψ⟦substAtom u b⟧))
      rw [ihφ, ihψ]

/-- Shannon split, payout form: `(setAtom v u b).payout φ = v.payout (φ⟦substAtom u b⟧)`.
Source: [[dose-response]] §6.1 Lemma A (LI accounting line)
Kind: L
Fidelity: exact -/
lemma payout_setAtom (v : PCWorld) (u : ℕ) (b : Bool) (φ : Sentence) :
    (setAtom v u b).payout φ = v.payout (φ⟦substAtom u b⟧) := by
  unfold PCWorld.payout
  by_cases h : (setAtom v u b).Holds φ
  · rw [if_pos h, if_pos ((holds_setAtom_iff v u b φ).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((holds_setAtom_iff v u b φ).mpr h'))]

/-- A world's own bit: `v.Holds φ ↔ v.Holds (φ⟦substAtom u (decide (v u))⟧)`.
Source: [[dose-response]] §6.1 Lemma A
Kind: L
Fidelity: exact -/
lemma holds_iff_holds_subst_self (v : PCWorld) (u : ℕ) [Decidable (v u)] (φ : Sentence) :
    v.Holds φ ↔ v.Holds (φ⟦substAtom u (decide (v u))⟧) := by
  rw [← holds_setAtom_iff]
  apply PCWorld.holds_congr_atomCodes
  intro a _
  by_cases h : a = u
  · subst h
    simp [setAtom]
  · exact (setAtom_of_ne v u _ h).symm

/-! ## Atom-freeness -/

/-- `φ` does not mention the atom `u`.
Source: [[dose-response]] §6.1 ("base" sentences); mandate T1 table
Kind: D
Fidelity: exact -/
def AtomFreeSentence (u : ℕ) (φ : Sentence) : Prop := u ∉ sentenceAtomCodes φ

/-- No stage of `DP` mentions the atom `u` — `u` is **fresh** for the process.
Source: [[dose-response]] §6.1 ("the deductive process never mentions `u`")
Kind: D
Fidelity: exact -/
def AtomFreeProcess (u : ℕ) (DP : DeductiveProcess) : Prop :=
  ∀ k, ∀ φ ∈ DP.D k, AtomFreeSentence u φ

/-- `AtomFreeSentence.imp`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma AtomFreeSentence.imp {u : ℕ} {φ ψ : Sentence} (hφ : AtomFreeSentence u φ)
    (hψ : AtomFreeSentence u ψ) : AtomFreeSentence u (φ 🡒 ψ) := by
  intro h
  rw [sentenceAtomCodes_imp, Finset.mem_union] at h
  exact h.elim hφ hψ

/-- `AtomFreeSentence.and`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma AtomFreeSentence.and {u : ℕ} {φ ψ : Sentence} (hφ : AtomFreeSentence u φ)
    (hψ : AtomFreeSentence u ψ) : AtomFreeSentence u (φ ⋏ ψ) := by
  intro h
  rw [sentenceAtomCodes_and, Finset.mem_union] at h
  exact h.elim hφ hψ

/-- `AtomFreeSentence.or`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma AtomFreeSentence.or {u : ℕ} {φ ψ : Sentence} (hφ : AtomFreeSentence u φ)
    (hψ : AtomFreeSentence u ψ) : AtomFreeSentence u (φ ⋎ ψ) := by
  intro h
  rw [sentenceAtomCodes_or, Finset.mem_union] at h
  exact h.elim hφ hψ

/-- `AtomFreeSentence.neg`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma AtomFreeSentence.neg {u : ℕ} {φ : Sentence} (hφ : AtomFreeSentence u φ) :
    AtomFreeSentence u (∼φ) := by
  intro h
  rw [sentenceAtomCodes_neg] at h
  exact hφ h

/-- `AtomFreeSentence.of_imp_left`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma AtomFreeSentence.of_imp_left {u : ℕ} {φ ψ : Sentence}
    (h : AtomFreeSentence u (φ 🡒 ψ)) : AtomFreeSentence u φ := by
  intro hm
  exact h (by rw [sentenceAtomCodes_imp, Finset.mem_union]; exact Or.inl hm)

/-- `AtomFreeSentence.of_imp_right`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma AtomFreeSentence.of_imp_right {u : ℕ} {φ ψ : Sentence}
    (h : AtomFreeSentence u (φ 🡒 ψ)) : AtomFreeSentence u ψ := by
  intro hm
  exact h (by rw [sentenceAtomCodes_imp, Finset.mem_union]; exact Or.inr hm)

/-- `AtomFreeSentence.of_and_left`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma AtomFreeSentence.of_and_left {u : ℕ} {φ ψ : Sentence}
    (h : AtomFreeSentence u (φ ⋏ ψ)) : AtomFreeSentence u φ := by
  intro hm
  exact h (by rw [sentenceAtomCodes_and, Finset.mem_union]; exact Or.inl hm)

/-- `AtomFreeSentence.of_and_right`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma AtomFreeSentence.of_and_right {u : ℕ} {φ ψ : Sentence}
    (h : AtomFreeSentence u (φ ⋏ ψ)) : AtomFreeSentence u ψ := by
  intro hm
  exact h (by rw [sentenceAtomCodes_and, Finset.mem_union]; exact Or.inr hm)

/-- `AtomFreeSentence.of_or_left`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma AtomFreeSentence.of_or_left {u : ℕ} {φ ψ : Sentence}
    (h : AtomFreeSentence u (φ ⋎ ψ)) : AtomFreeSentence u φ := by
  intro hm
  exact h (by rw [sentenceAtomCodes_or, Finset.mem_union]; exact Or.inl hm)

/-- `AtomFreeSentence.of_or_right`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma AtomFreeSentence.of_or_right {u : ℕ} {φ ψ : Sentence}
    (h : AtomFreeSentence u (φ ⋎ ψ)) : AtomFreeSentence u ψ := by
  intro hm
  exact h (by rw [sentenceAtomCodes_or, Finset.mem_union]; exact Or.inr hm)

/-- `AtomFreeSentence.atom_ne`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma AtomFreeSentence.atom_ne {u a : ℕ} (h : AtomFreeSentence u (Formula.atom a)) : a ≠ u := by
  intro hau
  exact h (by rw [sentenceAtomCodes_atom, Finset.mem_singleton]; exact hau.symm)

/-- `atomFreeSentence_atom_of_ne`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomFreeSentence_atom_of_ne {u a : ℕ} (h : a ≠ u) : AtomFreeSentence u (Formula.atom a) := by
  intro hm
  rw [sentenceAtomCodes_atom, Finset.mem_singleton] at hm
  exact h hm.symm

/-- `atomFreeSentence_top`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomFreeSentence_top (u : ℕ) : AtomFreeSentence u (⊤ : Sentence) := by
  intro h; rw [sentenceAtomCodes_verum] at h; exact Finset.notMem_empty _ h

/-- `atomFreeSentence_bot`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomFreeSentence_bot (u : ℕ) : AtomFreeSentence u (⊥ : Sentence) := by
  intro h; rw [sentenceAtomCodes_falsum] at h; exact Finset.notMem_empty _ h

/-- The substituted sentence never mentions `u`.
Source: [[dose-response]] §6.1 Lemma A (`α_φ`, `β_φ` are base sentences)
Kind: P
Fidelity: exact -/
lemma atomFreeSentence_subst (u : ℕ) (b : Bool) :
    ∀ φ : Sentence, AtomFreeSentence u (φ⟦substAtom u b⟧) := by
  intro φ
  induction φ using Formula.rec' with
  | hfalsum => exact atomFreeSentence_bot u
  | hatom a =>
      show AtomFreeSentence u (substAtom u b a)
      by_cases h : a = u
      · subst h
        simp only [substAtom, if_true]
        cases b
        · exact atomFreeSentence_bot _
        · exact atomFreeSentence_top _
      · rw [substAtom_of_ne u b h]
        exact atomFreeSentence_atom_of_ne h
  | himp φ ψ ihφ ihψ => exact ihφ.imp ihψ
  | hand φ ψ ihφ ihψ => exact ihφ.and ihψ
  | hor φ ψ ihφ ihψ => exact ihφ.or ihψ

/-- On a `u`-free sentence the substitution is the identity: `AtomFreeSentence u φ → φ⟦substAtom u b⟧ = φ`.
Source: [[dose-response]] §6.1 Lemma A ("base `φ` has `α_φ = β_φ = φ`")
Kind: P
Fidelity: exact -/
lemma subst_eq_self_of_atomFree (u : ℕ) (b : Bool) :
    ∀ φ : Sentence, AtomFreeSentence u φ → φ⟦substAtom u b⟧ = φ := by
  intro φ
  induction φ using Formula.rec' with
  | hfalsum => intro _; rfl
  | hatom a =>
      intro h
      show substAtom u b a = Formula.atom a
      exact substAtom_of_ne u b h.atom_ne
  | himp φ ψ ihφ ihψ =>
      intro h
      show φ⟦substAtom u b⟧ 🡒 ψ⟦substAtom u b⟧ = φ 🡒 ψ
      rw [ihφ h.of_imp_left, ihψ h.of_imp_right]
  | hand φ ψ ihφ ihψ =>
      intro h
      show φ⟦substAtom u b⟧ ⋏ ψ⟦substAtom u b⟧ = φ ⋏ ψ
      rw [ihφ h.of_and_left, ihψ h.of_and_right]
  | hor φ ψ ihφ ihψ =>
      intro h
      show φ⟦substAtom u b⟧ ⋎ ψ⟦substAtom u b⟧ = φ ⋎ ψ
      rw [ihφ h.of_or_left, ihψ h.of_or_right]

/-- Substituting for `u` in the atom `u` gives the constant.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma subst_atom_self (u : ℕ) (b : Bool) :
    (Formula.atom u : Sentence)⟦substAtom u b⟧ = if b then ⊤ else ⊥ := by
  show substAtom u b u = _
  simp [substAtom]

/-- Forcing `u` does not change the verdict on a `u`-free sentence.
Source: [[dose-response]] §6.1 Lemma A
Kind: L
Fidelity: exact -/
lemma holds_setAtom_of_atomFree (v : PCWorld) (u : ℕ) (b : Bool) {φ : Sentence}
    (h : AtomFreeSentence u φ) : ((setAtom v u b).Holds φ ↔ v.Holds φ) := by
  rw [holds_setAtom_iff, subst_eq_self_of_atomFree u b φ h]

/-! ## T1.2 The freshness lemma -/

/-- **Freshness lemma.** Over a process that never mentions `u`, a world is consistent with a
stage iff the same world with its `u`-bit forced is. This is what the dose-response zip's Lean
took as the definition of extended plausibility (`extPC`, its AUDIT §3.3); here it is a theorem,
derived from the Shannon split `holds_setAtom_iff` and `subst_eq_self_of_atomFree` (FAF's
`PCWorld.holds_congr_atomCodes` enters only through `holds_iff_holds_subst_self`).
Source: [[dose-response]] §6.1 Lemma A ("the plausible extended worlds are exactly the pairs `(W, b)`"); [[anson-2-inventory]] 028
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem consistentWith_setAtom_iff {u : ℕ} {DP : DeductiveProcess} (hu : AtomFreeProcess u DP)
    (v : PCWorld) (b : Bool) (n : ℕ) :
    (v.ConsistentWith (DP.D n) ↔ (setAtom v u b).ConsistentWith (DP.D n)) := by
  constructor
  · intro hv φ hφ
    exact (holds_setAtom_of_atomFree v u b (hu n φ hφ)).mpr (hv φ hφ)
  · intro hv φ hφ
    exact (holds_setAtom_of_atomFree v u b (hu n φ hφ)).mp (hv φ hφ)

/-- Both bits of a fresh atom are plausible at every day: there is a stage-consistent world
holding `u` (the premise shape of `lic_nonDogmatism`).
Source: [[dose-response]] §6.1 Lemma A ("both bits stay plausible forever"); [[anson-2-inventory]] 028
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem exists_consistent_holds_atom {u : ℕ} {DP : DeductiveProcess} (hu : AtomFreeProcess u DP)
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ v.Holds (Formula.atom u) := by
  obtain ⟨v, hv⟩ := hworld n
  exact ⟨setAtom v u true, (consistentWith_setAtom_iff hu v true n).mp hv,
    setAtom_holds_atom_true v u⟩

/-- Both bits of a fresh atom are plausible at every day: there is a stage-consistent world
falsifying `u` (the premise shape of `lic_nonDogmatism_dual`).
Source: [[dose-response]] §6.1 Lemma A; [[anson-2-inventory]] 028
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem exists_consistent_not_holds_atom {u : ℕ} {DP : DeductiveProcess}
    (hu : AtomFreeProcess u DP) (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith (DP.D n)) (n : ℕ) :
    ∃ v : PCWorld, v.ConsistentWith (DP.D n) ∧ ¬ v.Holds (Formula.atom u) := by
  obtain ⟨v, hv⟩ := hworld n
  exact ⟨setAtom v u false, (consistentWith_setAtom_iff hu v false n).mp hv,
    setAtom_not_holds_atom_false v u⟩

/-- A fresh atom is never decided by the completed theory either: both bits survive.
Source: [[dose-response]] §6.1 Lemma A
Kind: L
Fidelity: exact -/
theorem consistentWithTheory_setAtom_iff {u : ℕ} {DP : DeductiveProcess}
    (hu : AtomFreeProcess u DP) (v : PCWorld) (b : Bool) :
    (v.ConsistentWithTheory DP ↔ (setAtom v u b).ConsistentWithTheory DP) := by
  constructor
  · intro hv n; exact (consistentWith_setAtom_iff hu v b n).mp (hv n)
  · intro hv n; exact (consistentWith_setAtom_iff hu v b n).mpr (hv n)

/-! ## The family-4 fresh atoms -/

/-- The atom **index** of the `k`-th projection atom: family `4` of the run's registry, payload
`Nat.pair 0 (Nat.pair 0 k)` — day `0` first (registry rule, so `Size.atomDay` reads `0`), then
sub-family `0` (this package; `li-splice-condition` takes sub-family `1`), then the index `k`.
Source: mandate header (payload convention of record); [[plan]] §0.4 rule 10
Kind: D
Fidelity: n/a -/
def projAtomCode (k : ℕ) : ℕ := freshAtomCode 4 (Nat.pair 0 (Nat.pair 0 k))

/-- The `k`-th projection atom, as a sentence.
Source: mandate header; [[plan]] §0.4 rule 10
Kind: D
Fidelity: n/a -/
def projAtom (k : ℕ) : Sentence := Formula.atom (projAtomCode k)

/-- `projAtom_eq_freshAtom`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma projAtom_eq_freshAtom (k : ℕ) : projAtom k = freshAtom 4 (Nat.pair 0 (Nat.pair 0 k)) := rfl

/-- Distinct indices give distinct atoms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma projAtomCode_injective : Function.Injective projAtomCode := by
  intro k k' h
  have := (freshAtomCode_inj.mp h).2
  rw [Nat.pair_eq_pair] at this
  have := this.2
  rw [Nat.pair_eq_pair] at this
  exact this.2

/-- A projection atom's tag is above every tag FAF uses (`0`–`8`).
Source: none: infrastructure (`bli-found` `freshAtom_ne_faf`)
Kind: L
Fidelity: n/a -/
lemma projAtom_ne_faf (k : ℕ) : 8 < (projAtomCode k).unpair.1 :=
  freshAtomCode_tag_gt 4 _

/-- A cleanroom-free sentence (every atom in FAF's own vocabulary) is free of every projection atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomFreeSentence_of_cleanroomFree {φ : Sentence} (h : CleanroomFreeSentence φ) (k : ℕ) :
    AtomFreeSentence (projAtomCode k) φ :=
  h.freshAtomCode_notMem 4 _

/-- A cleanroom-free process (e.g. `paperDP T`, by `bli-found`'s `paperDP_cleanroomFree`) is free
of every projection atom.
Source: mandate T1.2 (`AtomFreeProcess (projAtomCode k) (paperDP T)`)
Kind: L
Fidelity: exact -/
lemma atomFreeProcess_of_cleanroomFree {DP : DeductiveProcess} (h : CleanroomFreeProcess DP)
    (k : ℕ) : AtomFreeProcess (projAtomCode k) DP :=
  fun n φ hφ => atomFreeSentence_of_cleanroomFree (h n φ hφ) k

/-- A sentence tag-free for family `4`'s tag is free of every projection atom (so `li-quote-lane`'s
family-`3` ledger atoms never collide with projection atoms).
Source: mandate T1.2 (freshness relative to the ledger is family `4 ≠ 3`)
Kind: L
Fidelity: exact -/
lemma atomFreeSentence_of_tagFree {φ : Sentence} (h : TagFreeSentence (cleanroomBaseTag + 4) φ)
    (k : ℕ) : AtomFreeSentence (projAtomCode k) φ :=
  h.freshAtomCode_notMem _

/-- A process tag-free for family `4`'s tag is free of every projection atom.
Source: mandate T1.2
Kind: L
Fidelity: exact -/
lemma atomFreeProcess_of_tagFree {DP : DeductiveProcess}
    (h : TagFreeProcess (cleanroomBaseTag + 4) DP) (k : ℕ) :
    AtomFreeProcess (projAtomCode k) DP :=
  fun n φ hφ => atomFreeSentence_of_tagFree (h n φ hφ) k

end Cleanroom.Li.LiProjection
