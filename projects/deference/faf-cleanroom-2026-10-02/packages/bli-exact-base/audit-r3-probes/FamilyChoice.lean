import Cleanroom.Bli.BliExactBase.Segment

/-!
# Probe (bli-exact-base audit r3, fidelity): the table the quantified cell quote code must decide
is itself selected by `Classical.choice`

Repair round 2 restated the OPEN row as
`linked_segment_day_exists : ∃ H n (q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)), 2 ≤ n ∧ n < H ∧ ⌜⊤⌝ ∈ pinned (linkedCFq H q) segmentIndex n`,
so that the program code is quantified and the row is "a genuine conjecture about the kernel".
But the predicate that `q` must decide, `spliceCellTruth H linkedPrice halfRound`, is a predicate
of `linkedPrice`, and `linkedPrice n` is the kernel mixture over the day-`n` family of record
`WAt n`, which re-indexes `W₀ n := Classical.choose (Classical.choose_spec (exists_completeFor …))`
(`k₀_is_choice`, `W₀_is_choice`, `linkedPrice_is_kernel_of_choice`, all `rfl`). The only fact
Lean has about `W₀ n` is its spec `0 < k ∧ consistent ∧ CompleteFor D (smallAtoms n) W`, and that
spec is blind to multiplicity: appending another copy of any member keeps it (`spec_of_snoc`).
The kernel's price at a non-overridden atom is the family's frequency (`kMix_atom_freq`), which a
duplicate changes whenever the family takes both values at the atom (`kMix_snoc_ne`); at every
stage of `paperDP 𝗜𝚺₁` and every day `n ≥ 2` this happens at the run-family atom `siblingCode`
(payload `⟨0, 1⟩`, a sibling of `freshCoord`), which is day-`n` small, stage-fresh, not
overridden by the kernel, and on which every complete family takes both values
(`kernel_price_depends_on_family`). So the day-`n` rounded table — the data the code `q` must
decide on day `n` — is not determined by the spec of the chosen family: with enough copies of a
world holding `siblingCode` the frequency passes `1/2` (cell `1`), with enough copies of one
refuting it, it stays below (cell `0`), and both families meet the spec.

Consequence (argued in the audit, not machine-checked): the shortest program deciding
`spliceCellTruth H linkedPrice halfRound` has length at least the Kolmogorov complexity of the
rounded day-`n` tables for `n < H`, and the spec admits families whose rounded tables are
incompressible (there are at least `2 ^ |smallAtoms n|` distinct rounded tables over complete
families, one per choice of which free atoms sit above `1/2`, while `|smallAtoms n|` is far above
`sizeBound n`); for such a choice no `q` has a day-`n` small literal on any day `< H`, so the row
is false; for the canonical family (every consistent pattern once) a uniform program should exist,
so the row is plausibly true. The row is therefore, as in round 2's B1, a statement about what
`Classical.choice` returned — now the family rather than the code — and is neither provable nor
refutable without fixing the family.
-/

namespace Cleanroom.Bli.BliExactBase.AuditR3Fid

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliLinkageB Cleanroom.Bli.BliLinkage
open Cleanroom.Bli.BliExactBase Cleanroom.Bli.BliExactBase.Kernel Cleanroom.Bli.BliExactBase.Segment

/-! ## The linked table is the kernel over a `Classical.choice`-selected family (definitional) -/

/-- The chosen size is `Classical.choose` of `exists_completeFor`. -/
theorem k₀_is_choice (n : ℕ) :
    k₀ n = Classical.choose (exists_completeFor ((paperDP 𝗜𝚺₁).D n) (smallAtoms n)
      (paperDP_hworld 𝗜𝚺₁ n)) := rfl

/-- The chosen family is `Classical.choose` of the spec of the chosen size. -/
theorem W₀_is_choice (n : ℕ) :
    W₀ n = Classical.choose (Classical.choose_spec (exists_completeFor ((paperDP 𝗜𝚺₁).D n)
      (smallAtoms n) (paperDP_hworld 𝗜𝚺₁ n))) := rfl

/-- The linked table is the kernel mixture over the re-indexed chosen family. -/
theorem linkedPrice_is_kernel_of_choice (n : ℕ) (φ : Sentence) :
    linkedPrice n φ = kMixRat ((paperDP 𝗜𝚺₁).D n) (n + 1)
      (fun j : Fin (2 ^ k₀ n) => W₀ n ⟨j.val % k₀ n, Nat.mod_lt _ (W₀_spec n).1⟩) φ := rfl

/-! ## The spec is blind to multiplicity -/

/-- Appending another copy of a member of a family keeps the spec of `W₀ n`. -/
theorem spec_of_snoc {D : Finset Sentence} {A : Finset ℕ} {k : ℕ} {W : Fin k → PCWorld}
    (h : 0 < k ∧ (∀ i, (W i).ConsistentWith D) ∧ CompleteFor D A W) (i₀ : Fin k) :
    0 < k + 1 ∧ (∀ i, ((Fin.snoc W (W i₀) : Fin (k + 1) → PCWorld) i).ConsistentWith D) ∧
      CompleteFor D A (Fin.snoc W (W i₀) : Fin (k + 1) → PCWorld) := by
  obtain ⟨_, hcons, hcomp⟩ := h
  refine ⟨Nat.succ_pos _, fun i => ?_, fun v hv => ?_⟩
  · induction i using Fin.lastCases with
    | last => simpa [Fin.snoc_last] using hcons i₀
    | cast i => simpa [Fin.snoc_castSucc] using hcons i
  · obtain ⟨i, hi⟩ := hcomp v hv
    exact ⟨Fin.castSucc i, by simpa [Fin.snoc_castSucc] using hi⟩

/-! ## The kernel's price at a non-overridden atom is the family's frequency -/

open Classical in
/-- At an atom that is neither `freshCode` nor of day-`m` literal shape, the kernel's price is
the fraction of members holding it. -/
theorem kMix_atom_freq {D : Finset Sentence} {m k : ℕ} (hk : 0 < k) (W : Fin k → PCWorld)
    {a : ℕ} (hne : a ≠ freshCode) (hsh : ¬ LitShape m a) :
    kMix D m W (Formula.atom a) = (∑ i, if W i a then (1 : ℝ) else 0) / k := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpay : ∀ (x y z : ℕ) (b : Prop) (i : Fin k),
      (slice D m x y z b (W i)).payout (Formula.atom a) = if W i a then (1 : ℝ) else 0 := by
    intro x y z b i
    refine payout_eq_ite ?_
    rw [PCWorld.holds_atom]
    exact slice_other hne (fun h => hsh h.1) x y z b (W i)
  unfold kMix
  rw [Fintype.sum_prod_type, eq_div_iff hk', Finset.sum_mul]
  simp only [Fintype.sum_bool, kWorld, hpay]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · field_simp
    try ring
  · simp

open Classical in
/-- Duplicating a member moves the kernel's price at any free atom on which the family takes
both values. -/
theorem kMix_snoc_ne {D : Finset Sentence} {m k : ℕ} (hk : 0 < k) (W : Fin k → PCWorld)
    {a : ℕ} (hne : a ≠ freshCode) (hsh : ¬ LitShape m a)
    (hT : ∃ i, W i a) (hF : ∃ i, ¬ W i a) (i₀ : Fin k) :
    kMix D m W (Formula.atom a) ≠
      kMix D m (Fin.snoc W (W i₀) : Fin (k + 1) → PCWorld) (Formula.atom a) := by
  have hS0 : (1 : ℝ) ≤ ∑ i, if W i a then (1 : ℝ) else 0 := by
    obtain ⟨i, hi⟩ := hT
    have := Finset.single_le_sum (f := fun j => if W j a then (1 : ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) (Finset.mem_univ i)
    simpa [hi] using this
  have hSk : (∑ i, if W i a then (1 : ℝ) else 0) < k := by
    obtain ⟨i, hi⟩ := hF
    have := Finset.sum_lt_sum (s := Finset.univ) (f := fun j => if W j a then (1 : ℝ) else 0)
      (g := fun _ => (1 : ℝ)) (fun j _ => by split_ifs <;> norm_num)
      ⟨i, Finset.mem_univ i, by simp [hi]⟩
    simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
  rw [kMix_atom_freq hk W hne hsh, kMix_atom_freq (Nat.succ_pos k) _ hne hsh,
    Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  intro heq
  rw [div_eq_div_iff hk' hk1] at heq
  push_cast at heq
  split_ifs at heq with h0
  · have : (∑ i, if W i a then (1 : ℝ) else 0) = k := by linarith
    exact absurd this hSk.ne
  · linarith

/-! ## A free, small, non-overridden atom at every stage: a sibling of `freshCoord` -/

/-- The run-family atom with payload `⟨0, 1⟩` (`freshCoord` has `⟨0, 0⟩`). -/
abbrev siblingCode : ℕ := freshAtomCode freshFamily (Nat.pair 0 1)

/-- The sibling is not `freshCode`. -/
lemma siblingCode_ne_freshCode : siblingCode ≠ freshCode := by
  intro h
  have := (Nat.pair_eq_pair.1 (freshAtomCode_inj.1 h).2).2
  omega

/-- The sibling has the run's tag, not the quotation tag: it is of no literal shape. -/
lemma siblingCode_not_litShape (m : ℕ) : ¬ LitShape m siblingCode := by
  rintro ⟨e, c, -, r, -, h⟩
  have := congrArg (fun a => a.unpair.1) h
  simp [litIdx, quotationClaimCode, freshAtomCode, freshFamily, cleanroomBaseTag] at this

/-- No stage of `paperDP 𝗜𝚺₁` mentions the sibling. -/
lemma siblingCode_free (k : ℕ) : FreshAt ((paperDP 𝗜𝚺₁).D k) siblingCode :=
  fun φ hφ => (paperDP_cleanroomFree 𝗜𝚺₁ k φ hφ).freshAtomCode_notMem _ _

/-- The sibling is a day-`n` small atom from day `2` on (as `freshCoord`: code `381`, five
base-4 digits). -/
lemma siblingCode_mem_smallAtoms {n : ℕ} (hn : 2 ≤ n) : siblingCode ∈ smallAtoms n := by
  have hcode : freshAtomCode freshFamily (Nat.pair 0 1) + 5 < 4 ^ 5 := by decide
  have hlen := length_natDigits4_le_of_lt_pow hcode
  have h16 : 16 ≤ sizeBound n :=
    calc 16 = sizeBound 2 := by norm_num [sizeBound]
      _ ≤ sizeBound n := sizeBound_mono hn
  have hsmall := (atom_pair_small n (freshAtomCode freshFamily (Nat.pair 0 1)) (by omega)).1
  rw [smallAtoms, Finset.mem_biUnion]
  exact ⟨Formula.atom siblingCode, hsmall, by simp [sentenceAtomCodes_atom]⟩

/-- **The kernel's day-`n` price at a day-`n` small atom depends on which complete family was
chosen**: for any family meeting the spec of `W₀ n` (`n ≥ 2`), its duplicate-extension meets the
same spec and gives a different kernel price at `siblingCode`. -/
theorem kernel_price_depends_on_family (n : ℕ) {k : ℕ} (W : Fin k → PCWorld)
    (h : 0 < k ∧ (∀ i, (W i).ConsistentWith ((paperDP 𝗜𝚺₁).D n)) ∧
      CompleteFor ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) W)
    (hn : 2 ≤ n) (i₀ : Fin k) :
    (0 < k + 1 ∧
      (∀ i, ((Fin.snoc W (W i₀) : Fin (k + 1) → PCWorld) i).ConsistentWith ((paperDP 𝗜𝚺₁).D n)) ∧
      CompleteFor ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) (Fin.snoc W (W i₀) : Fin (k + 1) → PCWorld)) ∧
    kMix ((paperDP 𝗜𝚺₁).D n) (n + 1) W (Formula.atom siblingCode) ≠
      kMix ((paperDP 𝗜𝚺₁).D n) (n + 1) (Fin.snoc W (W i₀) : Fin (k + 1) → PCWorld)
        (Formula.atom siblingCode) := by
  refine ⟨spec_of_snoc h i₀, ?_⟩
  obtain ⟨⟨v, hv, hva⟩, ⟨w, hw, hwa⟩⟩ :=
    free_atom_undecided (siblingCode_free n) (paperDP_hworld 𝗜𝚺₁ n)
  obtain ⟨i, hi⟩ := h.2.2 v hv
  obtain ⟨j, hj⟩ := h.2.2 w hw
  have hA := siblingCode_mem_smallAtoms hn
  refine kMix_snoc_ne h.1 W siblingCode_ne_freshCode (siblingCode_not_litShape _)
    ⟨i, ?_⟩ ⟨j, ?_⟩ i₀
  · exact (hi _ hA).2 (by simpa using hva)
  · intro hja
    exact hwa (by simpa using (hj _ hA).1 hja)

/-- The instance at the family of record: `W₀ n` meets the spec, so does its duplicate-extension,
and the two kernel prices at the sibling atom differ. -/
theorem W₀_price_depends_on_family {n : ℕ} (hn : 2 ≤ n) :
    kMix ((paperDP 𝗜𝚺₁).D n) (n + 1) (W₀ n) (Formula.atom siblingCode) ≠
      kMix ((paperDP 𝗜𝚺₁).D n) (n + 1)
        (Fin.snoc (W₀ n) (W₀ n ⟨0, (W₀_spec n).1⟩) : Fin (k₀ n + 1) → PCWorld)
        (Formula.atom siblingCode) :=
  (kernel_price_depends_on_family n (W₀ n) (W₀_spec n) hn ⟨0, (W₀_spec n).1⟩).2

end Cleanroom.Bli.BliExactBase.AuditR3Fid
