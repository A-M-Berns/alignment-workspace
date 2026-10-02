import Cleanroom.Bli.BliExactBase.Segment

/-!
# Probe (bli-exact-base audit r3, adversarial): the restated OPEN row quantifies the code, but
the table it is about is still a `Classical.choice`

Repair round 2 restated `Segment.linked_segment_day_exists` over an arbitrary cell quote code
`q : BooleanQuoteCode 𝗜𝚺₁ (spliceCellTruth H linkedPrice halfRound)` and calls it "a genuine
conjecture, plausibly true: the kernel is uniformly computable in the day". But the predicate
`q` must decide is the cell truth of `linkedPrice`, and `linkedPrice n` is the kernel market over
the family of record `WAt n`, which re-indexes `W₀ n` — and `W₀ n`, `k₀ n` are `Classical.choose`
of `exists_completeFor` (`k₀_is_choice`, `W₀_is_choice`, `linkedPrice_is_kernel_of_reidx`, all
`rfl`). The only thing Lean knows about the chosen family is `W₀_spec n`: positive size,
stage-consistent members, complete for the day-`n` small atoms. **That specification does not
fix the cell truth** (`spec_admits_both_cells`): for every day `n ≥ 2` there are two families
satisfying it exactly whose kernel markets round the stage-free small atom `a₁`
(`freshAtomCode freshFamily ⟨0, 1⟩`, the sibling of `freshCoord`) to cell `1` and to cell `0`
respectively — pad any complete family with copies of a world holding `a₁`, or with copies of one
refuting it; completeness and consistency survive padding, and the kernel's price of `a₁` is the
family's frequency of `a₁` (the slices override only `freshCode` and the literal-shaped atoms,
`kMixRat_atom`), preserved exactly by the `WAt` re-indexing when the size is a power of two
(`sum_reidx_eq`). And that bit is exactly what the row's code must decide at the input
`⟨n, ⟨⌜a₁⌝, r⟩⟩` for `n < H` (`cellTruth_a₁`).

Consequence (prose, as in audit r2 fidelity B1's probe): a `BooleanQuoteCode` of
`spliceCellTruth H linkedPrice halfRound` must prove `pos_complete`/`neg_complete` at every
input, i.e. its program's output at `⟨n, ⟨⌜a₁⌝, 1⟩⟩` must provably agree with
`halfRound n (linkedPrice n ⌜a₁⌝)`; for an explicit program that output is a fixed bit, and
`W₀_spec` admits families giving either value, so no explicit code can be certified — and
`pinned` needs a token-size bound, which no non-explicit (`Classical.choose`n) code has. Nor is
the row refutable (the chosen family might be the canonical one and the LIA's code short). So
`linked_segment_day_exists` as restated is still a statement about what `Classical.choice`
returned — now the family rather than the code — not a conjecture a continuation can settle;
findings F16 (b)'s "the linked table is the brute-force average over the stage-consistent
assignments" describes the intended kernel, not the Lean's `linkedPrice`.

Fix: make the family of record canonical — e.g. the family `exists_completeFor`'s proof builds
(the stage-consistent `FiniteWorld B` patterns, each once, summed over the `Finset` rather than
through `Fintype.equivFin`) — so that `linkedPrice` is a function of the stage alone; or relabel
the row as not settleable as stated.
-/

namespace Cleanroom.Bli.BliExactBase.AuditR3Adv

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliLinkageB
open Cleanroom.Bli.BliLinkage (atom_pair_small)
open Cleanroom.Bli.BliExactBase Cleanroom.Bli.BliExactBase.Kernel Cleanroom.Bli.BliExactBase.Segment

/-! ## The family of record is a choice (definitional) -/

/-- The size of the chosen family is `Classical.choose` of the existence lemma. -/
theorem k₀_is_choice (n : ℕ) :
    k₀ n = Classical.choose
      (exists_completeFor ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) (paperDP_hworld 𝗜𝚺₁ n)) := rfl

/-- The chosen family is `Classical.choose` of the existence lemma's inner `∃`. -/
theorem W₀_is_choice (n : ℕ) :
    W₀ n = Classical.choose (Classical.choose_spec
      (exists_completeFor ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) (paperDP_hworld 𝗜𝚺₁ n))) := rfl

/-- The re-indexing `WAt` of a positive-size family: `j ↦ j % k` over `Fin (2 ^ k)`. -/
noncomputable def reidx {k : ℕ} (hk : 0 < k) (W : Fin k → PCWorld) : Fin (2 ^ k) → PCWorld :=
  fun j => W ⟨j.val % k, Nat.mod_lt _ hk⟩

/-- `WAt n` is the re-indexing of the chosen family (definitional). -/
theorem WAt_is_reidx (n : ℕ) : WAt n = reidx (W₀_spec n).1 (W₀ n) := rfl

/-- The linked table is the kernel market over the re-indexed chosen family (definitional). -/
theorem linkedPrice_is_kernel_of_reidx (n : ℕ) (φ : Sentence) :
    linkedPrice n φ =
      kMixRat ((paperDP 𝗜𝚺₁).D n) (n + 1) (reidx (W₀_spec n).1 (W₀ n)) φ := rfl

/-! ## A second stage-free small atom -/

/-- The fresh atom of this package's family with payload `⟨0, 1⟩` (`freshCoord`'s is `⟨0, 0⟩`). -/
abbrev a₁ : ℕ := freshAtomCode freshFamily (Nat.pair 0 1)

lemma a₁_ne_freshCode : a₁ ≠ freshCode := by decide

lemma a₁_mem_smallSet {n : ℕ} (hn : 2 ≤ n) : Formula.atom a₁ ∈ smallSet n := by
  have hcode : a₁ + 5 < 4 ^ 5 := by decide
  have hlen := length_natDigits4_le_of_lt_pow hcode
  have h16 : 16 ≤ sizeBound n :=
    calc 16 = sizeBound 2 := by norm_num [sizeBound]
      _ ≤ sizeBound n := sizeBound_mono hn
  exact (atom_pair_small n a₁ (by omega)).1

lemma a₁_mem_smallAtoms {n : ℕ} (hn : 2 ≤ n) : a₁ ∈ smallAtoms n :=
  Finset.mem_biUnion.2 ⟨_, a₁_mem_smallSet hn, by simp⟩

lemma a₁_fresh (n : ℕ) : FreshAt ((paperDP 𝗜𝚺₁).D n) a₁ :=
  fun φ hφ => (paperDP_cleanroomFree 𝗜𝚺₁ n φ hφ).freshAtomCode_notMem _ _

lemma a₁_not_litShape (m : ℕ) : ¬ LitShape m a₁ := by
  rintro ⟨e, c, -, r, -, h⟩
  have := congrArg (fun a => a.unpair.1) h
  simp [litIdx, quotationClaimCode, freshAtomCode, freshFamily, cleanroomBaseTag] at this

/-! ## The kernel's price of an ordinary atom is the family's frequency -/

/-- At an atom that is neither `freshCode` nor of literal shape, the kernel market is the
average of the family's payouts. -/
lemma kMixRat_atom {D : Finset Sentence} {m k : ℕ} (hk : 0 < k) (W : Fin k → PCWorld) {a : ℕ}
    (hne : a ≠ freshCode) (hsh : ¬ LitShape m a) :
    kMixRat D m W (Formula.atom a) = (∑ i, (W i).payoutRat (Formula.atom a)) / k := by
  have hs : ∀ (x y z : ℕ) (b : Prop) (v : PCWorld),
      (slice D m x y z b v).payoutRat (Formula.atom a) = v.payoutRat (Formula.atom a) := by
    intro x y z b v
    have hiff := slice_other (D := D) (m := m) hne (fun h => hsh h.1) x y z b v
    unfold PCWorld.payoutRat
    by_cases hv : v a
    · rw [if_pos (show (slice D m x y z b v).Holds (Formula.atom a) from hiff.2 hv),
        if_pos (show v.Holds (Formula.atom a) from hv)]
    · rw [if_neg (show ¬ (slice D m x y z b v).Holds (Formula.atom a) from
          fun h => hv (hiff.1 h)),
        if_neg (show ¬ v.Holds (Formula.atom a) from hv)]
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  unfold kMixRat
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, kWorld, hs]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring

/-! ## Padding a complete family -/

/-- `W` on `j < k`, the world `v` elsewhere. -/
noncomputable def padF {k : ℕ} (W : Fin k → PCWorld) (v : PCWorld) (j : ℕ) : PCWorld :=
  if h : j < k then W ⟨j, h⟩ else v

/-- The family `W` padded to size `K` with copies of `v`. -/
noncomputable def pad {k : ℕ} (W : Fin k → PCWorld) (v : PCWorld) (K : ℕ) : Fin K → PCWorld :=
  fun i => padF W v i.val

lemma pad_consistent {D : Finset Sentence} {k : ℕ} {W : Fin k → PCWorld}
    (hW : ∀ i, (W i).ConsistentWith D) {v : PCWorld} (hv : v.ConsistentWith D) (K : ℕ) :
    ∀ i, (pad W v K i).ConsistentWith D := by
  intro i
  unfold pad padF
  split_ifs with h
  · exact hW _
  · exact hv

lemma pad_completeFor {D : Finset Sentence} {A : Finset ℕ} {k : ℕ} {W : Fin k → PCWorld}
    (hc : CompleteFor D A W) (v : PCWorld) {K : ℕ} (hK : k ≤ K) :
    CompleteFor D A (pad W v K) := by
  intro u hu
  obtain ⟨i, hi⟩ := hc u hu
  refine ⟨⟨i.val, lt_of_lt_of_le i.2 hK⟩, fun a ha => ?_⟩
  show padF W v i.val a ↔ u a
  unfold padF
  rw [dif_pos i.2]
  exact hi a ha

lemma sum_pad_ge {k : ℕ} (W : Fin k → PCWorld) {v : PCWorld} {a : ℕ} (hv : v a) {K : ℕ}
    (hK : k ≤ K) :
    ((K - k : ℕ) : ℚ) ≤ ∑ i : Fin K, (pad W v K i).payoutRat (Formula.atom a) := by
  rw [show (∑ i : Fin K, (pad W v K i).payoutRat (Formula.atom a)) =
      ∑ j ∈ Finset.range K, (padF W v j).payoutRat (Formula.atom a) from
      Fin.sum_univ_eq_sum_range (fun j => (padF W v j).payoutRat (Formula.atom a)) K,
    ← Finset.sum_range_add_sum_Ico _ hK]
  have h2 : ∑ j ∈ Finset.Ico k K, (padF W v j).payoutRat (Formula.atom a) = ((K - k : ℕ) : ℚ) := by
    rw [Finset.sum_congr rfl (g := fun _ => (1 : ℚ))]
    · simp
    · intro j hj
      rw [Finset.mem_Ico] at hj
      unfold padF PCWorld.payoutRat
      rw [dif_neg (by omega), if_pos (by simpa using hv)]
  have h1 : 0 ≤ ∑ j ∈ Finset.range k, (padF W v j).payoutRat (Formula.atom a) :=
    Finset.sum_nonneg fun j _ => by unfold PCWorld.payoutRat; split_ifs <;> norm_num
  rw [h2]
  linarith

lemma sum_pad_le {k : ℕ} (W : Fin k → PCWorld) {v : PCWorld} {a : ℕ} (hv : ¬ v a) {K : ℕ}
    (hK : k ≤ K) :
    ∑ i : Fin K, (pad W v K i).payoutRat (Formula.atom a) ≤ k := by
  rw [show (∑ i : Fin K, (pad W v K i).payoutRat (Formula.atom a)) =
      ∑ j ∈ Finset.range K, (padF W v j).payoutRat (Formula.atom a) from
      Fin.sum_univ_eq_sum_range (fun j => (padF W v j).payoutRat (Formula.atom a)) K,
    ← Finset.sum_range_add_sum_Ico _ hK]
  have h2 : ∑ j ∈ Finset.Ico k K, (padF W v j).payoutRat (Formula.atom a) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_Ico] at hj
    unfold padF PCWorld.payoutRat
    rw [dif_neg (by omega), if_neg (by simpa using hv)]
  have h1 : ∑ j ∈ Finset.range k, (padF W v j).payoutRat (Formula.atom a) ≤
      ∑ _j ∈ Finset.range k, (1 : ℚ) :=
    Finset.sum_le_sum fun j _ => by unfold PCWorld.payoutRat; split_ifs <;> norm_num
  rw [h2]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at h1
  linarith

/-! ## The `WAt` re-indexing preserves frequencies exactly at power-of-two sizes -/

lemma sum_reidx_eq {M : Type*} [AddCommMonoid M] {K c N : ℕ} (hN : N = c * K) (g : ℕ → M) :
    ∑ j : Fin N, g (j.val % K) = c • ∑ i : Fin K, g i.val := by
  subst hN
  rw [← Fintype.sum_equiv finProdFinEquiv (fun p : Fin c × Fin K => g p.2.val)
    (fun j => g (j.val % K)) ?_]
  · rw [Fintype.sum_prod_type]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  · intro p
    show g p.2.val = g ((p.2.val + K * p.1.val) % K)
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt p.2.2]

lemma kMixRat_reidx_atom {D : Finset Sentence} {m k : ℕ} (hk : 0 < k) (W : Fin k → PCWorld)
    (hdvd : k ∣ 2 ^ k) {a : ℕ} (hne : a ≠ freshCode) (hsh : ¬ LitShape m a) :
    kMixRat D m (reidx hk W) (Formula.atom a) = (∑ i, (W i).payoutRat (Formula.atom a)) / k := by
  rw [kMixRat_atom (Nat.two_pow_pos k) (reidx hk W) hne hsh]
  obtain ⟨c, hc⟩ := hdvd
  set g : ℕ → ℚ := fun j => if h : j < k then (W ⟨j, h⟩).payoutRat (Formula.atom a) else 0
    with hg
  have h1 : ∀ j : Fin (2 ^ k), (reidx hk W j).payoutRat (Formula.atom a) = g (j.val % k) := by
    intro j; simp only [hg, reidx, dif_pos (Nat.mod_lt _ hk)]
  have h2 : ∀ i : Fin k, (W i).payoutRat (Formula.atom a) = g i.val := by
    intro i; simp only [hg, dif_pos i.2]
  simp_rw [h1, h2]
  rw [sum_reidx_eq (by rw [hc, Nat.mul_comm]) g, nsmul_eq_mul, hc]
  have hc0 : (c : ℚ) ≠ 0 := by
    have : 0 < k * c := hc ▸ Nat.two_pow_pos k
    exact_mod_cast (Nat.pos_of_mul_pos_left this).ne'
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  push_cast
  field_simp

/-! ## The specification admits both cells -/

/-- **`W₀_spec` does not fix the rounded cell of `a₁`**: on every day `n` there are two
families satisfying exactly the chosen family's specification (positive size, stage-consistent,
complete for the day-`n` small atoms) whose kernel markets, re-indexed as `WAt` is, round `a₁` to
cell `1` and to cell `0`. -/
theorem spec_admits_both_cells (n : ℕ) :
    (∃ (k : ℕ) (W : Fin k → PCWorld) (hk : 0 < k),
      (∀ i, (W i).ConsistentWith ((paperDP 𝗜𝚺₁).D n)) ∧
      CompleteFor ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) W ∧
      halfRound n (kMixRat ((paperDP 𝗜𝚺₁).D n) (n + 1) (reidx hk W) (Formula.atom a₁)) = 1) ∧
    (∃ (k : ℕ) (W : Fin k → PCWorld) (hk : 0 < k),
      (∀ i, (W i).ConsistentWith ((paperDP 𝗜𝚺₁).D n)) ∧
      CompleteFor ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) W ∧
      halfRound n (kMixRat ((paperDP 𝗜𝚺₁).D n) (n + 1) (reidx hk W) (Formula.atom a₁)) = 0) := by
  obtain ⟨k, W, hk, hW, hc⟩ :=
    exists_completeFor ((paperDP 𝗜𝚺₁).D n) (smallAtoms n) (paperDP_hworld 𝗜𝚺₁ n)
  obtain ⟨⟨vp, hvp, hvpa⟩, ⟨vm, hvm, hvma⟩⟩ :=
    free_atom_undecided (a₁_fresh n) (paperDP_hworld 𝗜𝚺₁ n)
  have hk2 : k ≤ 2 ^ k := Nat.lt_two_pow_self.le
  have hK4 : 2 ^ (k + 2) = 4 * 2 ^ k := by ring
  have hkK : k ≤ 2 ^ (k + 2) := by omega
  have h4k : 4 * k ≤ 2 ^ (k + 2) := by omega
  have hKpos : 0 < 2 ^ (k + 2) := Nat.two_pow_pos _
  have hdvd : 2 ^ (k + 2) ∣ 2 ^ (2 ^ (k + 2)) := Nat.pow_dvd_pow 2 Nat.lt_two_pow_self.le
  have hne := a₁_ne_freshCode
  have hsh := a₁_not_litShape (n + 1)
  have hKq : (0 : ℚ) < 2 ^ (k + 2) := by positivity
  have h4q : (4 * k : ℚ) ≤ 2 ^ (k + 2) := by exact_mod_cast h4k
  refine ⟨⟨2 ^ (k + 2), pad W vp _, hKpos, pad_consistent hW hvp _, pad_completeFor hc vp hkK, ?_⟩,
    ⟨2 ^ (k + 2), pad W vm _, hKpos, pad_consistent hW hvm _, pad_completeFor hc vm hkK, ?_⟩⟩
  · rw [kMixRat_reidx_atom hKpos _ hdvd hne hsh]
    have hs := sum_pad_ge W (a := a₁) (by simpa using hvpa) hkK
    rw [Nat.cast_sub hkK] at hs
    have hge : (1 : ℚ) / 2 ≤ (∑ i, (pad W vp (2 ^ (k + 2)) i).payoutRat (Formula.atom a₁)) /
        ((2 ^ (k + 2) : ℕ) : ℚ) := by
      rw [le_div_iff₀ (by exact_mod_cast hKpos)]
      push_cast at hs ⊢
      linarith
    unfold halfRound
    rw [if_neg (not_lt.2 hge)]
  · rw [kMixRat_reidx_atom hKpos _ hdvd hne hsh]
    have hs := sum_pad_le W (a := a₁) (by simpa using hvma) hkK
    have hlt : (∑ i, (pad W vm (2 ^ (k + 2)) i).payoutRat (Formula.atom a₁)) /
        ((2 ^ (k + 2) : ℕ) : ℚ) < 1 / 2 := by
      rw [div_lt_iff₀ (by exact_mod_cast hKpos)]
      push_cast at hs ⊢
      linarith
    unfold halfRound
    rw [if_pos hlt]

/-! ## That bit is what the OPEN row's code must decide -/

/-- At the input `⟨n, ⟨⌜a₁⌝, r⟩⟩`, `n < H`, the cell truth the row's code must decide is the
rounded kernel price of `a₁` over the chosen family. -/
theorem cellTruth_a₁ {H n : ℕ} (hn : 2 ≤ n) (hnH : n < H) (r : ℕ) :
    spliceCellTruth H linkedPrice halfRound
        (Nat.pair n (Nat.pair (Encodable.encode (Formula.atom a₁)) r)) ↔
      halfRound n (kMixRat ((paperDP 𝗜𝚺₁).D n) (n + 1) (reidx (W₀_spec n).1 (W₀ n))
        (Formula.atom a₁)) = r := by
  simp only [spliceCellTruth, Nat.unpair_pair]
  rw [spliceValue_linked hnH (a₁_mem_smallSet hn)]
  exact Iff.rfl

end Cleanroom.Bli.BliExactBase.AuditR3Adv
