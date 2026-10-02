import Cleanroom.Bli.BliLinkage.AttemptA.AbstractInstance

/-!
# `bli-linkage`, attempt A — K2: the linkage trilemma's witnesses, sharpness, the free part

Over the abstract instance (`AbstractInstance.lean`: the Boolean family over the empty process,
representatives `(1/4, 3/4)`, one coordinate `c₀ = ⌜cohAtom⌝`, two tables, the witness day `2`
on which `c₀` is pinned):

* **(T1)** `baseQ` — the two-world mixture (everything true : `1/4`, everything false : `3/4`)
  violates `D_NNUcell` at `(2, c₀)` (`baseQ_viol`: `1/4 ≠ 1/4·1/4 + 3/4·3/4`); `P := baseQ`
  satisfies `PCPσ ∧ E1x ∧ E5σ` with both tables charged and **fails faith** at
  `(n, m, q, c) = (2, 3, tbl0, c₀)`: `P 2 (cohAtom ⋏ σ_{tbl0}) = 1/4 ≠ 1/4 · 1/4`.
* **(T3)** `faithfulP` — the four-world mixture with masses `1/4`, `3/4` on the tables and the
  coordinate true inside each in proportion `1/4`, `3/4` (weights `1/16, 3/16, 9/16, 3/16`)
  satisfies `PCPσ ∧ E2xσIdx ∧ E5σ` with both tables charged, and **fails `E1x baseQ`** at
  `(2, cohAtom)`: `5/8 ≠ 1/4` — it disagrees with the base exactly where the base violates
  no-net-update.
* **(T2)** `incoherentP` — `faithfulP` with the price of the negative literal `∼#(litCode (n+1) c₀)`
  raised by `1/8` on every day: it satisfies `E1x` (over itself), `E2xσIdx`, `E5σ` with both
  tables charged, violates `D_NNUcell` at `(2, c₀)`, and **fails `PCPσ`** at day `2` because
  `P 2 (lit) + P 2 (∼lit) = 9/8 ≠ 1`. **Why T2 is over its own base, not over `baseQ`**:
  `no_T2_over_coherent_base` — when the base is itself a partition-respecting world mixture
  and the day-`(n+1)` state sentences are small on day `n` (they are, on every pinned day of
  this instance), `E1x` transfers the base's coherence to the state algebra and
  `E1x ∧ E2xσIdx ∧ E5σ` already force no-net-update; the coherence horn of the trilemma is
  about the base's *own* coherence on its linked next-state beliefs.
* **Sharpness** `sharp`: `faithfulP` over itself satisfies all four conjuncts and `D_NNUcell`
  (through `determination`), with two tables charged and `d = 2` cells.
* **The free part** `free_marginal_day_zero`: on day `0` nothing is pinned, and `faithfulP` and
  `faithfulP'` (masses `1/2`, `1/2` on day `0`, `faithfulP` afterwards) both satisfy the full
  package over the same base with different marginals `1/4 ≠ 1/2` on `c₀` at day `0`.

Not done (recorded): the copula witness (two pinned coordinates with equal marginals and
different joint mass) — the instance has one coordinate; and the mandate's trajectory-law
sharpness base (`tentSkeleton`), replaced by the four-world mixture.
-/

namespace Cleanroom.Bli.BliLinkage.AttemptA

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

open Classical

namespace Abstract

/-- The family of record for the witnesses: representatives `1/4`, `3/4`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable abbrev fam : CellFamily emptyDP := boolFamily emptyDP (1 / 4) (3 / 4)

/-- The system of record for the witnesses.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable abbrev sys : StateSystem := absSystem (1 / 4) (3 / 4)

/-! ## The base and its violation -/

/-- **The base `Q` of the trilemma**: the mixture of the all-true world (`1/4`) and the all-false
world (`3/4`).
Source: mandate § K2 (T1: "the witness base `Q` must be built as a world mixture that violates
`D_NNUcell`")
Kind: D
Fidelity: n/a -/
noncomputable def baseQ : History := mix4 (1 / 4) 0 0 (3 / 4)

/-- **`baseQ` violates `D_NNUcell`** at `(2, c₀)`: `Q 2 cohAtom = 1/4` but
`1/4 · Q 2 (lit) + 3/4 · Q 2 (∼lit) = 1/16 + 9/16 = 5/8`.
Source: mandate § K2 (`hviol`)
Kind: N+
Fidelity: n/a -/
theorem baseQ_viol : ¬ D_NNUcell fam idx baseQ := by
  intro h
  have := (nnu_mix4_iff (1 / 4) (3 / 4) (1 / 4) 0 0 (3 / 4) 2).1 (h 2 c₀ (c₀_mem_pinned_two _ _ _))
  norm_num at this

/-- Both tables are charged by a `mix4` with `a + b > 0` and `c + d > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mix4_two_charged {a b c d : ℝ} (h0 : 0 < a + b) (h1 : 0 < c + d) (n : ℕ) :
    0 < mix4 a b c d n (stateOf fam (n + 1) tbl0) ∧
      0 < mix4 a b c d n (stateOf fam (n + 1) tbl1) := by
  rw [mix4_state0, mix4_state1]; exact ⟨h0, h1⟩

/-! ## T1: coherent and agreeing, not faithful -/

/-- **T1 — drop faith**: `P := baseQ` is `PCPσ`, `E1x baseQ`, `E5σ`, charges both tables
(`1/4`, `3/4`), and fails `E2xσIdx` at `(n, m, q, c) = (2, 3, tbl0, c₀)`:
`P 2 (cohAtom ⋏ σ_{tbl0}) = 1/4 ≠ 1/4 · P 2 σ_{tbl0} = 1/16`.
Source: [[bli-program]] §3.6(ii) (the trilemma); mandate § K2 (T1)
Kind: N+
Fidelity: n/a (two tables charged, `d = 2`)
Hyps: (a) -/
theorem T1_coherent_agreeing_not_faithful :
    PCPσ fam (stateOf fam) sys baseQ ∧ E1x baseQ baseQ ∧ E5σ (stateOf fam) sys baseQ ∧
      (0 < baseQ 2 (stateOf fam 3 tbl0) ∧ 0 < baseQ 2 (stateOf fam 3 tbl1)) ∧
      ¬ E2xσIdx (stateOf fam) idx sys baseQ := by
  refine ⟨mix4_PCPσ _ _ (by norm_num) le_rfl le_rfl (by norm_num) (by norm_num),
    fun _ _ _ => rfl, mix4_E5σ _ _ (by norm_num),
    mix4_two_charged (by norm_num) (by norm_num) 2, ?_⟩
  intro h
  have := h 2 3 (by norm_num) tbl0 (by simp [sys, absSystem, absStates]) c₀ (by simp [idx])
    (by rw [sentenceOfCode_c₀]; exact cohAtom_mem_Sminus (by norm_num))
  rw [sentenceOfCode_c₀, (absSystem_val_coh _ _ 3).1] at this
  unfold baseQ at this
  rw [mix4_coh_state0, mix4_state0] at this
  norm_num at this

/-! ## T3: coherent and faithful, not agreeing -/

/-- **The faithful mixture** (the K5 product coupling as a world mixture): masses `1/4`, `3/4` on
the tables, the coordinate true inside each in proportion `1/4`, `3/4`.
Source: mandate § K2 (T3), § K5 (the product coupling)
Kind: D
Fidelity: n/a -/
noncomputable def faithfulP : History :=
  mix4 ((1 / 4) * ((1 / 4 : ℚ) : ℝ)) ((1 / 4) * (1 - ((1 / 4 : ℚ) : ℝ)))
    ((3 / 4) * ((3 / 4 : ℚ) : ℝ)) ((3 / 4) * (1 - ((3 / 4 : ℚ) : ℝ)))

/-- **T3 — drop agreement**: `faithfulP` is `PCPσ`, `E2xσIdx`, `E5σ`, charges both tables, and
fails `E1x baseQ` at `(2, cohAtom)`: `faithfulP 2 cohAtom = 5/8 ≠ baseQ 2 cohAtom = 1/4`.
Source: [[bli-program]] §3.6(ii); mandate § K2 (T3)
Kind: N+
Fidelity: n/a (two tables charged, `d = 2`)
Hyps: (a) -/
theorem T3_coherent_faithful_not_agreeing :
    PCPσ fam (stateOf fam) sys faithfulP ∧ E2xσIdx (stateOf fam) idx sys faithfulP ∧
      E5σ (stateOf fam) sys faithfulP ∧
      (0 < faithfulP 2 (stateOf fam 3 tbl0) ∧ 0 < faithfulP 2 (stateOf fam 3 tbl1)) ∧
      ¬ E1x baseQ faithfulP := by
  refine ⟨mix4_PCPσ _ _ (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)
      (by push_cast; norm_num) (by push_cast; norm_num),
    mix4_E2xσIdx (1 / 4) (3 / 4) (1 / 4) (3 / 4), mix4_E5σ _ _ (by push_cast; norm_num),
    mix4_two_charged (by push_cast; norm_num) (by push_cast; norm_num) 2, ?_⟩
  intro h
  have := h 2 cohAtom (mem_smallSet.mpr (cohAtom_smallOn (by norm_num)))
  unfold faithfulP baseQ at this
  rw [mix4_coh, mix4_coh] at this
  push_cast at this
  norm_num at this

/-! ## T2: agreeing and faithful, not coherent -/

/-- **The incoherent market**: `faithfulP` with the negative literal's price raised by `1/8`.
Source: mandate § K2 (T2; the shape is this run's, see the module docstring)
Kind: D
Fidelity: n/a -/
noncomputable def incoherentP : History := fun n φ =>
  if φ = ∼ Formula.atom (litCode (n + 1) c₀) then faithfulP n φ + 1 / 8 else faithfulP n φ

/-- `incoherentP` agrees with `faithfulP` on every sentence that is not the raised literal.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma incoherentP_of_ne {n : ℕ} {φ : Sentence} (h : φ ≠ ∼ Formula.atom (litCode (n + 1) c₀)) :
    incoherentP n φ = faithfulP n φ := by
  simp [incoherentP, h]

/-- No conjunction is the raised literal (an `⋏` is not an `🡒`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma and_ne_neg_lit (φ ψ : Sentence) (a : ℕ) : (φ ⋏ ψ) ≠ ∼ Formula.atom a := by
  intro h; cases h

/-- **T2 — drop coherence**: `incoherentP` is `E1x` (over itself), `E2xσIdx`, `E5σ`, charges both
tables, violates `D_NNUcell` at `(2, c₀)`, and fails `PCPσ` at day `2`: in any partition-respecting
mixture `P 2 (lit) + P 2 (∼lit) = 1`, but here it is `9/8`.
Source: [[bli-program]] §3.6(ii); mandate § K2 (T2)
Kind: N+
Fidelity: n/a (two tables charged, `d = 2`; the base is `incoherentP` itself — see
`no_T2_over_coherent_base` for why it cannot be `baseQ`)
Hyps: (a) -/
theorem T2_agreeing_faithful_not_coherent :
    E1x incoherentP incoherentP ∧ E2xσIdx (stateOf fam) idx sys incoherentP ∧
      E5σ (stateOf fam) sys incoherentP ∧
      (0 < incoherentP 2 (stateOf fam 3 tbl0) ∧ 0 < incoherentP 2 (stateOf fam 3 tbl1)) ∧
      ¬ D_NNUcell fam idx incoherentP ∧ ¬ PCPσ fam (stateOf fam) sys incoherentP := by
  have hT3 := T3_coherent_faithful_not_agreeing
  have hs0 : ∀ n m, incoherentP n (stateOf fam m tbl0) = faithfulP n (stateOf fam m tbl0) :=
    fun n m => incoherentP_of_ne (by rw [stateOf_tbl0]; exact and_ne_neg_lit _ _ _)
  have hs1 : ∀ n m, incoherentP n (stateOf fam m tbl1) = faithfulP n (stateOf fam m tbl1) :=
    fun n m => incoherentP_of_ne (by rw [stateOf_tbl1]; exact and_ne_neg_lit _ _ _)
  refine ⟨fun _ _ _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · intro n m hnm q hq c hc hS
    rw [incoherentP_of_ne (and_ne_neg_lit _ _ _)]
    simp only [sys, absSystem, absStates, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · rw [hs0]; exact hT3.2.1 n m hnm tbl0 (by simp [absSystem, absStates]) c hc hS
    · rw [hs1]; exact hT3.2.1 n m hnm tbl1 (by simp [absSystem, absStates]) c hc hS
  · intro n
    refine ⟨?_, ?_⟩
    · show ∑ q ∈ ({tbl0, tbl1} : Finset ℕ), _ = 1
      rw [Finset.sum_pair tbl0_ne_tbl1, hs0, hs1]
      have := (hT3.2.2.1 n).1
      rwa [show ∑ q ∈ sys.states (n + 1), faithfulP n (stateOf fam (n + 1) q) =
        ∑ q ∈ ({tbl0, tbl1} : Finset ℕ), faithfulP n (stateOf fam (n + 1) q) from rfl,
        Finset.sum_pair tbl0_ne_tbl1] at this
    · intro q₁ hq₁ q₂ hq₂ hne
      rw [incoherentP_of_ne (and_ne_neg_lit _ _ _)]
      exact (hT3.2.2.1 n).2 q₁ hq₁ q₂ hq₂ hne
  · rw [hs0, hs1]; exact hT3.2.2.2.1
  · intro h
    have := h 2 c₀ (c₀_mem_pinned_two _ _ _)
    simp only [fam, boolFamily, sentenceOfCode_c₀] at this
    rw [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)] at this
    have e0 : incoherentP 2 cohAtom = faithfulP 2 cohAtom :=
      incoherentP_of_ne (by intro h; cases h)
    have e1 : incoherentP 2 (boolLit 3 c₀ 0) = faithfulP 2 (boolLit 3 c₀ 0) :=
      incoherentP_of_ne (by unfold boolLit; simp only [if_true]; intro h; cases h)
    have e2 : incoherentP 2 (boolLit 3 c₀ 1) = faithfulP 2 (boolLit 3 c₀ 1) + 1 / 8 := by
      unfold incoherentP boolLit; simp
    simp only [e0, e1, e2] at this
    unfold faithfulP at this
    rw [mix4_coh, mix4_lit0, mix4_lit1] at this
    push_cast at this
    norm_num at this
  · intro h
    obtain ⟨k, W, w, hW, hw, hsum, hrep⟩ := h 2
    have hlitA : sentenceAtomCodes (Formula.atom (litCode 3 c₀)) ⊆ pcpAtomsσ (stateOf fam) sys 2 :=
      (atoms_subset_smallAtoms (mem_smallSet.mpr (by simpa [boolLit] using smallOn_two_lit.1))).trans
        Finset.subset_union_left
    have hnegA : sentenceAtomCodes (∼ Formula.atom (litCode 3 c₀)) ⊆ pcpAtomsσ (stateOf fam) sys 2 := by
      rw [sentenceAtomCodes_neg]; exact hlitA
    have h1 := hrep _ hlitA
    have h2 := hrep _ hnegA
    have hone : incoherentP 2 (Formula.atom (litCode 3 c₀)) + incoherentP 2 (∼ Formula.atom (litCode 3 c₀)) = 1 := by
      rw [h1, h2, ← Finset.sum_add_distrib]
      calc ∑ i, (w i * (W i).payout (Formula.atom (litCode 3 c₀)) +
            w i * (W i).payout (∼ Formula.atom (litCode 3 c₀))) = ∑ i, w i := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← mul_add, payout_add_payout_neg, mul_one]
        _ = 1 := hsum
    have e1 : incoherentP 2 (Formula.atom (litCode 3 c₀)) = faithfulP 2 (boolLit 3 c₀ 0) :=
      incoherentP_of_ne (by intro h; cases h)
    have e2 : incoherentP 2 (∼ Formula.atom (litCode 3 c₀)) = faithfulP 2 (boolLit 3 c₀ 1) + 1 / 8 := by
      unfold incoherentP boolLit; simp
    rw [e1, e2] at hone
    unfold faithfulP at hone
    rw [mix4_lit0, mix4_lit1] at hone
    push_cast at hone
    norm_num at hone

/-! ## Why T2 cannot share T1's base -/

/-- **The coherence horn is the base's**: if the base `Q` is itself a partition-respecting world
mixture on the day-`n` algebra, and the day-`(n+1)` linked states, their pairwise conjunctions
and their conjunctions with the pinned coordinate are all small on day `n`, then
`E1x Q P ∧ E2xσIdx ∧ E5σ` already force `D_NNUcell` at `(n, c)` — without any coherence
assumption on `P`. So a T2 witness (faithful, agreeing, incoherent) over a coherent base exists
only on days where the linked states are *large*; on the pinned days of the abstract instance
they are small, which is why `incoherentP` is its own base.
Source: this run (strengthening of mandate § K2's trilemma: the (1)-horn located at the base)
Kind: C
Fidelity: exact
Hyps: (a); the smallness of the state algebra is an explicit hypothesis -/
theorem no_T2_over_coherent_base {DP : DeductiveProcess} (C : CellFamily DP)
    (index : ℕ → List ℕ) (S : StateSystem) (Q P : History) (hT : Tabular C index S) (n : ℕ)
    (D : Finset Sentence) (A : Finset ℕ) (hcohQ : CoherentOnCell C D (n + 1) A (Q n))
    (hAsmall : smallAtoms n ⊆ A)
    (hsmallσ : ∀ q ∈ S.states (n + 1), stateOf C (n + 1) q ∈ smallSet n)
    (hsmallσσ : ∀ q ∈ S.states (n + 1), ∀ q' ∈ S.states (n + 1),
      (stateOf C (n + 1) q ⋏ stateOf C (n + 1) q') ∈ smallSet n)
    (hE1 : E1x Q P) (hE2 : E2xσIdx (stateOf C) index S P) (hE5 : E5σ (stateOf C) S P)
    {c : ℕ} (hc : c ∈ pinned C index n)
    (hsmallφσ : ∀ q ∈ S.states (n + 1), (sentenceOfCode c ⋏ stateOf C (n + 1) q) ∈ smallSet n)
    (hφn : sentenceOfCode c ∈ smallSet n) (hφS : sentenceOfCode c ∈ Sminus (n + 1) (n + 1)) :
    Q n (sentenceOfCode c) =
      ∑ r ∈ C.cells (n + 1), (C.rep (n + 1) r : ℝ) * Q n (C.cellLit (n + 1) c r) := by
  have hcidx : c ∈ index (n + 1) := (mem_pinned.1 hc).1
  refine nnu_at C index S Q Q hT n D A hcohQ hAsmall
    (fun q hq => (atoms_subset_smallAtoms (hsmallσ q hq)).trans hAsmall) ?_ ?_
    (fun _ _ _ => rfl) ?_ hc hφn hφS
  · rw [← (hE5 n).1]
    exact Finset.sum_congr rfl fun q hq => (hE1 n _ (hsmallσ q hq)).symm
  · intro q₁ hq₁ q₂ hq₂ hne
    rw [← (hE5 n).2 q₁ hq₁ q₂ hq₂ hne]
    exact (hE1 n _ (hsmallσσ q₁ hq₁ q₂ hq₂)).symm
  · intro q hq _
    rw [← hE1 n _ (hsmallφσ q hq), ← hE1 n _ (hsmallσ q hq)]
    exact hE2 n (n + 1) (Nat.lt_succ_self n) q hq c hcidx hφS

/-! ## Sharpness -/

/-- **Sharpness — all three horns and `D_NNUcell` together**: `faithfulP` over itself satisfies
`PCPσ ∧ E1x ∧ E2xσIdx ∧ E5σ`, charges both tables with `d = 2` cells, and satisfies `D_NNUcell`
(by `determination`, exercising the theorem on a real instance).
Source: mandate § K2 ("Sharpness"); desiderata I6
Kind: N+
Fidelity: n/a (the four-world mixture in place of the mandate's trajectory-law base; disclosed)
Hyps: (a) -/
theorem sharp :
    PCPσ fam (stateOf fam) sys faithfulP ∧ E1x faithfulP faithfulP ∧
      E2xσIdx (stateOf fam) idx sys faithfulP ∧ E5σ (stateOf fam) sys faithfulP ∧
      (0 < faithfulP 2 (stateOf fam 3 tbl0) ∧ 0 < faithfulP 2 (stateOf fam 3 tbl1)) ∧
      D_NNUcell fam idx faithfulP := by
  have hT3 := T3_coherent_faithful_not_agreeing
  exact ⟨hT3.1, fun _ _ _ => rfl, hT3.2.1, hT3.2.2.1, hT3.2.2.2.1,
    determination fam idx sys faithfulP faithfulP (absSystem_tabular _ _ _) hT3.1 hT3.2.2.1
      (fun _ _ _ => rfl) hT3.2.1 (scope_idx _ _ _)⟩

/-! ## The free part: nothing is pinned on day `0`, and the day-`0` marginals are free -/

/-- `smallSet 0 = {⊥}`: on day `0` only `⊥` is small (`sizeBound 0 = 2`, every other sentence has
size `≥ 3`).
Source: bli-found F-9 (day `0` is special)
Kind: L
Fidelity: n/a -/
lemma eq_falsum_of_mem_smallSet_zero {φ : Sentence} (h : φ ∈ smallSet 0) : φ = ⊥ := by
  rw [mem_smallSet] at h
  unfold SmallOn at h
  have h2 : sizeBound 0 = 2 := by norm_num [sizeBound]
  rw [h2] at h
  cases φ with
  | falsum => rfl
  | atom a => have := three_le_tokenSize_atom a; omega
  | imp a b =>
      have := tokenSize_imp a b; have := one_le_tokenSize a; have := one_le_tokenSize b
      change tokenSize (a 🡒 b) ≤ 2 at h; omega
  | and a b =>
      have := tokenSize_and a b; have := one_le_tokenSize a; have := one_le_tokenSize b
      change tokenSize (a ⋏ b) ≤ 2 at h; omega
  | or a b =>
      have := tokenSize_or a b; have := one_le_tokenSize a; have := one_le_tokenSize b
      change tokenSize (a ⋎ b) ≤ 2 at h; omega

/-- `mix4` of `⊥` is `0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mix4_falsum (a b c d : ℝ) (n : ℕ) : mix4 a b c d n ⊥ = 0 := by
  simp [mix4, PCWorld.payout, PCWorld.Holds, LO.Propositional.Formula.Boolean.val]

/-- `faithfulP` with masses `1/2`, `1/2` on day `0`, `faithfulP` afterwards.
Source: mandate § K2 ("the free part")
Kind: D
Fidelity: n/a -/
noncomputable def faithfulP' : History := fun n φ =>
  if n = 0 then
    mix4 ((1 / 2) * ((1 / 4 : ℚ) : ℝ)) ((1 / 2) * (1 - ((1 / 4 : ℚ) : ℝ)))
      ((1 / 2) * ((3 / 4 : ℚ) : ℝ)) ((1 / 2) * (1 - ((3 / 4 : ℚ) : ℝ))) 0 φ
  else faithfulP n φ

/-- **The free part**: on day `0` nothing is pinned (`not_mem_pinned_zero`), and `faithfulP`,
`faithfulP'` both satisfy `PCPσ ∧ E1x faithfulP ∧ E2xσIdx ∧ E5σ` over the same base, with
different marginals on `c₀` at day `0`: `cellMass … 0 c₀ 0 = 1/4` versus `1/2`.
Source: mandate § K2 ("The free part")
Kind: N+
Fidelity: n/a (the unpinned day is day `0`, where `smallSet 0 = {⊥}`)
Hyps: (a) -/
theorem free_marginal_day_zero :
    c₀ ∉ pinned fam idx 0 ∧
      (PCPσ fam (stateOf fam) sys faithfulP' ∧ E1x faithfulP faithfulP' ∧
        E2xσIdx (stateOf fam) idx sys faithfulP' ∧ E5σ (stateOf fam) sys faithfulP') ∧
      cellMass (stateOf fam) sys faithfulP 0 c₀ 0 ≠ cellMass (stateOf fam) sys faithfulP' 0 c₀ 0 := by
  have hT3 := T3_coherent_faithful_not_agreeing
  have hmass0 : cellMass (stateOf fam) sys faithfulP 0 c₀ 0 = faithfulP 0 (stateOf fam 1 tbl0) := by
    unfold cellMass
    rw [show (sys.states (0 + 1)).filter (fun q => entryOf c₀ (tableOfCode q) = some 0) = {tbl0} from ?_]
    · simp
    · ext q
      simp only [Finset.mem_filter, sys, absSystem, absStates, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h⟩
        · rfl
        · unfold tbl1 at h; rw [tableOfCode_encode] at h; simp [entryOf] at h
      · rintro rfl
        exact ⟨Or.inl rfl, by unfold tbl0; rw [tableOfCode_encode]; simp [entryOf]⟩
  have hmass0' : cellMass (stateOf fam) sys faithfulP' 0 c₀ 0 = faithfulP' 0 (stateOf fam 1 tbl0) := by
    unfold cellMass
    rw [show (sys.states (0 + 1)).filter (fun q => entryOf c₀ (tableOfCode q) = some 0) = {tbl0} from ?_]
    · simp
    · ext q
      simp only [Finset.mem_filter, sys, absSystem, absStates, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, h⟩
        · rfl
        · unfold tbl1 at h; rw [tableOfCode_encode] at h; simp [entryOf] at h
      · rintro rfl
        exact ⟨Or.inl rfl, by unfold tbl0; rw [tableOfCode_encode]; simp [entryOf]⟩
  refine ⟨not_mem_pinned_zero _ _ _ _, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n
    by_cases hn : n = 0
    · subst hn
      show CoherentOnCell fam (emptyDP.D 0) 1 _ (faithfulP' 0)
      have : faithfulP' 0 = mix4 ((1 / 2) * ((1 / 4 : ℚ) : ℝ)) ((1 / 2) * (1 - ((1 / 4 : ℚ) : ℝ)))
          ((1 / 2) * ((3 / 4 : ℚ) : ℝ)) ((1 / 2) * (1 - ((3 / 4 : ℚ) : ℝ))) 0 := by
        funext φ; simp [faithfulP']
      rw [this]
      exact mix4_coherentOnCell _ _ (by push_cast; norm_num) (by push_cast; norm_num)
        (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num) 0 1 _ 0
    · have : faithfulP' n = faithfulP n := by funext φ; simp [faithfulP', hn]
      show CoherentOnCell fam (emptyDP.D n) (n + 1) _ (faithfulP' n)
      rw [this]; exact hT3.1 n
  · intro n φ hφ
    by_cases hn : n = 0
    · subst hn
      rw [eq_falsum_of_mem_smallSet_zero hφ]
      simp only [faithfulP', if_true]
      unfold faithfulP
      rw [mix4_falsum, mix4_falsum]
    · simp [faithfulP', hn]
  · intro n m hnm q hq c hc hS
    by_cases hn : n = 0
    · subst hn
      simp only [faithfulP', if_true]
      exact mix4_E2xσIdx (1 / 4) (3 / 4) (1 / 2) (1 / 2) 0 m hnm q hq c hc hS
    · simp only [faithfulP', hn, if_false]
      exact hT3.2.1 n m hnm q hq c hc hS
  · intro n
    by_cases hn : n = 0
    · subst hn
      have : faithfulP' 0 = mix4 ((1 / 2) * ((1 / 4 : ℚ) : ℝ)) ((1 / 2) * (1 - ((1 / 4 : ℚ) : ℝ)))
          ((1 / 2) * ((3 / 4 : ℚ) : ℝ)) ((1 / 2) * (1 - ((3 / 4 : ℚ) : ℝ))) 0 := by
        funext φ; simp [faithfulP']
      rw [this]
      exact mix4_E5σ (1 / 4) (3 / 4) (by push_cast; norm_num) 0
    · have : faithfulP' n = faithfulP n := by funext φ; simp [faithfulP', hn]
      rw [this]
      exact hT3.2.2.1 n
  · rw [hmass0, hmass0']
    simp only [faithfulP', if_true]
    unfold faithfulP
    rw [mix4_state0, mix4_state0]
    push_cast
    norm_num

end Abstract

end Cleanroom.Bli.BliLinkage.AttemptA
