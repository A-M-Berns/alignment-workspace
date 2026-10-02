import Cleanroom.Bli.BliLinkageB.Bracket

/-!
# bli-linkage, angle B — the scope of faith (K4), and what faith at a decided sentence forces

**Faith at a sentence the worlds decide pins the state's value.** In a world mixture, if every
world of the class decides `L` the same way (`L` holds in all, or in none), then faith
`p (L ⋏ σ_q) = val_q(L) · p σ_q` forces `val_q(L) ∈ {0, 1}` (the truth value) for every charged
candidate (`charged_val_eq_of_decided`). Three uses:

* **K4a, abstract and under interval linkage** (`faith_full_scope_inconsistent`): at the
  theory level the liar `L m` is decided by the price — `L m` holds iff `𝑸_m(L m) < p` — so a
  charged state must value it at its truth value; but the state's value lies in the open cell
  it assigns `L m`, and when that cell excludes the truth value, full-scope faith is
  inconsistent. For `halfRound` and `p = 1/2` the actual cell always excludes it (cell `0` lies
  below `1`, cell `1` above `0`), so K4a *survives* interval linkage: the straddling of `p` by
  the forced open cell (`straddle`, bli-found F-16) is irrelevant, because the contradiction is
  driven by the liar's truth under the actual price, not by what the forced quote reveals.
  The B2 instance over FAF's diagonal is `FaithB2.lean`.
* **Faith at `⊥` and `⊤`** (`faith_at_falsum`, `faith_at_verum`): `⊥` is in every `Sminus m m`
  and never holds; `⊤` is in `Sminus m m` for `m ≥ 1` and always holds. So under *any*
  coherence (stage or theory) and scoped faith, every charged candidate values `⊥` at `0` and
  `⊤` at `1`. Consequence (`InstanceB2.fixedSystem_witnessRep_unsat`): the B2 system on the
  index `[⌜⊥⌝, ⌜⊤⌝]` with interior representatives has **no** superbelief satisfying
  `PCPσ ∧ E5σ ∧ E2xσ` — a finding about `bli-found`'s witness grid, and the reason this
  package's N+ witnesses use an uncertain coordinate.
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

/-! ## The pinning lemma -/

section Pin

variable {𝒲 : PCWorld → Prop} {A : Finset ℕ} {p : Sentence → ℝ} {σ : ℕ → ℕ → Sentence}
variable {S : StateSystem} {m : ℕ}

/-- **Faith at a decided sentence pins the value.** If every world of the class decides `L` as
`t` and `p` is a mixture of such worlds, then faith at `L` gives `val_q(L) = [t]` for every
candidate of nonzero mass.
Source: mandate K4 (the mechanism of K4a); this package
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem charged_val_eq_of_decided (hcoh : CoherentOnW 𝒲 A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) {L : Sentence}
    (hLA : sentenceAtomCodes L ⊆ A) {t : Prop} (hL : ∀ v : PCWorld, 𝒲 v → (v.Holds L ↔ t))
    (hfaith : ∀ q ∈ S.states m, p (L ⋏ σ m q) = S.val m q L * p (σ m q)) {q : ℕ}
    (hq : q ∈ S.states m) (hpos : p (σ m q) ≠ 0) :
    (t → S.val m q L = 1) ∧ (¬ t → S.val m q L = 0) := by
  obtain ⟨k, W, w, hW, hM⟩ := (coherentOnW_iff _ _ _).1 hcoh
  have hf := hfaith q hq
  constructor
  · intro ht
    rw [hM.and_state_eq_of_forced (hσA q hq) hLA (fun i _ _ => (hL (W i) (hW i)).2 ht)] at hf
    exact mul_right_cancel₀ hpos (hf.symm.trans (one_mul _).symm)
  · intro ht
    rw [hM.and_state_eq_zero_of_excluded (hσA q hq) hLA
      (fun i _ _ hl => ht ((hL (W i) (hW i)).1 hl))] at hf
    rcases mul_eq_zero.1 hf.symm with h | h
    · exact h
    · exact absurd h hpos

/-- A sentence of nonzero mass holds in some charged world of the mixture.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem IsMixture.exists_holds_of_ne_zero {k : ℕ} {W : Fin k → PCWorld} {w : Fin k → ℝ}
    (hM : IsMixture W w A p) {ψ : Sentence} (hψ : sentenceAtomCodes ψ ⊆ A) (h : p ψ ≠ 0) :
    ∃ i, 0 < w i ∧ (W i).Holds ψ := by
  by_contra hcon
  apply h
  rw [hM.rep ψ hψ]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases (hM.nonneg i).lt_or_eq with hi | hi
  · rw [payout_of_not_holds fun hh => hcon ⟨i, hi, hh⟩, mul_zero]
  · rw [← hi, zero_mul]

/-- `⊥` holds in no world.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma not_holds_falsum (v : PCWorld) : ¬ v.Holds (⊥ : Sentence) := fun h => h

/-- **Faith at `⊥` forces `val_q(⊥) = 0`** for every charged candidate, under any coherence.
Source: this package (the vacuity mechanism); bli-found `falsum_mem_Sminus`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem faith_at_falsum (hcoh : CoherentOnW 𝒲 A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A)
    (hfaith : ∀ q ∈ S.states m, p (⊥ ⋏ σ m q) = S.val m q ⊥ * p (σ m q)) {q : ℕ}
    (hq : q ∈ S.states m) (hpos : p (σ m q) ≠ 0) : S.val m q ⊥ = 0 := by
  exact (charged_val_eq_of_decided hcoh hσA (L := (⊥ : Sentence)) (by simp) (t := False)
    (fun v _ => ⟨not_holds_falsum v, False.elim⟩) hfaith hq hpos).2 not_false

/-- **Faith at `⊤` forces `val_q(⊤) = 1`** for every charged candidate, under any coherence.
Source: this package; bli-trajectory `Partition.e4_iff_partition_mass` (⇒) (the `⊤` step)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem faith_at_verum (hcoh : CoherentOnW 𝒲 A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A)
    (hfaith : ∀ q ∈ S.states m, p (⊤ ⋏ σ m q) = S.val m q ⊤ * p (σ m q)) {q : ℕ}
    (hq : q ∈ S.states m) (hpos : p (σ m q) ≠ 0) : S.val m q ⊤ = 1 := by
  exact (charged_val_eq_of_decided hcoh hσA (L := (⊤ : Sentence)) (by simp) (t := True)
    (fun v _ => ⟨fun _ => trivial, fun _ => PCWorld.holds_top v⟩) hfaith hq hpos).1 trivial

/-- **A system every candidate of which values `⊥` away from `0` admits no coherent faithful
partition**: some candidate is charged (mass one), and faith at `⊥` pins its value to `0`.
Source: this package (the vacuity mechanism)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem no_partition_of_val_falsum_ne_zero (hcoh : CoherentOnW 𝒲 A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) (hpart : PartitionAt σ S p m)
    (hfaith : ∀ q ∈ S.states m, p (⊥ ⋏ σ m q) = S.val m q ⊥ * p (σ m q))
    (hval : ∀ q ∈ S.states m, S.val m q ⊥ ≠ 0) : False := by
  have hzero : ∀ q ∈ S.states m, p (σ m q) = 0 := fun q hq => by
    by_contra hpos
    exact hval q hq (faith_at_falsum hcoh hσA hfaith hq hpos)
  have := hpart.mass
  rw [Finset.sum_eq_zero hzero] at this
  exact zero_ne_one this

end Pin

/-! ## Day-level forms -/

section Day

variable {σ : ℕ → ℕ → Sentence} {S : StateSystem} {atoms : ℕ → Finset ℕ} {DP : DeductiveProcess}
variable {P : History}

/-- **`PCPσ ∧ E5σ ∧ E2xσ` is unsatisfiable over a system valuing `⊥` away from `0`** on every
candidate of some day `n+1`.
Source: this package (the vacuity finding)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem package_unsat_of_val_falsum_ne_zero (hatoms : ∀ n, stateAtoms σ S n ⊆ atoms n) (n : ℕ)
    (hval : ∀ q ∈ S.states (n + 1), S.val (n + 1) q ⊥ ≠ 0) :
    ¬ (PCPσ atoms DP P ∧ E5σ σ S P ∧ E2xσ σ S P) := by
  rintro ⟨hcoh, hE5, hE2⟩
  refine no_partition_of_val_falsum_ne_zero ((coherentOn_iff_coherentOnW _ _ _).1 (hcoh n))
    (fun q hq => (atoms_subset_stateAtoms σ S hq).trans ((hatoms n).trans Finset.subset_union_right))
    (partitionAt_of_E5σ hE5 n) (fun q hq => hE2 n (n + 1) (Nat.lt_succ_self n) q hq ⊥
      (falsum_mem_Sminus _ _)) hval

end Day

/-! ## K4a abstract: the liar under interval linkage -/

section Liar

variable {DP : DeductiveProcess} {A : Finset ℕ} {p : Sentence → ℝ} {σ : ℕ → ℕ → Sentence}
variable {S : StateSystem} {m : ℕ}

/-- **K4a, abstract.** Under theory-level coherence, if the liar `L` holds in every
completed-theory world iff `x < t` (its price-reflection), faith at `L` holds at every candidate,
and a charged candidate values `L` strictly inside the cell `(lo, hi)` it assigns `L`, then that
cell contains the liar's truth value: `lo < 1 < hi` when `x < t`, `lo < 0 < hi` otherwise. So
full-scope faith is inconsistent exactly when the charged cell excludes the truth value.
Source: [[bli-program]] §3.6(iv); [[bli-program-desiderata]] I4; mandate K4a
Kind: P
Fidelity: exact (abstract; `hL` is the diagonal's reflection, discharged at B2 by FAF's `BooleanQuoteCode.reflected`)
Hyps: (a) -/
theorem charged_cell_contains_truth (hcoh : CoherentOnTheory DP A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) {L : Sentence}
    (hLA : sentenceAtomCodes L ⊆ A) {x t : ℚ}
    (hL : ∀ v : PCWorld, v.ConsistentWithTheory DP → (v.Holds L ↔ x < t))
    (hfaith : ∀ q ∈ S.states m, p (L ⋏ σ m q) = S.val m q L * p (σ m q)) {q : ℕ}
    (hq : q ∈ S.states m) (hpos : p (σ m q) ≠ 0) {lo hi : ℚ}
    (hval : (lo : ℝ) < S.val m q L ∧ S.val m q L < hi) :
    (x < t ∧ lo < 1 ∧ 1 < hi) ∨ (t ≤ x ∧ lo < 0 ∧ 0 < hi) := by
  have h := charged_val_eq_of_decided hcoh hσA hLA hL hfaith hq hpos
  by_cases hxt : x < t
  · rw [h.1 hxt] at hval
    exact Or.inl ⟨hxt, by exact_mod_cast hval.1, by exact_mod_cast hval.2⟩
  · rw [h.2 hxt] at hval
    exact Or.inr ⟨not_lt.1 hxt, by exact_mod_cast hval.1, by exact_mod_cast hval.2⟩

/-- **K4a, the inconsistency**: with a charged candidate whose cell at the liar excludes the
truth value, full-scope faith is inconsistent.
Source: mandate K4a
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem faith_full_scope_inconsistent (hcoh : CoherentOnTheory DP A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) {L : Sentence}
    (hLA : sentenceAtomCodes L ⊆ A) {x t : ℚ}
    (hL : ∀ v : PCWorld, v.ConsistentWithTheory DP → (v.Holds L ↔ x < t))
    (hfaith : ∀ q ∈ S.states m, p (L ⋏ σ m q) = S.val m q L * p (σ m q)) {q : ℕ}
    (hq : q ∈ S.states m) (hpos : p (σ m q) ≠ 0) {lo hi : ℚ}
    (hval : (lo : ℝ) < S.val m q L ∧ S.val m q L < hi)
    (hcell : (x < t → hi ≤ 1 ∨ 1 ≤ lo) ∧ (t ≤ x → hi ≤ 0 ∨ 0 ≤ lo)) : False := by
  rcases charged_cell_contains_truth hcoh hσA hLA hL hfaith hq hpos hval with
    ⟨hxt, h1, h2⟩ | ⟨hxt, h1, h2⟩
  · rcases hcell.1 hxt with h | h <;> linarith
  · rcases hcell.2 hxt with h | h <;> linarith

/-- **The cell of the price straddles the price** for every legitimate rounding: the forced open
cell of `round m p` contains `p` in its interior (`bli-found` F-16's mechanism, at the threshold
`p`). This is why the *quote* forced by linkage cannot decide the liar at the cell containing `p`
— and why K4a's contradiction must come from the price-reflection of the liar instead
(`charged_cell_contains_truth`), where it does not matter.
Source: mandate K4 (angle B: "the open cell around ½ straddles p = ½"); bli-found F-16
Kind: L
Fidelity: n/a -/
theorem straddle (round : ℕ → ℚ → ℕ) (cellLo cellHi : ℕ → ℕ → ℚ)
    (hcell : ∀ m (x : ℚ) r, 0 ≤ x → x ≤ 1 → round m x = r → cellLo m r < x ∧ x < cellHi m r)
    (m : ℕ) {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    cellLo m (round m t) < t ∧ t < cellHi m (round m t) :=
  hcell m t _ h0 h1 rfl

/-- **`halfRound`'s cells always exclude the liar's truth value at `p = 1/2`**: a price below
`1/2` rounds to cell `0 = (-1, 1/2)`, which excludes `1`; a price at or above `1/2` rounds to
cell `1 = (1/4, 2)`, which excludes `0`. So K4a survives interval linkage at `halfRound`,
straddling notwithstanding.
Source: mandate K4 (angle B: "determine whether K4a survives for `halfRound`")
Kind: L
Fidelity: n/a -/
theorem halfRound_cell_excludes_truth (m : ℕ) (x : ℚ) :
    (x < 1 / 2 → halfHi m (halfRound m x) ≤ 1 ∨ 1 ≤ halfLo m (halfRound m x)) ∧
      (1 / 2 ≤ x → halfHi m (halfRound m x) ≤ 0 ∨ 0 ≤ halfLo m (halfRound m x)) := by
  constructor
  · intro h
    rw [halfRound, if_pos h]
    left; norm_num [halfHi]
  · intro h
    rw [halfRound, if_neg (not_lt.2 h)]
    right; norm_num [halfLo]

end Liar

end Cleanroom.Bli.BliLinkageB
