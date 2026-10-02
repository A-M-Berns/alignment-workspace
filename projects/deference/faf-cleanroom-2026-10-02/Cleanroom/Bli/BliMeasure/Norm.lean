import Cleanroom.Bli.BliMeasure.Worlds
import Cleanroom.Bli.BliFound.Size
import LogicalInduction.Construction.LIA

/-!
# `bli-measure` · Norm: Conjecture 2 repaired — a world measure from a market by online
normalization (target 6, stretch)

bli-soto-a-042 (Soto PDF 05, Conjecture 2) normalizes `P'_{n'}(φ_W)` over the worlds `W` with
`n' > n` the least day making the fraction well defined — it looks ahead, so `P_n` is not
available on day `n`. The **online repair**: normalize the day-`n` prices themselves, with the
uniform default when the sum is `0`.

* `normWeights P' n B` — `P' n (φ_u) / ∑_{u'} P' n (φ_{u'})`, uniform when the sum is `0`
  (disclosed default). (a) A probability vector on `FiniteWorld B` for nonnegative prices
  (`normWeights_nonneg`, `normWeights_sum`) — a world measure relative to `∅`, not relative to
  `DP.D n`: a logical inductor prices a refuted conjunction at `0` only in the limit.
* (b) **N−** (`normWeights_lia_default`): over FAF's LIA at a finite day `n`, with `B` beyond the
  day's support, every `φ_u` is quoted `0` (`quote_eq_zero_of_not_mem`), so the default branch is
  hit — this is exactly the look-ahead Soto's `n'` papers over.
* (c) the normalizer tends to `1` for fixed `B`: **proved** in `NormLimit.lean`
  (`normSum_tendsto_one`, repair round 2's push; the `OPEN` row `normSum_tendsto_one_open` of
  rounds 0–2 is retired), with the corollary `normWeights_tendsto`: the online weights converge
  to the limiting belief of the world conjunctions.
* (d) `normWeights_noExploit_open` — no e.c. trader exploits the sentence market induced by the
  normalized world measure, with an atom bound covering the day's small sentences: **OPEN**
  relative to FAF's `Exploits` (bli-soto-a-2-002 (a) asks it of the repaired PC-criterion, whose
  relation to FAF's is 2-002 (iii)'s open question); the literal PC-LIC is not a target
  (`bli-exactness` X5). Over an arbitrary (e.g. constant) `B` the statement is argued false.
-/

namespace Cleanroom.Bli.BliMeasure

open LogicalInduction LO.Propositional Finset BoolPCWorld Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliFound

/-- The normalizer: the day-`n` mass of the world conjunctions over `B` atoms.
Source: bli-soto-a-042 (Conjecture 2, online repair)
Kind: D
Fidelity: exact -/
noncomputable def normSum (P' : History) (n B : ℕ) : ℝ := ∑ u : FiniteWorld B, P' n (worldConj u)

/-- **The online normalization**: `P' n (φ_u) / ∑_{u'} P' n (φ_{u'})`, uniform when the sum is `0`
(disclosed default).
Source: bli-soto-a-042 (Conjecture 2), repaired online ([[bli-measure-mandate]] target 6)
Kind: D
Fidelity: variant: online (day-`n` prices, no look-ahead), uniform default (disclosed) -/
noncomputable def normWeights (P' : History) (n B : ℕ) : FiniteWorld B → ℝ :=
  fun u => if normSum P' n B = 0 then 1 / (Fintype.card (FiniteWorld B) : ℝ)
    else P' n (worldConj u) / normSum P' n B

/-- (a) The normalized weights are nonnegative for nonnegative prices.
Source: [[bli-measure-mandate]] target 6 (a)
Kind: L
Fidelity: exact -/
theorem normWeights_nonneg {P' : History} {n : ℕ} (hP : ∀ φ, 0 ≤ P' n φ) (B : ℕ)
    (u : FiniteWorld B) : 0 ≤ normWeights P' n B u := by
  unfold normWeights
  split_ifs
  · positivity
  · exact div_nonneg (hP _) (Finset.sum_nonneg fun u _ => hP _)

/-- (a) **The normalized weights sum to one** — a world measure relative to `∅` (`∑ xᵢ/S = 1`, or
the uniform sum: arithmetic).
Source: [[bli-measure-mandate]] target 6 (a)
Kind: L
Fidelity: exact
Hyps: (a) `hP` (nonnegative day-`n` prices; FAF's `def:market` range for a market) -/
theorem normWeights_sum {P' : History} {n : ℕ} (_hP : ∀ φ, 0 ≤ P' n φ) (B : ℕ) :
    ∑ u : FiniteWorld B, normWeights P' n B u = 1 := by
  unfold normWeights
  by_cases h : normSum P' n B = 0
  · simp only [h, if_true]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hc : (Fintype.card (FiniteWorld B) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := FiniteWorld B)).ne'
    field_simp
  · simp only [h, if_false]
    rw [← Finset.sum_div]
    show normSum P' n B / normSum P' n B = 1
    exact div_self h

/-! ## (b) N−: the default branch is hit by FAF's LIA at every finite day -/

/-- A member of a conjunction is within its atom bound.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma atomBound_le_sentenceConjunction_of_mem {l : List Sentence} {φ : Sentence} (h : φ ∈ l) :
    atomBound φ ≤ atomBound (sentenceConjunction l) := by
  induction l with
  | nil => simp at h
  | cons ψ l ih =>
      show atomBound φ ≤ max (atomBound ψ) (atomBound (sentenceConjunction l))
      rcases List.mem_cons.mp h with rfl | h'
      · exact le_max_left _ _
      · exact (ih h').trans (le_max_right _ _)

/-- A world conjunction over `B ≥ 1` atoms mentions atom `B - 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma le_atomBound_worldConj {B : ℕ} (hB : 0 < B) (u : FiniteWorld B) :
    B ≤ atomBound (worldConj u) := by
  unfold worldConj
  have hmem : litOf u ⟨B - 1, by omega⟩ ∈ (List.finRange B).map (litOf u) :=
    List.mem_map.mpr ⟨⟨B - 1, by omega⟩, List.mem_finRange _, rfl⟩
  refine le_trans ?_ (atomBound_le_sentenceConjunction_of_mem hmem)
  unfold litOf
  split_ifs
  · show B ≤ B - 1 + 1; omega
  · show B ≤ max (B - 1 + 1) 0; omega

/-- **(b) N− — at every finite day of FAF's LIA the normalizer vanishes beyond the day's support**:
every world conjunction over `B := sup atomBound (support) + 1` atoms is off the day's support,
hence quoted `0`.
Source: [[bli-measure-mandate]] target 6 (b); bli-soto-a-042 (the look-ahead)
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem normSum_lia_eq_zero (DP : DeductiveProcess) (n : ℕ) :
    ∃ B, 0 < B ∧ ∑ u : FiniteWorld B, liaQuote DP n (worldConj u) = 0 := by
  refine ⟨(liaStates DP n).support.sup atomBound + 1, Nat.succ_pos _, ?_⟩
  apply Finset.sum_eq_zero
  intro u _
  apply (liaStates DP n).quote_eq_zero_of_not_mem
  intro hmem
  have h1 := Finset.le_sup (f := atomBound) hmem
  have h2 := le_atomBound_worldConj (Nat.succ_pos _) u
  omega

/-- **(b) The default branch is hit** by the online normalization of FAF's LIA at every finite day:
for `B` beyond the day's support the normalized weights are the uniform default.
Source: [[bli-measure-mandate]] target 6 (b)
Kind: N−
Fidelity: exact
Hyps: (a) none -/
theorem normWeights_lia_default (DP : DeductiveProcess) (n : ℕ) :
    ∃ B, 0 < B ∧ ∀ u : FiniteWorld B,
      normWeights (liaHistory DP) n B u = 1 / (Fintype.card (FiniteWorld B) : ℝ) := by
  obtain ⟨B, hB, hsum⟩ := normSum_lia_eq_zero DP n
  refine ⟨B, hB, fun u => ?_⟩
  unfold normWeights
  rw [if_pos]
  unfold normSum
  have : ∀ u : FiniteWorld B, liaHistory DP n (worldConj u) = (liaQuote DP n (worldConj u) : ℝ) :=
    fun u => rfl
  simp only [this]
  rw [← Rat.cast_sum, hsum, Rat.cast_zero]

/-! ## (c): proved in `NormLimit.lean` (`normSum_tendsto_one`, `normWeights_tendsto`); (d): open -/

/-- **(d) OPEN — no e.c. trader exploits the sentence market induced by the normalized world
measure**, relative to **FAF's `Exploits`** — the program's object of record
([[bli-program-construction]] §3.5), *not* bli-soto-a-2-002's repaired PC-exploitation, whose
relation to FAF's criterion is 2-002 (iii)'s open question (the literal PC-LIC is not a target).
The atom bound `B n` must cover the day-`n` small sentences (`hB`, as `AtomBounds.B_cover`) and
the day-`n` stage (`hBD`, as `CoherentBase.B_stage`; added in repair round 2, audit r2
adversarial N3, so that no stage sentence is priced by the junk convention for atoms beyond the
bound): with a constant `B` the induced market prices every sentence with an atom `≥ B` by worlds
reading that atom `false` — `atom B` at `0` forever — so once the process decides it a trader
buying it is a plausible exploiter, and the universal over all `B` would be false, not open
(audit r1 adversarial N11; argued, not proved).
Source: [[bli-measure-mandate]] target 6 (d); bli-soto-a-2-002 (a)
Kind: OPEN
Fidelity: exact (with the covering bounds; the statement over an arbitrary `B` is not the conjecture)
Hyps: (a) `hB` (the bound covers the day's small sentences); (a) `hBD` (and the day's stage) -/
theorem normWeights_noExploit_open (P : History) (DP : DeductiveProcess) [IsLogicalInductor P DP]
    (B : ℕ → ℕ) (_hB : ∀ n, ∀ φ ∈ smallSet n, atomBound φ ≤ B n)
    (_hBD : ∀ n, ∀ φ ∈ DP.D n, atomBound φ ≤ B n) :
    ∀ Tr : Trader, EfficientlyComputable Tr →
      ¬ Tr.Exploits (fun n φ => ∑ u : FiniteWorld (B n), normWeights P n (B n) u * (worldOf u).payout φ)
        DP := by
  sorry

end Cleanroom.Bli.BliMeasure
