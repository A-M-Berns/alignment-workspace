import Cleanroom.Bli.BliLinkageB.Faith
import LogicalInduction.Construction.Paper.Market

/-!
# bli-linkage, angle B — K4 at B2: the liar over FAF's diagonal

The construction-facing half of K4. `liar T p m` is FAF's public diagonal atom for the single
market at threshold `p` (`paperDiagonalQuoteCode`, `Construction/Paper/Market.lean`): in every
completed-theory world of `paperDP T` it holds iff the market's own same-day price of it is
below `p` (`liar_reflected`, from `BooleanQuoteCode.reflected` at `paperQuotationPresentation`).

* **K4b, the scope lemma** (`liar_notMem_Sminus`): `liar T p m ∉ Sminus n m` for every `n` — the
  atom's packed input is `⟨code, m⟩`, whose `atomDay` is `m` (F-14's mechanism). So faith of
  record (`E2xσ`, scope `Sminus m m`) is silent on the liar: the definition of record's scope
  already excludes it, which is what "forced" means for the scope.
* **K4a at B2** (`liar_full_faith_inconsistent_B2`): over any B2 system whose candidates list
  the liar and value it at a representative inside its cell, with cells excluding the liar's
  truth value at the actual price (`halfRound` at `p = 1/2`:
  `Faith.halfRound_cell_excludes_truth`), theory-level coherence, partition and full-scope faith
  at the liar are inconsistent. Coherence is **relative to the completed theory**
  (`PCPσTheory`): the liar's price-reflection is a fact of the completed theory, not of a
  stage `D n` with `n < m`; the stage-relative variant is not claimed (see the report).

Both are about the same-day liar on day `m = n+1` with the mixture on day `n`.
-/

namespace Cleanroom.Bli.BliLinkageB

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

section Liar

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]

/-- **The liar of record**: FAF's public diagonal atom for the single market at threshold `p`,
"my own price today is below `p`".
Source: FAF `paperDiagonalQuoteCode` (`Construction/Paper/Market.lean:89`); mandate K4
Kind: D
Fidelity: exact -/
noncomputable def liar (p : ℚ) (m : ℕ) : Sentence :=
  (paperDiagonalQuoteCode T p).toBooleanQuoteCode.sentence m

/-- The liar is the quotation atom at `⟨code, m⟩`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma liar_eq (p : ℚ) (m : ℕ) :
    liar T p m = quoteAtom (Nat.pair (paperDiagonalQuoteCode T p).code m) := rfl

/-- **The liar's reflection**: in every completed-theory world of `paperDP T`, `liar T p m` holds
iff the market's day-`m` price of it is below `p`.
Source: FAF `BooleanQuoteCode.reflected` at `paperQuotationPresentation`; `diagonalPriceTruth`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem liar_reflected (p : ℚ) (m : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (liar T p m) ↔ paperQuote T m (Encodable.encode (liar T p m)) < p :=
  (paperDiagonalQuoteCode T p).toBooleanQuoteCode.reflected (paperQuotationPresentation T) m v hv

/-- **K4b — the scope lemma.** The liar of day `m` lies in no `Sminus n m`: its packed input is
`⟨code, m⟩`, read by `atomDay` as `m`. So `E2xσ` (scope `Sminus m m`) never asks for faith at
the liar — the scope of record already excludes it. (F-14: `Sminus` under-approximates the
prose boundary; this is the direction in which that is harmless.)
Source: [[bli-program]] §3.6(iv); bli-soto-a-003; mandate K4b; bli-found F-14
Kind: L
Fidelity: exact (for the scope of record; the prose boundary is a disclosed `(c)`, F-14)
Hyps: (a) -/
theorem liar_notMem_Sminus (p : ℚ) (m n : ℕ) : liar T p m ∉ Sminus n m := by
  intro h
  rw [mem_Sminus] at h
  have := h.2 (quotationClaimCode universalQuotePos universalQuoteNeg
    (Nat.pair (paperDiagonalQuoteCode T p).code m))
    (by simp [liar_eq, quoteAtom, quotationClaimSentence])
  rw [atomDay_quotationClaimCode, Nat.unpair_pair] at this
  exact lt_irrefl _ this

/-- The liar's price lies in `[0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma liar_price_mem (p : ℚ) (m : ℕ) :
    0 ≤ paperQuote T m (Encodable.encode (liar T p m)) ∧
      paperQuote T m (Encodable.encode (liar T p m)) ≤ 1 :=
  paperQuote_mem T m _

end Liar

section LiarB2

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [𝗥₀ ⪯ T]

/-- **K4a at B2.** Over `paperDP T`, a B2 system `b2StateSystem T round index states hact rep`
with representatives strictly inside legitimate cells, cells that exclude the liar's truth value
at every price (`hp`; `halfRound` at `1/2`: `halfRound_cell_excludes_truth`), and every day-`(n+1)`
candidate listing the liar: theory-level coherence on the day-`n` algebra containing the liar,
partition, and full-scope faith at the liar are inconsistent. Route: some candidate is charged
(mass one); it holds in a charged completed-theory world, so its entry at the liar is the
rounded price (`stateSentence_reflected`); its value is that cell's representative, inside the
cell; the liar's reflection pins the value to the truth value, which the cell excludes.
Source: [[bli-program]] §3.6(iv); [[bli-program-desiderata]] I4; bli-soto-a-003; mandate K4a
Kind: C
Fidelity: exact (theory-level coherence; the liar listed by every candidate; same-day liar at `m = n+1`)
Hyps: (a); `hp` is a condition on the rounding's cells (discharged at `halfRound`, `p = 1/2`) -/
theorem liar_full_faith_inconsistent_B2 (p : ℚ) (round : ℕ → ℚ → ℕ)
    (hround : Computable fun x : ℕ × ℚ => round x.1 x.2) (index : ℕ → List ℕ)
    (states : ℕ → Finset ℕ) (hact : ∀ m, actualCode T round index m ∈ states m)
    (rep : ℕ → ℕ → ℚ) (cellLo cellHi : ℕ → ℕ → ℚ)
    (hrep : ∀ m r, cellLo m r < rep m r ∧ rep m r < cellHi m r)
    (hp : ∀ m (x : ℚ), 0 ≤ x → x ≤ 1 →
      (x < p → cellHi m (round m x) ≤ 1 ∨ 1 ≤ cellLo m (round m x)) ∧
      (p ≤ x → cellHi m (round m x) ≤ 0 ∨ 0 ≤ cellLo m (round m x)))
    {A : Finset ℕ} {P : History} (n : ℕ)
    (hcoh : CoherentOnTheory (paperDP T) A (P n))
    (hσA : ∀ q ∈ states (n + 1), sentenceAtomCodes (stateSentence T round hround (n + 1) q) ⊆ A)
    (hLA : sentenceAtomCodes (liar T p (n + 1)) ⊆ A)
    (hpart : PartitionAt (stateSentence T round hround)
      (b2StateSystem T round index states hact rep) (P n) (n + 1))
    (hlist : ∀ q ∈ states (n + 1), ∃ r, entryOf (Encodable.encode (liar T p (n + 1)))
      (tableOfCode q) = some r)
    (hfaith : ∀ q ∈ states (n + 1),
      P n (liar T p (n + 1) ⋏ stateSentence T round hround (n + 1) q) =
        (b2StateSystem T round index states hact rep).val (n + 1) q (liar T p (n + 1)) *
          P n (stateSentence T round hround (n + 1) q)) : False := by
  -- a charged candidate
  obtain ⟨q, hq, hpos⟩ : ∃ q ∈ states (n + 1), P n (stateSentence T round hround (n + 1) q) ≠ 0 := by
    by_contra hcon
    have := hpart.mass
    rw [Finset.sum_eq_zero fun q hq => by
      by_contra h; exact hcon ⟨q, hq, h⟩] at this
    exact zero_ne_one this
  -- a charged completed-theory world holding it
  obtain ⟨k, W, w, hW, hM⟩ := (coherentOnW_iff _ _ _).1 hcoh
  obtain ⟨i, -, hi⟩ := hM.exists_holds_of_ne_zero (hσA q hq) hpos
  -- its entry at the liar is the rounded price
  obtain ⟨r, hr⟩ := hlist q hq
  have hent := (stateSentence_reflected T round hround (n + 1) q (W i) (hW i)).1 hi _
    (mem_of_entryOf_eq_some hr)
  simp only [marketValue_pair] at hent
  set x := paperQuote T (n + 1) (Encodable.encode (liar T p (n + 1))) with hx
  -- its value is the representative of that cell
  have hval : ((cellLo (n + 1) r : ℚ) : ℝ) <
      (b2StateSystem T round index states hact rep).val (n + 1) q (liar T p (n + 1)) ∧
      (b2StateSystem T round index states hact rep).val (n + 1) q (liar T p (n + 1)) <
        cellHi (n + 1) r := by
    show ((cellLo (n + 1) r : ℚ) : ℝ) < ((((entryOf _ (tableOfCode q)).map (rep (n + 1))).getD 0 : ℚ) : ℝ) ∧
      ((((entryOf _ (tableOfCode q)).map (rep (n + 1))).getD 0 : ℚ) : ℝ) < cellHi (n + 1) r
    rw [hr]
    simp only [Option.map_some, Option.getD_some]
    exact ⟨by exact_mod_cast (hrep (n + 1) r).1, by exact_mod_cast (hrep (n + 1) r).2⟩
  have hx01 := liar_price_mem T p (n + 1)
  have hcells := hp (n + 1) x hx01.1 hx01.2
  rw [hent] at hcells
  exact faith_full_scope_inconsistent hcoh hσA hLA (x := x) (t := p)
    (fun v hv => liar_reflected T p (n + 1) v hv) hfaith hq hpos hval hcells

end LiarB2

end Cleanroom.Bli.BliLinkageB
