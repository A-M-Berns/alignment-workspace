import Cleanroom.Bli.BliLinkage.AttemptA.InstanceB2
import LogicalInduction.Construction.Paper.Market

/-!
# `bli-linkage`, attempt A — K4: the scope of faith is forced on FAF's diagonal

`L m := (paperDiagonalQuoteCode T p).toBooleanQuoteCode.sentence m` is FAF's self-referential
price sentence ("my price on day `m` is below `p`"): in every completed-theory world of
`paperDP T` it holds iff `paperQuote T m ⌜L m⌝ < p` (`liar_holds_iff`). With `p = 1/2` and
`halfRound` the cell literal of `L m` at cell `0` says exactly that, so **in every
completed-theory world a linked state holding `(⌜L m⌝ ↦ r)` decides `L m` as `[r = 0]`**.

* **K4a** (`faith_full_scope_inconsistent`): `PCPσTheory ∧ E5σ ∧ E2xσIdxFull` (Appendix B's "any
  `φ`" scope `smallSet m`, restricted to the listed coordinates) is inconsistent over any
  `Tabular` system listing `⌜L (n+1)⌝` on day `n+1`, at a day `n` where `L (n+1)` is small,
  provided no representative is the truth value its cell forces (`rep 0 ≠ 1`, `rep 1 ≠ 0` — every
  cell on one side of `p`). Coherence is relative to the **completed theory**: the biconditional
  between `L m` and its cell literal is a fact of the completed theory, not of the stage `D n`
  for `n < m`; the stage-relative variant is not claimed (see the report).
* **K4b** (`liar_notMem_Sminus`, L): `L m ∉ Sminus n m` for every `n` — the tag-`2` atom's
  `atomDay` is `m` — so faith of record (scope `Sminus m m`) is silent on the liar: "forced" means
  the definition of record's scope already excludes it. The prose boundary "no quote of day
  `≥ m`" is a `(c)` inherited from `bli-found` F-14.
* **K4c, scoped witness** (`scoped_faith_consistent`, N−): over the index `[⌜L m⌝]` the point
  mass on one completed-theory world satisfies `PCPσTheory ∧ E5σ ∧ E2xσIdx` — faith on the index
  is vacuous by K4b, and `PCPσTheory ∧ E5σ` forces a point mass anyway
  (`theory_coherent_point_mass`), which is why the witness is N−. The unlinked B1 check (K4c,
  `stateAtom_free`) is not done.
-/

namespace Cleanroom.Bli.BliLinkage.AttemptA

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound Cleanroom.Bli.BliTrajectory

open Classical

namespace Liar

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]

/-- **FAF's diagonal price sentence** at threshold `p`: "my own day-`m` price is below `p`".
Source: FAF `paperDiagonalQuoteCode` (`Construction/Paper/Market.lean:89`); mandate § K4 (`L m`)
Kind: D
Fidelity: exact -/
noncomputable def L (p : ℚ) (m : ℕ) : Sentence :=
  (paperDiagonalQuoteCode T p).toBooleanQuoteCode.sentence m

/-- **Reflection of the liar**: in every completed-theory world of `paperDP T`, `L p m` holds iff
the market's day-`m` quote of it is below `p`.
Source: FAF `BooleanQuoteCode.reflected` at `paperQuotationPresentation`,
`parameterizedDiagonalQuoteCodeOfMarket_public_price_iff`
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem liar_holds_iff (p : ℚ) (m : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (L T p m) ↔ paperQuote T m (Encodable.encode (L T p m)) < p := by
  have h := BooleanQuoteCode.reflected (paperQuotationPresentation T)
    (paperDiagonalQuoteCode T p).toBooleanQuoteCode m v hv
  have h2 := parameterizedDiagonalQuoteCodeOfMarket_public_price_iff (paperMarketComputation T) T p m
  rw [paperQuote_eq_liaHistory] at h2
  unfold L
  rw [h, h2]
  exact Iff.intro (fun h => by exact_mod_cast h) (fun h => by exact_mod_cast h)

/-! ## K4b: the liar is outside the scope of record -/

/-- **K4b — the liar is outside faith's scope of record**: `L p m ∉ Sminus n m` for every `n`,
because its single atom's `atomDay` is `m`, not `< m`.
Source: [[bli-program]] §3.6(iv); desiderata I4; bli-soto-a-003; mandate § K4 (K4b); bli-found F-14
Kind: L
Fidelity: exact (for `bli-found`'s `Sminus`; the prose boundary is a `(c)` of F-14)
Hyps: (a) -/
theorem liar_notMem_Sminus (p : ℚ) (n m : ℕ) : L T p m ∉ Sminus n m := by
  intro h
  rw [mem_Sminus] at h
  have := h.2 (quotationClaimCode universalQuotePos universalQuoteNeg
    (Nat.pair (paperDiagonalQuoteCode T p).toBooleanQuoteCode.code m)) (by
      simp [L, BooleanQuoteCode.sentence, quoteAtom, quotationClaimSentence])
  rw [atomDay_quotationClaimCode, Nat.unpair_pair] at this
  omega

/-! ## K4a: full-scope faith on the liar is inconsistent with completed-theory coherence -/

/-- **`E2xσIdxFull` — faith on the listed coordinates with Appendix B's "any `φ`" scope**
(`smallSet m` in place of `Sminus m m`).
Source: Appendix B (`main.tex:433`); mandate § K4 (`E2xσFull`)
Kind: D
Fidelity: variant: the scope is `smallSet m` (the source's "any `φ`"), on the listed coordinates -/
def E2xσIdxFull (σ : ℕ → ℕ → Sentence) (index : ℕ → List ℕ) (S : StateSystem) (P : History) :
    Prop :=
  ∀ n m, n < m → ∀ q ∈ S.states m, ∀ c ∈ index m, sentenceOfCode c ∈ smallSet m →
    P n (sentenceOfCode c ⋏ σ m q) = S.val m q (sentenceOfCode c) * P n (σ m q)

/-- A completed-theory world holding the `halfRound` state `q` decides the liar by `q`'s cell:
`L (1/2) m` holds iff the entry is `0`.
Source: mandate § K4 ("every charged world holding `σ_{m,q}` holds the cell literal of `L m` at
`q`'s index `r`, hence holds `L m` iff `r = 0`")
Kind: L
Fidelity: n/a -/
lemma liar_decided_by_state (cells : ℕ → Finset ℕ) (hcells : ∀ m x, halfRound m x ∈ cells m)
    (rep : ℕ → ℕ → ℚ) (m q r : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T))
    (hσ : v.Holds (stateOf (B2.b2Family T halfRound halfRound_computable cells hcells rep) m q))
    (he : entryOf (Encodable.encode (L T (1 / 2) m)) (tableOfCode q) = some r) :
    v.Holds (L T (1 / 2) m) ↔ r = 0 := by
  have hlit := holds_lit_of_holds_stateOf hσ he
  change v.Holds (cellSentence T halfRound halfRound_computable m _ r) at hlit
  rw [cellSentence_reflected T halfRound halfRound_computable m _ r v hv, marketValue_pair] at hlit
  rw [liar_holds_iff T (1 / 2) m v hv]
  unfold halfRound at hlit
  constructor
  · intro hlt; rw [if_pos hlt] at hlit; exact hlit.symm
  · intro hr; rw [hr] at hlit; by_contra hlt; rw [if_neg hlt] at hlit; exact one_ne_zero hlit

/-- **K4a — faith with Appendix B's full scope is inconsistent with completed-theory coherence
on FAF's diagonal.** Over `paperDP T`, `halfRound`, a `Tabular` system over an index listing
`⌜L (1/2) (n+1)⌝` on day `n+1`, with `L (1/2) (n+1)` small on day `n` and representatives with
`rep (n+1) 0 ≠ 1` and `rep (n+1) 1 ≠ 0` (every cell on one side of `1/2`):
`PCPσTheory ∧ E5σ ∧ E2xσIdxFull` is false. The charged state `q` (from mass one) decides the
liar as `[r = 0]` in every completed-theory world (`liar_decided_by_state`), so
`P n (L ⋏ σ_q) = [r = 0] · P n σ_q`, while faith demands `rep r · P n σ_q`.
Source: [[bli-program]] §3.6(iv); desiderata I4; bli-soto-a-003; mandate § K4 (K4a)
Kind: P
Fidelity: exact (completed-theory coherence; the stage-relative variant is not claimed)
Hyps: (a); `hL` (the liar small on day `n`, true eventually), `hrep` (cells on one side of `p`) -/
theorem faith_full_scope_inconsistent (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, halfRound m x ∈ cells m) (rep : ℕ → ℕ → ℚ) (index : ℕ → List ℕ)
    (S : StateSystem)
    (hT : Tabular (B2.b2Family T halfRound halfRound_computable cells hcells rep) index S)
    (n : ℕ) (hidx : Encodable.encode (L T (1 / 2) (n + 1)) ∈ index (n + 1))
    (hL : L T (1 / 2) (n + 1) ∈ smallSet n)
    (hrep : rep (n + 1) 0 ≠ 1 ∧ rep (n + 1) 1 ≠ 0)
    (hcells01 : ∀ r ∈ cells (n + 1), r = 0 ∨ r = 1) (P : History) :
    ¬ (PCPσTheory (stateOf (B2.b2Family T halfRound halfRound_computable cells hcells rep)) S
        (paperDP T) P ∧
      E5σ (stateOf (B2.b2Family T halfRound halfRound_computable cells hcells rep)) S P ∧
      E2xσIdxFull (stateOf (B2.b2Family T halfRound halfRound_computable cells hcells rep)) index
        S P) := by
  rintro ⟨hcoh, hE5, hE2⟩
  set C := B2.b2Family T halfRound halfRound_computable cells hcells rep with hC
  obtain ⟨k, W, w, hW, hw, hsum, hrep'⟩ := hcoh n
  -- a charged state
  have hpos : ∃ q ∈ S.states (n + 1), 0 < P n (stateOf C (n + 1) q) := by
    by_contra hall
    have : ∑ q ∈ S.states (n + 1), P n (stateOf C (n + 1) q) ≤ 0 :=
      Finset.sum_nonpos fun q hq => not_lt.1 (fun h => hall ⟨q, hq, h⟩)
    linarith [(hE5 n).1]
  obtain ⟨q, hq, hqpos⟩ := hpos
  obtain ⟨r, hr, he⟩ := hT.keys (n + 1) q hq _ hidx
  have hAσ : sentenceAtomCodes (stateOf C (n + 1) q) ⊆ pcpAtomsσ (stateOf C) S n :=
    (atoms_subset_stateAtomsσ hq).trans Finset.subset_union_right
  have hAL : sentenceAtomCodes (L T (1 / 2) (n + 1)) ⊆ pcpAtomsσ (stateOf C) S n :=
    (atoms_subset_smallAtoms hL).trans Finset.subset_union_left
  -- the mixture's value of `L ⋏ σ_q` is `[r = 0] · P n σ_q`
  have h1 : P n (L T (1 / 2) (n + 1) ⋏ stateOf C (n + 1) q) =
      (if r = 0 then 1 else 0) * P n (stateOf C (n + 1) q) := by
    rw [hrep' _ (by rw [sentenceAtomCodes_and]; exact Finset.union_subset hAL hAσ), hrep' _ hAσ,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [payout_and]
    by_cases hσ : (W i).Holds (stateOf C (n + 1) q)
    · have hiff := liar_decided_by_state T cells hcells rep (n + 1) q r (W i) (hW i) hσ he
      unfold PCWorld.payout
      rw [if_pos hσ]
      by_cases hr0 : r = 0
      · rw [if_pos (hiff.2 hr0), if_pos hr0]; ring
      · rw [if_neg (fun h => hr0 (hiff.1 h)), if_neg hr0]; ring
    · unfold PCWorld.payout
      rw [if_neg hσ]; ring
  -- faith demands `rep r · P n σ_q`
  have h2 := hE2 n (n + 1) (Nat.lt_succ_self n) q hq _ hidx
    (by rw [sentenceOfCode_encode]; exact smallSet_mono (Nat.le_succ n) hL)
  rw [hT.val (n + 1) q hq _ hidx r he, sentenceOfCode_encode, h1] at h2
  have h3 : ((C.rep (n + 1) r : ℝ) - (if r = 0 then 1 else 0)) * P n (stateOf C (n + 1) q) = 0 := by
    linarith
  rcases mul_eq_zero.1 h3 with h4 | h4
  · rcases hcells01 r hr with rfl | rfl
    · simp only [if_true, sub_eq_zero] at h4
      exact hrep.1 (by exact_mod_cast h4)
    · simp only [one_ne_zero, if_false, sub_zero] at h4
      exact hrep.2 (by exact_mod_cast h4)
  · linarith

/-! ## K4c: the scoped form is consistent (a point mass, by necessity) -/

/-- The liar index: `[⌜L (1/2) m⌝]` on day `m`.
Source: mandate § K4 ("an index list containing `⌜L m⌝` on day `m`")
Kind: D
Fidelity: n/a -/
noncomputable def liarIndex : ℕ → List ℕ := fun m => [Encodable.encode (L T (1 / 2) m)]

/-- The two liar tables of day `m`: `⌜L m⌝` in cell `0` or in cell `1`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def liarStates (m : ℕ) : Finset ℕ :=
  {Encodable.encode [(Encodable.encode (L T (1 / 2) m), 0)],
    Encodable.encode [(Encodable.encode (L T (1 / 2) m), 1)]}

/-- The actual liar table is one of the two.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma actualCode_mem_liarStates (m : ℕ) :
    actualCode T halfRound (liarIndex T) m ∈ liarStates T m := by
  unfold actualCode actualTable liarIndex liarStates
  have := halfRound_le_one m (marketValue T (Nat.pair m (Encodable.encode (L T (1 / 2) m))))
  rw [List.map_cons, List.map_nil, Finset.mem_insert, Finset.mem_singleton]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h
  · left; rw [h]
  · right; rw [h]

/-- The liar system: the two liar tables, endpoint representatives.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def liarSystem : StateSystem :=
  b2StateSystem T halfRound (liarIndex T) (liarStates T) (actualCode_mem_liarStates T) B2.rep01

/-- The point-mass market on a completed-theory world.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
noncomputable def pointP (v : PCWorld) : History := fun _ φ => v.payout φ

/-- **K4c (scoped) — faith of record is consistent with completed-theory coherence over the
liar index**: for any completed-theory world `v` of `paperDP T` (`paperDP_nonvacuous`), the
point mass `pointP v` satisfies `PCPσTheory ∧ E5σ ∧ E2xσIdx` over `liarSystem`. Faith on the
index is vacuous (K4b: the liar is outside `Sminus m m`); exactly one liar table holds in `v`
(reflection). **N−**: one state charged, by necessity — `PCPσTheory ∧ E5σ` forces the point mass
on the realized state (`theory_coherent_point_mass`).
Source: mandate § K4 (K4c, "Scoped")
Kind: N-
Fidelity: n/a (point mass; the mandate's two-world mixture is impossible under completed-theory coherence)
Hyps: (a) -/
theorem scoped_faith_consistent (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    PCPσTheory (stateSentence T halfRound halfRound_computable) (liarSystem T) (paperDP T)
        (pointP v) ∧
      E5σ (stateSentence T halfRound halfRound_computable) (liarSystem T) (pointP v) ∧
      E2xσIdx (stateSentence T halfRound halfRound_computable) (liarIndex T) (liarSystem T)
        (pointP v) := by
  refine ⟨fun n => ⟨1, fun _ => v, fun _ => 1, fun _ => hv, fun _ => zero_le_one, by simp,
    fun φ _ => by simp [pointP]⟩, fun n => ⟨?_, ?_⟩, ?_⟩
  · -- exactly one of the two liar tables holds in `v`
    show ∑ q ∈ liarStates T (n + 1), v.payout (stateSentence T halfRound halfRound_computable (n + 1) q) = 1
    have hne : Encodable.encode [(Encodable.encode (L T (1 / 2) (n + 1)), 0)] ≠
        Encodable.encode [(Encodable.encode (L T (1 / 2) (n + 1)), 1)] := by
      intro h; have := Encodable.encode_inj.1 h; simp at this
    unfold liarStates
    rw [Finset.sum_pair hne]
    have key : ∀ r, v.Holds (stateSentence T halfRound halfRound_computable (n + 1)
        (Encodable.encode [(Encodable.encode (L T (1 / 2) (n + 1)), r)])) ↔
        halfRound (n + 1) (marketValue T (Nat.pair (n + 1) (Encodable.encode (L T (1 / 2) (n + 1))))) = r := by
      intro r
      rw [stateSentence_reflected T halfRound halfRound_computable _ _ v hv, tableOfCode_encode]
      simp
    unfold PCWorld.payout
    rw [key 0, key 1]
    have := halfRound_le_one (n + 1) (marketValue T (Nat.pair (n + 1) (Encodable.encode (L T (1 / 2) (n + 1)))))
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h <;> rw [h] <;> norm_num
  · intro q₁ hq₁ q₂ hq₂ hne
    show v.payout (_ ⋏ _) = 0
    rw [payout_and]
    simp only [liarSystem, b2StateSystem, liarStates, Finset.mem_insert, Finset.mem_singleton]
      at hq₁ hq₂
    have key : ∀ r, v.Holds (stateSentence T halfRound halfRound_computable (n + 1)
        (Encodable.encode [(Encodable.encode (L T (1 / 2) (n + 1)), r)])) ↔
        halfRound (n + 1) (marketValue T (Nat.pair (n + 1) (Encodable.encode (L T (1 / 2) (n + 1))))) = r := by
      intro r
      rw [stateSentence_reflected T halfRound halfRound_computable _ _ v hv, tableOfCode_encode]
      simp
    unfold PCWorld.payout
    have := halfRound_le_one (n + 1) (marketValue T (Nat.pair (n + 1) (Encodable.encode (L T (1 / 2) (n + 1)))))
    rcases hq₁ with rfl | rfl <;> rcases hq₂ with rfl | rfl
    · exact absurd rfl hne
    · rw [key 0, key 1]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h <;> rw [h] <;> norm_num
    · rw [key 1, key 0]
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp this with h | h <;> rw [h] <;> norm_num
    · exact absurd rfl hne
  · intro n m _ q _ c hc hS
    exfalso
    simp only [liarIndex, List.mem_singleton] at hc
    subst hc
    rw [sentenceOfCode_encode] at hS
    exact liar_notMem_Sminus T (1 / 2) m m hS

end Liar

end Cleanroom.Bli.BliLinkage.AttemptA
