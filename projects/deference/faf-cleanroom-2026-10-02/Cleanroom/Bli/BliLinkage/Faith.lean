import Cleanroom.Bli.BliLinkage.Bridge
import Cleanroom.Bli.BliLinkageB.FaithB2
import Cleanroom.Bli.BliLinkage.AttemptA.Faith

/-!
# `bli-linkage` — K4: the scope of faith is forced (of record)

Both attempts proved K4a (full-scope faith is inconsistent on FAF's diagonal under
completed-theory coherence) and K4b (the liar is outside `Sminus n m` for every `n`), by the
same mechanism and over the same FAF object (`paperDiagonalQuoteCode T p`): in every
completed-theory world of `paperDP T` the liar `L m` holds iff `𝑸_m(L m) < p`
(`BooleanQuoteCode.reflected` at `paperQuotationPresentation T`), so a charged candidate must
value it at its truth value, while its B2 value lies in the cell it assigns — and the
`halfRound` cell of the actual price always excludes the truth value. They differ in packaging:
attempt B's `liar_full_faith_inconsistent_B2` is over `b2StateSystem`, one day, `CoherentOnTheory`
and faith at the liar (the **form of record**, over record objects); attempt A's
`faith_full_scope_inconsistent` is over any `Tabular` system listing the liar with Appendix B's
"any `φ`" scope `E2xσIdxFull` and `PCPσTheory` (restated through the bridge as the second form).
Attempt B adds two things of its own: K4a **survives interval linkage** at `halfRound` (the
straddling of `p` by the forced open cell is irrelevant; FB-7), and the theory-level package is
**degenerate** with `E1x` (`Trilemma.theory_coherent_e1x_decides`; FB-3) — both attempts note
that `PCPσTheory ∧ E5σ` collapses the superbelief to a point mass. Attempt A alone built K4c's
scoped witness (`scoped_faith_consistent`, N− by necessity). Neither built the unlinked (B1)
check or the stage-relative variant.

**Finding of record** (both attempts): Appendix B's "any `φ`" is inconsistent under linkage; the
Notion reading (scope `S_m^-`, in the definition of record `Sminus m m`, which excludes the liar)
is the surviving neighbour; the prose boundary is `bli-found` F-14's disclosed `(c)`.
-/

namespace Cleanroom.Bli.BliLinkage

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliFound

section Abstract

variable {DP : DeductiveProcess} {A : Finset ℕ} {p : Sentence → ℝ} {σ : ℕ → ℕ → Sentence}
variable {S : StateSystem} {m : ℕ}

/-- **Faith at a sentence all worlds decide pins the charged candidate's value** to the truth
value — the mechanism of K4 and of the vacuity findings (`⊥`, `⊤`).
Source: mandate K4 (mechanism); attempt B `Faith.charged_val_eq_of_decided`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem charged_val_eq_of_decided {𝒲 : PCWorld → Prop} (hcoh : CoherentOnW 𝒲 A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) {L : Sentence}
    (hLA : sentenceAtomCodes L ⊆ A) {t : Prop} (hL : ∀ v : PCWorld, 𝒲 v → (v.Holds L ↔ t))
    (hfaith : ∀ q ∈ S.states m, p (L ⋏ σ m q) = S.val m q L * p (σ m q)) {q : ℕ}
    (hq : q ∈ S.states m) (hpos : p (σ m q) ≠ 0) :
    (t → S.val m q L = 1) ∧ (¬ t → S.val m q L = 0) :=
  Cleanroom.Bli.BliLinkageB.charged_val_eq_of_decided hcoh hσA hLA hL hfaith hq hpos

/-- **K4a, abstract**: under theory-level coherence, if `L` holds in every completed-theory world
iff `x < t` (the liar's price-reflection), faith at `L` holds at every candidate, and a charged
candidate values `L` strictly inside the cell `(lo, hi)` it assigns `L`, then that cell contains
the truth value — so full-scope faith is inconsistent whenever the cell excludes it (`hcell`).
Source: [[bli-program]] §3.6(iv); desiderata I4; mandate K4a; attempt B `Faith.faith_full_scope_inconsistent`
Kind: P
Fidelity: exact (abstract; theory level)
Hyps: (a) -/
theorem faith_full_scope_inconsistent (hcoh : CoherentOnTheory DP A p)
    (hσA : ∀ q ∈ S.states m, sentenceAtomCodes (σ m q) ⊆ A) {L : Sentence}
    (hLA : sentenceAtomCodes L ⊆ A) {x t : ℚ}
    (hL : ∀ v : PCWorld, v.ConsistentWithTheory DP → (v.Holds L ↔ x < t))
    (hfaith : ∀ q ∈ S.states m, p (L ⋏ σ m q) = S.val m q L * p (σ m q)) {q : ℕ}
    (hq : q ∈ S.states m) (hpos : p (σ m q) ≠ 0) {lo hi : ℚ}
    (hval : (lo : ℝ) < S.val m q L ∧ S.val m q L < hi)
    (hcell : (x < t → hi ≤ 1 ∨ 1 ≤ lo) ∧ (t ≤ x → hi ≤ 0 ∨ 0 ≤ lo)) : False :=
  Cleanroom.Bli.BliLinkageB.faith_full_scope_inconsistent hcoh hσA hLA hL hfaith hq hpos hval hcell

/-- **`halfRound`'s cell of the actual price always excludes the liar's truth value** at
`p = 1/2`: a price below `1/2` rounds to `(-1, 1/2) ∌ 1`, a price at or above to `(1/4, 2) ∌ 0`.
So K4a survives interval linkage at `halfRound`; the straddle of `p` by the forced open cell is
irrelevant (B's FB-7).
Source: mandate § Attempt angles (B: K4 under interval linkage); attempt B `Faith.halfRound_cell_excludes_truth`
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem halfRound_cell_excludes_truth (m : ℕ) (x : ℚ) :
    (x < 1 / 2 → halfHi m (halfRound m x) ≤ 1 ∨ 1 ≤ halfLo m (halfRound m x)) ∧
      (1 / 2 ≤ x → halfHi m (halfRound m x) ≤ 0 ∨ 0 ≤ halfLo m (halfRound m x)) :=
  Cleanroom.Bli.BliLinkageB.halfRound_cell_excludes_truth m x

end Abstract

section Diagonal

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T]

/-- **K4b — the scope lemma**: FAF's diagonal `liar T p m` (the sentence
`(paperDiagonalQuoteCode T p).toBooleanQuoteCode.sentence m`, "my own day-`m` price is below
`p`") is in no `Sminus n m` — its single tag-2 atom reads `atomDay = m`. So faith of record
(scope `Sminus m m`) is silent on the liar: "forced" is "the definition of record's scope already
excludes it". The prose boundary ("no quote of day `≥ m`") is the `(c)` of bli-found F-14.
Source: [[bli-program]] §3.6(iv); bli-soto-a-003; mandate K4b; attempt B `FaithB2.liar_notMem_Sminus` (A: `Liar.liar_notMem_Sminus`)
Kind: L
Fidelity: exact for the scope of record; (c) the prose boundary (F-14)
Hyps: (c) inherited: `Sminus` under-approximates the prose scope -/
theorem liar_notMem_Sminus (p : ℚ) (m n : ℕ) :
    Cleanroom.Bli.BliLinkageB.liar T p m ∉ Sminus n m :=
  Cleanroom.Bli.BliLinkageB.liar_notMem_Sminus T p m n

/-- **The liar's reflection**: in every completed-theory world of `paperDP T`, `liar T p m` holds
iff `paperQuote T m ⌜liar T p m⌝ < p`.
Source: FAF `BooleanQuoteCode.reflected`, `parameterizedDiagonalQuoteCodeOfMarket_public_price_iff`; attempt B `FaithB2.liar_reflected` (A: `Liar.liar_holds_iff`)
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem liar_reflected (p : ℚ) (m : ℕ) (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    v.Holds (Cleanroom.Bli.BliLinkageB.liar T p m) ↔
      paperQuote T m (Encodable.encode (Cleanroom.Bli.BliLinkageB.liar T p m)) < p :=
  Cleanroom.Bli.BliLinkageB.liar_reflected T p m v hv

end Diagonal

section DiagonalB2

variable (T : LO.FirstOrder.ArithmeticTheory) [T.Δ₁] [𝗣𝗔⁻ ⪯ T] [𝗥₀ ⪯ T]

/-- **K4a at B2 over FAF's diagonal (of record)**: for any B2 system listing the liar with
representatives strictly inside their cells and a rounding whose cell of the actual price
excludes the truth value (`hp`; `halfRound` at `p = 1/2` by `halfRound_cell_excludes_truth`),
theory-level coherence on an algebra containing the liar and the states (`CoherentOnTheory`),
the partition at day `n+1`, and faith at the liar on every candidate (Appendix B's "any `φ`") are
inconsistent. Coherence is relative to the **completed theory**, as the mandate prescribes
(the biconditional between the liar and its cell literal is a fact of the theory, not of the
stage `D n`); that level is degenerate with `E1x` (`Trilemma.theory_coherent_e1x_decides`), and
the stage-relative variant is not claimed. **Where the self-reference enters** (audit r1
fidelity N6): the engine `charged_val_eq_of_decided` pins the charged candidate's value at
*any* sentence the completed theory decides to its truth value; the liar is special only through
`hp` — the cell of the liar's *own* price excludes its truth value (`halfRound_cell_excludes_truth`),
which makes the inconsistency unconditional for the liar and conditional on the day's price for
a non-self-referential decided sentence such as `⊤`.
Source: [[bli-program]] §3.6(iv); desiderata I4; bli-soto-a-003; mandate K4a (judged item 4); attempt B `FaithB2.liar_full_faith_inconsistent_B2`
Kind: C
Fidelity: exact (theory level; same-day liar at `m = n+1`)
Hyps: (a) -/
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
    (hLA : sentenceAtomCodes (Cleanroom.Bli.BliLinkageB.liar T p (n + 1)) ⊆ A)
    (hpart : Cleanroom.Bli.BliLinkageB.PartitionAt (stateSentence T round hround)
      (b2StateSystem T round index states hact rep) (P n) (n + 1))
    (hlist : ∀ q ∈ states (n + 1), ∃ r,
      entryOf (Encodable.encode (Cleanroom.Bli.BliLinkageB.liar T p (n + 1))) (tableOfCode q) = some r)
    (hfaith : ∀ q ∈ states (n + 1),
      P n (Cleanroom.Bli.BliLinkageB.liar T p (n + 1) ⋏ stateSentence T round hround (n + 1) q) =
        (b2StateSystem T round index states hact rep).val (n + 1) q
            (Cleanroom.Bli.BliLinkageB.liar T p (n + 1)) *
          P n (stateSentence T round hround (n + 1) q)) : False :=
  Cleanroom.Bli.BliLinkageB.liar_full_faith_inconsistent_B2 T p round hround index states hact rep
    cellLo cellHi hrep hp n hcoh hσA hLA hpart hlist hfaith

/-- **K4a, attempt A's form** (second proof, restated through the bridge): over any `Tabular`
system listing `⌜L (1/2) (n+1)⌝` on day `n+1`, at a day `n` where the liar is small, with cells
in `{0, 1}` and representatives on one side of `1/2` (`rep 0 ≠ 1`, `rep 1 ≠ 0`),
`PCPσTheory ∧ E5σ ∧ E2xσIdxFull` (Appendix B's "any `φ`" scope `smallSet m` on the listed
coordinates) is false. The coherence hypothesis is stated in the record form (`PCPσTheory` at
the state atoms); the family and system are attempt A's `b2Family`/`Tabular`.
Source: [[bli-program]] §3.6(iv); mandate K4a; attempt A `Liar.faith_full_scope_inconsistent`
Kind: P (refutation)
Fidelity: exact (completed-theory coherence; the stage-relative variant not claimed; `hL` eventually true, not proved as `∃ N`)
Hyps: (a) -/
theorem faith_full_scope_inconsistent_tabular (cells : ℕ → Finset ℕ)
    (hcells : ∀ m x, halfRound m x ∈ cells m) (rep : ℕ → ℕ → ℚ) (index : ℕ → List ℕ)
    (S : StateSystem)
    (hT : AttemptA.Tabular (AttemptA.B2.b2Family T halfRound halfRound_computable cells hcells rep)
      index S)
    (n : ℕ) (hidx : Encodable.encode (AttemptA.Liar.L T (1 / 2) (n + 1)) ∈ index (n + 1))
    (hL : AttemptA.Liar.L T (1 / 2) (n + 1) ∈ smallSet n)
    (hrep : rep (n + 1) 0 ≠ 1 ∧ rep (n + 1) 1 ≠ 0)
    (hcells01 : ∀ r ∈ cells (n + 1), r = 0 ∨ r = 1) (P : History) :
    ¬ (PCPσTheory (stateAtoms
          (AttemptA.stateOf (AttemptA.B2.b2Family T halfRound halfRound_computable cells hcells rep))
          S) (paperDP T) P ∧
      E5σ (AttemptA.stateOf (AttemptA.B2.b2Family T halfRound halfRound_computable cells hcells rep))
        S P ∧
      AttemptA.Liar.E2xσIdxFull
        (AttemptA.stateOf (AttemptA.B2.b2Family T halfRound halfRound_computable cells hcells rep))
        index S P) := fun ⟨hcoh, hE5, hE2⟩ =>
  AttemptA.Liar.faith_full_scope_inconsistent T cells hcells rep index S hT n hidx hL hrep hcells01 P
    ⟨(pcpσTheory_iff _ _ _).2 hcoh, hE5, hE2⟩

/-- **K4c, scoped (N−)**: over the liar index `[⌜L m⌝]` with the two liar tables and endpoint
representatives, the point mass on any completed-theory world `v` of `paperDP T` satisfies
`PCPσTheory ∧ E5σ ∧ E2xσIdx` — faith on the index is vacuous by K4b, and exactly one liar table
holds in `v` (reflection). **N− by necessity**: `PCPσTheory ∧ E5σ` forces the point mass on the
realized state; the mandate's two-world mixture on `[⌜⊥⌝, ⌜⊤⌝]` cannot exist under
completed-theory coherence (and on that index not even under stage coherence,
`InstanceB2.charged_eq_tbl01`).
Source: mandate K4c ("Scoped"); attempt A `Liar.scoped_faith_consistent`
Kind: N-
Fidelity: n/a (point mass, forced)
Hyps: (a) -/
theorem scoped_faith_consistent (v : PCWorld) (hv : v.ConsistentWithTheory (paperDP T)) :
    PCPσTheory (stateAtoms (stateSentence T halfRound halfRound_computable)
        (AttemptA.Liar.liarSystem T)) (paperDP T) (AttemptA.Liar.pointP v) ∧
      E5σ (stateSentence T halfRound halfRound_computable) (AttemptA.Liar.liarSystem T)
        (AttemptA.Liar.pointP v) ∧
      E2xσIdx (stateSentence T halfRound halfRound_computable) (AttemptA.Liar.liarIndex T)
        (AttemptA.Liar.liarSystem T) (AttemptA.Liar.pointP v) :=
  let h := AttemptA.Liar.scoped_faith_consistent T v hv
  ⟨(pcpσTheory_iff _ _ _).1 h.1, h.2.1, h.2.2⟩

end DiagonalB2

end Cleanroom.Bli.BliLinkage
