import Cleanroom.Bli.BliCoherentMm.Recursion
import Cleanroom.Bli.BliCoherentMm.Contrast
import Cleanroom.Bli.BliCoherentMm.FixedPoint
import Cleanroom.Bli.BliCoherentMm.AttemptA.Witness
import Cleanroom.Bli.BliCoherentMm.AttemptB.Witness

/-!
# `bli-coherent-mm` · Witness (reconciled): T4(d) and T6's witness — the hypothesis package over
`paperDP 𝗜𝚺₁`

Every hypothesis of T1–T3 and T6 is discharged over a real deductive process: `hW` from FAF's
`paperDP_hworld` (every stage of the paper process has a consistent world, so the recursion's
fallback branch is never taken and the coherence clause is unconditional), `hB` computed as the
`sup` of the atom bounds. Both attempts built this package; the record carries attempt A's
instances over the record maker and recursion, attempt B's general-`B` discharge of `hW`
(`paperDP_stage_hW`), T1 in the mandate's shape at the paper process
(`coherent_fixed_point_paperDP`, no hypothesis left), the non-vacuity facts (the priced set is
nonempty from some day on; the plausible-assessment set is nonempty), and the grid recursion's
witness.

**Grade: N+ for the hypothesis package.** Not claimed: that `pcHistory` differs from
`liaHistory` on some day (T4 shows the two *makers* differ on `T_pair`, not that the firm ever
plays it); nothing about computability.

Sources: [[bli-coherent-mm-mandate]] T4(d), T6 (witness); FAF `paperDP_hworld`.
-/

namespace Cleanroom.Bli.BliCoherentMm

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-! ## Every stage of the paper process has a consistent world -/

/-- **Every stage of the paper process has a consistent world** (FAF's `paperDP_hworld`).
Source: [[bli-coherent-mm-mandate]] T4(d), T6 (witness); FAF `paperDP_hworld`
Kind: L
Fidelity: exact -/
theorem paperDP_hcons (n : ℕ) : ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) :=
  AttemptA.paperDP_hcons n

/-- **`hW` over the paper process, any atom bound covering the stage** (attempt B's form):
the day-`n` stage has a consistent finite world over `B` atoms.
Source: [[bli-coherent-mm-mandate]] T4(d) ("`hW` from `paperDP_hworld`")
Kind: L
Fidelity: exact -/
theorem paperDP_stage_hW (n : ℕ) {B : ℕ} (hB : ∀ φ ∈ (paperDP 𝗜𝚺₁).D n, atomBound φ ≤ B) :
    ∃ u : FiniteWorld B, (worldOf u).ConsistentWith ((paperDP 𝗜𝚺₁).D n) :=
  AttemptB.paperDP_stage_hW n hB

/-- An atom bound for the day-`n` stage of the paper process (attempt A's).
Source: [[bli-coherent-mm-mandate]] T4(d) ("`hB` computed")
Kind: D
Fidelity: exact -/
noncomputable abbrev paperDP_atoms (n : ℕ) : ℕ := AttemptA.paperDP_atoms n

/-- `hW` over the paper process at `paperDP_atoms n`.
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: L
Fidelity: exact -/
theorem paperDP_hW (n : ℕ) :
    ∃ u : FiniteWorld (paperDP_atoms n), (worldOf u).ConsistentWith ((paperDP 𝗜𝚺₁).D n) :=
  AttemptA.paperDP_hW n

/-- The simplex of the witness is nonempty.
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: N+
Fidelity: n/a -/
theorem paperDP_WD_nonempty (n : ℕ) : (WD ((paperDP 𝗜𝚺₁).D n) (paperDP_atoms n)).Nonempty :=
  AttemptA.paperDP_WD_nonempty n

/-- The computed atom bound of a sentence set (attempt B's `sup`).
Source: [[bli-coherent-mm-mandate]] T4(d) ("`hB` computed")
Kind: D
Fidelity: exact -/
abbrev atomBoundOf (A : Finset Sentence) : ℕ := AttemptB.atomBoundOf A

/-- The computed atom bound for a strategy at a stage of the paper process covers the mentioned
set and the stage (`hB`, discharged).
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: L
Fidelity: n/a -/
theorem paperDP_hB {n : ℕ} (T : Strategy n) :
    ∀ φ ∈ mentionedSet T ∪ (paperDP 𝗜𝚺₁).D n,
      atomBound φ ≤ atomBoundOf (mentionedSet T ∪ (paperDP 𝗜𝚺₁).D n) :=
  AttemptB.paperDP_hB T

/-! ## T4(d): T1–T3 with their full hypothesis package over the paper process -/

/-- **T4(d), T1 over `paperDP 𝗜𝚺₁`**: for every day-`n` strategy and past, the coherent fixed
point in the mandate's shape, with `hB` computed and `hW` from FAF — no hypothesis left.
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: N+
Fidelity: n/a
Hyps: (a) — none left -/
theorem coherent_fixed_point_paperDP {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) :
    ∃ p : FiniteWorld (atomBoundOf (mentionedSet T ∪ (paperDP 𝗜𝚺₁).D n)) → ℝ,
      (∀ u, 0 ≤ p u) ∧ ∑ u, p u = 1 ∧
      (∀ u, p u ≠ 0 → (worldOf u).ConsistentWith ((paperDP 𝗜𝚺₁).D n)) ∧
      (∀ u ∈ WD ((paperDP 𝗜𝚺₁).D n) (atomBoundOf (mentionedSet T ∪ (paperDP 𝗜𝚺₁).D n)),
        T.value (Function.update (beliefHistory past) n
          (fun φ => ∑ u, p u * (worldOf u).payout φ)) (worldOf u).payout ≤ 0) ∧
      ∀ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) →
        T.value (Function.update (beliefHistory past) n
          (fun φ => ∑ u, p u * (worldOf u).payout φ)) v.payout ≤ 0 :=
  coherent_fixed_point_mandate T past _ _ (paperDP_hB T)
    (paperDP_stage_hW n fun _ hφ => AttemptB.le_atomBoundOf (Finset.mem_union_right _ hφ))

/-- **T4(d). The record maker on `T_pair` over `paperDP 𝗜𝚺₁` quotes `φ` and `∼φ` to one** —
the full package inhabited, the output non-degenerate (attempt A's instance at `atom a`).
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: N+
Fidelity: n/a
Hyps: (a) `hε` only -/
theorem pair_paperDP_sum_one (a n : ℕ) (past : List RationalBeliefState) {ε : ℚ} (hε : 0 < ε) :
    (coherentMarketMaker (pairStrategy n (Formula.atom a)) past ((paperDP 𝗜𝚺₁).D n)
      (paperDP_atoms n) (mentionedSet (pairStrategy n (Formula.atom a))) subset_rfl (paperDP_hW n)
      hε).quote (Formula.atom a) +
    (coherentMarketMaker (pairStrategy n (Formula.atom a)) past ((paperDP 𝗜𝚺₁).D n)
      (paperDP_atoms n) (mentionedSet (pairStrategy n (Formula.atom a))) subset_rfl (paperDP_hW n)
      hε).quote (∼(Formula.atom a)) = 1 :=
  AttemptA.pair_paperDP_sum_one a n past hε

/-- **T4(d). The record maker on `T_pair` over `paperDP 𝗜𝚺₁` is accepted in every world
consistent with the day's stage.**
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pair_paperDP_accepts (a n : ℕ) (past : List RationalBeliefState) {ε : ℚ} (hε : 0 < ε) :
    ∀ u ∈ WD ((paperDP 𝗜𝚺₁).D n) (paperDP_atoms n),
      (pairStrategy n (Formula.atom a)).marketValueRat
        (candidateRationalHistory past n (coherentMarketMaker (pairStrategy n (Formula.atom a))
          past ((paperDP 𝗜𝚺₁).D n) (paperDP_atoms n)
          (mentionedSet (pairStrategy n (Formula.atom a))) subset_rfl (paperDP_hW n) hε))
        u.payoutRat ≤ ε :=
  AttemptA.pair_paperDP_accepts a n past hε

/-- **T4(d), the interior maker of record over `paperDP 𝗜𝚺₁`** on the day's mentioned set at
FAF's day-`n` error: the full package of T3 inhabited.
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: D
Fidelity: exact -/
noncomputable abbrev interiorMakerPaperDP {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) :
    RationalBeliefState :=
  interiorCoherentMarketMaker T past ((paperDP 𝗜𝚺₁).D n)
    (atomBoundOf (mentionedSet T ∪ (paperDP 𝗜𝚺₁).D n)) (mentionedSet T) subset_rfl
    (paperDP_stage_hW n fun _ hφ => AttemptB.le_atomBoundOf (Finset.mem_union_right _ hφ))
    (marketMakerError_pos n)

/-- The paper-process interior maker is accepted at `marketMakerError n` in every world
consistent with the day's stage.
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: N+
Fidelity: n/a
Hyps: (a) none left -/
theorem interiorMakerPaperDP_accepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) :
    ∀ u ∈ WD ((paperDP 𝗜𝚺₁).D n) (atomBoundOf (mentionedSet T ∪ (paperDP 𝗜𝚺₁).D n)),
      T.marketValueRat (candidateRationalHistory past n (interiorMakerPaperDP T past))
        u.payoutRat ≤ marketMakerError n :=
  interior_accepts _ _ _ _ _ _ _ _

/-- The paper-process interior maker's weights have full support on the stage's consistent
worlds.
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: N+
Fidelity: n/a
Hyps: (a) none left -/
theorem interiorMakerPaperDP_fullSupport {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) :
    ∀ u ∈ WD ((paperDP 𝗜𝚺₁).D n) (atomBoundOf (mentionedSet T ∪ (paperDP 𝗜𝚺₁).D n)),
      0 < interiorWeights T past ((paperDP 𝗜𝚺₁).D n)
        (atomBoundOf (mentionedSet T ∪ (paperDP 𝗜𝚺₁).D n)) (mentionedSet T) subset_rfl
        (paperDP_stage_hW n fun _ hφ => AttemptB.le_atomBoundOf (Finset.mem_union_right _ hφ))
        (marketMakerError_pos n) u :=
  interior_fullSupport _ _ _ _ _ _ _ _

/-! ## T6's witness: the coherent overlaid market over the paper process -/

/-- **T6 at the witness: `PCInductor (paperDP 𝗜𝚺₁)` is inhabited** by the coherent overlaid
recursion, for every overlay and priced-set parameter. "Inhabited; `ComputableMarket` open";
not a logical inductor.
Source: [[bli-coherent-mm-mandate]] T6 (witness); [[bli-program]] §4 row M3
Kind: N+
Fidelity: n/a
Hyps: (a) -/
noncomputable abbrev pcInductor_paperDP (ov : Overlay) (X : ℕ → Finset Sentence) :
    PCInductor (paperDP 𝗜𝚺₁) :=
  AttemptA.pcInductor_paperDP ov X

/-- **T6 at the witness: no efficiently computable trader exploits the coherent overlaid market
over `paperDP 𝗜𝚺₁`** — a process every stage of which has a consistent world.
Source: [[bli-coherent-mm-mandate]] T6 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pcOverlay_paperDP_no_ec_trader_exploits (ov : Overlay) (X : ℕ → Finset Sentence)
    (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (pcHistory (paperDP 𝗜𝚺₁) ov X) (paperDP 𝗜𝚺₁) :=
  AttemptA.pcOverlay_paperDP_no_ec_trader_exploits ov X Tr hTr

/-- **T6 at the witness: exactly coherent on the priced set every day** over `paperDP 𝗜𝚺₁`
(`hcons` discharged: the coherence clause is unconditional here).
Source: [[bli-coherent-mm-mandate]] T6 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pcOverlay_paperDP_coherent_mentioned (ov : Overlay) (X : ℕ → Finset Sentence) (n : ℕ) :
    IsWorldMeasure (pcCoreWeights (paperDP 𝗜𝚺₁) ov X n) ((paperDP 𝗜𝚺₁).D n) ∧
      ∀ φ ∈ pcSet (paperDP 𝗜𝚺₁) ov X n,
        pcQuote (paperDP 𝗜𝚺₁) ov X n φ = marginal (pcCoreWeights (paperDP 𝗜𝚺₁) ov X n) φ :=
  AttemptA.pcOverlay_paperDP_coherent_mentioned ov X n

/-- **The coherence clause is not vacuous at the witness**: from some day on, the priced set is
nonempty (`bli-overlay`'s `firm_mentions_something_paperDP`).
Source: [[bli-coherent-mm-mandate]] T6 (witness); [[bli-overlay-mandate]] T2 (witness)
Kind: N+
Fidelity: n/a -/
theorem pcOverlay_paperDP_mentioned_nonempty (ov : Overlay) (X : ℕ → Finset Sentence) :
    ∃ i, ∀ n ≥ i, (pcSet (paperDP 𝗜𝚺₁) ov X n).Nonempty :=
  AttemptA.pcOverlay_paperDP_mentioned_nonempty ov X

/-- **"Not exploited" is not vacuous at the witness**: the plausible-assessment set of any
trader on the coherent overlaid market over `paperDP 𝗜𝚺₁` is nonempty (attempt B's check,
over the record recursion).
Source: [[bli-coherent-mm-mandate]] T6 (witness); [[bli-overlay-mandate]] T4 trap (ii)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pcOverlay_paperDP_plausibleAssessments_nonempty (ov : Overlay) (X : ℕ → Finset Sentence)
    (Tr : Trader) :
    (Tr.plausibleAssessments (pcHistory (paperDP 𝗜𝚺₁) ov X) (paperDP 𝗜𝚺₁)).Nonempty := by
  obtain ⟨v, hv⟩ := paperDP_hworld 𝗜𝚺₁ 0
  exact ⟨_, 0, v, hv, rfl⟩

/-- **The assembly lemma at the witness**: over `paperDP 𝗜𝚺₁` (computable by FAF's
`paperDP_computable`), the coherent overlaid market is a logical inductor **if** it is a
computable market — `ComputableMarket` assumed, open.
Source: [[bli-coherent-mm-mandate]] T6 (assembly, witness)
Kind: L
Fidelity: weaker: `ComputableMarket` is a hypothesis
Hyps: (b) `hmarket` — assumed (open); (a) the process's computability is FAF's -/
theorem pcOverlay_paperDP_isLogicalInductor_of_computableMarket (ov : Overlay)
    (X : ℕ → Finset Sentence) (hmarket : ComputableMarket (pcHistory (paperDP 𝗜𝚺₁) ov X)) :
    IsLogicalInductor (pcHistory (paperDP 𝗜𝚺₁) ov X) (paperDP 𝗜𝚺₁) :=
  pcOverlay_isLogicalInductor_of_computableMarket _ ov X (paperDP_computable 𝗜𝚺₁) hmarket

/-! ## The grid recursion's witness -/

/-- **T6, grid variant, at the witness**: no efficiently computable trader exploits the grid
coherent overlaid market over `paperDP 𝗜𝚺₁`.
Source: [[bli-coherent-mm-mandate]] T6 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pcOverlayGrid_paperDP_no_ec_trader_exploits (ov : Overlay) (Tr : Trader)
    (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (pcHistoryGrid (paperDP 𝗜𝚺₁) ov) (paperDP 𝗜𝚺₁) :=
  AttemptB.pcOverlay_paperDP_no_ec_trader_exploits ov Tr hTr

/-- **T6, grid variant, at the witness**: exactly coherent on the mentioned set every day,
unconditionally.
Source: [[bli-coherent-mm-mandate]] T6 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pcOverlayGrid_paperDP_coherent_mentioned (ov : Overlay) (n : ℕ) :
    IsWorldMeasure (pcCoreWeightsGrid (paperDP 𝗜𝚺₁) ov n) ((paperDP 𝗜𝚺₁).D n) ∧
      ∀ φ ∈ mentionedSet (pcFirmStratGrid (paperDP 𝗜𝚺₁) ov n),
        pcQuoteGrid (paperDP 𝗜𝚺₁) ov n φ = marginal (pcCoreWeightsGrid (paperDP 𝗜𝚺₁) ov n) φ :=
  pcOverlayGrid_coherent_mentioned _ ov n (paperDP_hcons n)

/-- **`PCInductor (paperDP 𝗜𝚺₁)` is inhabited by the grid recursion too.**
Source: [[bli-coherent-mm-mandate]] T6 (witness); §Deliverables (cross-check)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
noncomputable def pcInductorGrid_paperDP (ov : Overlay) : PCInductor (paperDP 𝗜𝚺₁) :=
  pcInductorGrid _ ov paperDP_hcons

end Cleanroom.Bli.BliCoherentMm
