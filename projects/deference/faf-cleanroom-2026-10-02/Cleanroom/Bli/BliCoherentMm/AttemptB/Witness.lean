import Cleanroom.Bli.BliCoherentMm.AttemptB.Recursion
import Cleanroom.Bli.BliCoherentMm.AttemptB.Contrast
import Cleanroom.Bli.BliOverlay.Witness
import LogicalInduction.Construction.Paper.TheoremDP

/-!
# `bli-coherent-mm` (attempt B) · Witness: the hypothesis package over `paperDP 𝗜𝚺₁`
(T4(d), T6's witness)

Over FAF's single-market process `paperDP 𝗜𝚺₁` (the process `paperLIA` runs on):

* `hW` is discharged at every stage from FAF's `paperDP_hworld` (restricted to the day's atoms,
  `paperDP_stage_hW`), and `hB` is computed as `atomBoundOf (mentionedSet T ∪ D n)`
  (`le_atomBoundOf`) — so T1, T2 and T3 hold with their **full** hypothesis package for every
  day-`n` strategy and past (`coherent_fixed_point_paperDP`, `interiorMaker_paperDP_accepts`,
  `interiorMaker_paperDP_fullSupport`);
* for the recursion, **every stage is inhabited** (`pcOverlay_paperDP_stageInhabited`), so the
  coherence headline is unconditional in the day (`pcOverlay_paperDP_coherent_mentioned`), no
  e.c. trader exploits the coherent overlaid market
  (`pcOverlay_paperDP_no_ec_trader_exploits`), the plausible-assessment set is nonempty (the
  non-exploitation is not vacuous, trap (ii)), and from `bli-overlay`'s enumeration index on
  the firm mentions something every day (`pcOverlay_paperDP_firm_mentions_something`, so the
  coherence statement is about a nonempty set).

**Grading.** N+ for the hypothesis package (every hypothesis of T1–T3 and T6 discharged over a
real process whose every stage has a consistent world). Whether `pcHistory` differs from
`liaHistory` on some day is **not** claimed: T4 shows the makers differ on `T_pair`, not that the
firm ever plays that strategy. The computability of the market is not addressed.

Sources: [[bli-coherent-mm-mandate]] T4(d), T6 (witness); [[bli-overlay-mandate]] T5.
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptB

open LogicalInduction LogicalInduction.BoolPCWorld LO.Propositional Cleanroom.Bli.BliFound
  Cleanroom.Bli.BliOverlay Cleanroom.Bli.BliFinite Finset

noncomputable section

/-! ## The computed atom bound and the discharged `hW` -/

/-- The atom bound of a finite sentence set, computed as the `sup`.
Source: [[bli-coherent-mm-mandate]] T4(d) ("`hB` computed")
Kind: D
Fidelity: exact -/
def atomBoundOf (A : Finset Sentence) : ℕ := A.sup atomBound

/-- The computed atom bound covers its set.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma le_atomBoundOf {A : Finset Sentence} {φ : Sentence} (hφ : φ ∈ A) :
    atomBound φ ≤ atomBoundOf A :=
  Finset.le_sup hφ

/-- **`hW` over the paper process**: every stage of `paperDP 𝗜𝚺₁` has a consistent finite world
over any atom bound covering the stage (FAF's `paperDP_hworld`, restricted).
Source: [[bli-coherent-mm-mandate]] T4(d) ("`hW` from `paperDP_hworld`")
Kind: L
Fidelity: exact
Hyps: (a) — the instances `[𝗜𝚺₁.Δ₁] [𝗣𝗔⁻ ⪯ 𝗜𝚺₁] [Entailment.Consistent 𝗜𝚺₁]` are FAF's own,
as `paperLIA` uses them -/
theorem paperDP_stage_hW (n : ℕ) {B : ℕ} (hB : ∀ φ ∈ (paperDP 𝗜𝚺₁).D n, atomBound φ ≤ B) :
    ∃ u : FiniteWorld B, (worldOf u).ConsistentWith ((paperDP 𝗜𝚺₁).D n) := by
  obtain ⟨v, hv⟩ := paperDP_hworld 𝗜𝚺₁ n
  exact ⟨_, mem_worldsOf.mp (restrict_mem_worldsOf hB hv)⟩

/-- The computed atom bound for a strategy at a stage of the paper process covers the
mentioned set and the stage (`hB`, discharged).
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: L
Fidelity: n/a -/
lemma paperDP_hB {n : ℕ} (T : Strategy n) :
    ∀ φ ∈ mentionedSet T ∪ (paperDP 𝗜𝚺₁).D n,
      atomBound φ ≤ atomBoundOf (mentionedSet T ∪ (paperDP 𝗜𝚺₁).D n) :=
  fun _ hφ => le_atomBoundOf hφ

/-! ## T4(d): T1–T3 with their full hypothesis package over the paper process -/

/-- **T4(d), T1 over `paperDP 𝗜𝚺₁`**: for every day-`n` strategy and past, the coherent fixed
point exists with `hB` computed and `hW` from FAF — the full hypothesis package of T1 inhabited
over a real process.
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: N+
Fidelity: n/a
Hyps: (a) — none left: `hB` is `paperDP_hB`, `hW` is `paperDP_stage_hW` -/
theorem coherent_fixed_point_paperDP {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) :
    ∃ p : FiniteWorld (atomBoundOf (mentionedSet T ∪ (paperDP 𝗜𝚺₁).D n)) → ℝ,
      IsRealWorldMeasure ((paperDP 𝗜𝚺₁).D n) (atomBoundOf (mentionedSet T ∪ (paperDP 𝗜𝚺₁).D n)) p ∧
      (∀ u ∈ worldsOf ((paperDP 𝗜𝚺₁).D n) (atomBoundOf (mentionedSet T ∪ (paperDP 𝗜𝚺₁).D n)),
        T.value (Function.update (beliefHistory past) n
          (fun φ => ∑ u, p u * (worldOf u).payout φ)) (worldOf u).payout ≤ 0) ∧
      ∀ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) →
        T.value (Function.update (beliefHistory past) n
          (fun φ => ∑ u, p u * (worldOf u).payout φ)) v.payout ≤ 0 :=
  coherent_fixed_point T past _ _ (paperDP_hB T)
    (paperDP_stage_hW n fun _ hφ => le_atomBoundOf (Finset.mem_union_right _ hφ))

/-- **T4(d), the interior maker over `paperDP 𝗜𝚺₁`** on the day's mentioned set, at FAF's
day-`n` error: the full package of T3 inhabited.
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: D
Fidelity: exact -/
def interiorMakerPaperDP {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) :
    RationalBeliefState :=
  interiorCoherentMarketMaker T past ((paperDP 𝗜𝚺₁).D n) _ (paperDP_hB T)
    (paperDP_stage_hW n fun _ hφ => le_atomBoundOf (Finset.mem_union_right _ hφ))
    (mentionedSet T) (Finset.Subset.refl _) (marketMakerError n) (marketMakerError_pos n)

/-- The paper-process interior maker is coherently accepted at `marketMakerError n`.
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: N+
Fidelity: n/a
Hyps: (a) none left -/
theorem interiorMaker_paperDP_accepts {n : ℕ} (T : Strategy n) (past : List RationalBeliefState) :
    CoherentAccepts T past ((paperDP 𝗜𝚺₁).D n) _ (mentionedSet T) (marketMakerError n)
      (interiorWeights T past ((paperDP 𝗜𝚺₁).D n) _ (paperDP_hB T)
        (paperDP_stage_hW n fun _ hφ => le_atomBoundOf (Finset.mem_union_right _ hφ))
        (mentionedSet T) (Finset.Subset.refl _) (marketMakerError n) (marketMakerError_pos n)) :=
  interior_accepts _ _ _ _ _ _ _ _ _ _

/-- The paper-process interior maker has full support on the stage's consistent worlds.
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: N+
Fidelity: n/a
Hyps: (a) none left -/
theorem interiorMaker_paperDP_fullSupport {n : ℕ} (T : Strategy n)
    (past : List RationalBeliefState) :
    ∀ u ∈ worldsOf ((paperDP 𝗜𝚺₁).D n) (atomBoundOf (mentionedSet T ∪ (paperDP 𝗜𝚺₁).D n)),
      0 < interiorWeights T past ((paperDP 𝗜𝚺₁).D n) _ (paperDP_hB T)
        (paperDP_stage_hW n fun _ hφ => le_atomBoundOf (Finset.mem_union_right _ hφ))
        (mentionedSet T) (Finset.Subset.refl _) (marketMakerError n) (marketMakerError_pos n) u :=
  interior_fullSupport _ _ _ _ _ _ _ _ _ _

/-! ## T6's witness: the coherent overlaid market over the paper process -/

/-- **Every stage of the recursion over `paperDP 𝗜𝚺₁` is inhabited**: the fallback branch of
`pcCore` is never taken.
Source: [[bli-coherent-mm-mandate]] T6 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pcOverlay_paperDP_stageInhabited (ov : Overlay) (n : ℕ) :
    StageInhabited (paperDP 𝗜𝚺₁) ov n :=
  (stageInhabited_iff _ ov n).mpr (paperDP_hworld 𝗜𝚺₁ n)

/-- **T6 at the witness: exact coherence on every day's mentioned set, unconditionally**, over
`paperDP 𝗜𝚺₁` and every overlay.
Source: [[bli-coherent-mm-mandate]] T6 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pcOverlay_paperDP_coherent_mentioned (ov : Overlay) (n : ℕ) :
    IsWorldMarginal (piTable (pcCoreWeights (paperDP 𝗜𝚺₁) ov n))
        (mentionedSet (pcFirmStrat (paperDP 𝗜𝚺₁) ov n)) ((paperDP 𝗜𝚺₁).D n)
        (pcB (paperDP 𝗜𝚺₁) ov n) ∧
      ∀ φ ∈ mentionedSet (pcFirmStrat (paperDP 𝗜𝚺₁) ov n),
        pcQuote (paperDP 𝗜𝚺₁) ov n φ = piTable (pcCoreWeights (paperDP 𝗜𝚺₁) ov n) φ :=
  pcOverlay_coherent_mentioned _ ov n (paperDP_hworld 𝗜𝚺₁ n)

/-- **T6 at the witness: no efficiently computable trader exploits the coherent overlaid market
over `paperDP 𝗜𝚺₁`** — a process every stage of which has a consistent world.
Source: [[bli-coherent-mm-mandate]] T6 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pcOverlay_paperDP_no_ec_trader_exploits (ov : Overlay) (Tr : Trader)
    (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (pcHistory (paperDP 𝗜𝚺₁) ov) (paperDP 𝗜𝚺₁) :=
  pcOverlay_no_ec_trader_exploits _ ov Tr hTr

/-- **The assembly lemma at the witness**: over `paperDP 𝗜𝚺₁` (whose computability is FAF's
`paperDP_computable`), the coherent overlaid market is a logical inductor **if** it is a
computable market — `ComputableMarket` assumed, open.
Source: [[bli-coherent-mm-mandate]] T6 (assembly, witness)
Kind: L
Fidelity: weaker: `ComputableMarket (pcHistory (paperDP 𝗜𝚺₁) ov)` is a hypothesis
Hyps: (b) `hmarket` — assumed (OPEN); (a) the process's computability is FAF's -/
theorem pcOverlay_paperDP_isLogicalInductor_of_computableMarket (ov : Overlay)
    (hmarket : ComputableMarket (pcHistory (paperDP 𝗜𝚺₁) ov)) :
    IsLogicalInductor (pcHistory (paperDP 𝗜𝚺₁) ov) (paperDP 𝗜𝚺₁) :=
  pcOverlay_isLogicalInductor_of_computableMarket _ ov (paperDP_computable 𝗜𝚺₁) hmarket

/-- The plausible-assessment set of any trader on the coherent overlaid market over
`paperDP 𝗜𝚺₁` is nonempty: "not exploited" is not vacuous (trap (ii)).
Source: [[bli-coherent-mm-mandate]] T6 (witness); [[bli-overlay-mandate]] T4 trap (ii)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pcOverlay_paperDP_plausibleAssessments_nonempty (ov : Overlay) (Tr : Trader) :
    (Tr.plausibleAssessments (pcHistory (paperDP 𝗜𝚺₁) ov) (paperDP 𝗜𝚺₁)).Nonempty := by
  obtain ⟨v, hv⟩ := paperDP_hworld 𝗜𝚺₁ 0
  exact ⟨_, 0, v, hv, rfl⟩

/-- **From `bli-overlay`'s enumeration index on, the coherent firm mentions something every
day** over `paperDP 𝗜𝚺₁`: the coherence statement `pcOverlay_paperDP_coherent_mentioned` is
about a nonempty set on every late day.
Source: [[bli-coherent-mm-mandate]] T6 (witness); [[bli-overlay-mandate]] T2 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pcOverlay_paperDP_firm_mentions_something (ov : Overlay) :
    ∃ i, ∀ n ≥ i, (mentionedSet (pcFirmStrat (paperDP 𝗜𝚺₁) ov n)).Nonempty := by
  obtain ⟨i, hi⟩ := firm_mentions_something_paperDP
  exact ⟨i, fun n hn => hi n hn (pcQuote (paperDP 𝗜𝚺₁) ov)⟩

/-- **The non-dogmatism of the coherent overlaid market at the witness**: on every day, every
mentioned sentence some stage-consistent finite world holds and some fails is priced strictly
inside `(0, 1)`.
Source: [[bli-coherent-mm-mandate]] T6 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pcOverlay_paperDP_nonDogmatic (ov : Overlay) (n : ℕ) {φ : Sentence}
    (hφ : φ ∈ mentionedSet (pcFirmStrat (paperDP 𝗜𝚺₁) ov n))
    (h1 : ∃ u ∈ worldsOf ((paperDP 𝗜𝚺₁).D n) (pcB (paperDP 𝗜𝚺₁) ov n), (worldOf u).Holds φ)
    (h0 : ∃ u ∈ worldsOf ((paperDP 𝗜𝚺₁).D n) (pcB (paperDP 𝗜𝚺₁) ov n), ¬ (worldOf u).Holds φ) :
    0 < pcQuote (paperDP 𝗜𝚺₁) ov n φ ∧ pcQuote (paperDP 𝗜𝚺₁) ov n φ < 1 :=
  pcOverlay_nonDogmatic _ ov n (paperDP_hworld 𝗜𝚺₁ n) hφ h1 h0

end

end Cleanroom.Bli.BliCoherentMm.AttemptB
