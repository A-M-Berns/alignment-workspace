import Cleanroom.Bli.BliCoherentMm.AttemptA.Recursion
import Cleanroom.Bli.BliCoherentMm.AttemptA.Contrast
import LogicalInduction.Construction.Paper.TheoremDP

/-!
# `bli-coherent-mm` (attempt A) · Witness: the hypothesis package over `paperDP 𝗜𝚺₁` (T4(d), T6's witness)

**The only file importing `Construction.Paper.TheoremDP`.** Over FAF's single-market process
`paperDP 𝗜𝚺₁` (the process `paperLIA` runs on; `paperDP_hworld` gives every stage a consistent
world):

* **T4(d)**: the coherent maker's hypothesis package is inhabited over a real process — stage
  `D = (paperDP 𝗜𝚺₁).D n`, `hW` discharged from `paperDP_hworld` through the atom bound
  `B := ((paperDP 𝗜𝚺₁).D n).sup atomBound + 1` (`paperDP_hW`), and on `T_pair` the maker returns
  `quote φ + quote (∼φ) = 1` and is accepted in every stage-consistent world
  (`pair_paperDP_sum_one`, `pair_paperDP_accepts`). Grade N+: a real process, a real strategy,
  a simplex with at least one world and a non-degenerate output (`φ`/`∼φ` priced to one, FAF's
  maker forced to `≥ 2 − ε` on the same strategy, `Contrast.lean`).
* **T6's witness**: `pcInductor_paperDP` inhabits `PCInductor (paperDP 𝗜𝚺₁)` for every overlay
  and priced-set parameter; `pcOverlay_paperDP_no_ec_trader_exploits` and
  `pcOverlay_paperDP_coherent_mentioned` restate the headlines at the witness, and
  `pcOverlay_paperDP_mentioned_nonempty` (from `bli-overlay`'s `firm_mentions_something_paperDP`)
  shows the coherence clause is not vacuous: from some day on the firm's mentioned set is
  nonempty. Whether `pcHistory` differs from `liaHistory` on some day is **not** established
  (the mandate does not require it; T4 shows the makers differ on a strategy, not that the firm
  plays one) — the grade is N+ on the hypothesis package, not on "a different market".

Sources: [[bli-coherent-mm-mandate]] T4(d), T6 (witness); FAF `paperDP_hworld`.
-/

namespace Cleanroom.Bli.BliCoherentMm.AttemptA

open LogicalInduction LO.Propositional BoolPCWorld Cleanroom.Bli.BliFound Cleanroom.Bli.BliFinite
  Cleanroom.Bli.BliOverlay

/-! ## Every stage of the paper process has a consistent world -/

/-- **Every stage of the paper process has a consistent world** (FAF's `paperDP_hworld`, restated
beside the witness).
Source: [[bli-coherent-mm-mandate]] T4(d), T6 (witness); FAF `paperDP_hworld`
Kind: L
Fidelity: exact -/
theorem paperDP_hcons (n : ℕ) : ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) :=
  paperDP_hworld 𝗜𝚺₁ n

/-- An atom bound for the day-`n` stage of the paper process.
Source: [[bli-coherent-mm-mandate]] T4(d) ("`hB` computed")
Kind: D
Fidelity: exact -/
noncomputable def paperDP_atoms (n : ℕ) : ℕ := ((paperDP 𝗜𝚺₁).D n).sup atomBound + 1

/-- The stage is within its atom bound.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma paperDP_atoms_bound (n : ℕ) : ∀ φ ∈ (paperDP 𝗜𝚺₁).D n, atomBound φ ≤ paperDP_atoms n :=
  fun _ hφ => Nat.le_succ_of_le (Finset.le_sup hφ)

/-- **`hW` over the paper process**: the day-`n` stage has a consistent finite world over
`paperDP_atoms n` atoms (from `paperDP_hworld` by restriction).
Source: [[bli-coherent-mm-mandate]] T4(d) ("`hW` from `paperDP_hworld`")
Kind: L
Fidelity: exact -/
theorem paperDP_hW (n : ℕ) :
    ∃ u : FiniteWorld (paperDP_atoms n), (worldOf u).ConsistentWith ((paperDP 𝗜𝚺₁).D n) :=
  exists_consistent_of_pcWorld (paperDP_atoms_bound n) (paperDP_hcons n)

/-! ## T4(d): the coherent maker on `T_pair` over the paper process -/

/-- **T4(d). The coherent maker on `T_pair` over `paperDP 𝗜𝚺₁` quotes `φ` and `∼φ` to one.** The
full hypothesis package — a real stage, `hW` from `paperDP_hworld`, `hB` computed — is inhabited
and the output is non-degenerate.
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: N+
Fidelity: n/a
Hyps: (a) `hε` only -/
theorem pair_paperDP_sum_one (a n : ℕ) (past : List RationalBeliefState) {ε : ℚ} (hε : 0 < ε) :
    (coherentMarketMaker (pairStrategy a n) past ((paperDP 𝗜𝚺₁).D n) (paperDP_atoms n)
      (mentionedSet (pairStrategy a n)) subset_rfl (paperDP_hW n) hε).quote (Formula.atom a) +
    (coherentMarketMaker (pairStrategy a n) past ((paperDP 𝗜𝚺₁).D n) (paperDP_atoms n)
      (mentionedSet (pairStrategy a n)) subset_rfl (paperDP_hW n) hε).quote (∼(Formula.atom a)) = 1 := by
  rw [coherentMarketMaker_quote_eq_pi _ _ _ _ _ _ _ _
      (support_subset_mentionedSet _ (atom_mem_support_pair a n)),
    coherentMarketMaker_quote_eq_pi _ _ _ _ _ _ _ _
      (support_subset_mentionedSet _ (neg_atom_mem_support_pair a n))]
  exact marginal_neg_add (coherentWeights_isWorldMeasure _ _ _ _ _ _ _ _) _

/-- **T4(d). The coherent maker on `T_pair` over `paperDP 𝗜𝚺₁` is accepted in every world
consistent with the day's stage** (and FAF's maker is not coherent on the same strategy at any
`ε < 1`, `Contrast.lean`).
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pair_paperDP_accepts (a n : ℕ) (past : List RationalBeliefState) {ε : ℚ} (hε : 0 < ε) :
    ∀ u ∈ WD ((paperDP 𝗜𝚺₁).D n) (paperDP_atoms n),
      (pairStrategy a n).marketValueRat
        (candidateRationalHistory past n (coherentMarketMaker (pairStrategy a n) past
          ((paperDP 𝗜𝚺₁).D n) (paperDP_atoms n) (mentionedSet (pairStrategy a n)) subset_rfl
          (paperDP_hW n) hε)) u.payoutRat ≤ ε :=
  coherentMarketMaker_accepts _ _ _ _ _ _ _ _

/-- The simplex of the witness is nonempty (`WD` over the paper stage has a world).
Source: [[bli-coherent-mm-mandate]] T4(d)
Kind: N+
Fidelity: n/a -/
theorem paperDP_WD_nonempty (n : ℕ) : (WD ((paperDP 𝗜𝚺₁).D n) (paperDP_atoms n)).Nonempty := by
  obtain ⟨u, hu⟩ := paperDP_hW n
  exact ⟨u, mem_WD.mpr hu⟩

/-! ## T6's witness: `PCInductor (paperDP 𝗜𝚺₁)` -/

/-- **T6 at the witness: `PCInductor (paperDP 𝗜𝚺₁)` is inhabited** by the coherent overlaid
recursion, for every overlay and priced-set parameter. Ledger: "inhabited; `ComputableMarket`
open"; not a logical inductor.
Source: [[bli-coherent-mm-mandate]] T6 (witness); [[bli-program]] §4 row M3
Kind: N+
Fidelity: n/a
Hyps: (a) -/
noncomputable def pcInductor_paperDP (ov : Overlay) (X : ℕ → Finset Sentence) :
    PCInductor (paperDP 𝗜𝚺₁) :=
  pcInductor (paperDP 𝗜𝚺₁) ov X paperDP_hcons

/-- **T6 at the witness: no efficiently computable trader exploits the coherent overlaid market
over `paperDP 𝗜𝚺₁`** — a process every stage of which has a consistent world, so "not exploited"
is not empty.
Source: [[bli-coherent-mm-mandate]] T6 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pcOverlay_paperDP_no_ec_trader_exploits (ov : Overlay) (X : ℕ → Finset Sentence)
    (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (pcHistory (paperDP 𝗜𝚺₁) ov X) (paperDP 𝗜𝚺₁) :=
  pcOverlay_no_ec_trader_exploits (paperDP 𝗜𝚺₁) ov X Tr hTr

/-- **T6 at the witness: exactly coherent on the priced set every day** over `paperDP 𝗜𝚺₁`
(`hcons` discharged, so the coherence clause is unconditional here).
Source: [[bli-coherent-mm-mandate]] T6 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem pcOverlay_paperDP_coherent_mentioned (ov : Overlay) (X : ℕ → Finset Sentence) (n : ℕ) :
    IsWorldMeasure (pcCoreWeights (paperDP 𝗜𝚺₁) ov X n) ((paperDP 𝗜𝚺₁).D n) ∧
      ∀ φ ∈ pcSet (paperDP 𝗜𝚺₁) ov X n,
        pcQuote (paperDP 𝗜𝚺₁) ov X n φ = marginal (pcCoreWeights (paperDP 𝗜𝚺₁) ov X n) φ :=
  pcOverlay_coherent_mentioned (paperDP 𝗜𝚺₁) ov X n (paperDP_hcons n)

/-- **The coherence clause is not vacuous at the witness**: from some day on, the firm's
mentioned set (hence the priced set) is nonempty (`bli-overlay`'s
`firm_mentions_something_paperDP`).
Source: [[bli-coherent-mm-mandate]] T6 (witness); [[bli-overlay-mandate]] T2 (witness)
Kind: N+
Fidelity: n/a -/
theorem pcOverlay_paperDP_mentioned_nonempty (ov : Overlay) (X : ℕ → Finset Sentence) :
    ∃ i, ∀ n ≥ i, (pcSet (paperDP 𝗜𝚺₁) ov X n).Nonempty := by
  obtain ⟨i, hi⟩ := BliOverlay.AttemptA.firm_mentions_something_paperDP
  refine ⟨i, fun n hn => ?_⟩
  obtain ⟨φ, hφ⟩ := hi n hn (pcQuote (paperDP 𝗜𝚺₁) ov X)
  exact ⟨φ, Finset.mem_union_left _ hφ⟩

end Cleanroom.Bli.BliCoherentMm.AttemptA
