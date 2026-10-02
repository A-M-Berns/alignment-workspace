import Cleanroom.Bli.BliOverlay.AttemptA.Recursion
import Cleanroom.Bli.BliOverlay.AttemptA.FirmSupport
import LogicalInduction.Construction.Paper.TheoremDP

/-!
# `bli-overlay` (attempt A) · Witness: a nontrivial overlay over the paper process (T5)

**The only file importing `Construction.Paper.TheoremDP`.** Over FAF's single-market process
`paperDP 𝗜𝚺₁` (the process `paperLIA` runs on; `paperDP_hworld` gives every stage a consistent
world, so "not exploited" is not empty — trap (ii)) and the constant overlay `Overlay.half`:

* **T5, `overlay_half_ne_lia`** (N+): on day `N₀` (the firm-support day of T2) the overlaid
  market prices the large sentence `⌜a_{4^{sizeBound N₀}}⌝` at `1/2` while FAF's LIA prices it
  at `0` — the overlay changes a price on a real day of a real process. The route: the sentence
  is not small on day `N₀` (`largeOn_witness`), so by T2 neither firm mentions it; the overlaid
  quote is then the overlay (`overlayQuote_of_not_mem`), and the LIA quote is `0` because the
  LIA state's support is inside the firm's support (`MarketMakerAccepts.1`), which is inside the
  mentioned set. The day is T2's existential `N₀` (a non-constructive day is still a day).
* The headline at the witness: `overlay_half_paperDP_no_ec_trader_exploits`, with
  `paperDP_hworld` restated beside it (`overlay_half_paperDP_hworld`).
* T2's witness at the paper process: `firm_mentions_something_paperDP`.

Sources: [[bli-overlay-mandate]] T5, T2 (witness), trap (ii)/(iii); [[bli-program]] §7 items 4, 11.
-/

namespace Cleanroom.Bli.BliOverlay.AttemptA

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-! ## The LIA quotes `0` off the firm's mentioned set -/

/-- A sentence the LIA's day-`n` firm does not mention quotes `0` in the LIA: the LIA state's
support is inside the firm's support (`MarketMaker_accepts`, first conjunct), which is inside
the mentioned set.
Source: [[bli-overlay-mandate]] T5
Kind: L
Fidelity: exact -/
lemma liaQuote_eq_zero_of_not_mentioned (DP : DeductiveProcess) (n : ℕ) {φ : Sentence}
    (h : ¬ MentionedBy ((TradingFirm DP).action n (List.ofFn fun i : Fin n => liaStates DP i)) φ) :
    liaQuote DP n φ = 0 := by
  unfold liaQuote
  apply RationalBeliefState.quote_eq_zero_of_not_mem
  intro hsupp
  apply h
  have hacc := MarketMaker_accepts
    ((TradingFirm DP).action n (List.ofFn fun i : Fin n => liaStates DP i))
    (List.ofFn fun i : Fin n => liaStates DP i) (marketMakerError n) (marketMakerError_pos n)
  rw [liaStates_eq] at hsupp
  exact mem_mentionedSet_iff.mp (support_subset_mentionedSet _ (hacc.1 hsupp))

/-! ## T5: the witness -/

/-- **T5 (N+). The half overlay changes a price of the paper process's LIA.** On T2's day `N₀`,
the large sentence `⌜a_{4^{sizeBound N₀}}⌝` is priced `1/2` by the overlaid market over
`paperDP 𝗜𝚺₁` and `0` by FAF's LIA over the same process.
Source: [[bli-overlay-mandate]] T5; [[bli-program]] §7 item 11
Kind: N+
Fidelity: n/a
Hyps: (a) — the instances `[𝗜𝚺₁.Δ₁] [𝗣𝗔⁻ ⪯ 𝗜𝚺₁] [Entailment.Consistent 𝗜𝚺₁]` are FAF's own,
as `paperLIA` uses them -/
theorem overlay_half_ne_lia :
    ∃ n φ, overlayQuote (paperDP 𝗜𝚺₁) Overlay.half n φ ≠ liaQuote (paperDP 𝗜𝚺₁) n φ := by
  obtain ⟨N₀, hN₀⟩ := firm_mentioned_small
  refine ⟨N₀, Formula.atom (4 ^ sizeBound N₀), ?_⟩
  have hlarge := largeOn_witness N₀
  have hnot : Formula.atom (4 ^ sizeBound N₀) ∉
      mentionedSet (firmStrat (paperDP 𝗜𝚺₁) Overlay.half N₀) := by
    intro hmem
    exact hlarge (hN₀ N₀ le_rfl _ _ _ (mem_mentionedSet_iff.mp hmem))
  rw [overlayQuote_of_not_mem _ _ hnot]
  have hlia : liaQuote (paperDP 𝗜𝚺₁) N₀ (Formula.atom (4 ^ sizeBound N₀)) = 0 := by
    apply liaQuote_eq_zero_of_not_mentioned
    intro hmem
    exact hlarge (hN₀ N₀ le_rfl _ _ _ hmem)
  rw [hlia]
  show (1 / 2 : ℚ) ≠ 0
  norm_num

/-- The overlaid market of the witness is not the LIA market (the history form of T5).
Source: [[bli-overlay-mandate]] T5
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem overlayHistory_half_ne_liaHistory :
    overlayHistory (paperDP 𝗜𝚺₁) Overlay.half ≠ liaHistory (paperDP 𝗜𝚺₁) := by
  intro heq
  obtain ⟨n, φ, hne⟩ := overlay_half_ne_lia
  apply hne
  have := congrFun (congrFun heq n) φ
  rw [overlayHistory_eq_quote_cast, liaHistory_eq_quote_cast] at this
  exact_mod_cast this

/-! ## The headline at the witness -/

/-- **Every stage of the paper process has a consistent world** (FAF's `paperDP_hworld`,
restated beside the witness): "not exploited" over `paperDP 𝗜𝚺₁` is not empty (trap (ii)).
Source: [[bli-overlay-mandate]] T4 trap (ii), T5
Kind: L
Fidelity: exact -/
theorem overlay_half_paperDP_hworld (n : ℕ) :
    ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) :=
  paperDP_hworld 𝗜𝚺₁ n

/-- **T4 at the witness**: no efficiently computable trader exploits the half-overlaid market
over `paperDP 𝗜𝚺₁` — a market that differs from FAF's LIA (`overlayHistory_half_ne_liaHistory`)
over a process every stage of which has a consistent world (`overlay_half_paperDP_hworld`).
Source: [[bli-overlay-mandate]] T4, T5
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem overlay_half_paperDP_no_ec_trader_exploits (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (overlayHistory (paperDP 𝗜𝚺₁) Overlay.half) (paperDP 𝗜𝚺₁) :=
  overlay_no_ec_trader_exploits (paperDP 𝗜𝚺₁) Overlay.half Tr hTr

/-! ## T2's witness at the paper process -/

/-- **N+ for T2 at `paperDP 𝗜𝚺₁`**: from `buyAtomDaily`'s enumeration index on, the firm's day-`n`
mentioned set contains `⌜aₙ⌝`, for every table `Q`.
Source: [[bli-overlay-mandate]] T2 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem firm_mentions_something_paperDP :
    ∃ i, ∀ n ≥ i, ∀ Q : ℕ → Sentence → ℚ,
      (mentionedSet (TradingFirmAt (paperDP 𝗜𝚺₁) Q n)).Nonempty := by
  obtain ⟨i, hi⟩ := firm_mentions_something
  exact ⟨i, fun n hn Q => ⟨_, hi n hn (paperDP 𝗜𝚺₁) Q⟩⟩

end Cleanroom.Bli.BliOverlay.AttemptA
