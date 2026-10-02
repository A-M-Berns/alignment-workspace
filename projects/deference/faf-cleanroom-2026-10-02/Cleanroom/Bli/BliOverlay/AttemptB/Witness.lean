import Cleanroom.Bli.BliOverlay.AttemptB.Recursion
import Cleanroom.Bli.BliOverlay.AttemptB.FirmSupport
import LogicalInduction.Construction.Paper.TheoremDP

/-!
# `bli-overlay` (attempt B) · Witness: a nontrivial overlay over the paper process (T5)

The constant-half overlay over `paperDP 𝗜𝚺₁` changes a price: on every day `n ≥ N₀` (T2's
day) the large atom `⌜a_{4^{sizeBound n}}⌝` — not small on day `n` (`largeOn_witness`), hence not
mentioned by the firm on day `n` (T2), whatever table the firm reads — is quoted `1/2` by the
overlaid recursion and `0` by FAF's LIA (it is off the LIA state's support, which is inside the
firm's support). The plausible-assessment sets over `paperDP 𝗜𝚺₁` are nonempty
(`paperDP_hworld`), so "not exploited" is not empty over this process (T4 trap (ii)).
-/

namespace Cleanroom.Bli.BliOverlay.AttemptB

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

/-- The day-`n` large atom `⌜a_{4^{sizeBound n}}⌝` (bli-found's `largeOn_witness` sentence).
Source: [[bli-overlay-mandate]] T5
Kind: D
Fidelity: exact -/
def largeAtom (n : ℕ) : Sentence := Formula.atom (4 ^ sizeBound n)

/-- The large atom is not mentioned by the firm on day `n ≥ N₀`, for any process and table.
Source: [[bli-overlay-mandate]] T5
Kind: L
Fidelity: exact -/
lemma largeAtom_not_mentioned :
    ∃ N₀, ∀ n ≥ N₀, ∀ (DP : DeductiveProcess) (Q : ℕ → Sentence → ℚ),
      ¬ MentionedBy (TradingFirmAt DP Q n) (largeAtom n) := by
  obtain ⟨N₀, hN⟩ := firm_mentioned_small
  exact ⟨N₀, fun n hn DP Q h => largeOn_witness n (hN n hn DP Q _ h)⟩

/-- **The half overlay quotes the large atom `1/2`** from `N₀` on, for every process.
Source: [[bli-overlay-mandate]] T5
Kind: N+
Fidelity: n/a -/
theorem overlayQuote_half_largeAtom (DP : DeductiveProcess) :
    ∃ N₀, ∀ n ≥ N₀, overlayQuote DP Overlay.half n (largeAtom n) = 1 / 2 := by
  obtain ⟨N₀, hN⟩ := largeAtom_not_mentioned
  refine ⟨N₀, fun n hn => ?_⟩
  rw [overlayQuote_of_not_mem]
  · rfl
  · intro hmem
    exact hN n hn DP _ ((mem_mentionedSet_iff _ _).mp hmem)

/-- **FAF's LIA quotes the large atom `0`** from `N₀` on, for every process: it is not in the
firm's support on day `n`, hence not in the LIA state's support (`MarketMaker_accepts`).
Source: [[bli-overlay-mandate]] T5
Kind: L
Fidelity: exact -/
theorem liaQuote_largeAtom_eq_zero (DP : DeductiveProcess) :
    ∃ N₀, ∀ n ≥ N₀, liaQuote DP n (largeAtom n) = 0 := by
  obtain ⟨N₀, hN⟩ := largeAtom_not_mentioned
  refine ⟨N₀, fun n hn => ?_⟩
  unfold liaQuote
  rw [liaStates_eq_MM]
  apply RationalBeliefState.quote_eq_zero_of_not_mem
  intro hsupp
  have hacc := MarketMaker_accepts
    (TradingFirmAt DP (rationalHistory (List.ofFn fun i : Fin n => liaStates DP i)) n)
    (List.ofFn fun i : Fin n => liaStates DP i) (marketMakerError n) (marketMakerError_pos n)
  exact hN n hn DP _ ((mem_mentionedSet_iff _ _).mp
    (support_subset_mentionedSet _ (hacc.1 hsupp)))

/-- **T5, strong form.** For every process, from some day on the half overlay and FAF's LIA differ
at the day's large atom (`1/2` against `0`).
Source: [[bli-overlay-mandate]] T5
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem overlay_half_differs_from (DP : DeductiveProcess) :
    ∃ N₀, ∀ n ≥ N₀, overlayQuote DP Overlay.half n (largeAtom n) = 1 / 2 ∧
      liaQuote DP n (largeAtom n) = 0 := by
  obtain ⟨N₁, h₁⟩ := overlayQuote_half_largeAtom DP
  obtain ⟨N₂, h₂⟩ := liaQuote_largeAtom_eq_zero DP
  exact ⟨max N₁ N₂, fun n hn =>
    ⟨h₁ n (le_trans (le_max_left _ _) hn), h₂ n (le_trans (le_max_right _ _) hn)⟩⟩

/-- **T5 (N+). The witness over the paper process.** Over `paperDP 𝗜𝚺₁` (FAF's own single market,
with `paperDP_hworld` supplying a consistent world at every stage) the constant-half overlay
produces a table different from FAF's LIA: on some day `n` and some sentence `φ` (the day's large
atom) the overlaid quote is `1/2` and the LIA quote is `0`. The day is T2's existential `N₀`
(`(C+16)^2`, `676` at `C = 10`); the overlay changes a price.
Source: [[bli-overlay-mandate]] T5 (`overlay_half_ne_lia`)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem overlay_half_ne_lia :
    ∃ n φ, overlayQuote (paperDP 𝗜𝚺₁) Overlay.half n φ ≠ liaQuote (paperDP 𝗜𝚺₁) n φ := by
  obtain ⟨N₀, hN⟩ := overlay_half_differs_from (paperDP 𝗜𝚺₁)
  refine ⟨N₀, largeAtom N₀, ?_⟩
  rw [(hN N₀ le_rfl).1, (hN N₀ le_rfl).2]
  norm_num

/-- The plausible-assessment set of any trader on the overlaid market over `paperDP 𝗜𝚺₁` is
nonempty (a consistent world exists at every stage, `paperDP_hworld`): "not exploited" is not
vacuous through the process (T4 trap (ii)).
Source: [[bli-overlay-mandate]] T4 traps (ii); T5
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem overlay_plausibleAssessments_nonempty (ov : Overlay) (Tr : Trader) :
    (Tr.plausibleAssessments (overlayHistory (paperDP 𝗜𝚺₁) ov) (paperDP 𝗜𝚺₁)).Nonempty := by
  obtain ⟨v, hv⟩ := paperDP_hworld 𝗜𝚺₁ 0
  exact ⟨_, 0, v, hv, rfl⟩

/-- **T4 at the witness**: no e.c. trader exploits the half-overlaid recursion over `paperDP 𝗜𝚺₁`,
a market that differs from FAF's LIA and over a process with consistent worlds at every stage.
Source: [[bli-overlay-mandate]] T4, T5
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem overlay_half_paperDP_no_ec_trader_exploits (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (overlayHistory (paperDP 𝗜𝚺₁) Overlay.half) (paperDP 𝗜𝚺₁) :=
  overlay_no_ec_trader_exploits (paperDP 𝗜𝚺₁) Overlay.half Tr hTr

end Cleanroom.Bli.BliOverlay.AttemptB
