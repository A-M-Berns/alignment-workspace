import Cleanroom.Bli.BliOverlay.CrossCheck
import Cleanroom.Bli.BliOverlay.AttemptA.Witness
import Cleanroom.Bli.BliOverlay.AttemptB.Witness

/-!
# `bli-overlay` · Witness (reconciled): T5, a nontrivial overlay over the paper process

Over FAF's single-market process `paperDP 𝗜𝚺₁` (`paperDP_hworld` gives every stage a consistent
world) and the constant overlay `Overlay.half`, both attempts prove that the overlaid market
differs from FAF's LIA on a real day (T2's `N₀`) at the day's large atom
`⌜a_{4^{sizeBound n}}⌝`: `1/2` against `0`. The record takes attempt A's `overlay_half_ne_lia`
(stated over the definitions of record) and transports attempt B's strong form — for **every**
process, from `N₀` on, at every day's large atom — through the cross-check.

Sources: [[bli-overlay-mandate]] T5, T4 traps (ii)/(iii); [[bli-program]] §7 item 11.
-/

namespace Cleanroom.Bli.BliOverlay

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound

noncomputable section

/-- The day-`n` large atom `⌜a_{4^{sizeBound n}}⌝` (bli-found's `largeOn_witness` sentence).
Source: [[bli-overlay-mandate]] T5
Kind: D
Fidelity: exact -/
abbrev largeAtom (n : ℕ) : Sentence := AttemptB.largeAtom n

/-- **T5 (N+). The half overlay changes a price of the paper process's LIA.** On T2's day `N₀`,
the large sentence `⌜a_{4^{sizeBound N₀}}⌝` is priced `1/2` by the overlaid market over
`paperDP 𝗜𝚺₁` and `0` by FAF's LIA over the same process. The day is T2's existential `N₀`
(a non-constructive day is still a day); the overlay changes a price; the process has a
consistent world at every stage (`overlay_half_paperDP_hworld`).
Source: [[bli-overlay-mandate]] T5; [[bli-program]] §7 item 11
Kind: N+
Fidelity: n/a
Hyps: (a) — the instances `[𝗜𝚺₁.Δ₁] [𝗣𝗔⁻ ⪯ 𝗜𝚺₁] [Entailment.Consistent 𝗜𝚺₁]` are FAF's own,
as `paperLIA` uses them -/
theorem overlay_half_ne_lia :
    ∃ n φ, overlayQuote (paperDP 𝗜𝚺₁) Overlay.half n φ ≠ liaQuote (paperDP 𝗜𝚺₁) n φ :=
  AttemptA.overlay_half_ne_lia

/-- **T5, strong form** (attempt B's, transported): for **every** process, from some day on the
half overlay prices the day's large atom `1/2` while FAF's LIA prices it `0`.
Source: [[bli-overlay-mandate]] T5
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem overlay_half_differs_from (DP : DeductiveProcess) :
    ∃ N₀, ∀ n ≥ N₀, overlayQuote DP Overlay.half n (largeAtom n) = 1 / 2 ∧
      liaQuote DP n (largeAtom n) = 0 := by
  rw [overlayQuote_eq_attemptB, Overlay.half_toB]
  exact AttemptB.overlay_half_differs_from DP

/-- The overlaid market of the witness is not the LIA market (the history form of T5).
Source: [[bli-overlay-mandate]] T5
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem overlayHistory_half_ne_liaHistory :
    overlayHistory (paperDP 𝗜𝚺₁) Overlay.half ≠ liaHistory (paperDP 𝗜𝚺₁) :=
  AttemptA.overlayHistory_half_ne_liaHistory

/-- **Every stage of the paper process has a consistent world** (FAF's `paperDP_hworld`,
restated beside the witness): "not exploited" over `paperDP 𝗜𝚺₁` is not empty (trap (ii)).
Source: [[bli-overlay-mandate]] T4 trap (ii), T5
Kind: L
Fidelity: exact -/
theorem overlay_half_paperDP_hworld (n : ℕ) :
    ∃ v : PCWorld, v.ConsistentWith ((paperDP 𝗜𝚺₁).D n) :=
  AttemptA.overlay_half_paperDP_hworld n

/-- The plausible-assessment set of any trader on any overlaid market over `paperDP 𝗜𝚺₁` is
nonempty (attempt B's form of trap (ii), transported).
Source: [[bli-overlay-mandate]] T4 trap (ii), T5
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem overlay_plausibleAssessments_nonempty (ov : Overlay) (Tr : Trader) :
    (Tr.plausibleAssessments (overlayHistory (paperDP 𝗜𝚺₁) ov) (paperDP 𝗜𝚺₁)).Nonempty := by
  rw [overlayHistory_eq_attemptB]
  exact AttemptB.overlay_plausibleAssessments_nonempty ov.toB Tr

/-- **T4 at the witness**: no efficiently computable trader exploits the half-overlaid market
over `paperDP 𝗜𝚺₁` — a market that differs from FAF's LIA (`overlayHistory_half_ne_liaHistory`)
over a process every stage of which has a consistent world (`overlay_half_paperDP_hworld`).
Source: [[bli-overlay-mandate]] T4, T5
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem overlay_half_paperDP_no_ec_trader_exploits (Tr : Trader) (hTr : EfficientlyComputable Tr) :
    ¬ Tr.Exploits (overlayHistory (paperDP 𝗜𝚺₁) Overlay.half) (paperDP 𝗜𝚺₁) :=
  AttemptA.overlay_half_paperDP_no_ec_trader_exploits Tr hTr

/-- **N+ for T2 at `paperDP 𝗜𝚺₁`**: from `buyAtomDaily`'s enumeration index on, the firm's
day-`n` mentioned set is nonempty, for every table `Q`.
Source: [[bli-overlay-mandate]] T2 (witness)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem firm_mentions_something_paperDP :
    ∃ i, ∀ n ≥ i, ∀ Q : ℕ → Sentence → ℚ,
      (mentionedSet (TradingFirmAt (paperDP 𝗜𝚺₁) Q n)).Nonempty :=
  AttemptA.firm_mentions_something_paperDP

end

end Cleanroom.Bli.BliOverlay
