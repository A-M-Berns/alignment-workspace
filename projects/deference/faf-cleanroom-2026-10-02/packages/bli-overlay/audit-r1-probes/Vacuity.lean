import Cleanroom.Bli.BliOverlay.Witness

/-!
# `bli-overlay` · audit r1 (adversarial) · probe: vacuity and definitional edges

Not imported by the library. One claim per `example`, each cheap (no `decide` on FAF data;
every proof is a rewrite chain through the package's own lemmas).

* **(a)** T4's hypothesis `hTr : EfficientlyComputable Tr` is inhabited (FAF's `buyAtomDaily`),
  so the headline quantifies over a nonempty class.
* **(b)** The overlay parameter matters for **every** process, not only `paperDP 𝗜𝚺₁`:
  `Overlay.half` and `Overlay.zero` give different overlaid markets (from the transported strong
  form `overlay_half_differs_from` and the sanity identity `overlayQuote_zero_eq_liaQuote`).
* **(c)** An edge of D3 worth recording: a sentence the day-`n` firm **mentions but does not
  trade** (a rank-`n` price leaf of an untraded sentence, or a past-day leaf) is priced `0` by
  the overlaid market on day `n` — the core state's support is inside the firm's support
  (`MarketMakerAccepts.1`), so the "core quote" on such a cell is FAF's junk `0`. The overlay
  can put a value only on *unmentioned* cells, not on every untraded one; FAF's LIA does the
  same, so this is a fact about the definition of record, not an error.
* **(d)** F2 is a statement about the *firm*, not about strategies: on every day some
  `Strategy n` mentions a non-small sentence. So `firm_mentioned_small` is not true for the
  trivial reason that strategies cannot name large sentences.
* **(e)** The restriction set handed to `MarketMaker` is immaterial: **any** past that agrees
  with the overlaid table on the mentioned cells of days `< n` yields the same core state. The
  junk `0` that `restrictState` writes off the mentioned set never reaches a headline.
-/

namespace Cleanroom.Bli.BliOverlay.AuditR1Adversarial

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Bli.BliOverlay

/-- (a) The class T4 quantifies over is nonempty. -/
example : ∃ Tr : Trader, EfficientlyComputable Tr :=
  ⟨buyAtomDaily, efficientlyComputable_buyAtomDaily⟩

/-- (b) For every process the half overlay and the zero overlay are different markets. -/
example (DP : DeductiveProcess) :
    overlayHistory DP Overlay.half ≠ overlayHistory DP Overlay.zero := by
  intro heq
  obtain ⟨N₀, hN₀⟩ := overlay_half_differs_from DP
  obtain ⟨h1, h2⟩ := hN₀ N₀ le_rfl
  have hz : overlayQuote DP Overlay.zero N₀ (largeAtom N₀) = 0 := by
    rw [overlayQuote_zero_eq_liaQuote]
    exact h2
  have hcell : ((overlayQuote DP Overlay.half N₀ (largeAtom N₀) : ℚ) : ℝ) =
      ((overlayQuote DP Overlay.zero N₀ (largeAtom N₀) : ℚ) : ℝ) :=
    congrFun (congrFun heq N₀) (largeAtom N₀)
  rw [h1, hz] at hcell
  norm_num at hcell

/-- (c) Mentioned but untraded ⟹ priced `0` on that day (FAF's junk `0` off the support). -/
example (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) (φ : Sentence)
    (hm : φ ∈ mentionedSet (firmStrat DP ov n)) (hs : φ ∉ (firmStrat DP ov n).support) :
    overlayQuote DP ov n φ = 0 := by
  rw [overlayQuote_of_mem DP ov hm]
  apply RationalBeliefState.quote_eq_zero_of_not_mem
  intro h
  exact hs ((coreState_accepts DP ov n).1 h)

/-- (d) Strategies in general can mention non-small sentences; F2 is about the firm. -/
example (n : ℕ) : ∃ (T : Strategy n) (φ : Sentence), MentionedBy T φ ∧ ¬ SmallOn n φ :=
  ⟨⟨[(EF.const 1, (Formula.atom (4 ^ sizeBound n) : Sentence))], by simp⟩,
    Formula.atom (4 ^ sizeBound n), Or.inl ⟨EF.const 1, List.mem_singleton_self _⟩,
    largeOn_witness n⟩

/-- (e) Any past agreeing with the overlaid table on the mentioned past cells gives the same
core state: the restricted past is one representative, not a load-bearing choice. -/
example (DP : DeductiveProcess) (ov : Overlay) (n : ℕ) (past : List RationalBeliefState)
    (h : ∀ φ, MentionedBy (firmStrat DP ov n) φ → ∀ k < n,
      rationalHistory past k φ = overlayQuote DP ov k φ) :
    coreState DP ov n =
      MarketMaker (firmStrat DP ov n) past (marketMakerError n) (marketMakerError_pos n) := by
  rw [coreState_eq]
  apply MarketMaker_eq_of_eqOn_mentioned
  intro φ hφ k hk
  rw [rationalHistory_overlayRestrictedPast DP ov hk (mem_mentionedSet_iff.mpr hφ), h φ hφ k hk]

end Cleanroom.Bli.BliOverlay.AuditR1Adversarial
