import Cleanroom.Corrigibility.CorrLiShutdown.Pairs
import Cleanroom.Corrigibility.CorrLiShutdown.Identity
import Cleanroom.Found.LiQuoteLane.Witnesses

/-!
# `corr-li-shutdown` — PaperPair: the inductor-overseer shutdown pair over FAF's paper process

Audit round 1 (adversarial B2): the ledger named `li-quote-lane`'s `paperOneWayPair` as the
witness of `ShutdownPair.ofOneWayPair`, but that pair publishes every item on the **next** day
(`PublicationSchedule.succ`), so the constructor's same-day hypothesis `hsame` fails on it
(probe `OfOneWayPairNoPaperWitness.lean`); every shipped `ShutdownPair` was an `ofTable` pair
with the always-press overseer, and the package's tag object — the agent reading an *inductor*
overseer through the same-day ledger — had no inhabitant.

This file builds it. `paperSameDayPair` is `OneWayPair.ofLIA` over `paperDP 𝗜𝚺₁` on both sides,
quoting `li-quote-lane`'s tag-`0` atoms `witnessQuoted j n` with **same-day** publication
(`PublicationSchedule.sameDay`, computable); `paperShutdownPair := ShutdownPair.ofOneWayPair`
of it, with the e.c. certificate of item `0` from `li-quote-lane` (`witnessQuoted_machineSentenceCodes`).
Its overseer is FAF's paper LIA and its press is that LIA's own day-`n` price of the verdict
atom (`paperShutdownPair_press`). Grade **N+** for the *definition* (a real inductor on both
sides, every field from FAF's facts), with `li-quote-lane`'s caveat that the LIA's quotes are not
shown to vary; no obedience theorem is instantiated on it here (its press pattern is not known
to be poly-time, so `PressReadable` is a hypothesis on it — F13).

Also here (audit r1 fidelity N4): T1(c) `press_expect_iff_price` instantiated on both paper
pairs, the ledger's named witness now built.
-/

namespace Cleanroom.Corrigibility.CorrLiShutdown

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc
open Filter Topology

/-- Same-day publication for every item is computable (the identity on the day).
Source: none: infrastructure (`li-coupled-pair` has the same one-liner)
Kind: L
Fidelity: n/a -/
lemma sameDaySchedule_computable' :
    Computable fun p : ℕ × ℕ => ((fun _ : ℕ => PublicationSchedule.sameDay) p.1).e p.2 :=
  Computable.snd.of_eq fun _ => rfl

/-- **The same-day one-way pair over `paperDP 𝗜𝚺₁`**: `A = liaHistory (paperDP 𝗜𝚺₁)` reads
nothing; `H⁺ = liaHistory (paperDP 𝗜𝚺₁ ⊕ ledger)` reads `A`'s day-`n` prices of the tag-`0`
atoms `⟨0, ⟨j, n⟩⟩`, published the **same day**. Every field from FAF's own facts
(`paperDP_computable`, `paperDP_cleanroomFree`, `paperDP_hworld`, `LIA_is_logical_inductor`).
Source: audit r1 adversarial B2 (fix (a)); `li-quote-lane` `paperOneWayPair` with the schedule changed
Kind: N+
Fidelity: variant: plain trader class (as `paperOneWayPair`)
Hyps: (a) none -/
noncomputable def paperSameDayPair : OneWayPair :=
  OneWayPair.ofLIA (paperDP 𝗜𝚺₁) (paperDP 𝗜𝚺₁) (paperDP_computable 𝗜𝚺₁)
    (paperDP_computable 𝗜𝚺₁) witnessQuoted witnessQuoted_computable
    (fun _ => PublicationSchedule.sameDay) sameDaySchedule_computable'
    (processFreeOf_ledgerSchedule_of_cleanroomFree (paperDP_cleanroomFree 𝗜𝚺₁))
    (paperDP_hworld 𝗜𝚺₁)

/-- Item `0` of `paperSameDayPair` is published on the same day.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperSameDayPair_sameDay : ∀ n, (paperSameDayPair.e 0).e n ≤ n := fun _ => le_rfl

/-- **The inductor-overseer shutdown pair** (design decision 1's object, inhabited):
`ShutdownPair.ofOneWayPair` of `paperSameDayPair` — the overseer is FAF's paper LIA, the agent
is FAF's LIA over the paper process plus the same-day ledger of the overseer's prices, the
verdict family is the tag-`0` atoms `witnessQuoted 0 n` (e.c. by
`witnessQuoted_machineSentenceCodes`).
Source: audit r1 adversarial B2; mandate design decision 1
Kind: N+
Fidelity: variant: plain trader class; the overseer's press pattern is not shown to be poly-time (`PressReadable` is a hypothesis on it, F13)
Hyps: (a) none -/
noncomputable def paperShutdownPair : ShutdownPair :=
  ShutdownPair.ofOneWayPair paperSameDayPair witnessQuoted_machineSentenceCodes
    paperSameDayPair_sameDay

/-- The press of `paperShutdownPair` is the paper LIA's own day-`n` price of the verdict atom.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperShutdownPair_press (n : ℕ) :
    (paperShutdownPair.press n : ℝ) = liaHistory (paperDP 𝗜𝚺₁) n (witnessQuoted 0 n) :=
  ShutdownPair.ofOneWayPair_press _ _ _ n

/-- The agent of `paperShutdownPair` is FAF's LIA over the paper process plus the same-day
ledger of the paper LIA's quotes, definitionally.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem paperShutdownPair_agent :
    paperShutdownPair.agent = liaHistory (ledgerProcess (paperDP 𝗜𝚺₁)
      (fun j n => liaQuote (paperDP 𝗜𝚺₁) n (witnessQuoted j n))
      (fun _ => PublicationSchedule.sameDay)) := rfl

/-! ## T1(c) instantiated on the paper pairs (audit r1 fidelity N4) -/

/-- **T1(c) on `paperOneWayPair`** (N+): the two press forms agree up to `o(1)` over FAF's
paper LIA, with `hworldA := paperDP_hworld 𝗜𝚺₁` and the e.c. certificate of the tag-`0` atoms.
Source: audit r1 fidelity N4 (the ledger's witness cell, now built)
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem paperOneWayPair_press_expect_iff_price {c h : ℚ} (hch : 0 < (c : ℝ) + h) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      ((toyX c h (paperOneWayPair.quoted 0) n).expect paperOneWayPair.A n ≤ -ε →
        Cleanroom.Found.CorrThreeStep.complianceThreshold c h + ε / (2 * ((c : ℝ) + h)) <
          (paperOneWayPair.a 0 n : ℝ)) ∧
      (Cleanroom.Found.CorrThreeStep.complianceThreshold c h + ε < (paperOneWayPair.a 0 n : ℝ) →
        (toyX c h (paperOneWayPair.quoted 0) n).expect paperOneWayPair.A n < 0) :=
  press_expect_iff_price paperOneWayPair (paperDP_hworld 𝗜𝚺₁) witnessQuoted_machineSentenceCodes
    hch

/-- **T1(c) on `paperSameDayPair`** (N+): the same over the same-day pair.
Source: audit r1 fidelity N4
Kind: N+
Fidelity: n/a
Hyps: (a) -/
theorem paperSameDayPair_press_expect_iff_price {c h : ℚ} (hch : 0 < (c : ℝ) + h) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      ((toyX c h (paperSameDayPair.quoted 0) n).expect paperSameDayPair.A n ≤ -ε →
        Cleanroom.Found.CorrThreeStep.complianceThreshold c h + ε / (2 * ((c : ℝ) + h)) <
          (paperSameDayPair.a 0 n : ℝ)) ∧
      (Cleanroom.Found.CorrThreeStep.complianceThreshold c h + ε < (paperSameDayPair.a 0 n : ℝ) →
        (toyX c h (paperSameDayPair.quoted 0) n).expect paperSameDayPair.A n < 0) :=
  press_expect_iff_price paperSameDayPair (paperDP_hworld 𝗜𝚺₁) witnessQuoted_machineSentenceCodes
    hch

end Cleanroom.Corrigibility.CorrLiShutdown
