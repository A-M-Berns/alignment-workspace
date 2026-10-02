/-
  Payor's lemma over Foundation's GL, and Payor-bot cooperation.

  Target 9 of [[dp-troll-bridge-mandate]]. FAF has no `Payor` (grepped 2026-09-29); the lemma
  is three lines from Löb's rule. The `n`-agent form is the Payor-bot cooperation theorem; the
  two-agent Löbian-circle instance in FAF is `fairBot_vs_fairBot` (`ModalAgents/Cooperation`),
  recorded below as an `example`. Abram's "Nash-as-Löb" gloss is ATTRIBUTION-UNVETTED and not
  claimed by any statement here.
-/

import Cleanroom.Decision.DpTrollBridge.Basic
import ModalAgents.GL
import ModalAgents.Cooperation

open LO LO.Modal
open LO.Entailment LO.Modal.Entailment

namespace Cleanroom.Decision.DpTrollBridge

/-- **Payor's lemma.** If `GL ⊢ □(□x 🡒 x) 🡒 x` then `GL ⊢ x`. Proof: `□x 🡒 □(□x 🡒 x)` (K on
the necessitated tautology `x 🡒 (□x 🡒 x)`), so `□x 🡒 x` by the hypothesis, then `lob_rule`.
Source: Payor 2023, "Modal Fixpoint Cooperation without Löb's Theorem" (the lemma); [[bli-paper-2-inventory]] 025(a)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem payor {x : Modal.Formula ℕ} (h : Modal.GL ⊢ □(□x 🡒 x) 🡒 x) : Modal.GL ⊢ x := by
  have h1 : Modal.GL ⊢ □x 🡒 □(□x 🡒 x) := imply_box_distribute'! (by cl_prover)
  have h2 : Modal.GL ⊢ □x 🡒 x := by cl_prover [h1, h]
  exact ⟨lob_rule h2.some⟩

/-- **Payor-bot cooperation, `n` agents.** For `x := ⋀ xs` and each `xᵢ ∈ xs` with
`GL ⊢ xᵢ 🡘 □(□x 🡒 x)` (each agent cooperates iff it is provable that "if everyone's
cooperation is provable then everyone cooperates"), `GL ⊢ x`: everyone cooperates. Kind C:
`right_Conj₂!_intro` collects `□(□x 🡒 x) 🡒 xᵢ` into `□(□x 🡒 x) 🡒 x`, then `payor`. The
empty list is the vacuous case (`⋀[] = ⊤`).
Source: Payor 2023 (the cooperation theorem); [[bli-paper-2-inventory]] 025(b)
Kind: C
Fidelity: exact (of the modal statement; the "Nash-as-Löb" reading is not claimed)
Hyps: (a) none -/
theorem payor_bots (xs : List (Modal.Formula ℕ))
    (h : ∀ xᵢ ∈ xs, Modal.GL ⊢ xᵢ 🡘 □(□(⋀xs) 🡒 ⋀xs)) : Modal.GL ⊢ ⋀xs := by
  apply payor
  apply right_Conj₂!_intro
  intro xᵢ hi
  have := h xᵢ hi
  cl_prover [this]

/-- The two-agent Löbian-circle instance in FAF: FairBot cooperates with FairBot
(`fairBot_vs_fairBot`, via `lobian_circle`). Recorded here so the ledger row points at FAF's
own theorem; nothing is re-proved.
Source: FAF `ModalAgents/Cooperation.lean` `fairBot_vs_fairBot`; Barasz et al. §3
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem fairBot_cooperates_fairBot : Cooperates fairBot fairBot := fairBot_vs_fairBot

end Cleanroom.Decision.DpTrollBridge
