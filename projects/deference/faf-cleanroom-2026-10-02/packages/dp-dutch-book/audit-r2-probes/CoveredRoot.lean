import Cleanroom.Decision.DpDutchBook.WhoBuys
import Cleanroom.Decision.DpCalibration.Miniature

/-!
Audit round 2, adversarial lens — probe 4: `Covered` on the nested miniature (findings F-D; the
round-1 fidelity audit asked the adversarial lens to probe `Covered` at a simulation node).

F-D says: "on nested trees — Remark 4.3's miniature, opaque Newcomb — no single node is met by
all `O_d`-runs … so `Covered` fails for every `q₀`". That is false at the **root**: the predictor's
sample node is a `d`-node met by every run, so `Covered C miniature root ⊤` holds for every
procedure (`covered_root`). What fails there is node-action veridicality (`root_not_nav`): its edge
is the sample, not the live act. So the T2 headlines (`sophisticated_values`,
`regardless_buys_iff`, `myopic_buy_sub_decline`), which assume `Covered` but not NAV, *do* apply
with `q₀ = root` on the miniature — and there `bookGapExt` is a bet on the predictor's sample
(`M_a/M = P(sample = a)`, `P_a/M_a = 𝔼[r ∣ sample = a]`), not P12's `Δ = P_{s_d}(a)|c − e(a)|`.
The identification with P12's `Δ` is `bookGapExt_eq`, which does require NAV, so the ledger's
T2 rows are not oversold; but F-D's sentence should read "fails for every *node-action-veridical*
`q₀`" — which is what `live_not_covered` shows for the live node under sample `a` at any properly
mixed label (a run with sample `b` never passes it).
Not imported by the library.
-/

namespace Cleanroom.Decision.DpDutchBook.AuditR2Adv

open Cleanroom.Found.DpCoreTree Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue Cleanroom.Decision.DpCalibration
open Cleanroom.Decision.DpDutchBook

/-- The miniature's root decision node: the predictor's sample. -/
def miniRoot : miniature.DecNode := none

/-- The live node under sample `s`. -/
def miniLive (s : Act2) : miniature.DecNode := some ⟨s, none⟩

/-- `Covered` holds at the root for every procedure: every run passes the sample node. -/
theorem covered_root (C : Proc Unit (fun _ => Act2) ℚ) :
    Covered C miniature miniRoot (miniObs ()) := by
  intro ℓ _ _
  unfold miniature at ℓ ⊢
  unfold miniRoot
  rcases ℓ with ⟨s, l, _⟩
  simp

/-- The root is not node-action-veridical: its edge is the sample, not the live act. -/
theorem root_not_nav : ¬ NodeActionVeridical miniActEv miniature miniRoot := by
  intro h
  unfold NodeActionVeridical at h
  unfold miniature miniRoot at h
  have := h ⟨.a, .b, ()⟩ .a (by simp)
  simp [miniActEv] at this

/-- `Covered` fails at the live node under sample `a` at every properly mixed label: the run
`(sample b, live a)` has positive mass and does not pass it. -/
theorem live_not_covered (q : ℚ) (h0 : 0 < q) (h1 : q < 1) :
    ¬ Covered (procQ q h0.le h1.le) miniature (miniLive .a) (miniObs ()) := by
  intro h
  unfold Covered at h
  unfold miniature miniLive at h
  have hpos : 0 < leafLaw (procQ q h0.le h1.le)
      (.decision () fun s => .decision () fun l => .leaf (s, l) (miniPay s l)) ⟨.b, .a, ()⟩ := by
    simp [procQ]
    nlinarith [mul_pos (sub_pos.mpr h1) h0]
  have := h ⟨.b, .a, ()⟩ hpos (by simp [miniObs])
  simp at this

end Cleanroom.Decision.DpDutchBook.AuditR2Adv
