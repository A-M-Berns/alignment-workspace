import Cleanroom.Bli.UdtBliTiling.IndepCalc
import Cleanroom.Bli.UdtBliCore.Mugging
import Cleanroom.Bli.UdtBliSist.Defs

/-!
# `udt-bli-tiling` · Omega: "don't outthink Omega" under two readings of Omega's read (T7,
stretch)

bli-soto-b-2-024 (journal l. 1493): the agent should "think exactly as long as Omega" — decide
from a state no better informed about the coin than Omega's model of it. The item's own flag:
ill-posed until Omega's simulation is modelled. Two readings, on the mugging prior, each a cheap
theorem, with **opposite verdicts** (finding F6):

* **(R1) Omega reads the agent's actual point at the paired `Ask` table** — this is
  `muggingPrior r` itself (the `Rec` branch pays iff `π Ask = pay`). The ex-ante optimum is
  attained by a policy measurable with respect to the empty class structure (constant: it
  "thinks no longer than Omega"): `r1_coarse_optimal`. Refusing on a known-bad coin would forfeit
  the paired payout — "don't outthink Omega" holds.
* **(R2) Omega reads a coarser point** — `muggingPrior2 r`: the same prior with the `Rec` branch
  paying iff the policy pays at the *coarse* table `Other` (Omega's model of the agent sees only
  the coarse state), the `Ask` branch charging for the actual `Ask` point. The ex-ante optimum is
  the non-measurable "outthinking" policy (refuse at `Ask`, pay at `Other`), strictly better than
  every constant policy: `r2_outthink_optimal`. The slogan is false here.

So the slogan is a statement about Omega's read, not about the agent, and the sources fix neither
reading; neither reading is attributed to the journal beyond the quoted line
(ATTRIBUTION-UNVETTED). "Frozen at depth `k`" is rendered as `MeasurableOn Σ`: constant on every
`Σ`-class (sist's `agreesOn`); the theorems use `Σ = ∅` (the coarsest freeze), where
measurability is constancy — the minimal instance of the mandate's two-depth model.

Sources: bli-soto-b-2-024; mandate T7.
-/

namespace Cleanroom.Bli.UdtBliTiling

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliCore.Mugging
  Cleanroom.Bli.UdtBliSist Finset

namespace Omega

variable (r : Bool → ℚ)

/-- **A policy frozen at the class structure `Σ`**: constant on every `Σ`-class
(`agreesOn Σ T T' → π T = π T'`). With `Σ = ∅` this is constancy.
Source: bli-soto-b-2-024 ("behave as if it's exactly that updateful"); mandate T7 ("frozen at
depth `k`")
Kind: D
Fidelity: variant: depth rendered as a class structure on day-1 tables (disclosed) -/
def MeasurableOn (Sig : Finset ↥(witIndex.S 1)) (π : Policy mugTables Bool) : Prop :=
  ∀ T T', agreesOn Sig T T' → π T = π T'

/-- At `Σ = ∅`, measurability is constancy.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma measurableOn_empty_iff (π : Policy mugTables Bool) :
    MeasurableOn ∅ π ↔ ∀ T T', π T = π T' := by
  unfold MeasurableOn agreesOn
  simp

/-- **(R1) Omega reads the actual `Ask` point: the optimum is attained by a coarse policy.** On
`muggingPrior r` (`|r| ≤ 10`), the constant policy "pay" is `∅`-measurable and prior-optimal, so
nothing is gained by deciding from a finer state — "don't outthink Omega".
Source: bli-soto-b-2-024 (R1); mandate T7
Kind: C (`isPriorOptimal_const_pay`)
Fidelity: exact (the minimal depth structure)
Hyps: (a) `|r a| ≤ 10`; does not use faith -/
theorem r1_coarse_optimal (hr : ∀ a, |r a| ≤ 10) :
    MeasurableOn ∅ (fun _ => true) ∧ (muggingPrior r).IsPriorOptimal (fun _ => true) :=
  ⟨fun _ _ _ => rfl, isPriorOptimal_const_pay r hr⟩

/-- The (R2) utility: `−10·[π Ask]` at `Ask`, `100·[π Other]` at `Rec` (Omega's model reads the
coarse table), `r (π Ask)` at `Other`.
Source: bli-soto-b-2-024 (R2); mandate T7
Kind: D
Fidelity: exact -/
def mugU2 : Fin 3 → Bool → Bool → ℚ
  | 0 => fun a _ => if a then -10 else 0
  | 1 => fun _ o => if o then 100 else 0
  | 2 => fun a _ => r a

/-- **The (R2) data**: the mugging's base and points, the utility reading the actual `Ask` point
and the coarse `Other` point.
Source: bli-soto-b-2-024 (R2); mandate T7
Kind: D
Fidelity: exact -/
def muggingData2 : IndepData witIndex 1 mugTables Bool :=
  { muggingData r with U₀ := fun s π => mugU2 r s (π askT) (π otherT) }

/-- **The (R2) prior.**
Source: bli-soto-b-2-024 (R2); mandate T7
Kind: D
Fidelity: exact -/
def muggingPrior2 : FiniteBLIPrior witIndex 1 mugTables Bool := (muggingData2 r).toPrior

/-- **The outthinking policy**: refuse at `Ask` (the coin is known there), pay at the coarse
`Other` table (what Omega's model sees).
Source: bli-soto-b-2-024 (R2: "the simulation gives, the agent refuses")
Kind: D
Fidelity: exact -/
def outthink : Policy mugTables Bool := fun T => decide (T = otherT)

/-- `outthink Ask = refuse`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma outthink_askT : outthink askT = false := by simp [outthink, mAsk_ne_mOther]

/-- `outthink Other = pay`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma outthink_otherT : outthink otherT = true := by simp [outthink]

/-- The ex-ante value under (R2): `(49/100)·(−10·[π Ask]) + (49/100)·(100·[π Other]) +
(2/100)·r (π Ask)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma exAnteValue2 (π : Policy mugTables Bool) :
    (muggingPrior2 r).exAnteValue π =
      49 / 100 * (if π askT then -10 else 0) + 49 / 100 * (if π otherT then 100 else 0) +
        2 / 100 * r (π askT) := by
  unfold muggingPrior2
  rw [IndepCalc.exAnteValue_toPrior (muggingData2 r) π
    (prodLaw_pos (fun _ _ => by simp [mugHalf]) π)]
  change ∑ s : Fin 3, mugMass s * mugU2 r s (π askT) (π otherT) = _
  rw [Fin.sum_univ_three]
  simp only [mugMass_zero, mugMass_one, mugMass_two, mugU2]

/-- **(R2) Omega reads the coarse point: the optimum outthinks Omega.** On `muggingPrior2 r`
(`|r| ≤ 10`), the policy "refuse at `Ask`, pay at `Other`" is prior-optimal, is not
`∅`-measurable, and strictly beats every `∅`-measurable (constant) policy: `49 + (2/100)·r refuse`
against `441/10 + (2/100)·r pay` (constant pay) or `(2/100)·r refuse` (constant refuse). The
slogan "don't outthink Omega" is false under this reading.
Source: bli-soto-b-2-024 (R2: "outthinking Omega pays; then the slogan is false"); mandate T7
Kind: P / N+
Fidelity: exact (the minimal depth structure)
Hyps: (a) `|r a| ≤ 10`; does not use faith -/
theorem r2_outthink_optimal (hr : ∀ a, |r a| ≤ 10) :
    (muggingPrior2 r).IsPriorOptimal outthink ∧ ¬ MeasurableOn ∅ outthink ∧
      ∀ π, MeasurableOn ∅ π →
        (muggingPrior2 r).exAnteValue π < (muggingPrior2 r).exAnteValue outthink := by
  have h1 := (abs_le.mp (hr true)).1
  have h1' := (abs_le.mp (hr true)).2
  have h2 := (abs_le.mp (hr false)).1
  have h2' := (abs_le.mp (hr false)).2
  refine ⟨fun π => ?_, fun h => ?_, fun π hπ => ?_⟩
  · rw [exAnteValue2, exAnteValue2, outthink_askT, outthink_otherT]
    cases ha : π askT <;> cases ho : π otherT <;> simp <;> linarith
  · rw [measurableOn_empty_iff] at h
    have := h askT otherT
    rw [outthink_askT, outthink_otherT] at this
    exact Bool.false_ne_true this
  · rw [measurableOn_empty_iff] at hπ
    have hc : π otherT = π askT := hπ otherT askT
    rw [exAnteValue2, exAnteValue2, outthink_askT, outthink_otherT, hc]
    cases ha : π askT <;> simp <;> linarith

end Omega

end Cleanroom.Bli.UdtBliTiling
