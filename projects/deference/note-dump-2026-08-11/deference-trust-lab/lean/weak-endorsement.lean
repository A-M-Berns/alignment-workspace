/-
  weak-endorsement.lean   —   UNCHECKED — for the Lean-verify agent.

  Thread: "weak endorsement ⇒ weak deference; self-reference / Gödel" (Idea 1/4).

  ============================================================================
  WHAT INFORMAL CLAIM THIS IS MEANT TO CAPTURE
  ============================================================================
  The thread's pivot is: the SYMMETRIC, HARD, EQUALITY form of endorsement
  ("Reflection": on learning the expert estimates X to be *exactly* t, estimate
  *exactly* t) is too strong — on a finite frame it forces the expert to be
  IMMODEST (certain of its own credence, P_w(P=P_w)=1, the S5/partitional case),
  which is exactly the case Gödel/diagonalization forbids for a self-modeling
  reasoner. Only the ONE-SIDED, SOFT inequality form ("Self-Trust", LI 4.12.4)
  survives modesty and self-reference.

  This file kernel-targets the *finite algebraic core* of the EQUALITY ⇒ IMMODESTY
  half (`equality_endorsement_implies_immodest`). The hypothesis `hCM` is the
  exact-frame shadow of the equality/conditional-martingale identity at a world
  `w`: the expert's credence `E_w(X) = ∑ P w v · X v` equals the novice's
  estimate of `X` conditioned on the fiber `{v | P v = P w}` (the event "the
  expert's credence is P_w"). The conclusion is immodesty at `w`.

  It is the SAME mathematical fact as `DeferenceExtra.CM_implies_immodest` in the
  confirmed `lean-deference/LeanDeference.lean`, but RE-STATED and RE-PROVED here
  from scratch in the lab's own namespace, with targeted (fast) imports, so the
  Lean-verify agent confirms it independently rather than trusting a cross-file
  claim.

  TWO lemmas:
   (A) `equality_endorsement_implies_immodest`  — equality endorsement ⇒ immodesty.
   (B) `immodest_satisfies_immodesty`           — NON-VACUITY: an immodest expert
        (probability vector P_w with no mass off its own fiber) attains the
        conclusion `P_w(fiber w) = 1`. This shows (A)'s conclusion is the genuine,
        attainable immodesty condition (so (A) is not vacuous), and that a *modest*
        expert (mass off its fiber) would instead give `< 1`.

  ============================================================================
  FIDELITY AUDIT — does the Lean actually say what the prose says? (read this)
  ============================================================================
  * FAITHFUL: `hCM` is the conditional-martingale identity, i.e. the algebraic
    shadow of HARD/EQUALITY conditional endorsement at `w`. It does NOT smuggle in
    the conclusion: the conclusion `∑ v, P w v * 1[fiber] = 1` (= P_w(fiber w)=1
    = immodesty) is obtained by *instantiating* `hCM` at the fiber's own indicator,
    not assumed.
  * NON-VACUOUS: lemma (B) exhibits a model of `hCM` (the immodest expert), and
    the conclusion there is genuinely `=1`, not provable for an arbitrary frame —
    a modest expert (mass off its fiber) would make the conclusion `<1`, so the
    implication has real content. (B) also rules out the "hypotheses are
    contradictory / could prove `True`" failure mode.
  * QUANTIFIERS MATCH: `hCM` quantifies over ALL `X : W → ℝ` (matches "for every
    random variable" in equality endorsement); `w` is a fixed world with positive
    novice mass `hw : 0 < π w` (matches "on the novice's support").
  * WHAT THIS DOES *NOT* CLAIM (the honest boundary, = prose gap):
     - It does NOT formalize the SOFT/ONE-SIDED Self-Trust side, nor that the
       one-sided form FAILS to force immodesty (that needs a witness frame —
       UNCHECKED prose in the findings file).
     - It does NOT formalize the soft⇒hard "no spectral gap" reduction that, on a
       finite frame, is what *produces* the hard hypothesis `hCM` from the soft
       one. That step is the load-bearing infinite-frame move and is left as prose
       (v2 §5.2).
     - No LUVs, no market/trader, no LI criterion, no `≂ₙ` asymptotics. Finite,
       exact, real-valued only.
   So: this verifies the `=`-side of the Idea-1 pivot ("equality endorsement is
   exactly immodesty"), which is the one new finitary nugget the thread adds; it
   does not by itself establish the full weak⇒weak theorem (that is v2 §3) nor the
   diagonal no-go (Idea 2).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

open Finset

namespace WeakEndorsement

/-- **(A) Equality endorsement ⇒ immodesty (finite algebraic core).**

If, at world `w` (with positive novice mass `π w > 0`), the expert's credence
`E_w(X) = ∑ v, P w v * X v` equals the novice's estimate of `X` conditioned on the
fiber `{v | P v = P w}` — for *every* `X` — then the expert is immodest at `w`:
its credence puts full mass on its own fiber, `∑ v, P w v * 1[P v = P w] = 1`.

`fiber v := if P v = P w then 1 else 0` is the indicator of the event
"the expert's credence equals `P_w`". -/
theorem equality_endorsement_implies_immodest
    {W : Type*} [Fintype W]
    (π : W → ℝ) (P : W → W → ℝ) (hπ : ∀ v, 0 ≤ π v) (w : W) (hw : 0 < π w)
    (hCM : ∀ X : W → ℝ,
        (∑ v, P w v * X v)
        = (∑ v, π v * (if P v = P w then (1 : ℝ) else 0) * X v)
          / (∑ v, π v * (if P v = P w then (1 : ℝ) else 0))) :
    (∑ v, P w v * (if P v = P w then (1 : ℝ) else 0)) = 1 := by
  -- The fiber's novice-mass is strictly positive (w sees itself: P w = P w).
  have hden : 0 < ∑ v, π v * (if P v = P w then (1 : ℝ) else 0) := by
    have hle : π w * (if P w = P w then (1 : ℝ) else 0)
            ≤ ∑ v, π v * (if P v = P w then (1 : ℝ) else 0) :=
      Finset.single_le_sum (f := fun v => π v * (if P v = P w then (1 : ℝ) else 0))
        (fun v _ => mul_nonneg (hπ v) (by by_cases h : P v = P w <;> simp [h]))
        (Finset.mem_univ w)
    rw [if_pos rfl, mul_one] at hle
    linarith
  -- Instantiate the endorsement identity at the fiber's OWN indicator.
  have key := hCM (fun v => if P v = P w then (1 : ℝ) else 0)
  -- The indicator is idempotent: 1[·] * 1[·] = 1[·], so the numerator collapses.
  have hnum : (∑ v, π v * (if P v = P w then (1 : ℝ) else 0) * (if P v = P w then (1 : ℝ) else 0))
            = ∑ v, π v * (if P v = P w then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl (fun v _ => by by_cases h : P v = P w <;> simp [h])
  rw [hnum, div_self (ne_of_gt hden)] at key
  exact key

/-- **(B) Non-vacuity / converse direction.**

An *immodest* expert at `w` — whose credence `P_w` is a probability vector
(`∑ v, P w v = 1`, hypothesis `hprob`) that is supported on its own fiber
(`himmodest`: `P w v ≠ 0 → P v = P w`, i.e. no mass off the fiber `{v | P v = P w}`)
— satisfies the immodesty conclusion of (A): `∑ v, P w v * 1[fiber] = 1`.

This shows (A)'s conclusion is the *genuine* immodesty condition and is *attainable*
(so (A) is non-vacuous, its hypotheses are consistent). Conversely a *modest* expert
— mass off its fiber — would make this sum `< 1`. The normalization `hprob` is the
honest content: "P_w(fiber w) = 1" only means immodesty for a P_w that already sums
to 1; without it the bare identity `∑ P w v · 1[fiber] = ∑ P w v` is all one gets. -/
theorem immodest_satisfies_immodesty
    {W : Type*} [Fintype W]
    (P : W → W → ℝ) (w : W)
    (hprob : (∑ v, P w v) = 1)
    (himmodest : ∀ v, P w v ≠ 0 → P v = P w) :
    (∑ v, P w v * (if P v = P w then (1 : ℝ) else 0)) = 1 := by
  -- For each v: P w v · 1[P v = P w] = P w v.  If P v = P w the indicator is 1;
  -- if P v ≠ P w then by `himmodest` (contrapositive) P w v = 0, so both sides are 0.
  have h1 : ∀ v ∈ (Finset.univ : Finset W),
      P w v * (if P v = P w then (1 : ℝ) else 0) = P w v := by
    intro v _
    by_cases h : P v = P w
    · simp [h]
    · have hzero : P w v = 0 := by
        by_contra hne
        exact h (himmodest v hne)
      simp [h, hzero]
  rw [Finset.sum_congr rfl h1, hprob]

end WeakEndorsement

-- Axiom audit: both lemmas must depend ONLY on the standard axioms
-- [propext, Classical.choice, Quot.sound] and NOT on sorryAx.
#print axioms WeakEndorsement.equality_endorsement_implies_immodest
#print axioms WeakEndorsement.immodest_satisfies_immodesty
