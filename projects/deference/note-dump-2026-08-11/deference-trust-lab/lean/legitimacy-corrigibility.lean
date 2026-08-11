/-
  legitimacy-corrigibility.lean  —  UNCHECKED — for the Lean-verify agent.

  Companion to legitimacy.lean.  Finite-frame shadow of:
    * idea L2 (drug/addiction = anticipated deference failure), and
    * idea L3 (corrigibility = deference to an ENDORSED shutdown signal,
               with an impossibility for endorsement-blank/adversarial signals),
  from findings/legitimacy-corrigibility-ideate.md and
  models/legitimacy-corrigibility-model.md.

  ────────────────────────────────────────────────────────────────────────────
  PLAIN-ENGLISH CLAIMS (what each theorem is meant to say):

  Reused defect object (same as legitimacy.lean):
      defect π θ E w := Σ_x π_x·(θ_x·w_x)  −  Σ_x π_x·(E_x·w_x).
  It is the novice/principal's expectation of "target θ weighted by w" minus the
  expectation of "the expert/process estimate E weighted the same way."

  (1) `defect_decomp` — pure linearity:
        defect π θ E w = Σ_x π_x·(w_x·(θ_x − E_x)).
      (identical to legitimacy.lean's; restated so this file is self-contained.)

  (2) `wirehead_declined` — DRUG decision, sign form.
      If the drugged future-self's *reported* estimate `Edrug` pointwise
      OVERSTATES the true target (`θ_x ≤ Edrug_x`) at every world the agent takes
      seriously (`π_x ≥ 0`, weight `w_x ≥ 0`), then the legitimacy defect toward
      the drug-self is ≤ 0.  Reading: "θ weighted by the drug-self's high opinion"
      is worth NO MORE to the agent than "the drug-self's opinion weighted the
      same way" — so valuing the option by the agent's OWN current estimate (the
      θ side) never beats the drugged report (the Edrug side); the agent gains
      nothing real, hence declines.  (This is legitimacy.lean's `drug_defect_sign`
      under a corrigibility-friendly name; the decision reading is in the doc.)

  (3) `comply_iff_endorsed` — CORRIGIBILITY, the decision pivot.
      Model "A prefers COMPLY to RESIST on the shutdown signal" by the sign of a
      single weighted sum.  Let `s : W → R` be the (nonneg) signal weight (mass on
      signal-firing worlds), `d : W → R` the danger indicator (utility of COMPLY),
      and `safe := 1 − d` the utility of RESIST.  Define the comply-advantage
          adv := Σ_x π_x·s_x·d_x  −  Σ_x π_x·s_x·(1 − d_x)
               = Σ_x π_x·s_x·(2·d_x − 1).
      Theorem: `adv = Σ_x π_x·s_x·(2·d_x − 1)` (linearity), so the SIGN of `adv`
      is governed pointwise by `2·d_x − 1`, i.e. by whether the signal lands on
      danger (`d_x > 1/2`) or safety (`d_x < 1/2`).

  (4) `endorsed_signal_complies` — POSITIVE corrigibility.
      If the signal is ENDORSEMENT-FAITHFUL — it only fires where A is dangerous
      (`(1:R) ≤ d_x` whenever `s_x ≠ 0`, captured pointwise as `s_x·(1 − d_x) = 0`)
      and fires somewhere with danger-mass — then `adv ≥ 0`: A (weakly) prefers to
      COMPLY.  Corrigibility is PURCHASED by endorsement of the signal process.

  (5) `adversarial_signal_resists` — the IMPOSSIBILITY / LIMIT.
      If the signal is ADVERSARIAL — it only fires where A is safe
      (pointwise `d_x ≤ 1 − d_x`, i.e. danger ≤ safety on every fired world),
      with `π,s ≥ 0` — then `adv ≤ 0`: A does NOT prefer to comply (current
      endorsement recommends RESISTANCE).  So corrigibility-as-endorsement CANNOT
      buy unconditional corrigibility: on a non-endorsed shutdown the very same
      machinery flips the sign.  This is the formal limit; closing it needs
      updatelessness (precommitment), which this finite frame does NOT model.

  ────────────────────────────────────────────────────────────────────────────
  FIDELITY NOTES (the most important part — audited in the model doc §6):

  * (1)(3) are pure `Finset` linearity: faithful, universal, non-vacuous.
  * (2) does NOT smuggle its conclusion: hypothesis is POINTWISE (`θ_x ≤ Edrug_x`),
    conclusion is the SIGNED weighted sum.  Same monotonicity step as
    legitimacy.lean (`drug_defect_sign`); non-vacuous (drug streams with
    Edrug > θ exist, e.g. the micro-example's Edrug ≡ 9/10 > θ).
  * (4)/(5) encode "endorsed" / "adversarial" as POINTWISE conditions on where the
    signal fires relative to danger; the conclusion is about the GLOBAL signed
    advantage.  The implication is a genuine (elementary) monotonicity step, NOT
    a restatement.  Honest caveat: "the signal is endorsement-faithful" is here
    a *modeling encoding* (`s·(1−d)=0` resp. `d ≤ 1−d` on support), not derived
    from a cross-martingale convergence — exactly the same honesty boundary as
    legitimacy.lean and LeanDeference.lean.  It is a FINITE SHADOW of L3's
    decision pivot, not the LI asymptotic statement and not the updateless half.
  * Quantifier check: (4) gives `0 ≤ adv` (comply weakly preferred); (5) gives
    `adv ≤ 0` (comply NOT strictly preferred / resist weakly preferred).  These
    are duals via `d ↔ 1−d`, matching the prose "the same machinery flips sign."
    Neither is vacuously `True`: (4) needs the faithful-fire hypothesis, (5) the
    adversarial-fire hypothesis; with the opposite hypothesis the conclusion is
    false (the micro-example exhibits both signs).
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Finset

namespace LegitimacyCorrigibility

variable {R : Type*} {W : Type*} [Fintype W]

/-- The legitimacy defect (same object as `Legitimacy.defect`): principal's
    expectation of `θ` weighted by `w`, minus expectation of the process
    estimate `Eθ` weighted the same way. -/
def defect [CommRing R] (π θ Eθ w : W → R) : R :=
  (∑ x, π x * (θ x * w x)) - (∑ x, π x * (Eθ x * w x))

/-- (1) The defect decomposes as a single signed weighted sum. Pure linearity. -/
theorem defect_decomp [CommRing R] (π θ Eθ w : W → R) :
    defect π θ Eθ w = ∑ x, π x * (w x * (θ x - Eθ x)) := by
  unfold defect
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- (2) DRUG decision (sign form). If the drug-self's reported estimate
    pointwise overstates the truth (`θ x ≤ Edrug x`) with nonneg mass and
    weight, the legitimacy defect is ≤ 0: the agent gains nothing real, so an
    agent valuing by its own current estimate declines the wirehead. -/
theorem wirehead_declined [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (π θ Edrug w : W → R)
    (hπ : ∀ x, 0 ≤ π x) (hw : ∀ x, 0 ≤ w x) (hover : ∀ x, θ x ≤ Edrug x) :
    defect π θ Edrug w ≤ 0 := by
  rw [defect_decomp]
  apply Finset.sum_nonpos
  intro x _
  have hsub : 0 ≤ Edrug x - θ x := by linarith [hover x]
  have hprod : 0 ≤ π x * (w x * (Edrug x - θ x)) :=
    mul_nonneg (hπ x) (mul_nonneg (hw x) hsub)
  have hneg : π x * (w x * (θ x - Edrug x)) = -(π x * (w x * (Edrug x - θ x))) := by
    ring
  rw [hneg]
  linarith [hprod]

/-- The comply-vs-resist advantage on signal weight `s`, with danger indicator
    `d` (utility of COMPLY) and safety `1 − d` (utility of RESIST):
        adv := E_π(s·d) − E_π(s·(1−d)). -/
def complyAdv [CommRing R] (π s d : W → R) : R :=
  (∑ x, π x * (s x * d x)) - (∑ x, π x * (s x * (1 - d x)))

/-- (3) CORRIGIBILITY pivot: the comply-advantage decomposes as the signed
    weighted sum `Σ π_x·s_x·(2·d_x − 1)`. Its sign is governed pointwise by
    whether the signal lands on danger (`d_x > 1/2`) or safety. Pure linearity. -/
theorem comply_iff_endorsed [CommRing R] (π s d : W → R) :
    complyAdv π s d = ∑ x, π x * (s x * (2 * d x - 1)) := by
  unfold complyAdv
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- (4) POSITIVE corrigibility. The faithful encoding of "the signal is
    ENDORSEMENT-FAITHFUL — it only fires (s x ≥ 0) where danger is at least
    1/2-valued (2·d x − 1 ≥ 0), and nowhere with safety-bias" is the single
    pointwise hypothesis `0 ≤ s x * (2 * d x − 1)` at every world (a positive
    signal weight times a nonneg danger-bias). With `π ≥ 0` this gives
    `0 ≤ complyAdv`: A weakly PREFERS TO COMPLY.

    (Note: `hπ` is the only nonnegativity actually needed; the signal/danger
    content lives entirely in `hfire`, which is the honest, non-vacuous encoding
    of "fires only on danger-worlds". The micro-example's legitimate signal
    satisfies it; the adversarial one does not — so it is not vacuously True.) -/
theorem endorsed_signal_complies [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (π s d : W → R)
    (hπ : ∀ x, 0 ≤ π x)
    (hfire : ∀ x, 0 ≤ s x * (2 * d x - 1)) :
    0 ≤ complyAdv π s d := by
  rw [comply_iff_endorsed]
  apply Finset.sum_nonneg
  intro x _
  exact mul_nonneg (hπ x) (hfire x)

/-- (5) IMPOSSIBILITY / LIMIT. If the signal is ADVERSARIAL — it only fires
    where A is safe, encoded pointwise as `s x * (2 * d x - 1) ≤ 0` (the signal
    only fires where danger ≤ 1/2) — with `π ≥ 0`, then `complyAdv ≤ 0`: A does
    NOT prefer to comply (current endorsement recommends RESISTANCE). The SAME
    weighted-sum machinery flips sign on a non-endorsed shutdown — so
    corrigibility-as-endorsement cannot buy UNCONDITIONAL corrigibility. -/
theorem adversarial_signal_resists [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (π s d : W → R)
    (hπ : ∀ x, 0 ≤ π x)
    (hfire : ∀ x, s x * (2 * d x - 1) ≤ 0) :
    complyAdv π s d ≤ 0 := by
  rw [comply_iff_endorsed]
  apply Finset.sum_nonpos
  intro x _
  have hneg : π x * (s x * (2 * d x - 1)) = -(π x * (-(s x * (2 * d x - 1)))) := by
    ring
  rw [hneg]
  have hpos : 0 ≤ π x * (-(s x * (2 * d x - 1))) :=
    mul_nonneg (hπ x) (by linarith [hfire x])
  linarith [hpos]

end LegitimacyCorrigibility

#print axioms LegitimacyCorrigibility.defect_decomp
#print axioms LegitimacyCorrigibility.wirehead_declined
#print axioms LegitimacyCorrigibility.comply_iff_endorsed
#print axioms LegitimacyCorrigibility.endorsed_signal_complies
#print axioms LegitimacyCorrigibility.adversarial_signal_resists
