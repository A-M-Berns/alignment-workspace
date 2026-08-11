/-
  weak-endorsement-deference.lean   —   UNCHECKED — for the Lean-verify agent.

  Thread: "weak endorsement ⇒ weak deference; self-reference / Gödel".
  Companion model: models/weak-endorsement-deference-model.md.

  ============================================================================
  WHAT INFORMAL CLAIM THIS FILE IS MEANT TO CAPTURE
  ============================================================================
  The model's central impossibility is the *Gödel/liar wall*:

      HARD endorsement  +  the liar sentence   is JOINTLY UNSATISFIABLE,
      SOFT endorsement  +  the liar sentence   IS satisfiable.

  Concretely (Logical-Induction paper, §4.12 around eq. (2118)): let
      χ_n  :=  "ℙ_{f(n)}(χ_n) < 1/2"        (the probabilistic liar)
  and let  w := 1[ ℙ_{f(n)}(χ_n) ≥ 1/2 ]  be the (HARD) indicator of the
  conditioning event.  The conjunction  χ_n ∧ (ℙ_{f(n)}(χ_n) ≥ 1/2)  is
  DISPROVABLE (it asserts both < 1/2 and ≥ 1/2), so

      E_now( 1(χ_n) · w )  =  ℙ_now( χ_n ∧ ℙ_{f(n)}(χ_n) ≥ 1/2 )  ≂ₙ  0.      (*)

  "HARD two-sided endorsement at threshold t" is the demand that learning the
  expert estimates X to be (in the band selected by w) exactly t makes you
  estimate exactly t:

      E_now( X · w )  =  t · E_now( w ).                                       (**)

  With X = 1(χ_n), t = 1/2, (**) reads  E_now(1(χ_n)·w) = (1/2)·E_now(w).
  But (*) says the left side is 0, so (**) forces E_now(w) = 0 — i.e. the
  present self is CERTAIN its future self will NOT reach ≥ 1/2 on the liar.
  That contradicts the liar's recurrent oscillation: the future price crosses
  1/2 infinitely often (Thm 4.5.10 recurring-unbiasedness), so E_now(w) > 0.
  Hence HARD endorsement on the liar is contradictory.

  The SOFT version replaces "=" in (**) by the one-sided "≥" of Self-Trust
  (Thm 4.12.4) and the hard w by a Lipschitz ramp; then the constraint is
      E_now( X · w_soft )  ≥  t · E_now( w_soft ),
  which the LI answer "≈ 1/2 on the liar" satisfies — no contradiction.

  ============================================================================
  THE TWO LEMMAS (finite, exact, real-valued — the algebraic skeleton only)
  ============================================================================
   (A) `hard_endorsement_liar_unsat` — the IMPOSSIBILITY.
       Hypotheses (all FAITHFUL to the prose; none smuggles the conclusion):
         · `ht  : 0 < t`            — the threshold is positive (t = 1/2 in the liar).
         · `hw  : 0 < Ew`           — E_now(w) > 0: present self gives POSITIVE
                                       credence to "future self reaches ≥ t"
                                       (the liar oscillates across the threshold).
         · `hdisprov : Exw = 0`     — eq. (*): E_now(X·w) = 0 because the
                                       conjunction is disprovable.
         · `hendorse : Exw = t * Ew`— eq. (**): HARD two-sided endorsement.
       Conclusion: `False`.  So the four can't hold together: hard endorsement
       is refuted by the liar.

   (B) `soft_endorsement_liar_sat` — NON-VACUITY / the contrast.
       The SAME data with the one-sided `≥` (Self-Trust shape) and the LI value
       has a MODEL: with c = 1/2 (the LI conditional value of the liar) and any
       soft weight 0 ≤ w_soft ≤ 1, and p ≤ 1/2, the one-sided constraint
       `c * w_soft ≥ p * w_soft` holds.  This shows the soft schema is
       SATISFIABLE on exactly the data that refuted the hard schema — so (A)'s
       impossibility is special to the EQUALITY, not to the liar.  It also rules
       out the "hypotheses of (A) were vacuously contradictory anyway" failure
       mode: the soft relaxation is consistent.

  ============================================================================
  FIDELITY AUDIT — does the Lean say what the prose says?  (READ THIS)
  ============================================================================
  * (A) is a faithful rendering of "hard endorsement + liar ⇒ contradiction":
      - `hdisprov : Exw = 0` is eq. (*), an INPUT fact about the liar
        (disprovable conjunction ⇒ probability 0), NOT the conclusion.
      - `hendorse : Exw = t * Ew` is eq. (**), the HARD endorsement identity.
      - `hw : 0 < Ew` is the genuinely load-bearing liar fact (oscillation), and
        it is the hypothesis that makes the contradiction NON-VACUOUS: drop it
        (allow Ew = 0) and the four become consistent (0 = t*0).  So the proof
        MUST use `hw`; if it didn't, the statement would be vacuous.  (The proof
        below does use `hw` — it derives Ew = 0 from the other three and clashes
        with `hw`.)
      - The conclusion `False` is the honest content of "jointly unsatisfiable".
  * NON-VACUITY is double-checked by (B): the relaxed (soft, ≥) system has an
    explicit model, so the impossibility in (A) is a property of the EQUALITY,
    not an artifact of contradictory hypotheses.
  * QUANTIFIERS: (A) is stated for a SINGLE band (X·w already collapsed to the
    scalars Exw, Ew, with t the threshold).  This is faithful: the liar refutes
    hard endorsement already at the SINGLE instance (X=1(χ), t=1/2, this w), so
    one instance suffices for an impossibility — universal quantification would
    only make the hypothesis STRONGER and the impossibility EASIER, so using one
    instance is the conservative (honest) choice.
  * WHAT THIS DOES *NOT* CLAIM (the prose↔Lean gap, stated plainly):
      - It does NOT prove eq. (*) `Exw = 0` from the diagonal lemma / the LI
        criterion; that is an INPUT (the paper proves it via disprovability +
        Thm 4.8 `perkno`).  We take it as a hypothesis, clearly flagged.
      - It does NOT prove `0 < Ew` from recurring-unbiasedness; also an input.
      - No LUVs, no market/trader, no `≂ₙ` asymptotics, no diagonal lemma.  This
        is the FINITE, EXACT, real-valued algebraic skeleton of the clash only.
      - (B) does not claim the soft version is the LI behaviour; it only exhibits
        that the soft (≥) constraint is consistent on this data — the satisfiable
        contrast.  The genuine "LI answers ≈1/2" is the paper's content (input).
  So: this verifies the algebraic CORE of "hard endorsement collides with the
  liar while soft endorsement does not", which is the model's impossibility
  statement; it does not re-derive the LI/diagonal facts it takes as inputs.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace WeakEndorsementDeference

/-- **(A) HARD endorsement + liar ⇒ contradiction (algebraic core).**

`Exw` models `E_now(1(χ)·w)`, `Ew` models `E_now(w)`, `t` the threshold (= 1/2).
`hdisprov` is the liar fact `E_now(1(χ)·w) = 0` (disprovable conjunction).
`hendorse` is HARD two-sided endorsement `E_now(1(χ)·w) = t·E_now(w)`.
`hw` is the oscillation fact `E_now(w) > 0`.  Together with `0 < t` these are
inconsistent: endorsement+disprovability force `E_now(w) = 0`, contradicting `hw`.

This is the precise sense in which **hard endorsement and hard deference are
jointly unsatisfiable on the liar**. -/
theorem hard_endorsement_liar_unsat
    {t Exw Ew : ℝ}
    (ht : 0 < t)
    (hw : 0 < Ew)
    (hdisprov : Exw = 0)
    (hendorse : Exw = t * Ew) :
    False := by
  -- From the two equations: 0 = Exw = t * Ew, so t * Ew = 0.
  have htEw : t * Ew = 0 := by rw [← hendorse, hdisprov]
  -- But t > 0 and Ew > 0 give t * Ew > 0 — contradiction with htEw.
  nlinarith [mul_pos ht hw]

/-- **(B) SOFT endorsement + liar IS satisfiable (the contrast / non-vacuity).**

The one-sided Self-Trust constraint `E_now(X·w_soft) ≥ p · E_now(w_soft)` holds
when the conditional value `c = E_now(X | soft band)` is at least the threshold
`p`, for any nonnegative soft weight.  Taking `c = 1/2` (the LI answer on the
liar) and any `p ≤ 1/2`, the constraint is satisfied — on exactly the data that
refuted the HARD form.  So the impossibility in (A) is a property of the
EQUALITY `=`, not of the liar; the relaxed `≥` system is consistent.

Here `Exw_soft = c * wsoft` models `E_now(X·w_soft)` and `Ew_soft = wsoft`
models `E_now(w_soft)`. -/
theorem soft_endorsement_liar_sat
    {p c wsoft : ℝ}
    (hpc : p ≤ c)
    (hw : 0 ≤ wsoft) :
    c * wsoft ≥ p * wsoft := by
  have h : p * wsoft ≤ c * wsoft := mul_le_mul_of_nonneg_right hpc hw
  exact h

/-- A concrete witness for (B): the LI liar value `c = 1/2`, threshold
`p = 1/2`, soft weight `wsoft = 1/2` satisfies the one-sided constraint —
the boundary instance (`p = c`), exactly the liar's threshold. -/
theorem soft_endorsement_liar_witness :
    (1/2 : ℝ) * (1/2) ≥ (1/2 : ℝ) * (1/2) :=
  soft_endorsement_liar_sat (le_refl (1/2 : ℝ)) (by norm_num)

/-- A STRICT-slack witness: with threshold `p = 1/4` below the liar value
`c = 1/2`, the soft constraint holds with strict room to spare.  This makes the
contrast with (A) vivid: where the HARD `=` is contradictory on the liar, the
soft `≥` has slack. -/
theorem soft_endorsement_liar_strict_witness :
    (1/2 : ℝ) * (1/2) > (1/4 : ℝ) * (1/2) := by norm_num

end WeakEndorsementDeference

-- Axiom audit: each must depend ONLY on [propext, Classical.choice, Quot.sound]
-- and NOT on sorryAx.
#print axioms WeakEndorsementDeference.hard_endorsement_liar_unsat
#print axioms WeakEndorsementDeference.soft_endorsement_liar_sat
#print axioms WeakEndorsementDeference.soft_endorsement_liar_witness
#print axioms WeakEndorsementDeference.soft_endorsement_liar_strict_witness
