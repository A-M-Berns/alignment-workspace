import Cleanroom.Udt.UdtCommTrust.Advice
import Cleanroom.Udt.UdtCtExamples.Realized

/-!
# `Cleanroom.Udt.UdtCtExamples.Convention`: the rule and the probability-zero convention
(T5(a), T5(b))

Work package `udt-ct-examples`, target T5(a)–(b) (udt-rep-090). Sources:
[[communication-trust-translated]] lines 265–270 (the `[0,1]` bound; "When `P(X = x) = 0`, we
stipulate `E(U ∣ X = x) = −1`"; the footnote: "This ensures an agent will not choose a
probability-zero action. An earlier draft used `E(U∣X=x)=2` in such cases; however, this causes
problems with the 'instances are believed to follow recommendations' assumption"), 441–442 (the
rule); [[notation]] §3.2–3.3.

* (a) **The rule of record is `udt-comm-trust`'s `UdtRule`/`UdtRuleAt`**; no new rule is defined.
  `score_eq_ctForm` is the identity of the score with the C&T display `E[U ∣ Π*(ȯ, ö) = a]`
  under junk `−1`, by `rfl`. The identification with `udt-policy-calc`'s
  `Transparent.ctScore` (`TransparentNewcomb.lean`, `ctScore μ ε o a = condExpJunk (jointW μ ε)
  payoffΩ {π o = a} (−1)`, and `ctScore_eq`) is *by inspection*: the same shape,
  `condExpJunk _ U {policy outputs a at o} (−1)`, on another carrier (`TPolicy × Bool` with the
  coin as `D_E`); not a theorem here (the carriers differ; T5(d) is the attempt to relate them).
* (b) **The convention quantified.** `scoreJ j` is the score with an arbitrary junk value;
  `UdtRuleJ j` the rule with it. (i) with `j < 0` an unattained action is never an argmax once
  any action is attained; (ii) with `j > 1` an unattained action beats every attained one, so
  the rule forces *every* action attained at *every* input; `UdtRuleJ 2 ↔ UdtRule ∧ all attained`.
  (iii) The footnote made exact: under `UdtRuleJ 2`, `P(Π̈ = R) = 1`, `hnosim` and `hlink`, at
  every recommended input the non-empty deviation events are disjoint from the input event
  (`deviation_unrealized`): junk `2` forces mass on chosen policies that deviate at inputs they
  never realize. `J2` (`Realized.lean`) shows the package is consistent. (iv) The `[0,1]` bound
  is what makes `−1` a floor: an unbounded utility can score below `−1` on an attained event.
-/

namespace Cleanroom.Udt.UdtCtExamples

open Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtCommTrust Finset

section Abstract

variable {Ω OI OE AI AE DI DE DB OH OC : Type} [Fintype Ω] [DecidableEq AI] [DecidableEq AE]
variable (S : AbstractDS Ω OI OE AI AE DI DE DB OH OC)

/-- **T5(a): the score is the C&T display** `E[U ∣ Π*(ȯ, ö) = a]` with junk `−1` — by
definition; the rule of record is `UdtRule`.
Source: [[communication-trust-translated]] lines 269, 441–442 (udt-rep-090); mandate T5(a)
Kind: L
Fidelity: exact
Hyps: none -/
theorem score_eq_ctForm (o : OI) (e : OE) (a : AI × AE) :
    S.score o e a = condExpJunk S.μ.w S.U (S.evS o e a) (-1) := rfl

/-- **The score with an arbitrary junk value.**
Source: [[communication-trust-translated]] lines 265–270 (the convention as a parameter); mandate T5(b)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def scoreJ (j : ℝ) (o : OI) (e : OE) (a : AI × AE) : ℝ :=
  condExpJunk S.μ.w S.U (S.evS o e a) j

/-- **The UDT rule with an arbitrary junk value** (pointwise, as `UdtRule`).
Source: [[communication-trust-translated]] lines 441–442, read with the convention as a parameter; mandate T5(b)
Kind: D
Fidelity: exact (pointwise reading, as `UdtRule`)
Hyps: n/a -/
def UdtRuleJ (j : ℝ) : Prop := ∀ ω o e, IsArgmax (scoreJ S j o e) (S.polS ω (o, e))

/-- **`scoreJ (−1)` is `score`, `UdtRuleJ (−1)` is `UdtRule`.**
Source: mandate T5(b)
Kind: L
Fidelity: exact
Hyps: none -/
theorem scoreJ_neg_one : scoreJ S (-1) = S.score ∧ (UdtRuleJ S (-1) ↔ S.UdtRule) := ⟨rfl, Iff.rfl⟩

/-- Supporting lemma: on a non-empty event the junk value is irrelevant.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem scoreJ_of_nonempty {o : OI} {e : OE} {a : AI × AE} (ha : (S.evS o e a).Nonempty) (j j' : ℝ) :
    scoreJ S j o e a = scoreJ S j' o e a := by
  unfold scoreJ
  rw [condExpJunk_of_pos (mass_pos_of_nonempty S.pos ha),
    condExpJunk_of_pos (mass_pos_of_nonempty S.pos ha)]

/-- **(i) With a negative junk value an unattained action is never an argmax** once some action
is attained (generalizes `evS_nonempty_of_isArgmax`).
Source: [[communication-trust-translated]] line 270 ("This ensures an agent will not choose a probability-zero action"); mandate T5(b)(i)
Kind: L
Fidelity: exact
Hyps: none -/
theorem not_isArgmax_of_empty_of_neg {j : ℝ} (hj : j < 0) {o : OI} {e : OE} {a : AI × AE}
    (ha : S.evS o e a = ∅) {a' : AI × AE} (ha' : (S.evS o e a').Nonempty) :
    ¬ IsArgmax (scoreJ S j o e) a := by
  intro h
  have h1 : scoreJ S j o e a = j := by unfold scoreJ; rw [ha, condExpJunk_of_empty]
  have h2 : 0 ≤ scoreJ S j o e a' := condExpJunk_nonneg_of_nonempty S.pos S.U_nonneg ha' j
  have := h a'
  linarith

/-- Supporting lemma: an attained action scores at most `1`.
Source: none: infrastructure (`U ∈ [0,1]`)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem scoreJ_le_one {j : ℝ} {o : OI} {e : OE} {a : AI × AE} (ha : (S.evS o e a).Nonempty) :
    scoreJ S j o e a ≤ 1 :=
  condExpJunk_le_of_le (fun ω => (S.pos ω).le) (mass_pos_of_nonempty S.pos ha)
    fun ω _ => (S.U_mem ω).2

/-- **(ii) With a junk value above `1` an unattained action beats every attained one** — the
earlier draft's `2` makes a probability-zero action strictly best.
Source: [[communication-trust-translated]] line 270 (the footnote's earlier draft); mandate T5(b)(ii)
Kind: L
Fidelity: exact
Hyps: none -/
theorem scoreJ_lt_of_empty_of_gt_one {j : ℝ} (hj : 1 < j) {o : OI} {e : OE} {a a' : AI × AE}
    (ha : S.evS o e a = ∅) (ha' : (S.evS o e a').Nonempty) :
    scoreJ S j o e a' < scoreJ S j o e a := by
  have h1 : scoreJ S j o e a = j := by unfold scoreJ; rw [ha, condExpJunk_of_empty]
  rw [h1]
  exact lt_of_le_of_lt (scoreJ_le_one S ha') hj

/-- **(ii) The rule with a junk value above `1` forces every action attained at every input.**
A two-line consequence of `scoreJ_lt_of_empty_of_gt_one` (regraded `C`, audit r2 fidelity N5).
Source: mandate T5(b)(ii)
Kind: C
Fidelity: exact
Hyps: (a); §3 (c) -/
theorem attained_of_udtRuleJ {j : ℝ} (hj : 1 < j) (h : UdtRuleJ S j) (o : OI) (e : OE)
    (a : AI × AE) : (S.evS o e a).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  exact absurd (h S.w₀ o e a)
    (not_le.2 (scoreJ_lt_of_empty_of_gt_one S hj hne (S.evS_self_nonempty S.w₀ o e)))

/-- **`UdtRuleJ 2` is `UdtRule` together with total attainment.** Chains
`attained_of_udtRuleJ` with `scoreJ_of_nonempty` (regraded `C`, audit r2 fidelity N5).
Source: mandate T5(b)(ii)
Kind: C
Fidelity: exact
Hyps: (a); §3 (c) -/
theorem udtRuleJ_two_iff : UdtRuleJ S 2 ↔ S.UdtRule ∧ ∀ o e a, (S.evS o e a).Nonempty := by
  constructor
  · intro h
    refine ⟨fun ω o e a => ?_, attained_of_udtRuleJ S (by norm_num) h⟩
    have hall := attained_of_udtRuleJ S (by norm_num) h
    have := h ω o e a
    rwa [scoreJ_of_nonempty S (hall o e a) 2 (-1),
      scoreJ_of_nonempty S (hall o e (S.polS ω (o, e))) 2 (-1)] at this
  · rintro ⟨h, hall⟩ ω o e a
    have := h ω o e a
    show scoreJ S 2 o e a ≤ scoreJ S 2 o e (S.polS ω (o, e))
    rwa [scoreJ_of_nonempty S (hall o e a) 2 (-1),
      scoreJ_of_nonempty S (hall o e (S.polS ω (o, e))) 2 (-1)]

end Abstract

section Concrete

variable {Ω OI OE AI AE DI DE DB OH OC : Type} [Fintype Ω] [DecidableEq Ω]
  [Fintype OE] [DecidableEq OE] [Fintype AE] [DecidableEq AE] [DecidableEq AI] [DecidableEq OI]
variable (S : ConcreteDS Ω OI OE AI AE DI DE DB OH OC)

/-- **(iii) The footnote made exact**: under `UdtRuleJ 2`, `P(Π̈ = R) = 1`, `hnosim` and `hlink`,
at every recommended input `(ȯ, ö)` and every `a ≠ r(ö)`, the event `{Π*(ȯ, ö) = (ȧ, a)}` is
non-empty (junk `2` forces attainment) *and* disjoint from `{Ȯ = ȯ ∧ Ö = ö}` (following forbids
deviation where the input is realized): junk `2` and the follow-recommendations assumption
together force mass on chosen policies that deviate at inputs they never realize. This is the
package's reading of the footnote's "problems" (ATTRIBUTION-UNVETTED); `J2.footnote_package`
shows the conjunction is consistent.
Source: [[communication-trust-translated]] line 270 (footnote); mandate T5(b)(iii)
Kind: C
Fidelity: exact for the stated reading
Hyps: (a) `attained_of_udtRuleJ`, `deviation_unrealized`; `hlink` as there; §3 (c) -/
theorem footnote_exact (h2 : UdtRuleJ S.toAbstractDS 2) (h1 : mass S.μ.w S.evFollowsR = 1)
    (hnosim : ∀ e o, (S.s e (S.projOH o)).isSome → S.p e (S.projOC o) = none)
    (hlink : ∀ ω, S.P ω (S.oE ω) = none → S.polD ω (S.O ω) = S.polS ω (S.O ω))
    {o : OI} {e : OE} {a₀ : AE} (hs : S.s e (S.projOH o) = some a₀) (ai : AI) {a : AE}
    (ha : a ≠ a₀) : (S.evS o e (ai, a)).Nonempty ∧ S.evS o e (ai, a) ∩ evInput S o e = ∅ :=
  ⟨attained_of_udtRuleJ S.toAbstractDS (by norm_num) h2 o e (ai, a),
    deviation_unrealized S h1 hnosim hlink hs ai ha⟩

end Concrete

/-! ### `J2` satisfies `UdtRuleJ 2`: the footnote's package is consistent -/

namespace J2

/-- Supporting lemma: every action is attained at every input on `J2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem evS_nonempty (o : Fin 2) (e : Fin 1) (a : Fin 1 × Fin 2) : (S.evS o e a).Nonempty := by
  obtain ⟨ai, x⟩ := a
  have : ai = 0 := Subsingleton.elim _ _
  subst this
  exact ⟨(x, 0), by simp [S, absDS]⟩

/-- **Every two actions tie on `J2`** (`E[U ∣ d] = 1/2` for both dynamics).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem scoreJ_tie (j : ℝ) (o : Fin 2) (e : Fin 1) (a a' : Fin 1 × Fin 2) :
    scoreJ S.toAbstractDS j o e a = scoreJ S.toAbstractDS j o e a' := by
  obtain ⟨ai, x⟩ := a
  obtain ⟨ai', x'⟩ := a'
  have : ai = 0 := Subsingleton.elim _ _
  have : ai' = 0 := Subsingleton.elim _ _
  subst ai ai'
  show condExpJunk weights.w (natDiv u 1) (S.evS o e (0, x)) j =
    condExpJunk weights.w (natDiv u 1) (S.evS o e (0, x')) j
  refine condExpJunk_natDiv_eq weights u (by norm_num) (evS_nonempty o e _) (evS_nonempty o e _)
    ?_ j
  show csum weights u (event fun ω : Ω => ((0 : Fin 1), ω.1) = (0, x)) *
      weights.cnt (event fun ω : Ω => ((0 : Fin 1), ω.1) = (0, x')) =
    csum weights u (event fun ω : Ω => ((0 : Fin 1), ω.1) = (0, x')) *
      weights.cnt (event fun ω : Ω => ((0 : Fin 1), ω.1) = (0, x))
  revert x x'
  decide +kernel

/-- **`J2` satisfies the rule with junk `2`**: every action is attained everywhere and all tie.
Source: mandate T5(b)(iii)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem udtRuleJ_two : UdtRuleJ S.toAbstractDS 2 := fun ω o e a => (scoreJ_tie 2 o e a _).le

/-- **The footnote's package is consistent** (T5(b)(iii), N+): `J2` has `UdtRuleJ 2`,
`P(Π̈ = R) = 1`, `hnosim`, `hlink`, and a realized non-silent recommendation at which the
deviation event is non-empty and disjoint from the input event — exactly the shape
`footnote_exact` predicts, with the utility depending on the action (a genuine tie, not a
constant utility).
Source: mandate T5(b)(iii)
Kind: N+
Fidelity: n/a
Hyps: none -/
theorem footnote_package :
    UdtRuleJ S.toAbstractDS 2 ∧ mass S.μ.w S.evFollowsR = 1 ∧
      (∀ e o, (S.s e (S.projOH o)).isSome → S.p e (S.projOC o) = none) ∧
      (∀ ω, S.P ω (S.oE ω) = none → S.polD ω (S.O ω) = S.polS ω (S.O ω)) ∧
      S.s 0 (S.projOH 0) = some 0 ∧ (S.evS 0 0 (0, 1)).Nonempty ∧
      S.evS 0 0 (0, 1) ∩ evInput S 0 0 = ∅ :=
  ⟨udtRuleJ_two, followsR, hnosim, hlink, deviation_witness.1, deviation_witness.2.1,
    deviation_unrealized_J2⟩

end J2

/-! ### (iv) The `[0,1]` bound is what makes `−1` a floor -/

/-- **An unbounded utility can score below the junk `−1` on an attained event**: two equiprobable
points with utility `−2`. The LaTeX draft's `U : Ω → ℝ` without the bound (bli-paper-079) does
not support the convention's purpose (findings F-6).
Source: [[communication-trust-translated]] line 268 (the `[0,1]` bound); mandate T5(b)(iv)
Kind: N−
Fidelity: n/a (a two-point check outside any decision structure, which carries the bound as a field)
Hyps: none -/
theorem unbounded_scores_below_junk :
    condExpJunk (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ => -2) univ (-1) < -1 := by
  have hm : mass (fun _ : Fin 2 => (1 / 2 : ℝ)) univ = 1 := by
    simp [mass, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [condExpJunk_of_pos (by rw [hm]; norm_num), hm]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]

end Cleanroom.Udt.UdtCtExamples
