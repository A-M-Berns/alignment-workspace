import Cleanroom.Trust.LegitFiniteDefect.Defs
import Cleanroom.Trust.LegitFiniteDefect.Detection
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The defect sign derived from an update rule

Package `legit-finite-defect`, Target 5 (load-bearing 3; item 2-031). A corruption model over the
*belief-formation process*: binary target, finite signal type `S`, prior `p₀`, likelihoods `a`
(under `θ = 1`) and `b` (under `θ = 0`). The honest report is the Bayes posterior `p s`; the
`λ`-exaggerated report `q λ s` has posterior odds `= prior odds × (likelihood ratio)^λ`. The
**only corruption hypothesis is `1 < λ`**; the overstatement that round 1 assumed (`hover`) is
here a lemma (`p_lt_q_iff`, `p₀_lt_q_iff`), and the headline `defect_neg_of_exaggeration`
concludes that the report-gate defect at any threshold `t ≥ p₀` with positive fired mass is
strictly negative. Near-misses: `λ = 1` gives zero defect on every signal-measurable gate (Bayes
is calibrated — through Target 4(1)), and `0 < λ < 1` (numbing) flips the sign on the same gate.

Pre-registered fake (the source's): any `θ ≤ R` or `p ≤ q` hypothesis in the headline. None
appears. Register: finite Bayes; no LI object.
-/

namespace Cleanroom.Trust.LegitFiniteDefect.DerivedSign

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Trust.LegitFiniteDefect

noncomputable section

set_option linter.unusedSectionVars false

/-- The binary-target Bayes model: prior `p₀ ∈ (0, 1)`, positive likelihoods `a` (under `θ = 1`)
and `b` (under `θ = 0`) summing to one over the signal type. The two sum fields `a_sum`, `b_sum`
are carried for the model's meaning (they make `prior` a probability) and are **used by no
theorem** in this file: every sign result holds for arbitrary positive `a, b`.
Source: trust-lab-2-031; `run3/questions/scout-legitimacy.md` Q3; mandate Target 5
Kind: D
Fidelity: exact -/
structure Model (S : Type) [Fintype S] where
  /-- the prior probability of `θ = 1` -/
  p₀ : ℝ
  /-- the likelihood of each signal under `θ = 1` -/
  a : S → ℝ
  /-- the likelihood of each signal under `θ = 0` -/
  b : S → ℝ
  p₀_pos : 0 < p₀
  p₀_lt_one : p₀ < 1
  a_pos : ∀ s, 0 < a s
  b_pos : ∀ s, 0 < b s
  a_sum : ∑ s, a s = 1
  b_sum : ∑ s, b s = 1

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The target `θ` as a real variable on worlds `(θ, s)`.
Source: mandate Target 5
Kind: D
Fidelity: exact -/
def target : Bool × S → ℝ := fun x => if x.1 then 1 else 0

namespace Model

variable (M : Model S)

/-- The signal's marginal mass `m s = p₀ a s + (1 − p₀) b s`.
Source: mandate Target 5
Kind: D
Fidelity: exact -/
def m (s : S) : ℝ := M.p₀ * M.a s + (1 - M.p₀) * M.b s

/-- The honest report: the Bayes posterior `p s = p₀ a s / m s`.
Source: trust-lab-2-031 ("honest report `p(s)` = Bayes posterior")
Kind: D
Fidelity: exact -/
def p (s : S) : ℝ := M.p₀ * M.a s / M.m s

/-- The prior odds `p₀ / (1 − p₀)`.
Source: mandate Target 5
Kind: D
Fidelity: exact -/
def k : ℝ := M.p₀ / (1 - M.p₀)

/-- The `λ`-exaggerated posterior odds `k · (a s / b s)^λ` (`Real.rpow`).
Source: trust-lab-2-031 ("posterior odds = prior odds × likelihood-ratio^λ")
Kind: D
Fidelity: exact -/
def odds (l : ℝ) (s : S) : ℝ := M.k * (M.a s / M.b s) ^ l

/-- The `λ`-exaggerated report `q λ s = odds / (1 + odds)`.
Source: trust-lab-2-031 (corrupted report `q_λ(s)`)
Kind: D
Fidelity: exact -/
def q (l : ℝ) (s : S) : ℝ := M.odds l s / (1 + M.odds l s)

/-- The joint prior on worlds `(θ, s) : Bool × S`.
Source: mandate Target 5
Kind: D
Fidelity: exact -/
def prior : Bool × S → ℝ := fun x => if x.1 then M.p₀ * M.a x.2 else (1 - M.p₀) * M.b x.2


/-! ### Positivity, stated once -/

/-- Every denominator in the model is positive: `1 − p₀`, `m s`, the prior odds, the exaggerated
odds and `1 + odds`; and the prior is nonnegative.
Source: none: infrastructure (mandate: "positivity of every denominator is a lemma, stated once")
Kind: L
Fidelity: n/a -/
theorem pos (l : ℝ) (s : S) :
    0 < 1 - M.p₀ ∧ 0 < M.m s ∧ 0 < M.k ∧ 0 < M.odds l s ∧ 0 < 1 + M.odds l s := by
  have h1 : 0 < 1 - M.p₀ := by linarith [M.p₀_lt_one]
  have hm : 0 < M.m s := by
    unfold m
    have := M.a_pos s; have := M.b_pos s; have := M.p₀_pos
    positivity
  have hk : 0 < M.k := div_pos M.p₀_pos h1
  have ho : 0 < M.odds l s :=
    mul_pos hk (Real.rpow_pos_of_pos (div_pos (M.a_pos s) (M.b_pos s)) l)
  exact ⟨h1, hm, hk, ho, by linarith⟩

/-- The joint prior is nonnegative.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem prior_nonneg : ∀ x, 0 ≤ M.prior x := by
  intro x
  unfold prior
  split_ifs
  · exact (mul_pos M.p₀_pos (M.a_pos _)).le
  · exact (mul_pos (by linarith [M.p₀_lt_one]) (M.b_pos _)).le

/-- Multiplication by a positive constant preserves strict order (both directions).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mul_lt_mul_left_pos {k x y : ℝ} (hk : 0 < k) : k * x < k * y ↔ x < y :=
  ⟨fun h => lt_of_mul_lt_mul_left h hk.le, fun h => mul_lt_mul_of_pos_left h hk⟩

/-- The logistic map `o ↦ o / (1 + o)` is strictly increasing on positive odds.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem logistic_lt_iff {o o' : ℝ} (ho : 0 < o) (ho' : 0 < o') :
    o / (1 + o) < o' / (1 + o') ↔ o < o' := by
  rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 1 + o), div_mul_eq_mul_div,
    lt_div_iff₀ (by linarith : (0 : ℝ) < 1 + o')]
  constructor <;> intro h <;> nlinarith

/-- **`q 1 = p`**: at `λ = 1` the exaggerated report is the honest Bayes posterior.
Source: trust-lab-2-031 (3) (`λ = 1`)
Kind: L
Fidelity: exact -/
theorem q_one (s : S) : M.q 1 s = M.p s := by
  obtain ⟨h1, hm, _, _, _⟩ := M.pos 1 s
  have ha := M.a_pos s
  have hb := M.b_pos s
  have hp := M.p₀_pos
  unfold q odds k p
  rw [Real.rpow_one]
  unfold m at hm ⊢
  field_simp
  ring

/-- The prior in logistic form: `p₀ = k / (1 + k)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem p₀_eq_logistic : M.p₀ = M.k / (1 + M.k) := by
  have h1 : 0 < 1 - M.p₀ := by linarith [M.p₀_lt_one]
  unfold k
  field_simp
  ring

/-- **Sign lemma (1)** (`1 < λ`): the exaggerated report overstates the honest posterior exactly
where the likelihood ratio exceeds `1`, and understates it exactly where the ratio is below `1`.
Source: trust-lab-2-031 (1); `scout-legitimacy.md` Q3 (1)
Kind: P
Fidelity: exact
Hyps: (a) `1 < λ` -/
theorem p_lt_q_iff {l : ℝ} (hl : 1 < l) (s : S) :
    (M.p s < M.q l s ↔ 1 < M.a s / M.b s) ∧ (M.q l s < M.p s ↔ M.a s / M.b s < 1) := by
  obtain ⟨_, _, hk, ho1, _⟩ := M.pos 1 s
  obtain ⟨_, _, _, hol, _⟩ := M.pos l s
  have hr : 0 < M.a s / M.b s := div_pos (M.a_pos s) (M.b_pos s)
  rw [← M.q_one s]
  unfold q
  rw [logistic_lt_iff ho1 hol, logistic_lt_iff hol ho1]
  unfold odds
  rw [mul_lt_mul_left_pos hk, mul_lt_mul_left_pos hk, Real.rpow_one]
  rcases lt_trichotomy (M.a s / M.b s) 1 with hlt | heq | hgt
  · have h2 : (M.a s / M.b s) ^ l < M.a s / M.b s := by
      have := (Real.rpow_lt_rpow_left_iff_of_base_lt_one hr hlt).2 hl
      rwa [Real.rpow_one] at this
    have h1 : ¬ (M.a s / M.b s < (M.a s / M.b s) ^ l) := not_lt.2 h2.le
    exact ⟨⟨fun h => absurd h h1, fun h => absurd h (not_lt.2 hlt.le)⟩,
      ⟨fun _ => hlt, fun _ => h2⟩⟩
  · rw [heq, Real.one_rpow]
    simp
  · have h1 : M.a s / M.b s < (M.a s / M.b s) ^ l :=
      Real.self_lt_rpow_of_one_lt hgt hl
    exact ⟨⟨fun _ => hgt, fun _ => h1⟩,
      ⟨fun h => absurd h (not_lt.2 h1.le), fun h => absurd h (not_lt.2 hgt.le)⟩⟩

/-- **Sign lemma (2)** (`0 < λ`): the exaggerated report exceeds the prior exactly on the
favourable signals `b s < a s`.
Source: trust-lab-2-031 (2) (threshold `t ≥ prior`)
Kind: P
Fidelity: exact
Hyps: (a) `0 < λ` -/
theorem p₀_lt_q_iff {l : ℝ} (hl : 0 < l) (s : S) : M.p₀ < M.q l s ↔ M.b s < M.a s := by
  obtain ⟨_, _, hk, hol, _⟩ := M.pos l s
  have hr : 0 < M.a s / M.b s := div_pos (M.a_pos s) (M.b_pos s)
  rw [M.p₀_eq_logistic]
  unfold q
  rw [logistic_lt_iff hk hol]
  unfold odds
  rw [lt_mul_iff_one_lt_right hk, Real.one_lt_rpow_iff_of_pos hr, one_lt_div (M.b_pos s)]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact h
    · exact absurd hl (not_lt.2 h.le)
  · intro h
    exact Or.inl ⟨h, hl⟩

/-- **The fibre form** (a Target 4(1) instance over the signal type): for any report `R` read
through the signal and any signal-measurable gate `v ∘ snd`,
`defect prior target (R ∘ snd) (v ∘ snd) = ∑ s, v s · m s · (p s − R s)`.
Source: mandate Target 5 (3)
Kind: L
Fidelity: exact -/
theorem defect_fibre (R v : S → ℝ) :
    defect M.prior target (fun x => R x.2) (fun x => v x.2) =
      ∑ s, v s * M.m s * (M.p s - R s) := by
  rw [defect_decomp, Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro s _
  rw [Fintype.sum_bool]
  simp only [prior, target, Bool.false_eq_true, if_true, if_false]
  have hm := (M.pos 1 s).2.1
  unfold p
  unfold m at hm ⊢
  field_simp
  ring

/-- Signal-measurable gates fired above the threshold, in filter form.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem defect_threshold_gate (R : S → ℝ) (t : ℝ) :
    defect M.prior target (fun x => R x.2) (fun x => if t < R x.2 then 1 else 0) =
      ∑ s ∈ univ.filter (fun s => t < R s), M.m s * (M.p s - R s) := by
  rw [M.defect_fibre R (fun s => if t < R s then 1 else 0), Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s _
  split_ifs <;> ring

/-- **The derived sign.** For `1 < λ`, a threshold `t ≥ p₀`, the report gate `𝟙[t < q λ (snd ·)]`
and positive fired mass, the defect of the exaggerated report is strictly negative: the update
rule `1 < λ` is the only corruption hypothesis; the overstatement on the fired region is derived
(`p₀_lt_q_iff` then `p_lt_q_iff`).
Source: trust-lab-2-031 (2); `scout-legitimacy.md` Q3 (2); mandate Target 5 (load-bearing 3)
Kind: P
Fidelity: exact
Hyps: (a) `1 < λ`; (a) `p₀ ≤ t`; (a) positive fired mass `0 < ∑_{t < q λ s} m s` (without it the
gate is empty and the defect is `0`) -/
theorem defect_neg_of_exaggeration {l t : ℝ} (hl : 1 < l) (ht : M.p₀ ≤ t)
    (hmass : 0 < ∑ s ∈ univ.filter (fun s => t < M.q l s), M.m s) :
    defect M.prior target (fun x => M.q l x.2) (fun x => if t < M.q l x.2 then 1 else 0) < 0 := by
  rw [M.defect_threshold_gate]
  have hne : (univ.filter (fun s => t < M.q l s)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hmass
    exact lt_irrefl _ hmass
  apply Finset.sum_neg _ hne
  intro s hs
  rw [mem_filter] at hs
  have hq : M.p₀ < M.q l s := lt_of_le_of_lt ht hs.2
  have hab := (M.p₀_lt_q_iff (by linarith) s).1 hq
  have hpq : M.p s < M.q l s := (M.p_lt_q_iff hl s).1.2 ((one_lt_div (M.b_pos s)).2 hab)
  exact mul_neg_of_pos_of_neg (M.pos 1 s).2.1 (by linarith)

/-! ### Near-misses -/

/-- **`λ = 1`**: honest Bayes has zero defect on every signal-measurable gate, and is calibrated
(through Target 4(1): every report gate of `p ∘ snd` is signal-measurable).
Source: trust-lab-2-031 (3) (`λ = 1` ties to 2-030(1))
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem bayes_calibrated :
    (∀ v : S → ℝ, defect M.prior target (fun x => M.q 1 x.2) (fun x => v x.2) = 0) ∧
      Calibrated M.prior target (fun x => M.p x.2) := by
  constructor
  · intro v
    rw [M.defect_fibre]
    apply Finset.sum_eq_zero
    intro s _
    rw [M.q_one]; ring
  · rw [← endorses_reportGates_iff_calibrated M.prior_nonneg]
    rintro w ⟨_, hw⟩
    have hsnd : DeterminedBy Prod.snd w := fun x y h => hw x y (by simp only [h])
    obtain ⟨v, rfl⟩ := hsnd.exists_comp
    show defect M.prior target (fun x => M.p x.2) (fun x => v x.2) = 0
    rw [M.defect_fibre M.p v]
    apply Finset.sum_eq_zero
    intro s _
    ring

/-- **`0 < λ < 1` (numbing)**: on the same gate, with the same threshold and positive fired mass,
the defect is strictly positive — under-confidence flips the sign.
Source: trust-lab-2-031 (3) (`λ < 1` flips the sign)
Kind: P
Fidelity: exact
Hyps: (a) `0 < λ < 1`; (a) `p₀ ≤ t`; (a) positive fired mass -/
theorem defect_pos_of_numbing {l t : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (ht : M.p₀ ≤ t)
    (hmass : 0 < ∑ s ∈ univ.filter (fun s => t < M.q l s), M.m s) :
    0 < defect M.prior target (fun x => M.q l x.2) (fun x => if t < M.q l x.2 then 1 else 0) := by
  rw [M.defect_threshold_gate]
  have hne : (univ.filter (fun s => t < M.q l s)).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hmass
    exact lt_irrefl _ hmass
  apply Finset.sum_pos _ hne
  intro s hs
  rw [mem_filter] at hs
  have hq : M.p₀ < M.q l s := lt_of_le_of_lt ht hs.2
  have hab := (M.p₀_lt_q_iff hl0 s).1 hq
  have hr : 1 < M.a s / M.b s := (one_lt_div (M.b_pos s)).2 hab
  obtain ⟨_, hm, hk, ho1, _⟩ := M.pos 1 s
  obtain ⟨_, _, _, hol, _⟩ := M.pos l s
  have hqp : M.q l s < M.p s := by
    rw [← M.q_one s]
    unfold q
    rw [logistic_lt_iff hol ho1]
    unfold odds
    rw [mul_lt_mul_left_pos hk, Real.rpow_one]
    exact Real.rpow_lt_self_of_one_lt hr hl1
  exact mul_pos hm (by linarith)

end Model

/-! ## Witness -/

namespace Witness

/-- The witness model: `S = Fin 2`, `p₀ = 1/2`, `a = (3/4, 1/4)`, `b = (1/4, 3/4)`.
Source: mandate Target 5 (witness)
Kind: D
Fidelity: n/a -/
def Mw : Model (Fin 2) where
  p₀ := 1 / 2
  a := ![3 / 4, 1 / 4]
  b := ![1 / 4, 3 / 4]
  p₀_pos := by norm_num
  p₀_lt_one := by norm_num
  a_pos := fun s => by fin_cases s <;> norm_num
  b_pos := fun s => by fin_cases s <;> norm_num
  a_sum := by simp [Fin.sum_univ_two]; norm_num
  b_sum := by simp [Fin.sum_univ_two]; norm_num

/-- The witness values: `m ≡ 1/2`, honest posteriors `(3/4, 1/4)`, exaggerated (`λ = 2`) reports
`(9/10, 1/10)`.
Source: mandate Target 5 (witness: "`q 2 = 9/10 > 3/4 = p`")
Kind: L
Fidelity: n/a -/
theorem values :
    Mw.m 0 = 1 / 2 ∧ Mw.m 1 = 1 / 2 ∧ Mw.p 0 = 3 / 4 ∧ Mw.p 1 = 1 / 4 ∧
      Mw.q 2 0 = 9 / 10 ∧ Mw.q 2 1 = 1 / 10 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Model.m, Mw]; norm_num
  · simp [Model.m, Mw]; norm_num
  · simp [Model.p, Model.m, Mw]; norm_num
  · simp [Model.p, Model.m, Mw]; norm_num
  · simp [Model.q, Model.odds, Model.k, Mw] <;> norm_num
  · simp [Model.q, Model.odds, Model.k, Mw] <;> norm_num

/-- **Witness (`λ = 2`, `t = 1/2`).** The fired mass is `1/2` and the defect is `−3/40`.
Source: mandate Target 5 (witness); trust-lab-2-031
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exaggeration_instance :
    (∑ s ∈ univ.filter (fun s => (1 / 2 : ℝ) < Mw.q 2 s), Mw.m s) = 1 / 2 ∧
      defect Mw.prior target (fun x => Mw.q 2 x.2)
        (fun x => if (1 / 2 : ℝ) < Mw.q 2 x.2 then 1 else 0) = -3 / 40 := by
  obtain ⟨hm0, hm1, hp0, hp1, hq0, hq1⟩ := values
  constructor
  · rw [Finset.sum_filter, Fin.sum_univ_two, hq0, hq1, hm0, hm1]
    norm_num
  · rw [Mw.defect_threshold_gate, Finset.sum_filter, Fin.sum_univ_two, hq0, hq1, hm0, hm1, hp0,
      hp1]
    norm_num

/-- **Witness (`λ = 1/2`, `t = 1/2`)**: sign only (the value is irrational): the numbing report
has strictly positive defect on the same gate; the favourable signal fires because
`3^(1/2) > 1` gives `q > 1/2`.
Source: mandate Target 5 ("for `λ = 1/2` state the sign only")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem numbing_instance :
    0 < defect Mw.prior target (fun x => Mw.q (1 / 2) x.2)
      (fun x => if (1 / 2 : ℝ) < Mw.q (1 / 2) x.2 then 1 else 0) := by
  apply Mw.defect_pos_of_numbing (by norm_num) (by norm_num) (by norm_num [Mw])
  have hfire : (1 / 2 : ℝ) < Mw.q (1 / 2) 0 := by
    have hodds : Mw.odds (1 / 2) 0 = (3 : ℝ) ^ ((1 : ℝ) / 2) := by
      simp [Model.odds, Model.k, Mw] <;> norm_num
    have h3 : 1 < (3 : ℝ) ^ ((1 : ℝ) / 2) :=
      (Real.one_lt_rpow_iff_of_pos (by norm_num)).2 (Or.inl ⟨by norm_num, by norm_num⟩)
    unfold Model.q
    rw [hodds, lt_div_iff₀ (by linarith)]
    linarith
  have hmem : (0 : Fin 2) ∈ univ.filter (fun s => (1 / 2 : ℝ) < Mw.q (1 / 2) s) :=
    mem_filter.2 ⟨mem_univ _, hfire⟩
  have hm0 : Mw.m 0 = 1 / 2 := values.1
  calc (0 : ℝ) < Mw.m 0 := by rw [hm0]; norm_num
    _ ≤ ∑ s ∈ univ.filter (fun s => (1 / 2 : ℝ) < Mw.q (1 / 2) s), Mw.m s :=
        Finset.single_le_sum (fun s _ => (Mw.pos 1 s).2.1.le) hmem

end Witness

end

end Cleanroom.Trust.LegitFiniteDefect.DerivedSign
