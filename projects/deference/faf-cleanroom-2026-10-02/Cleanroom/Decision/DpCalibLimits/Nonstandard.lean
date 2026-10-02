import Cleanroom.Decision.DpCalibLimits.Rays
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Algebra.Polynomial.Div

/-!
# T3(a),(b) — Nonstandard labels in polynomial coordinates: the bridge lemma and the
quantifier shift

[[dp-calib-limits-mandate]] T3 (dp-sl-2-021, P07 I1′, S21).

* **The bridge lemma** `nonnegNear0_iff_eventually`: a polynomial is `NonnegNear0` (zero, or
  positive trailing coefficient) iff it is non-negative on some interval `(0, ε₀)`. This is
  the whole content of "the sign of a rational function near `0⁺` is its order in `ℝ(ε)`":
  every ∃-small-`ε` device reduces to it. No Archimedean hypothesis is needed (the mandate
  expected one): `ε₀` is `min 1 (c / (M + 1))` with `M` a coefficient bound.
* **Proposition (i) in polynomial coordinates** `eventTremble_iff_nonnegNear0`: the
  fixed-procedure device D2 (FF) holds iff, at every queried point with tremble-realizable
  observation and some tremble-realizable act event, every supported act's event is
  tremble-realizable and, against every tremble-realizable act, the cross-multiplied
  polynomial `payPoly a · nuPoly b − payPoly b · nuPoly a` is `NonnegNear0` — the standard
  label is a best reply at the state strictly calibrated to `C^ε` for every positive
  infinitesimal `ε`. The escape clause is `ε`-free (`exists_nuPoly_ne_zero_iff_exists_pos`,
  the mandate's trap), and the uniform `ε₀` over the finitely many `(d, a, b)` is a finite
  minimum (`eventually_forall_finset`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibLimits

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Finset

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-! ## Eventually near `0⁺` -/

/-- "Eventually near `0⁺`" is closed under finite conjunction: one `ε₀` for a finite family.
Source: none: infrastructure (mandate T3(b): "one `ε₀` by taking a minimum")
Kind: L -/
theorem eventually_forall_finset {α : Type} (S : Finset α) (P : α → K → Prop)
    (h : ∀ i ∈ S, ∃ ε₀ > (0 : K), ∀ ε, 0 < ε → ε < ε₀ → P i ε) :
    ∃ ε₀ > (0 : K), ∀ ε, 0 < ε → ε < ε₀ → ∀ i ∈ S, P i ε := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun _ _ _ _ h => by simp at h⟩
  | insert j S hj ih =>
    obtain ⟨ε₁, hε₁, h₁⟩ := h j (Finset.mem_insert_self j S)
    obtain ⟨ε₂, hε₂, h₂⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun ε h0 hε i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact h₁ ε h0 (lt_of_lt_of_le hε (min_le_left _ _))
    · exact h₂ ε h0 (lt_of_lt_of_le hε (min_le_right _ _)) i hi

/-! ## The bridge lemma -/

/-- A coefficient bound on `|p.eval ε|` for `0 ≤ ε ≤ 1`: the sum of the absolute coefficients.
Source: none: infrastructure. Kind: L -/
theorem abs_eval_le_sum_abs_coeff (p : Polynomial K) (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    |p.eval ε| ≤ ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| := by
  rw [Polynomial.eval_eq_sum_range]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul, abs_pow, abs_of_nonneg h0]
  calc |p.coeff i| * ε ^ i ≤ |p.coeff i| * 1 :=
        mul_le_mul_of_nonneg_left (pow_le_one₀ h0 h1) (abs_nonneg _)
    _ = |p.coeff i| := mul_one _

/-- **A polynomial with positive trailing coefficient is positive on some `(0, ε₀)`.** Write
`p = X^k · (c + X · q)` with `c = trailingCoeff p > 0`; on `(0, min 1 (c/(M+1)))`, `M` the
coefficient bound of `q`, `|ε · q(ε)| < c`.
Source: P07 I1′ ("sign of a rational function near `0⁺` = its order in `ℝ(ε)`"); mandate §3.4
Kind: P
Fidelity: exact -/
theorem eval_pos_near0 {p : Polynomial K} (hp : 0 < p.trailingCoeff) :
    ∃ ε₀ > (0 : K), ∀ ε, 0 < ε → ε < ε₀ → 0 < p.eval ε := by
  have hne : p ≠ 0 := fun h => by rw [h, Polynomial.trailingCoeff_zero] at hp; exact lt_irrefl 0 hp
  -- `p = X^k * q` with `q.coeff 0 = trailingCoeff p`
  obtain ⟨q, hq⟩ : Polynomial.X ^ p.natTrailingDegree ∣ p :=
    Polynomial.X_pow_dvd_iff.mpr fun d hd => Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hd
  have hq0 : q.coeff 0 = p.trailingCoeff := by
    have := congrArg (fun r : Polynomial K => r.coeff p.natTrailingDegree) hq
    rw [Polynomial.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self] at this
    rw [Polynomial.trailingCoeff]; exact this.symm
  -- `q = X * q' + C c`
  set q' := q.divX with hq'
  have hsplit : q = Polynomial.X * q' + Polynomial.C (q.coeff 0) := (Polynomial.X_mul_divX_add q).symm
  set M := ∑ i ∈ Finset.range (q'.natDegree + 1), |q'.coeff i| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨min 1 (p.trailingCoeff / (M + 1)), lt_min one_pos (div_pos hp (by linarith)), ?_⟩
  intro ε hε hε₀
  have hε1 : ε ≤ 1 := (lt_of_lt_of_le hε₀ (min_le_left _ _)).le
  have hεM : ε * (M + 1) < p.trailingCoeff := by
    have := lt_of_lt_of_le hε₀ (min_le_right _ _)
    rwa [lt_div_iff₀ (by linarith)] at this
  have hbound : |ε * q'.eval ε| ≤ ε * M := by
    rw [abs_mul, abs_of_pos hε]
    exact mul_le_mul_of_nonneg_left (abs_eval_le_sum_abs_coeff q' ε hε.le hε1) hε.le
  have hqpos : 0 < q.eval ε := by
    rw [hsplit, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C, hq0]
    have := (abs_le.mp hbound).1
    nlinarith
  rw [hq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  exact mul_pos (pow_pos hε _) hqpos

/-- `trailingCoeff (-p) = -trailingCoeff p`. Source: none: infrastructure. Kind: L -/
theorem trailingCoeff_neg' (p : Polynomial K) : (-p).trailingCoeff = -p.trailingCoeff := by
  rw [Polynomial.trailingCoeff, Polynomial.trailingCoeff, Polynomial.natTrailingDegree_neg,
    Polynomial.coeff_neg]

/-- **The bridge lemma**: `NonnegNear0 p` iff `p` is non-negative on some `(0, ε₀)`.
Source: P07 I1′ ("sign of a rational function near `0⁺` = its order in `ℝ(ε)`"); mandate
§3.4 (`nonnegNear0_iff_eventually`)
Kind: P
Fidelity: exact (polynomial coordinates for `ℝ(ε)`; no Archimedean hypothesis needed)
Hyps: none -/
theorem nonnegNear0_iff_eventually (p : Polynomial K) :
    NonnegNear0 p ↔ ∃ ε₀ > (0 : K), ∀ ε, 0 < ε → ε < ε₀ → 0 ≤ p.eval ε := by
  constructor
  · rintro (h | h)
    · exact ⟨1, one_pos, fun ε _ _ => by rw [h, Polynomial.eval_zero]⟩
    · obtain ⟨ε₀, hε₀, hpos⟩ := eval_pos_near0 h
      exact ⟨ε₀, hε₀, fun ε h0 h1 => (hpos ε h0 h1).le⟩
  · rintro ⟨ε₀, hε₀, hnn⟩
    by_cases hp : p = 0
    · exact Or.inl hp
    · right
      rcases lt_trichotomy 0 p.trailingCoeff with hpos | hzero | hneg
      · exact hpos
      · exact absurd hzero.symm (Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr hp)
      · exfalso
        have hneg' : 0 < (-p).trailingCoeff := by rw [trailingCoeff_neg']; linarith
        obtain ⟨ε₁, hε₁, hpos⟩ := eval_pos_near0 hneg'
        have hε : 0 < min ε₀ ε₁ / 2 := by positivity
        have h1 := hnn _ hε (by
          calc min ε₀ ε₁ / 2 < min ε₀ ε₁ := by linarith [lt_min hε₀ hε₁]
            _ ≤ ε₀ := min_le_left _ _)
        have h2 := hpos _ hε (by
          calc min ε₀ ε₁ / 2 < min ε₀ ε₁ := by linarith [lt_min hε₀ hε₁]
            _ ≤ ε₁ := min_le_right _ _)
        rw [Polynomial.eval_neg] at h2
        linarith

/-- The strict form: positive trailing coefficient iff positive on some `(0, ε₀)`.
Source: P07 I1′. Kind: L -/
theorem trailingCoeff_pos_iff_eventually_pos (p : Polynomial K) :
    0 < p.trailingCoeff ↔ ∃ ε₀ > (0 : K), ∀ ε, 0 < ε → ε < ε₀ → 0 < p.eval ε := by
  constructor
  · exact eval_pos_near0
  · rintro ⟨ε₀, hε₀, hpos⟩
    have hnn : NonnegNear0 p := (nonnegNear0_iff_eventually p).mpr
      ⟨ε₀, hε₀, fun ε h0 h1 => (hpos ε h0 h1).le⟩
    rcases hnn with h | h
    · exfalso
      have := hpos (ε₀ / 2) (by positivity) (by linarith)
      rw [h, Polynomial.eval_zero] at this
      exact lt_irrefl 0 this
    · exact h

/-! ## Proposition (i): D2 in polynomial coordinates -/

section propI

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]
  (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω) (C : Proc ι acts K)
  (B : Tree Ω ι acts K)

/-- A positive trembled mass at one `ε` forces `nuPoly ≠ 0`.
Source: none: infrastructure. Kind: L -/
theorem nuPoly_ne_zero_of_nu_tremble_pos (X : Finset Ω) (ε : K) (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (h : 0 < nu (tremble C ε h0 h1) B X) : nuPoly C B X ≠ 0 := by
  intro hz
  rw [← eval_nuPoly C B X ε h0 h1, hz, Polynomial.eval_zero] at h
  exact lt_irrefl 0 h

/-- **The escape clause is `ε`-free**: some act event within `O_d` is realized under `C^ε` at
one (equivalently every) `ε ∈ (0, 1]` iff some `nuPoly (b ∧ O_d) ≠ 0`.
Source: mandate T3(b) (the trap: "the D2 escape clause is `ε`-dependent as written")
Kind: L -/
theorem exists_nuPoly_ne_zero_iff_exists_pos (d : ι) (ε : K) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    (∃ b, nuPoly C B (actEv d b ∩ obs d) ≠ 0) ↔
      ∃ b, 0 < nu (tremble C ε h0.le h1) B (actEv d b ∩ obs d) := by
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨b, (nuPoly_ne_zero_iff_forall_pos C B _).mp hb ε h0 h1⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, nuPoly_ne_zero_of_nu_tremble_pos C B _ ε h0.le h1 hb⟩

/-- The cross-multiplied comparison polynomial of two act events.
Source: mandate T3(b). Kind: D -/
noncomputable def crossPoly (Y Z : Finset Ω) : Polynomial K :=
  payPoly C B Y * nuPoly C B Z - payPoly C B Z * nuPoly C B Y

/-- At `ε ∈ (0,1]` with both trembled masses positive, the D2 comparison is the sign of the
cross polynomial. Source: none: infrastructure. Kind: L -/
theorem condExp_le_iff_crossPoly (Y Z : Finset Ω) (ε : K) (h0 : 0 < ε) (h1 : ε ≤ 1)
    (hY : 0 < nu (tremble C ε h0.le h1) B Y) (hZ : 0 < nu (tremble C ε h0.le h1) B Z) :
    condExp (tremble C ε h0.le h1) B Z ≤ condExp (tremble C ε h0.le h1) B Y ↔
      0 ≤ (crossPoly C B Y Z).eval ε := by
  unfold condExp crossPoly
  rw [div_le_div_iff₀ hZ hY, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul,
    eval_payPoly, eval_payPoly, eval_nuPoly, eval_nuPoly, sub_nonneg]

/-- **Proposition (i) in polynomial coordinates** (P07 I1′): the fixed-procedure device D2
(FF) holds for `C` on `B` iff at every queried `d` with tremble-realizable `O_d` and some
tremble-realizable act event, every supported act `a` has `nuPoly (a ∧ O_d) ≠ 0` and, against
every `b` with `nuPoly (b ∧ O_d) ≠ 0`, the cross polynomial
`payPoly (a ∧ O_d) · nuPoly (b ∧ O_d) − payPoly (b ∧ O_d) · nuPoly (a ∧ O_d)` is
`NonnegNear0` — i.e. the standard label is a best reply at the state strictly calibrated to
`C^ε` for every positive infinitesimal `ε`. The escape clause is `ε`-free
(`exists_nuPoly_ne_zero_iff_exists_pos`); the uniform `ε₀` is a finite minimum.
Source: P07 I1′ Proposition (i) ("`C` is tremble-consistent in Remark 3.12's fixed-procedure
sense iff the standard label `C(d)` is a best reply at the state strictly calibrated to `C^ε`
for every positive infinitesimal `ε`"); dp-sl-2-021; S21
Kind: C
Fidelity: exact up to §3.4's polynomial coordinates (D2's domain convention)
Hyps: none -/
theorem eventTremble_iff_nonnegNear0 :
    EventTrembleEdtConsistent obs actEv C B ↔
      ∀ d ∈ queried B, nuPoly C B (obs d) ≠ 0 → (∃ b, nuPoly C B (actEv d b ∩ obs d) ≠ 0) →
        ∀ a, 0 < (C d).w a → nuPoly C B (actEv d a ∩ obs d) ≠ 0 ∧
          ∀ b, nuPoly C B (actEv d b ∩ obs d) ≠ 0 →
            NonnegNear0 (crossPoly C B (actEv d a ∩ obs d) (actEv d b ∩ obs d)) := by
  constructor
  · rintro ⟨ε₀, hε₀, hD2⟩ d hd hO hex a ha
    -- a convenient `ε` in `(0, min ε₀ 1)`
    have hεm : 0 < min ε₀ 1 / 2 := by positivity
    have hεlt : min ε₀ 1 / 2 < ε₀ := by
      calc min ε₀ 1 / 2 < min ε₀ 1 := by linarith [lt_min hε₀ one_pos]
        _ ≤ ε₀ := min_le_left _ _
    have hεle : min ε₀ 1 / 2 ≤ 1 := by
      calc min ε₀ 1 / 2 ≤ min ε₀ 1 := by linarith [lt_min hε₀ one_pos]
        _ ≤ 1 := min_le_right _ _
    have hexε := (exists_nuPoly_ne_zero_iff_exists_pos obs actEv C B d _ hεm hεle).mp hex
    have hposa : 0 < nu (tremble C _ hεm.le hεle) B (actEv d a ∩ obs d) :=
      (hD2 _ hεm hεle hεlt d hd hO hexε a ha).1
    refine ⟨nuPoly_ne_zero_of_nu_tremble_pos C B _ _ hεm.le hεle hposa, fun b hb => ?_⟩
    rw [nonnegNear0_iff_eventually]
    refine ⟨min ε₀ 1, lt_min hε₀ one_pos, fun ε h0 hε => ?_⟩
    have hεlt' : ε < ε₀ := lt_of_lt_of_le hε (min_le_left _ _)
    have hεle' : ε ≤ 1 := (lt_of_lt_of_le hε (min_le_right _ _)).le
    have hexε' := (exists_nuPoly_ne_zero_iff_exists_pos obs actEv C B d ε h0 hεle').mp hex
    obtain ⟨hpa, hcmp⟩ := hD2 ε h0 hεle' hεlt' d hd hO hexε' a ha
    have hpb : 0 < nu (tremble C ε h0.le hεle') B (actEv d b ∩ obs d) :=
      (nuPoly_ne_zero_iff_forall_pos C B _).mp hb ε h0 hεle'
    exact (condExp_le_iff_crossPoly C B _ _ ε h0 hεle' hpa hpb).mp (hcmp b hpb)
  · intro h
    -- one `ε₀` for all `(d, a, b)`
    have key : ∀ d ∈ queried B, ∃ ε₀ > (0 : K), ∀ ε, 0 < ε → ε < ε₀ →
        ∀ a ∈ (Finset.univ : Finset (acts d)), ∀ b ∈ (Finset.univ : Finset (acts d)),
          nuPoly C B (obs d) ≠ 0 → (∃ b, nuPoly C B (actEv d b ∩ obs d) ≠ 0) →
          0 < (C d).w a → nuPoly C B (actEv d b ∩ obs d) ≠ 0 →
          0 ≤ (crossPoly C B (actEv d a ∩ obs d) (actEv d b ∩ obs d)).eval ε := by
      intro d hd
      apply eventually_forall_finset Finset.univ
      intro a _
      apply eventually_forall_finset Finset.univ
      intro b _
      by_cases hg : nuPoly C B (obs d) ≠ 0 ∧ (∃ b, nuPoly C B (actEv d b ∩ obs d) ≠ 0) ∧
          0 < (C d).w a ∧ nuPoly C B (actEv d b ∩ obs d) ≠ 0
      · obtain ⟨hO, hex, ha, hb⟩ := hg
        obtain ⟨ε₀, hε₀, hev⟩ :=
          (nonnegNear0_iff_eventually _).mp ((h d hd hO hex a ha).2 b hb)
        exact ⟨ε₀, hε₀, fun ε h0 hε _ _ _ _ => hev ε h0 hε⟩
      · refine ⟨1, one_pos, fun ε _ _ hO hex ha hb => ?_⟩
        exact absurd ⟨hO, hex, ha, hb⟩ hg
    obtain ⟨ε₀, hε₀, hall⟩ := eventually_forall_finset (queried B) _ key
    refine ⟨ε₀, hε₀, fun ε h0 h1 hε d hd hO hexε a ha => ?_⟩
    have hex := (exists_nuPoly_ne_zero_iff_exists_pos obs actEv C B d ε h0 h1).mpr hexε
    obtain ⟨hpa, hcross⟩ := h d hd hO hex a ha
    have hposa : 0 < nu (tremble C ε h0.le h1) B (actEv d a ∩ obs d) :=
      (nuPoly_ne_zero_iff_forall_pos C B _).mp hpa ε h0 h1
    refine ⟨hposa, fun b hposb => ?_⟩
    have hb : nuPoly C B (actEv d b ∩ obs d) ≠ 0 :=
      nuPoly_ne_zero_of_nu_tremble_pos C B _ ε h0.le h1 hposb
    rw [condExp_le_iff_crossPoly C B _ _ ε h0 h1 hposa hposb]
    exact hall ε h0 hε d hd a (Finset.mem_univ _) b (Finset.mem_univ _) hO hex ha hb

end propI

end Cleanroom.Decision.DpCalibLimits
