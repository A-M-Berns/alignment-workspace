/-
# Certificate bounds: margin ⇒ agreement, override, defect, advantage, and the grade register

Source: `prompts/2026-08-11-deference-certificates/REPORT.md` §1.2 (L1, L2, L3, L7) and
§1.3 (Theorem C′), with the inhabitation witness of that report's §6.1 (the worked
shutdown/correction case, also carried as data in that round's `worked-case.json`).

Finite, exact-rational, order-and-arithmetic only. The trust relation **(TR-ε)** —
`E_P[η] ≤ ε` — is a named hypothesis of every statement that uses it (`AGENTS.md`
standard 4); the source's §4.1 records that nothing in the corpus supplies it, and nothing
here changes that.

**Not ported, deliberately.** Theorem C's V-register comparator clause and the `2M`
delegation bridge (source L4, L5, L6) rest on the movement hypothesis (MV-M), the uniform
grade-to-quantity relation this phase exists to replace. Promoting them would give kernel
status to a hypothesis whose shape is expected to change.

Provisional names (`AGENTS.md` §6): `gradeValuation`, `gatedAct`, `defect`, `advantage`,
`margin_forces_agreement`, `selection_eq_of_margin`, `override_bound`, `defect_bound`,
`advantage_estimate`, `gradeRegister_strict`.
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace Workspace.Deference.Contrib.CertificateBounds

open Finset

variable {Ω P : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq P]

/-- `G_n(c)`, the grade-register valuation of the source's §1.1. Used with the principal's
grade `v⁺` and also with the model's grade `v̂⁺`. -/
def gradeValuation (p : Ω → ℚ) (v : Ω → P → ℚ) (sel : Ω → P) : ℚ :=
  ∑ ω, p ω * v ω (sel ω)

/-- `ACT[j,S]` of the source's §1.1: take `j` on the certified event `S`, follow the
principal's selection off it. -/
def gatedAct (S : Finset Ω) (j : P) (J : Ω → P) : Ω → P :=
  fun ω => if ω ∈ S then j else J ω

/-- `D_{n,j}`, the certified-region defect of the source's §1.1: the principal's grade
advantage over `j`, integrated over the certified event. -/
def defect (p : Ω → ℚ) (v : Ω → P → ℚ) (J : Ω → P) (j : P) (S : Finset Ω) : ℚ :=
  ∑ ω ∈ S, p ω * (v ω (J ω) - v ω j)

/-- `Γ_n(π)`, the delegation advantage of the source's §1.1: `G_n(DELEGATE) − G_n(FIXED[π])`.
Applied to `(v, J)` it is `Γ_n`; applied to the model's grade and induced choice it is
the decision-time estimate
`Γ̂_n`. -/
def advantage (p : Ω → ℚ) (v : Ω → P → ℚ) (J : Ω → P) (π : P) : ℚ :=
  gradeValuation p v J - gradeValuation p v (fun _ => π)

/-! ## L1 — margin implies agreement -/

omit [Fintype Ω] [DecidableEq Ω] [DecidableEq P] in
/-- **L1.** Source: `prompts/2026-08-11-deference-certificates/REPORT.md` §1.2.

At a state where the model's predicted margin for `j` exceeds twice the model's grade
error, `j` is the *strict* maximizer of the principal's own grade. Uniqueness is
established, not assumed: no tie-break is consulted. -/
theorem margin_forces_agreement {v vh : P → ℚ} {j : P} {η γ : ℚ}
    (herr : ∀ π, |v π - vh π| ≤ η)
    (hmargin : ∀ π, π ≠ j → vh π + γ ≤ vh j)
    (hγ : 2 * η < γ) :
    ∀ π, π ≠ j → v π < v j := by
  intro π hπ
  have h1 := (abs_le.mp (herr j)).1
  have h2 := (abs_le.mp (herr π)).2
  have h3 := hmargin π hπ
  linarith

omit [Fintype Ω] [DecidableEq Ω] [DecidableEq P] in
/-- **L1, in the form the later lemmas use.** Any maximizer of the principal's grade at
such a state *is* `j`. -/
theorem selection_eq_of_margin {v vh : P → ℚ} {j J : P} {η γ : ℚ}
    (herr : ∀ π, |v π - vh π| ≤ η)
    (hmargin : ∀ π, π ≠ j → vh π + γ ≤ vh j)
    (hγ : 2 * η < γ)
    (hJ : ∀ π, v π ≤ v J) :
    J = j := by
  by_contra h
  exact absurd (hJ j) (not_le.mpr (margin_forces_agreement herr hmargin hγ J h))

/-! ## L2 — the override bound -/

omit [DecidableEq Ω] in
/-- **L2.** Source: same report, §1.2. Under (TR-ε), the principal overrides `j` on at most
`2ε/γ` of the credence inside a certified event of margin `γ`.

`hTR` is (TR-ε) itself; the constant `2` is the one L1 supplies and the source's §6.6
records it as sharp but unattained, which is not formalized here. -/
theorem override_bound {p η : Ω → ℚ} {v vh : Ω → P → ℚ} {J : Ω → P} {j : P}
    {S : Finset Ω} {γ ε : ℚ}
    (hp : ∀ ω, 0 ≤ p ω) (hη : ∀ ω, 0 ≤ η ω)
    (herr : ∀ ω π, |v ω π - vh ω π| ≤ η ω)
    (hmargin : ∀ ω ∈ S, ∀ π, π ≠ j → vh ω π + γ ≤ vh ω j)
    (hJ : ∀ ω π, v ω π ≤ v ω (J ω))
    (hγ : 0 < γ)
    (hTR : ∑ ω, p ω * η ω ≤ ε) :
    ∑ ω ∈ S.filter (fun ω => J ω ≠ j), p ω ≤ 2 * ε / γ := by
  have hbad : ∀ ω ∈ S.filter (fun ω => J ω ≠ j), γ ≤ 2 * η ω := by
    intro ω hω
    obtain ⟨hωS, hωJ⟩ := Finset.mem_filter.mp hω
    by_contra h
    exact hωJ (selection_eq_of_margin (herr ω) (hmargin ω hωS) (not_le.mp h) (hJ ω))
  have step : γ * ∑ ω ∈ S.filter (fun ω => J ω ≠ j), p ω ≤ 2 * ∑ ω, p ω * η ω := by
    rw [Finset.mul_sum, Finset.mul_sum]
    calc ∑ ω ∈ S.filter (fun ω => J ω ≠ j), γ * p ω
        ≤ ∑ ω ∈ S.filter (fun ω => J ω ≠ j), 2 * (p ω * η ω) := by
          refine Finset.sum_le_sum fun ω hω => ?_
          nlinarith [hbad ω hω, hp ω]
      _ ≤ ∑ ω, 2 * (p ω * η ω) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
          intro ω _ _
          have := mul_nonneg (hp ω) (hη ω)
          linarith
  rw [le_div_iff₀ hγ]
  nlinarith [step, hTR]

/-! ## L3 — the defect bound -/

omit [DecidableEq Ω] in
/-- **L3.** Source: same report, §1.2. Under (TR-ε), the certified-region defect is at most
`4Bε/(2B+γ)`. The source records the constant as sharp and attained (§6.5), which is not
formalized here.

The pointwise step is `(2B+γ)·d ≤ γ·2B + 2B·(2η−γ) = 4Bη`, using `d ≤ 2B` from the carrier
bound and `d ≤ 2η−γ` from the margin — the second available only because L1 puts the
disagreement states inside `{2η ≥ γ}`. -/
theorem defect_bound {p η : Ω → ℚ} {v vh : Ω → P → ℚ} {J : Ω → P} {j : P}
    {S : Finset Ω} {γ ε B : ℚ}
    (hp : ∀ ω, 0 ≤ p ω) (hη : ∀ ω, 0 ≤ η ω)
    (herr : ∀ ω π, |v ω π - vh ω π| ≤ η ω)
    (hbound : ∀ ω π, |v ω π| ≤ B)
    (hmargin : ∀ ω ∈ S, ∀ π, π ≠ j → vh ω π + γ ≤ vh ω j)
    (hJ : ∀ ω π, v ω π ≤ v ω (J ω))
    (hB : 0 < B) (hγ : 0 ≤ γ)
    (hTR : ∑ ω, p ω * η ω ≤ ε) :
    defect p v J j S ≤ 4 * B * ε / (2 * B + γ) := by
  have hden : 0 < 2 * B + γ := by linarith
  have pointwise : ∀ ω ∈ S,
      (2 * B + γ) * (p ω * (v ω (J ω) - v ω j)) ≤ 4 * B * (p ω * η ω) := by
    intro ω hω
    have hd0 : 0 ≤ v ω (J ω) - v ω j := by linarith [hJ ω j]
    have hkey : (2 * B + γ) * (v ω (J ω) - v ω j) ≤ 4 * B * η ω := by
      by_cases hJj : J ω = j
      · rw [hJj]
        have := mul_nonneg (le_of_lt hB) (hη ω)
        nlinarith [hη ω]
      · have h2B : v ω (J ω) - v ω j ≤ 2 * B := by
          have hu := (abs_le.mp (hbound ω (J ω))).2
          have hl := (abs_le.mp (hbound ω j)).1
          linarith
        have hmg : v ω (J ω) - v ω j ≤ 2 * η ω - γ := by
          have h1 := (abs_le.mp (herr ω (J ω))).2
          have h2 := (abs_le.mp (herr ω j)).1
          have h3 := hmargin ω hω (J ω) hJj
          linarith
        nlinarith
    nlinarith [hp ω]
  have hsum : (2 * B + γ) * defect p v J j S ≤ 4 * B * ∑ ω, p ω * η ω := by
    unfold defect
    rw [Finset.mul_sum, Finset.mul_sum]
    calc ∑ ω ∈ S, (2 * B + γ) * (p ω * (v ω (J ω) - v ω j))
        ≤ ∑ ω ∈ S, 4 * B * (p ω * η ω) := Finset.sum_le_sum pointwise
      _ ≤ ∑ ω, 4 * B * (p ω * η ω) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
          intro ω _ _
          have := mul_nonneg (hp ω) (hη ω)
          nlinarith
  rw [le_div_iff₀ hden]
  nlinarith [hsum, hTR]

/-! ## L7 — the advantage estimate -/

omit [DecidableEq Ω] [DecidableEq P] in
/-- **L7.** Source: same report, §1.2. Under (TR-ε), the decision-time estimate `Γ̂_n(π)` of
the delegation advantage is within `2ε` of the realized `Γ_n(π)`: both the grade of the
selected intervention and the grade of the comparator move by at most `η`. -/
theorem advantage_estimate {p η : Ω → ℚ} {v vh : Ω → P → ℚ} {J Jhat : Ω → P} {π : P} {ε : ℚ}
    (hp : ∀ ω, 0 ≤ p ω)
    (herr : ∀ ω π, |v ω π - vh ω π| ≤ η ω)
    (hJ : ∀ ω π, v ω π ≤ v ω (J ω))
    (hJhat : ∀ ω π, vh ω π ≤ vh ω (Jhat ω))
    (hTR : ∑ ω, p ω * η ω ≤ ε) :
    |advantage p v J π - advantage p vh Jhat π| ≤ 2 * ε := by
  have hrw : advantage p v J π - advantage p vh Jhat π
      = ∑ ω, p ω * ((v ω (J ω) - v ω π) - (vh ω (Jhat ω) - vh ω π)) := by
    simp only [advantage, gradeValuation, mul_sub, Finset.sum_sub_distrib]
  have pointwise : ∀ ω : Ω,
      |(v ω (J ω) - v ω π) - (vh ω (Jhat ω) - vh ω π)| ≤ 2 * η ω := by
    intro ω
    have hmax : |v ω (J ω) - vh ω (Jhat ω)| ≤ η ω := by
      rw [abs_le]
      constructor
      · have h1 := (abs_le.mp (herr ω (Jhat ω))).1
        have h2 := hJ ω (Jhat ω)
        linarith
      · have h1 := (abs_le.mp (herr ω (J ω))).2
        have h2 := hJhat ω (J ω)
        linarith
    have hcmp := herr ω π
    have hm := abs_le.mp hmax
    have hc := abs_le.mp hcmp
    rw [abs_le]
    constructor <;> linarith [hm.1, hm.2, hc.1, hc.2]
  rw [hrw]
  calc |∑ ω, p ω * ((v ω (J ω) - v ω π) - (vh ω (Jhat ω) - vh ω π))|
      ≤ ∑ ω, |p ω * ((v ω (J ω) - v ω π) - (vh ω (Jhat ω) - vh ω π))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ ω, p ω * (2 * η ω) := by
        refine Finset.sum_le_sum fun ω _ => ?_
        rw [abs_mul, abs_of_nonneg (hp ω)]
        exact mul_le_mul_of_nonneg_left (pointwise ω) (hp ω)
    _ ≤ 2 * ε := by
        rw [show ∑ ω, p ω * (2 * η ω) = 2 * ∑ ω, p ω * η ω by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun ω _ => by ring]
        linarith

/-! ## Theorem C′ — the grade register -/

omit [DecidableEq P] in
/-- The gated act's grade valuation is the delegate's, less the defect. An identity: no
hypothesis. -/
theorem gatedAct_gradeValuation (p : Ω → ℚ) (v : Ω → P → ℚ) (J : Ω → P) (j : P)
    (S : Finset Ω) :
    gradeValuation p v (gatedAct S j J) = gradeValuation p v J - defect p v J j S := by
  have h : ∀ ω : Ω, p ω * v ω (gatedAct S j J ω)
      = p ω * v ω (J ω) - (if ω ∈ S then p ω * (v ω (J ω) - v ω j) else 0) := by
    intro ω
    by_cases hω : ω ∈ S <;> simp [gatedAct, hω]
    ring
  simp only [gradeValuation, h, Finset.sum_sub_distrib, defect]
  congr 1
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- **Theorem C′, the grade register.** Source:
`prompts/2026-08-11-deference-certificates/REPORT.md` §1.3.

Under (TR-ε) *alone* — no settlement hypothesis, no movement term — a decision-time
certificate consisting of the margin `γ` on `S` plus the estimated advantage clause
`Γ̂_n(π) > 2ε + 4Bε/(2B+γ)` implies that the gated act strictly beats the fixed comparator
`π` in the grade register.

Two things the statement does not say, both from the source's §4.8. `G_n` makes `DELEGATE`
a maximizer by construction, so the theorem measures how much preemption is affordable, not
that deference is profitable; and the strictness lives entirely in `hcert`, which is an
assumed decision-time observation. -/
theorem gradeRegister_strict {p η : Ω → ℚ} {v vh : Ω → P → ℚ} {J Jhat : Ω → P} {j π : P}
    {S : Finset Ω} {γ ε B : ℚ}
    (hp : ∀ ω, 0 ≤ p ω) (hη : ∀ ω, 0 ≤ η ω)
    (herr : ∀ ω π, |v ω π - vh ω π| ≤ η ω)
    (hbound : ∀ ω π, |v ω π| ≤ B)
    (hmargin : ∀ ω ∈ S, ∀ π, π ≠ j → vh ω π + γ ≤ vh ω j)
    (hJ : ∀ ω π, v ω π ≤ v ω (J ω))
    (hJhat : ∀ ω π, vh ω π ≤ vh ω (Jhat ω))
    (hB : 0 < B) (hγ : 0 ≤ γ)
    (hTR : ∑ ω, p ω * η ω ≤ ε)
    (hcert : 2 * ε + 4 * B * ε / (2 * B + γ) < advantage p vh Jhat π) :
    gradeValuation p v (fun _ => π) < gradeValuation p v (gatedAct S j J) := by
  have hD := defect_bound hp hη herr hbound hmargin hJ hB hγ hTR
  have hL7 := advantage_estimate (η := η) (π := π) hp herr hJ hJhat hTR
  have hΓ : advantage p vh Jhat π - 2 * ε ≤ advantage p v J π := by
    have := (abs_le.mp hL7).1
    linarith
  rw [gatedAct_gradeValuation]
  have hadv : gradeValuation p v J = gradeValuation p v (fun _ => π) + advantage p v J π := by
    unfold advantage; ring
  rw [hadv]
  linarith

/-! ## The worked shutdown/correction case — the inhabitation witness

Source: `prompts/2026-08-11-deference-certificates/REPORT.md` §6.1 and that round's
`worked-case.json`. Four states, `B = 2`, credence `(9/20, 1/20, 1/5, 3/10)`, menu
`{continue, shutdown}` as `{0, 1}`, certified event `S = {w1, w2}` and `j = continue`.

The instance is not degenerate. The model is wrong at `w2` — the principal calls for
shutdown there and the model missed it — so `Ĵ ≠ J`, `η` is non-constant with `E_p[η]` equal
to the declared `ε = 1/4` exactly, both cells carry mass, and the certificate fires against
`FIXED[shutdown]` while *declining* against `FIXED[continue]`. The `4 = |Ω|` states and
`2 = |Π|` interventions are the source's, unmodified.
-/

namespace WorkedCase

/-- `0` is *continue*, `1` is *shutdown*. -/
abbrev Act := Fin 2

def p : Fin 4 → ℚ := ![9/20, 1/20, 1/5, 3/10]
def vhat : Fin 4 → Act → ℚ := ![![3/2, -1/2], ![3/2, -1/2], ![1/4, 1/2], ![1/4, 1/2]]
def v : Fin 4 → Act → ℚ := ![![3/2, -1/2], ![-1/2, 1], ![1/2, 1/4], ![-1/12, 1/2]]
def eta : Fin 4 → ℚ := ![0, 2, 1/4, 1/3]
def J : Fin 4 → Act := ![0, 1, 0, 1]
def Jhat : Fin 4 → Act := ![0, 0, 1, 1]
def S : Finset (Fin 4) := {0, 1}

theorem p_nonneg : ∀ ω, 0 ≤ p ω := by
  intro ω; fin_cases ω <;> norm_num [p]

theorem eta_nonneg : ∀ ω, 0 ≤ eta ω := by
  intro ω; fin_cases ω <;> norm_num [eta]

theorem err : ∀ ω π, |v ω π - vhat ω π| ≤ eta ω := by
  intro ω π; fin_cases ω <;> fin_cases π <;> norm_num [v, vhat, eta, abs_le]

theorem bounded : ∀ ω π, |v ω π| ≤ 2 := by
  intro ω π; fin_cases ω <;> fin_cases π <;> norm_num [v, abs_le]

theorem margin : ∀ ω ∈ S, ∀ π, π ≠ (0 : Act) → vhat ω π + 2 ≤ vhat ω 0 := by
  intro ω hω π hπ
  fin_cases π
  · exact absurd rfl hπ
  · have : ω = 0 ∨ ω = 1 := by
      simpa [S, Finset.mem_insert, Finset.mem_singleton] using hω
    rcases this with h | h <;> subst h <;> norm_num [vhat]

theorem J_max : ∀ ω π, v ω π ≤ v ω (J ω) := by
  intro ω π; fin_cases ω <;> fin_cases π <;> norm_num [v, J]

theorem Jhat_max : ∀ ω π, vhat ω π ≤ vhat ω (Jhat ω) := by
  intro ω π; fin_cases ω <;> fin_cases π <;> norm_num [vhat, Jhat]

/-- (TR-ε) holds at `ε = 1/4`, with equality: the tolerance is exactly the model's mean
grade error, not a slack constant. -/
theorem TR : ∑ ω, p ω * eta ω = 1/4 := by
  norm_num [p, eta, Fin.sum_univ_succ]

theorem override_mass : ∑ ω ∈ S.filter (fun ω => J ω ≠ 0), p ω = 1/20 := by
  have hfilter : S.filter (fun ω => J ω ≠ 0) = {1} := by decide
  rw [hfilter, Finset.sum_singleton]
  norm_num [p]

theorem defect_eq : defect p v J 0 S = 3/40 := by
  rw [defect, show S = insert (0 : Fin 4) {1} from rfl,
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [p, v, J]

theorem advantage_hat : advantage p vhat Jhat 1 = 1 := by
  norm_num [advantage, gradeValuation, p, vhat, Jhat, Fin.sum_univ_succ]

theorem advantage_true : advantage p v J 1 = 19/20 := by
  norm_num [advantage, gradeValuation, p, v, J, Fin.sum_univ_succ]

theorem gradeValuation_act : gradeValuation p v (gatedAct S 0 J) = 9/10 := by
  rw [gatedAct_gradeValuation, defect_eq]
  norm_num [gradeValuation, p, v, J, Fin.sum_univ_succ]

theorem gradeValuation_fixed_shutdown : gradeValuation p v (fun _ => 1) = 1/40 := by
  norm_num [gradeValuation, p, v, Fin.sum_univ_succ]

/-- The certificate clause of Theorem C′ at the worked case: `Γ̂(shutdown) = 1` exceeds the
threshold `2ε + 4Bε/(2B+γ) = 5/6`. -/
theorem cert_fires : 2 * (1/4 : ℚ) + 4 * 2 * (1/4) / (2 * 2 + 2) < advantage p vhat Jhat 1 := by
  rw [advantage_hat]; norm_num

/-- Every hypothesis of `gradeRegister_strict` holds at the worked case, and the theorem's
conclusion there is the strict inequality `1/40 < 9/10` the source records. -/
theorem gradeRegister_strict_nonvacuous :
    gradeValuation p v (fun _ => 1) < gradeValuation p v (gatedAct S 0 J) :=
  gradeRegister_strict (η := eta) (γ := 2) (ε := 1/4) (B := 2)
    p_nonneg eta_nonneg err bounded margin J_max Jhat_max (by norm_num) (by norm_num)
    (le_of_eq TR) cert_fires

/-- The same package inhabits L2's hypotheses; the bound `2ε/γ = 1/4` holds at the actual
override mass `1/20`. -/
theorem override_bound_nonvacuous :
    ∑ ω ∈ S.filter (fun ω => J ω ≠ 0), p ω ≤ 2 * (1/4 : ℚ) / 2 :=
  override_bound (η := eta) (γ := 2) (ε := 1/4)
    p_nonneg eta_nonneg err margin J_max (by norm_num) (le_of_eq TR)

/-- And L3's; the bound `4Bε/(2B+γ) = 1/3` holds at the actual defect `3/40`. -/
theorem defect_bound_nonvacuous :
    defect p v J 0 S ≤ 4 * 2 * (1/4 : ℚ) / (2 * 2 + 2) :=
  defect_bound (η := eta) (γ := 2) (ε := 1/4) (B := 2)
    p_nonneg eta_nonneg err bounded margin J_max (by norm_num) (by norm_num) (le_of_eq TR)

/-- And L7's; the estimate is off by `1/20`, well inside `2ε = 1/2`. -/
theorem advantage_estimate_nonvacuous :
    |advantage p v J 1 - advantage p vhat Jhat 1| ≤ 2 * (1/4 : ℚ) :=
  advantage_estimate (η := eta) (ε := 1/4) p_nonneg err J_max Jhat_max (le_of_eq TR)

/-- L1's hypothesis package is inhabited at `w1`, where the model is exact and the margin is
the full `γ = 2`; the conclusion is that the principal's selection there is `continue`.

The companion fact below is what keeps this from being an empty check: at `w3` the same
model has `2η = 1/2 > 1/4 = γ̂`, L1's hypothesis fails, and its conclusion fails too —
`Ĵ(w3) = shutdown` while `J(w3) = continue`. -/
theorem L1_nonvacuous : J 0 = (0 : Act) :=
  selection_eq_of_margin (v := v 0) (vh := vhat 0) (η := 0) (γ := 2)
    (by intro π; fin_cases π <;> norm_num [v, vhat, abs_le])
    (by
      intro π hπ
      fin_cases π
      · exact absurd rfl hπ
      · norm_num [vhat])
    (by norm_num)
    (by intro π; fin_cases π <;> norm_num [v, J])

/-- The model's induced choice differs from the principal's exactly where L1 does not
apply. -/
theorem L1_hypothesis_is_load_bearing : Jhat 2 ≠ J 2 := by decide

end WorkedCase

#print axioms margin_forces_agreement
#print axioms selection_eq_of_margin
#print axioms override_bound
#print axioms defect_bound
#print axioms advantage_estimate
#print axioms gatedAct_gradeValuation
#print axioms gradeRegister_strict
#print axioms WorkedCase.p_nonneg
#print axioms WorkedCase.eta_nonneg
#print axioms WorkedCase.err
#print axioms WorkedCase.bounded
#print axioms WorkedCase.margin
#print axioms WorkedCase.J_max
#print axioms WorkedCase.Jhat_max
#print axioms WorkedCase.TR
#print axioms WorkedCase.override_mass
#print axioms WorkedCase.defect_eq
#print axioms WorkedCase.advantage_hat
#print axioms WorkedCase.advantage_true
#print axioms WorkedCase.gradeValuation_act
#print axioms WorkedCase.gradeValuation_fixed_shutdown
#print axioms WorkedCase.cert_fires
#print axioms WorkedCase.gradeRegister_strict_nonvacuous
#print axioms WorkedCase.override_bound_nonvacuous
#print axioms WorkedCase.defect_bound_nonvacuous
#print axioms WorkedCase.advantage_estimate_nonvacuous
#print axioms WorkedCase.L1_nonvacuous
#print axioms WorkedCase.L1_hypothesis_is_load_bearing

end Workspace.Deference.Contrib.CertificateBounds
