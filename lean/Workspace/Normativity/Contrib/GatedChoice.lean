/-
# The gated decision adapter and the coupling hypothesis of the adequate-set route

Round `projects/deference/rounds/2026-09-06-decision-theory-bill/`.

The adequate-set route to `PracticalCert` (`PracticalCertificate.adequate_set_route`)
consumes one hypothesis that is decision theory rather than semantics: the *coupling*
`Σ_{q ∉ A} p q ≤ κ d + θ` between the realized response distribution's mass off the
adequate set and the public defect `d`.  This file says what a decision adapter has to be
for that hypothesis to hold, and what it cannot be.

**Register.**  A finite menu `Q`; an adequacy price `b q` displayed for each response; a
region point `u` at which the compiled norm holds — every inadequate response has
`u q ≤ τ` (`Region`) and some adequate response is marked with margin `τ + 2δ`
(`Margin`); the public defect is a sup-distance bound `d` between `b` and `u`.  The
**soft gate** weights each response by the ramp `clamp((b q − τ)/δ, 0, 1)` times a
positive task preference and normalizes.

* `softGate_massOff_le` — with the margin and `d ≤ δ`, the soft gate's mass off `A` is
  at most `κ d` with `κ = |Q| · pmax / (pmin · δ)`; and `massOff_le_one` covers `d > δ`.
  So the coupling holds with `θ = 0` — `softGate_coupling`.
* `softGate_practicalCert` — composed with `adequate_set_route`: the reason-responsive
  choice theorem in its finite form.
* `hardGate_discontinuous` — the hard gate (task-argmax over `{q : b q > τ}`) admits an
  inadequate response with mass one at every positive defect: no `κ` exists.
* `scalar_bribery` and `gate_invariant` — a compensatory scalar objective is flipped by a
  task stake above `λ · D`; a gated argmax is invariant to the forbidden response's task
  value.

**What this does not establish.**  That the adequacy prices mean what they say
(`Region` and `Margin` at the realized market are the compiler's soundness and the
market's accuracy on settling adequacy sentences, both external); that the preference
`pref` is the task objective anyone wants; anything about the inquiry response the gate
returns when no response is confidently adequate, which is charged at the worst loss by
the Progress statistic and is not a violation.  Names are provisional (`AGENTS.md`
standard 6).
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Workspace.Normativity.Contrib.PracticalCertificate

namespace Workspace.Normativity.Contrib.GatedChoice

open Finset
open Workspace.Normativity.Contrib.PracticalCertificate

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The ramp `clamp(x, 0, 1)`. -/
noncomputable def ramp (x : ℝ) : ℝ := max 0 (min 1 x)

theorem ramp_nonneg (x : ℝ) : 0 ≤ ramp x := le_max_left _ _
theorem ramp_le_one (x : ℝ) : ramp x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)
theorem ramp_le (x : ℝ) : ramp x ≤ max 0 x :=
  max_le_max le_rfl (min_le_right _ _)
theorem ramp_eq_one {x : ℝ} (h : 1 ≤ x) : ramp x = 1 := by
  unfold ramp
  rw [min_eq_left h]
  exact max_eq_right zero_le_one

/-- The soft gate's unnormalized weight on `q`. -/
noncomputable def weight (b : Q → ℝ) (pref : Q → ℝ) (τ δ : ℝ) (q : Q) : ℝ :=
  ramp ((b q - τ) / δ) * pref q

/-- The normalizer. -/
noncomputable def total (b : Q → ℝ) (pref : Q → ℝ) (τ δ : ℝ) : ℝ :=
  ∑ q, weight b pref τ δ q

/-- The soft gate's response distribution. -/
noncomputable def softGate (b : Q → ℝ) (pref : Q → ℝ) (τ δ : ℝ) (q : Q) : ℝ :=
  weight b pref τ δ q / total b pref τ δ

/-- Mass off the adequate set `A`. -/
noncomputable def massOff (p : Q → ℝ) (A : Finset Q) : ℝ := ∑ q ∈ univ \ A, p q

/-- The compiled norm at a region point: inadequate responses are priced at most `τ`. -/
def Region (u : Q → ℝ) (A : Finset Q) (τ : ℝ) : Prop := ∀ q, q ∉ A → u q ≤ τ

/-- The margin: some adequate response is priced at least `τ + 2δ`. -/
def Margin (u : Q → ℝ) (A : Finset Q) (τ δ : ℝ) : Prop := ∃ q ∈ A, τ + 2 * δ ≤ u q

/-- Sup-distance bound between the displayed prices and the region point. -/
def Within (b u : Q → ℝ) (d : ℝ) : Prop := ∀ q, |b q - u q| ≤ d

section Soft

variable {b u pref : Q → ℝ} {A : Finset Q} {τ δ d pmin pmax : ℝ}

omit [Fintype Q] [DecidableEq Q] in
theorem weight_nonneg (hpref : ∀ q, 0 ≤ pref q) (q : Q) : 0 ≤ weight b pref τ δ q :=
  mul_nonneg (ramp_nonneg _) (hpref q)

omit [DecidableEq Q] in
theorem total_nonneg (hpref : ∀ q, 0 ≤ pref q) : 0 ≤ total b pref τ δ :=
  Finset.sum_nonneg fun q _ => weight_nonneg hpref q

omit [DecidableEq Q] in
/-- Under the margin and `d ≤ δ`, the marked adequate response has weight exactly its
preference, so the normalizer is at least `pmin`. -/
theorem total_ge_pmin (hδ : 0 < δ) (hpref : ∀ q, 0 ≤ pref q) (hmin : ∀ q, pmin ≤ pref q)
    (hM : Margin u A τ δ) (hW : Within b u d) (hd : d ≤ δ) :
    pmin ≤ total b pref τ δ := by
  obtain ⟨q₀, _, hq₀⟩ := hM
  have hb : τ + δ ≤ b q₀ := by
    have := (abs_le.mp (hW q₀)).1
    linarith
  have hw : weight b pref τ δ q₀ = pref q₀ := by
    unfold weight
    rw [ramp_eq_one, one_mul]
    rw [le_div_iff₀ hδ]
    linarith
  calc pmin ≤ pref q₀ := hmin q₀
    _ = weight b pref τ δ q₀ := hw.symm
    _ ≤ total b pref τ δ := by
        unfold total
        exact Finset.single_le_sum (fun q _ => weight_nonneg hpref q) (Finset.mem_univ q₀)

omit [Fintype Q] [DecidableEq Q] in
/-- Off the adequate set the weight is at most `pmax · d / δ`. -/
theorem weight_off_le (hδ : 0 < δ) (hd0 : 0 ≤ d) (hpref : ∀ q, 0 ≤ pref q)
    (hmax : ∀ q, pref q ≤ pmax) (hR : Region u A τ) (hW : Within b u d)
    {q : Q} (hq : q ∉ A) :
    weight b pref τ δ q ≤ pmax * (d / δ) := by
  have hb : b q ≤ τ + d := by
    have := (abs_le.mp (hW q)).2
    have := hR q hq
    linarith
  have hr : ramp ((b q - τ) / δ) ≤ d / δ := by
    calc ramp ((b q - τ) / δ) ≤ max 0 ((b q - τ) / δ) := ramp_le _
      _ ≤ d / δ := by
          apply max_le (div_nonneg hd0 hδ.le)
          exact div_le_div_of_nonneg_right (by linarith) hδ.le
  have hpm : 0 ≤ pmax := le_trans (hpref q) (hmax q)
  calc weight b pref τ δ q = ramp ((b q - τ) / δ) * pref q := rfl
    _ ≤ (d / δ) * pmax :=
        mul_le_mul hr (hmax q) (hpref q) (div_nonneg hd0 hδ.le)
    _ = pmax * (d / δ) := by ring

/-- **Soft-gate coupling, the margin case.**  With the margin and `d ≤ δ`, the mass off
`A` is at most `κ d` with `κ = |Q| · pmax / (pmin · δ)`. -/
theorem softGate_massOff_le (hδ : 0 < δ) (hd0 : 0 ≤ d) (hd : d ≤ δ)
    (hpref : ∀ q, 0 ≤ pref q) (hmin : ∀ q, pmin ≤ pref q) (hmax : ∀ q, pref q ≤ pmax)
    (hpmin : 0 < pmin) (hR : Region u A τ) (hM : Margin u A τ δ) (hW : Within b u d) :
    massOff (softGate b pref τ δ) A ≤ (Fintype.card Q * pmax / (pmin * δ)) * d := by
  have hM' := hM
  obtain ⟨q₀, _, _⟩ := hM'
  have hpm : 0 ≤ pmax := le_trans (hpref q₀) (hmax q₀)
  have hZ : pmin ≤ total b pref τ δ := total_ge_pmin hδ hpref hmin hM hW hd
  have hZpos : 0 < total b pref τ δ := lt_of_lt_of_le hpmin hZ
  have hnum : ∑ q ∈ univ \ A, weight b pref τ δ q ≤ Fintype.card Q * (pmax * (d / δ)) := by
    calc ∑ q ∈ univ \ A, weight b pref τ δ q
        ≤ ∑ q ∈ univ \ A, pmax * (d / δ) := by
          apply Finset.sum_le_sum
          intro q hq
          exact weight_off_le hδ hd0 hpref hmax hR hW (Finset.mem_sdiff.mp hq).2
      _ = (univ \ A).card * (pmax * (d / δ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Fintype.card Q * (pmax * (d / δ)) := by
          apply mul_le_mul_of_nonneg_right _ (mul_nonneg hpm (div_nonneg hd0 hδ.le))
          exact_mod_cast Finset.card_le_univ _
  have hmass : massOff (softGate b pref τ δ) A
      = (∑ q ∈ univ \ A, weight b pref τ δ q) / total b pref τ δ := by
    unfold massOff softGate
    rw [Finset.sum_div]
  have hκ0 : 0 ≤ Fintype.card Q * pmax / (pmin * δ) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hpm) (mul_nonneg hpmin.le hδ.le)
  have hkey : (Fintype.card Q : ℝ) * (pmax * (d / δ))
      = (Fintype.card Q * pmax / (pmin * δ)) * d * pmin := by
    field_simp
  rw [hmass, div_le_iff₀ hZpos]
  calc ∑ q ∈ univ \ A, weight b pref τ δ q
      ≤ Fintype.card Q * (pmax * (d / δ)) := hnum
    _ = (Fintype.card Q * pmax / (pmin * δ)) * d * pmin := hkey
    _ ≤ (Fintype.card Q * pmax / (pmin * δ)) * d * total b pref τ δ :=
        mul_le_mul_of_nonneg_left hZ (mul_nonneg hκ0 hd0)

/-- A normalized gate has mass at most one off any set. -/
theorem massOff_le_one (hpref : ∀ q, 0 ≤ pref q) (hZ : 0 < total b pref τ δ) :
    massOff (softGate b pref τ δ) A ≤ 1 := by
  unfold massOff softGate
  rw [← Finset.sum_div, div_le_one hZ]
  unfold total
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun q _ _ => weight_nonneg hpref q

/-- **The coupling hypothesis of the adequate-set route**, for every defect `d ≥ 0`. -/
theorem softGate_coupling (hδ : 0 < δ) (hd0 : 0 ≤ d)
    (hpref : ∀ q, 0 ≤ pref q) (hmin : ∀ q, pmin ≤ pref q) (hmax : ∀ q, pref q ≤ pmax)
    (hpmin : 0 < pmin) (hR : Region u A τ) (hM : Margin u A τ δ) (hW : Within b u d)
    (hZ : 0 < total b pref τ δ) :
    massOff (softGate b pref τ δ) A ≤ (Fintype.card Q * pmax / (pmin * δ)) * d + 0 := by
  rw [add_zero]
  by_cases hd : d ≤ δ
  · exact softGate_massOff_le hδ hd0 hd hpref hmin hmax hpmin hR hM hW
  · have hd' : δ < d := lt_of_not_ge hd
    have hM' := hM
    obtain ⟨q₀, _, _⟩ := hM'
    have hcard : (1 : ℝ) ≤ Fintype.card Q := by
      exact_mod_cast Fintype.card_pos_iff.mpr ⟨q₀⟩
    have hratio : pmin ≤ pmax := le_trans (hmin q₀) (hmax q₀)
    have hpm : 0 ≤ pmax := le_trans (hpref q₀) (hmax q₀)
    have hκ : (1 : ℝ) ≤ (Fintype.card Q * pmax / (pmin * δ)) * d := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (mul_pos hpmin hδ)]
      have h1 : pmin * δ ≤ pmax * d := by nlinarith
      have h2 : (1 : ℝ) * (pmax * d) ≤ Fintype.card Q * (pmax * d) :=
        mul_le_mul_of_nonneg_right hcard (mul_nonneg hpm hd0)
      nlinarith
    exact le_trans (massOff_le_one hpref hZ) hκ

/-- **Reason-responsive choice, finite form.**  The soft gate's anchored loss satisfies
`PracticalCert` with `M = D κ` and `ε = εad`: the coupling is decision theory, the two
loss hypotheses are semantics. -/
theorem softGate_practicalCert {lam : Q → ℝ} {εad D : ℝ}
    (hδ : 0 < δ) (hd0 : 0 ≤ d)
    (hpref : ∀ q, 0 ≤ pref q) (hmin : ∀ q, pmin ≤ pref q) (hmax : ∀ q, pref q ≤ pmax)
    (hpmin : 0 < pmin) (hR : Region u A τ) (hM : Margin u A τ δ) (hW : Within b u d)
    (hZ : 0 < total b pref τ δ)
    (hεad : 0 ≤ εad) (hD : 0 ≤ D)
    (hadequate : ∀ q ∈ A, lam q ≤ εad) (hbound : ∀ q, lam q ≤ D) :
    anchoredLoss univ (softGate b pref τ δ) lam
      ≤ (D * (Fintype.card Q * pmax / (pmin * δ))) * d + (εad + D * 0) := by
  have hprob : ∑ q ∈ univ, softGate b pref τ δ q = 1 := by
    unfold softGate
    rw [← Finset.sum_div]
    exact div_self hZ.ne'
  refine adequate_set_route univ A (Finset.subset_univ _)
    (fun q _ => div_nonneg (weight_nonneg hpref q) hZ.le) hprob hεad hD hadequate
    (fun q _ => hbound q) ?_
  exact softGate_coupling hδ hd0 hpref hmin hmax hpmin hR hM hW hZ

end Soft

/-! ## The hard gate -/

/-- Mass the task-argmax over `{q : b q > τ}` puts on `q`. -/
noncomputable def hardGate (b pref : Q → ℝ) (τ : ℝ) (q : Q) : ℝ :=
  if b q > τ ∧ (∀ q', b q' > τ → pref q' ≤ pref q) then 1 else 0

namespace Witness

/-- Two responses: `0` adequate, `1` not; the task prefers `1`. -/
def A : Finset (Fin 2) := {0}
noncomputable def pref : Fin 2 → ℝ := fun q => if q = 0 then 1 else 2
noncomputable def u : Fin 2 → ℝ := fun q => if q = 0 then 1 else 1 / 2
noncomputable def b (d : ℝ) : Fin 2 → ℝ := fun q => if q = 0 then 1 else 1 / 2 + d

/-- **The hard gate has no Lipschitz constant.**  At every defect `d > 0` the displayed
prices are within `d` of a region point with margin, and the hard gate executes the
inadequate response with mass one. -/
theorem hardGate_discontinuous (d : ℝ) (hd : 0 < d) :
    Region u A (1 / 2) ∧ Margin u A (1 / 2) (1 / 4) ∧ Within (b d) u d ∧
    massOff (hardGate (b d) pref (1 / 2)) A = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    fin_cases q
    · simp [A] at hq
    · simp [u]
  · exact ⟨0, by simp [A], by norm_num [u]⟩
  · intro q
    fin_cases q <;> simp [b, u, abs_of_nonneg hd.le, hd.le]
  · have hA : (univ \ A : Finset (Fin 2)) = {1} := by decide
    rw [massOff, hA, Finset.sum_singleton]
    unfold hardGate
    rw [if_pos]
    refine ⟨by simp [b]; linarith, ?_⟩
    intro q' _
    fin_cases q' <;> simp [pref]

end Witness

/-! ## Scalar compensation versus the gate -/

/-- A compensatory scalar objective is flipped by a task stake exceeding `λ` times the
loss range. -/
theorem scalar_bribery {tA tF lossF lam D : ℝ} (hloss : lossF ≤ D) (hstake : tA + lam * D < tF)
    (hlam : 0 ≤ lam) :
    tA - lam * 0 < tF - lam * lossF := by
  nlinarith

/-- A gated argmax never consults the forbidden response's task value. -/
theorem gate_invariant {Q : Type*} (A : Finset Q) (task task' : Q → ℝ)
    (hagree : ∀ q ∈ A, task q = task' q) :
    (∀ q ∈ A, ∀ q' ∈ A, task q' ≤ task q) ↔ (∀ q ∈ A, ∀ q' ∈ A, task' q' ≤ task' q) := by
  constructor <;> intro h q hq q' hq' <;>
    · have := h q hq q' hq'
      rw [hagree q hq, hagree q' hq'] at *
      linarith

end Workspace.Normativity.Contrib.GatedChoice

#print axioms Workspace.Normativity.Contrib.GatedChoice.total_ge_pmin
#print axioms Workspace.Normativity.Contrib.GatedChoice.weight_off_le
#print axioms Workspace.Normativity.Contrib.GatedChoice.softGate_massOff_le
#print axioms Workspace.Normativity.Contrib.GatedChoice.massOff_le_one
#print axioms Workspace.Normativity.Contrib.GatedChoice.softGate_coupling
#print axioms Workspace.Normativity.Contrib.GatedChoice.softGate_practicalCert
#print axioms Workspace.Normativity.Contrib.GatedChoice.Witness.hardGate_discontinuous
#print axioms Workspace.Normativity.Contrib.GatedChoice.scalar_bribery
#print axioms Workspace.Normativity.Contrib.GatedChoice.gate_invariant
