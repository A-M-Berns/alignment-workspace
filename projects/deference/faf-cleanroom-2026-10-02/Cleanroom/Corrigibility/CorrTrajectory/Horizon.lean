import Cleanroom.Corrigibility.CorrTrajectory.Process

/-!
# `corr-trajectory` — `Horizon`: Statement 4, finite-horizon harm and omission under compliance (T3)

Layer F, on a `ShutdownProc` with a finite magnitude type `M`. The named hypotheses:

* **compliance** `κ_t = 1` for `t ≤ T`;
* **`(βmin)`**: on every pre-press atom and every magnitude `m`,
  `β^min_t · P*(W_t ∧ mag_t = m ∣ 𝓕_t^-) ≤ P*(W_t ∧ mag_t = m ∧ Pr_t ∣ 𝓕_t^-)` — the overseers
  catch wrong proposals of every magnitude at rate at least `β^min_t` (`detectionLB`);
* **`(MI)`**: the press rate is one `β_t` across magnitudes (`detectionEq`);
* **`(αmax)`** dually: on every pre-press atom and every magnitude `m`,
  `P*(¬W_t ∧ mag_t = m ∧ Pr_t ∣ 𝓕_t^-) ≤ α^max_t · P*(¬W_t ∧ mag_t = m ∣ 𝓕_t^-)` — the overseers
  falsely press right proposals of every magnitude at rate at most `α^max_t` (`detectionUB`), with
  `(MI)` for the false press as `detectionEqUB` (added in repair round 2, audit r2 fidelity B1).

Conclusions: `E*[Harm_T] ≤ ∑_{t ≤ T} E*[(1 − β^min_t) W_t H_t]` (`harm_le_detection`), with equality
under `(MI)` (`harm_eq_detection`); the display's form `∑ E*[(1 − β^min_t) ε_t h_t]` through the
tower identity `E*[Y · W_t H_t] = E*[Y · (ε_t h_t)]` where `ε_t h_t` is the product-form conditional
sum divided by the atom mass (`expect_mul_condSum_div`, junk-safe: a mass-zero atom contributes `0`
on both sides); **the omission half** `E*[Omit_T] ≤ ∑_{t ≤ T} E*[α^max_t (1 − W_t) C_t]`
(`omit_le_detection`), its `(MI)` equality (`omit_eq_detection`) and display form
(`omit_le_detection_ratio`, through `epsC` = `(1 − ε_t) c_t`), and both halves together for `Reg_T`
(`reg_le_detection`); universal defiance gives `Harm_T = ∑ W_t H_t`, `Omit_T = 0`. The refutation of
the develop's identity without `(MI)` (A6) and the three-round `(MI)` witness (C7, both halves
through the theorems) are in `HorizonWitness`.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Corrigibility.CorrTrajectory

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Corrigibility.CorrJointProcess
open Finset hiding expect

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- `condSum` of a finite sum of functions. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma condSum_sum {μ : Distr Ω} {A : Atoms Ω} {ι : Type} (s : Finset ι) (t : ℕ) (f : ι → Ω → ℝ) (ω : Ω) :
    condSum μ A t (fun ω' => ∑ i ∈ s, f i ω') ω = ∑ i ∈ s, condSum μ A t (f i) ω := by
  simp only [condSum, mul_sum]
  exact sum_comm

/-- **The tower identity for the ratio form**: for `𝓕_t`-measurable `Y`,
`E*[Y · (condSum_t X / atomMass_t)] = E*[Y · X]`. A mass-zero atom contributes `0` on both sides, so no
positivity is needed; this is how `ε_t h_t` gets its meaning.
Source: [[corr-wf14-inventory]] 074 / invariant-final.md proof of Statement 4 ("take `E*` (tower)")
Kind: L
Fidelity: exact -/
lemma expect_mul_condSum_div {μ : Distr Ω} {A : Atoms Ω} (t : ℕ) {Y : Ω → ℝ} (hY : A.Meas t Y) (X : Ω → ℝ) :
    expect μ (fun ω => Y ω * (condSum μ A t X ω / atomMass μ A t ω)) = expect μ (fun ω => Y ω * X ω) := by
  unfold expect
  rw [A.sum_eq_sum_atoms t, A.sum_eq_sum_atoms t (fun ω => μ.mass ω * (Y ω * X ω))]
  refine sum_congr rfl fun B hB => ?_
  obtain ⟨a, -, rfl⟩ := mem_image.1 hB
  have hc : ∀ ω ∈ A.fib t a, condSum μ A t X ω = condSum μ A t X a := fun ω h => condSum_meas t X a ω h
  have hm : ∀ ω ∈ A.fib t a, atomMass μ A t ω = atomMass μ A t a := fun ω h => atomMass_meas t a ω h
  have hy : ∀ ω ∈ A.fib t a, Y ω = Y a := fun ω h => hY a ω h
  have e1 : ∑ ω ∈ A.fib t a, μ.mass ω * (Y ω * (condSum μ A t X ω / atomMass μ A t ω)) =
      (Y a * (condSum μ A t X a / atomMass μ A t a)) * atomMass μ A t a := by
    have hterm : ∀ ω ∈ A.fib t a, μ.mass ω * (Y ω * (condSum μ A t X ω / atomMass μ A t ω)) =
        (Y a * (condSum μ A t X a / atomMass μ A t a)) * μ.mass ω := fun ω h => by
      rw [hc ω h, hm ω h, hy ω h]; ring
    rw [sum_congr rfl hterm, ← Finset.mul_sum]
    rfl
  have e2 : ∑ ω ∈ A.fib t a, μ.mass ω * (Y ω * X ω) = Y a * condSum μ A t X a := by
    rw [condSum, Finset.mul_sum]
    refine sum_congr rfl fun ω h => ?_
    rw [hy ω h]; ring
  rw [e1, e2]
  rcases eq_or_ne (atomMass μ A t a) 0 with h0 | h0
  · have hz : condSum μ A t X a = 0 := by
      unfold condSum
      refine sum_eq_zero fun ω h => ?_
      have : μ.mass ω = 0 := by
        have := (sum_eq_zero_iff_of_nonneg fun ω' _ => μ.nonneg ω').1 h0 ω h
        exact this
      rw [this, zero_mul]
    rw [h0, hz]; simp
  · field_simp

namespace ShutdownProc

variable {M : Type} [Fintype M] [DecidableEq M] (S : ShutdownProc Ω M)

/-- The magnitude indicator `𝟙[mag_t = m]`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def magInd (t : ℕ) (m : M) (ω : Ω) : ℝ := if S.mag t ω = m then 1 else 0

/-- `H_eq_sum_magInd` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma H_eq_sum_magInd (t : ℕ) (ω : Ω) : S.H t ω = ∑ m, S.magInd t m ω * S.hOf m := by
  unfold H magInd
  simp [ite_mul]

/-- **`(βmin)`: the detection lower bound** per magnitude on the pre-press atoms.
Source: [[corr-wf14-inventory]] 074 / invariant-final.md S2 step 3 (`β^min_t := ess inf_H β_t(H)`), Statement 4
Kind: D
Fidelity: exact (product form) -/
def detectionLB (βmin : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω m, βmin t ω * condSum S.μ S.Fpre t (fun ω' => indB (S.wrong t) ω' * S.magInd t m ω') ω ≤
    condSum S.μ S.Fpre t (fun ω' => indB (S.wrong t) ω' * S.magInd t m ω' * indB (S.pressed t) ω') ω

/-- **`(MI)`: magnitude-independent press** — one rate `β_t` across magnitudes, as an equality.
Source: [[corr-wf14-inventory]] 074 / invariant-final.md S2 step 3 (`(MI)`)
Kind: D
Fidelity: exact (product form) -/
def detectionEq (β : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω m, condSum S.μ S.Fpre t (fun ω' => indB (S.wrong t) ω' * S.magInd t m ω' * indB (S.pressed t) ω') ω =
    β t ω * condSum S.μ S.Fpre t (fun ω' => indB (S.wrong t) ω' * S.magInd t m ω') ω

/-- `(MI)` implies `(βmin)` with `β^min = β`. Source: Statement 4. Kind: L. Fidelity: exact -/
lemma detectionLB_of_eq {β : ℕ → Ω → ℝ} {t : ℕ} (h : S.detectionEq β t) : S.detectionLB β t :=
  fun ω m => (h ω m).ge

/-- `(βmin)` in harm-weighted form: `β^min_t · E*[W_t H_t 1_atom] ≤ E*[W_t H_t Pr_t 1_atom]` (`h ≥ 0`).
Source: invariant-final.md proof of Statement 4. Kind: L. Fidelity: exact -/
lemma detectionLB_harm {βmin : ℕ → Ω → ℝ} {t : ℕ} (hβ : S.detectionLB βmin t) (ω : Ω) :
    βmin t ω * condSum S.μ S.Fpre t (fun ω' => indB (S.wrong t) ω' * S.H t ω') ω ≤
      condSum S.μ S.Fpre t (fun ω' => indB (S.wrong t) ω' * S.H t ω' * indB (S.pressed t) ω') ω := by
  have e1 : (fun ω' => indB (S.wrong t) ω' * S.H t ω') =
      fun ω' => ∑ m, S.hOf m * (indB (S.wrong t) ω' * S.magInd t m ω') := by
    funext ω'; rw [S.H_eq_sum_magInd, Finset.mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have e2 : (fun ω' => indB (S.wrong t) ω' * S.H t ω' * indB (S.pressed t) ω') =
      fun ω' => ∑ m, S.hOf m * (indB (S.wrong t) ω' * S.magInd t m ω' * indB (S.pressed t) ω') := by
    funext ω'; rw [S.H_eq_sum_magInd, Finset.mul_sum, Finset.sum_mul]
    exact sum_congr rfl fun m _ => by ring
  rw [e1, e2, condSum_sum, condSum_sum, Finset.mul_sum]
  refine sum_le_sum fun m _ => ?_
  rw [condSum_const_mul, condSum_const_mul]
  calc βmin t ω * (S.hOf m * condSum S.μ S.Fpre t (fun ω' => indB (S.wrong t) ω' * S.magInd t m ω') ω)
      = S.hOf m * (βmin t ω * condSum S.μ S.Fpre t (fun ω' => indB (S.wrong t) ω' * S.magInd t m ω') ω) := by
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hβ ω m) (S.hOf_nonneg m)

/-- `(MI)` in harm-weighted form (equality). Source: invariant-final.md proof of Statement 4. Kind: L. Fidelity: exact -/
lemma detectionEq_harm {β : ℕ → Ω → ℝ} {t : ℕ} (hβ : S.detectionEq β t) (ω : Ω) :
    condSum S.μ S.Fpre t (fun ω' => indB (S.wrong t) ω' * S.H t ω' * indB (S.pressed t) ω') ω =
      β t ω * condSum S.μ S.Fpre t (fun ω' => indB (S.wrong t) ω' * S.H t ω') ω := by
  have e1 : (fun ω' => indB (S.wrong t) ω' * S.H t ω') =
      fun ω' => ∑ m, S.hOf m * (indB (S.wrong t) ω' * S.magInd t m ω') := by
    funext ω'; rw [S.H_eq_sum_magInd, Finset.mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have e2 : (fun ω' => indB (S.wrong t) ω' * S.H t ω' * indB (S.pressed t) ω') =
      fun ω' => ∑ m, S.hOf m * (indB (S.wrong t) ω' * S.magInd t m ω' * indB (S.pressed t) ω') := by
    funext ω'; rw [S.H_eq_sum_magInd, Finset.mul_sum, Finset.sum_mul]
    exact sum_congr rfl fun m _ => by ring
  rw [e1, e2, condSum_sum, condSum_sum, Finset.mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [condSum_const_mul, condSum_const_mul, hβ ω m]; ring

/-- Under compliance at `t`, `harm_t = W_t H_t − W_t H_t Pr_t`. Source: proof of Statement 4. Kind: L. Fidelity: exact -/
lemma harm_eq_sub_of_kappa (t : ℕ) (hk : ∀ ω, S.kappa t ω = true) :
    S.harm t = fun ω => indB (S.wrong t) ω * S.H t ω - indB (S.wrong t) ω * S.H t ω * indB (S.pressed t) ω := by
  funext ω; rw [S.harm_of_kappa t ω (hk ω)]; ring

/-- **Statement 4, one round**: under compliance and `(βmin)` (with `β^min_t` `𝓕_t^-`-measurable),
`E*[harm_t] ≤ E*[(1 − β^min_t) W_t H_t]`.
Source: [[corr-wf14-inventory]] 074 / invariant-final.md Statement 4, proof
Kind: P (small: the tower step on the pre-press atoms)
Fidelity: exact
Hyps: (a) only -/
theorem expect_harm_le (t : ℕ) (βmin : ℕ → Ω → ℝ) (hk : ∀ ω, S.kappa t ω = true)
    (hβ : S.detectionLB βmin t) (hmeas : S.Fpre.Meas t (βmin t)) :
    expect S.μ (S.harm t) ≤ expect S.μ (fun ω => (1 - βmin t ω) * (indB (S.wrong t) ω * S.H t ω)) := by
  rw [S.harm_eq_sub_of_kappa t hk, Found.CorrThreeStep.expect_sub]
  have h1 : expect S.μ (fun ω => βmin t ω * (indB (S.wrong t) ω * S.H t ω)) ≤
      expect S.μ (fun ω => indB (S.wrong t) ω * S.H t ω * indB (S.pressed t) ω) := by
    refine expect_le_of_condSum_le (A := S.Fpre) t fun ω => ?_
    rw [condSum_mul_meas t hmeas]
    exact S.detectionLB_harm hβ ω
  have h2 : expect S.μ (fun ω => (1 - βmin t ω) * (indB (S.wrong t) ω * S.H t ω)) =
      expect S.μ (fun ω => indB (S.wrong t) ω * S.H t ω) -
        expect S.μ (fun ω => βmin t ω * (indB (S.wrong t) ω * S.H t ω)) := by
    rw [← Found.CorrThreeStep.expect_sub]
    exact congrArg _ (funext fun ω => by ring)
  linarith

/-- **Statement 4, one round, equality under `(MI)`**: `E*[harm_t] = E*[(1 − β_t) W_t H_t]`.
Source: [[corr-wf14-inventory]] 074 / invariant-final.md Statement 4 ("with equality in both under (MI)")
Kind: P (small)
Fidelity: exact
Hyps: (a) only -/
theorem expect_harm_eq (t : ℕ) (β : ℕ → Ω → ℝ) (hk : ∀ ω, S.kappa t ω = true)
    (hβ : S.detectionEq β t) (hmeas : S.Fpre.Meas t (β t)) :
    expect S.μ (S.harm t) = expect S.μ (fun ω => (1 - β t ω) * (indB (S.wrong t) ω * S.H t ω)) := by
  rw [S.harm_eq_sub_of_kappa t hk, Found.CorrThreeStep.expect_sub]
  have h1 : expect S.μ (fun ω => β t ω * (indB (S.wrong t) ω * S.H t ω)) =
      expect S.μ (fun ω => indB (S.wrong t) ω * S.H t ω * indB (S.pressed t) ω) := by
    refine expect_eq_of_condSum_eq (A := S.Fpre) t fun ω => ?_
    rw [condSum_mul_meas t hmeas]
    exact (S.detectionEq_harm hβ ω).symm
  have h2 : expect S.μ (fun ω => (1 - β t ω) * (indB (S.wrong t) ω * S.H t ω)) =
      expect S.μ (fun ω => indB (S.wrong t) ω * S.H t ω) -
        expect S.μ (fun ω => β t ω * (indB (S.wrong t) ω * S.H t ω)) := by
    rw [← Found.CorrThreeStep.expect_sub]
    exact congrArg _ (funext fun ω => by ring)
  linarith

/-- **Statement 4 (D6): the finite-horizon harm bound under compliance.**
`E*[Harm_T] ≤ ∑_{t ≤ T} E*[(1 − β^min_t) W_t H_t]` — compliance multiplies each round's expected harm
by the miss rate; it does not bound the total.
Source: [[corr-wf14-inventory]] 074, 2-020 / invariant-final.md Statement 4 (first display, `≤` form)
Kind: P (small: the one-round tower step summed)
Fidelity: exact (`W_t H_t` in place of the display's `ε_t h_t`; `harm_le_detection_ratio` is the display)
Hyps: (a) only -/
theorem harm_le_detection (T : ℕ) (βmin : ℕ → Ω → ℝ) (hk : ∀ t ≤ T, ∀ ω, S.kappa t ω = true)
    (hβ : ∀ t ≤ T, S.detectionLB βmin t) (hmeas : ∀ t ≤ T, S.Fpre.Meas t (βmin t)) :
    expect S.μ (S.Harm T) ≤
      ∑ t ∈ range (T + 1), expect S.μ (fun ω => (1 - βmin t ω) * (indB (S.wrong t) ω * S.H t ω)) := by
  unfold Harm
  rw [expect_sum_range]
  refine sum_le_sum fun t ht => ?_
  have htT := Nat.lt_succ_iff.1 (mem_range.1 ht)
  exact S.expect_harm_le t βmin (hk t htT) (hβ t htT) (hmeas t htT)

/-- **Statement 4, equality under `(MI)`.**
Source: [[corr-wf14-inventory]] 074 / invariant-final.md Statement 4 ("with equality … under (MI)")
Kind: P (small)
Fidelity: exact
Hyps: (a) only -/
theorem harm_eq_detection (T : ℕ) (β : ℕ → Ω → ℝ) (hk : ∀ t ≤ T, ∀ ω, S.kappa t ω = true)
    (hβ : ∀ t ≤ T, S.detectionEq β t) (hmeas : ∀ t ≤ T, S.Fpre.Meas t (β t)) :
    expect S.μ (S.Harm T) =
      ∑ t ∈ range (T + 1), expect S.μ (fun ω => (1 - β t ω) * (indB (S.wrong t) ω * S.H t ω)) := by
  unfold Harm
  rw [expect_sum_range]
  refine sum_congr rfl fun t ht => ?_
  have htT := Nat.lt_succ_iff.1 (mem_range.1 ht)
  exact S.expect_harm_eq t β (hk t htT) (hβ t htT) (hmeas t htT)

/-- `ε_t h_t`: the conditional expected wrongness-weighted harm on the pre-press atom, as a ratio
(junk-safe through `expect_mul_condSum_div`).
Source: [[corr-wf14-inventory]] 074 / invariant-final.md S2 step 2–3 (`ε_t`, `h_t`)
Kind: D
Fidelity: exact (the product `ε_t h_t` directly; the two factors are not separated) -/
noncomputable def epsH (t : ℕ) (ω : Ω) : ℝ :=
  condSum S.μ S.Fpre t (fun ω' => indB (S.wrong t) ω' * S.H t ω') ω / atomMass S.μ S.Fpre t ω

/-- **The display's form**: `E*[Harm_T] ≤ ∑_{t ≤ T} E*[(1 − β^min_t) ε_t h_t]`.
Source: [[corr-wf14-inventory]] 074 / invariant-final.md Statement 4 (first display)
Kind: C (`harm_le_detection` + the tower identity)
Fidelity: exact
Hyps: (a) only -/
theorem harm_le_detection_ratio (T : ℕ) (βmin : ℕ → Ω → ℝ) (hk : ∀ t ≤ T, ∀ ω, S.kappa t ω = true)
    (hβ : ∀ t ≤ T, S.detectionLB βmin t) (hmeas : ∀ t ≤ T, S.Fpre.Meas t (βmin t)) :
    expect S.μ (S.Harm T) ≤ ∑ t ∈ range (T + 1), expect S.μ (fun ω => (1 - βmin t ω) * S.epsH t ω) := by
  refine (S.harm_le_detection T βmin hk hβ hmeas).trans (le_of_eq (sum_congr rfl fun t ht => ?_))
  have htT := Nat.lt_succ_iff.1 (mem_range.1 ht)
  unfold epsH
  exact (expect_mul_condSum_div t (hmeas t htT).one_sub _).symm

/-! ### The omission half of Statement 4 (added in repair round 2, audit r2 fidelity B1)

The second display, `E*[Omit_T] ≤ E*[∑_{t ≤ T} (1 − ε_t) α^max_t c_t]`, with equality under `(MI)`:
the exact mirror of the harm half, with `(αmax)` (the false-press *upper* bound per magnitude on the
pre-press atoms) in place of `(βmin)`, `¬W_t` for `W_t`, `C_t` for `H_t`, and the omission incurred
under compliance exactly when right and pressed (`omission_of_kappa`). -/

/-- `C_eq_sum_magInd` (supporting lemma). Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma C_eq_sum_magInd (t : ℕ) (ω : Ω) : S.C t ω = ∑ m, S.magInd t m ω * S.cOf m := by
  unfold C magInd
  simp [ite_mul]

/-- **`(αmax)`: the false-press upper bound** per magnitude on the pre-press atoms — the dual of
`detectionLB`: `P*(¬W_t ∧ mag_t = m ∧ Pr_t ∣ 𝓕_t^-) ≤ α^max_t · P*(¬W_t ∧ mag_t = m ∣ 𝓕_t^-)`, the
overseers falsely press right proposals of every magnitude at rate at most `α^max_t`.
Source: [[corr-wf14-inventory]] 074 / invariant-final.md S2 step 3 (`α^max_t := ess sup α_t(·)`), Statement 4 (second display)
Kind: D
Fidelity: exact (product form) -/
def detectionUB (αmax : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω m, condSum S.μ S.Fpre t
      (fun ω' => (1 - indB (S.wrong t) ω') * S.magInd t m ω' * indB (S.pressed t) ω') ω ≤
    αmax t ω * condSum S.μ S.Fpre t (fun ω' => (1 - indB (S.wrong t) ω') * S.magInd t m ω') ω

/-- **`(MI)` for the false press** — one rate `α_t` across magnitudes, as an equality (the dual of
`detectionEq`).
Source: [[corr-wf14-inventory]] 074 / invariant-final.md S2 step 3 (`(MI)`), Statement 4 ("with equality in both under (MI)")
Kind: D
Fidelity: exact (product form) -/
def detectionEqUB (α : ℕ → Ω → ℝ) (t : ℕ) : Prop :=
  ∀ ω m, condSum S.μ S.Fpre t
      (fun ω' => (1 - indB (S.wrong t) ω') * S.magInd t m ω' * indB (S.pressed t) ω') ω =
    α t ω * condSum S.μ S.Fpre t (fun ω' => (1 - indB (S.wrong t) ω') * S.magInd t m ω') ω

/-- `(MI)` for the false press implies `(αmax)` with `α^max = α`. Source: Statement 4. Kind: L. Fidelity: exact -/
lemma detectionUB_of_eq {α : ℕ → Ω → ℝ} {t : ℕ} (h : S.detectionEqUB α t) : S.detectionUB α t :=
  fun ω m => (h ω m).le

/-- `(αmax)` in cost-weighted form: `E*[¬W_t C_t Pr_t 1_atom] ≤ α^max_t · E*[¬W_t C_t 1_atom]` (`c ≥ 0`).
Source: invariant-final.md proof of Statement 4 ("Omission likewise with `α^max_t`"). Kind: L. Fidelity: exact -/
lemma detectionUB_cost {αmax : ℕ → Ω → ℝ} {t : ℕ} (hα : S.detectionUB αmax t) (ω : Ω) :
    condSum S.μ S.Fpre t (fun ω' => (1 - indB (S.wrong t) ω') * S.C t ω' * indB (S.pressed t) ω') ω ≤
      αmax t ω * condSum S.μ S.Fpre t (fun ω' => (1 - indB (S.wrong t) ω') * S.C t ω') ω := by
  have e1 : (fun ω' => (1 - indB (S.wrong t) ω') * S.C t ω') =
      fun ω' => ∑ m, S.cOf m * ((1 - indB (S.wrong t) ω') * S.magInd t m ω') := by
    funext ω'; rw [S.C_eq_sum_magInd, Finset.mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have e2 : (fun ω' => (1 - indB (S.wrong t) ω') * S.C t ω' * indB (S.pressed t) ω') =
      fun ω' => ∑ m, S.cOf m * ((1 - indB (S.wrong t) ω') * S.magInd t m ω' * indB (S.pressed t) ω') := by
    funext ω'; rw [S.C_eq_sum_magInd, Finset.mul_sum, Finset.sum_mul]
    exact sum_congr rfl fun m _ => by ring
  rw [e1, e2, condSum_sum, condSum_sum, Finset.mul_sum]
  refine sum_le_sum fun m _ => ?_
  rw [condSum_const_mul, condSum_const_mul]
  calc S.cOf m * condSum S.μ S.Fpre t
        (fun ω' => (1 - indB (S.wrong t) ω') * S.magInd t m ω' * indB (S.pressed t) ω') ω
      ≤ S.cOf m * (αmax t ω * condSum S.μ S.Fpre t
          (fun ω' => (1 - indB (S.wrong t) ω') * S.magInd t m ω') ω) :=
        mul_le_mul_of_nonneg_left (hα ω m) (S.cOf_nonneg m)
    _ = _ := by ring

/-- `(MI)` for the false press in cost-weighted form (equality).
Source: invariant-final.md proof of Statement 4. Kind: L. Fidelity: exact -/
lemma detectionEqUB_cost {α : ℕ → Ω → ℝ} {t : ℕ} (hα : S.detectionEqUB α t) (ω : Ω) :
    condSum S.μ S.Fpre t (fun ω' => (1 - indB (S.wrong t) ω') * S.C t ω' * indB (S.pressed t) ω') ω =
      α t ω * condSum S.μ S.Fpre t (fun ω' => (1 - indB (S.wrong t) ω') * S.C t ω') ω := by
  have e1 : (fun ω' => (1 - indB (S.wrong t) ω') * S.C t ω') =
      fun ω' => ∑ m, S.cOf m * ((1 - indB (S.wrong t) ω') * S.magInd t m ω') := by
    funext ω'; rw [S.C_eq_sum_magInd, Finset.mul_sum]
    exact sum_congr rfl fun m _ => by ring
  have e2 : (fun ω' => (1 - indB (S.wrong t) ω') * S.C t ω' * indB (S.pressed t) ω') =
      fun ω' => ∑ m, S.cOf m * ((1 - indB (S.wrong t) ω') * S.magInd t m ω' * indB (S.pressed t) ω') := by
    funext ω'; rw [S.C_eq_sum_magInd, Finset.mul_sum, Finset.sum_mul]
    exact sum_congr rfl fun m _ => by ring
  rw [e1, e2, condSum_sum, condSum_sum, Finset.mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [condSum_const_mul, condSum_const_mul, hα ω m]; ring

/-- Under compliance at `t` the omission is incurred exactly when right and pressed:
`omission_t = (1 − W_t) C_t Pr_t`.
Source: invariant-final.md proof of Statement 4 ("Omission likewise"). Kind: L. Fidelity: exact -/
lemma omission_of_kappa (t : ℕ) (ω : Ω) (hk : S.kappa t ω = true) :
    S.omission t ω = (1 - indB (S.wrong t) ω) * S.C t ω * indB (S.pressed t) ω := by
  unfold omission executed
  cases hp : S.pressed t ω <;> simp [indB, hk, hp]

/-- **Statement 4, the omission half, one round**: under compliance and `(αmax)` (`α^max_t`
`𝓕_t^-`-measurable), `E*[omission_t] ≤ E*[α^max_t (1 − W_t) C_t]` — the same tower step as
`expect_harm_le`, on the right-and-pressed event.
Source: [[corr-wf14-inventory]] 074 / invariant-final.md Statement 4 (second display), proof ("Omission likewise with `α^max_t`")
Kind: P (small: the tower step on the pre-press atoms)
Fidelity: exact
Hyps: (a) only -/
theorem expect_omission_le (t : ℕ) (αmax : ℕ → Ω → ℝ) (hk : ∀ ω, S.kappa t ω = true)
    (hα : S.detectionUB αmax t) (hmeas : S.Fpre.Meas t (αmax t)) :
    expect S.μ (S.omission t) ≤
      expect S.μ (fun ω => αmax t ω * ((1 - indB (S.wrong t) ω) * S.C t ω)) := by
  have e : S.omission t = fun ω => (1 - indB (S.wrong t) ω) * S.C t ω * indB (S.pressed t) ω :=
    funext fun ω => S.omission_of_kappa t ω (hk ω)
  rw [e]
  refine expect_le_of_condSum_le (A := S.Fpre) t fun ω => ?_
  rw [condSum_mul_meas t hmeas]
  exact S.detectionUB_cost hα ω

/-- **Statement 4, the omission half, one round, equality under `(MI)`**:
`E*[omission_t] = E*[α_t (1 − W_t) C_t]`.
Source: [[corr-wf14-inventory]] 074 / invariant-final.md Statement 4 ("with equality in both under (MI)")
Kind: P (small)
Fidelity: exact
Hyps: (a) only -/
theorem expect_omission_eq (t : ℕ) (α : ℕ → Ω → ℝ) (hk : ∀ ω, S.kappa t ω = true)
    (hα : S.detectionEqUB α t) (hmeas : S.Fpre.Meas t (α t)) :
    expect S.μ (S.omission t) =
      expect S.μ (fun ω => α t ω * ((1 - indB (S.wrong t) ω) * S.C t ω)) := by
  have e : S.omission t = fun ω => (1 - indB (S.wrong t) ω) * S.C t ω * indB (S.pressed t) ω :=
    funext fun ω => S.omission_of_kappa t ω (hk ω)
  rw [e]
  refine expect_eq_of_condSum_eq (A := S.Fpre) t fun ω => ?_
  rw [condSum_mul_meas t hmeas]
  exact S.detectionEqUB_cost hα ω

/-- **Statement 4 (D6), the omission half: the finite-horizon omission bound under compliance.**
`E*[Omit_T] ≤ ∑_{t ≤ T} E*[α^max_t (1 − W_t) C_t]` — compliance multiplies each round's expected
omission cost by the false-press rate.
Source: [[corr-wf14-inventory]] 074, 2-020 / invariant-final.md Statement 4 (second display, `≤` form)
Kind: P (small: the one-round tower step summed)
Fidelity: exact (`(1 − W_t) C_t` in place of the display's `(1 − ε_t) c_t`; `omit_le_detection_ratio` is the display)
Hyps: (a) only -/
theorem omit_le_detection (T : ℕ) (αmax : ℕ → Ω → ℝ) (hk : ∀ t ≤ T, ∀ ω, S.kappa t ω = true)
    (hα : ∀ t ≤ T, S.detectionUB αmax t) (hmeas : ∀ t ≤ T, S.Fpre.Meas t (αmax t)) :
    expect S.μ (S.Omit T) ≤
      ∑ t ∈ range (T + 1), expect S.μ (fun ω => αmax t ω * ((1 - indB (S.wrong t) ω) * S.C t ω)) := by
  unfold Omit
  rw [expect_sum_range]
  refine sum_le_sum fun t ht => ?_
  have htT := Nat.lt_succ_iff.1 (mem_range.1 ht)
  exact S.expect_omission_le t αmax (hk t htT) (hα t htT) (hmeas t htT)

/-- **Statement 4, the omission half, equality under `(MI)`.**
Source: [[corr-wf14-inventory]] 074 / invariant-final.md Statement 4 ("with equality in both under (MI)")
Kind: P (small)
Fidelity: exact
Hyps: (a) only -/
theorem omit_eq_detection (T : ℕ) (α : ℕ → Ω → ℝ) (hk : ∀ t ≤ T, ∀ ω, S.kappa t ω = true)
    (hα : ∀ t ≤ T, S.detectionEqUB α t) (hmeas : ∀ t ≤ T, S.Fpre.Meas t (α t)) :
    expect S.μ (S.Omit T) =
      ∑ t ∈ range (T + 1), expect S.μ (fun ω => α t ω * ((1 - indB (S.wrong t) ω) * S.C t ω)) := by
  unfold Omit
  rw [expect_sum_range]
  refine sum_congr rfl fun t ht => ?_
  have htT := Nat.lt_succ_iff.1 (mem_range.1 ht)
  exact S.expect_omission_eq t α (hk t htT) (hα t htT) (hmeas t htT)

/-- `(1 − ε_t) c_t`: the conditional expected rightness-weighted omission cost on the pre-press atom,
as a ratio (junk-safe through `expect_mul_condSum_div`) — the dual of `epsH`.
Source: [[corr-wf14-inventory]] 074 / invariant-final.md S2 step 2–3 (`ε_t`, `c_t`)
Kind: D
Fidelity: exact (the product `(1 − ε_t) c_t` directly; the two factors are not separated) -/
noncomputable def epsC (t : ℕ) (ω : Ω) : ℝ :=
  condSum S.μ S.Fpre t (fun ω' => (1 - indB (S.wrong t) ω') * S.C t ω') ω / atomMass S.μ S.Fpre t ω

/-- **The second display's form**: `E*[Omit_T] ≤ ∑_{t ≤ T} E*[α^max_t (1 − ε_t) c_t]`.
Source: [[corr-wf14-inventory]] 074 / invariant-final.md Statement 4 (second display)
Kind: C (`omit_le_detection` + the tower identity)
Fidelity: exact
Hyps: (a) only -/
theorem omit_le_detection_ratio (T : ℕ) (αmax : ℕ → Ω → ℝ) (hk : ∀ t ≤ T, ∀ ω, S.kappa t ω = true)
    (hα : ∀ t ≤ T, S.detectionUB αmax t) (hmeas : ∀ t ≤ T, S.Fpre.Meas t (αmax t)) :
    expect S.μ (S.Omit T) ≤ ∑ t ∈ range (T + 1), expect S.μ (fun ω => αmax t ω * S.epsC t ω) := by
  refine (S.omit_le_detection T αmax hk hα hmeas).trans (le_of_eq (sum_congr rfl fun t ht => ?_))
  have htT := Nat.lt_succ_iff.1 (mem_range.1 ht)
  unfold epsC
  exact (expect_mul_condSum_div t (hmeas t htT) _).symm

/-- **Statement 4, both halves together (D6 for `Reg_T`)**: under compliance, `(βmin)` and `(αmax)`,
`E*[Reg_T] ≤ ∑_{t ≤ T} E*[(1 − β^min_t) W_t H_t] + ∑_{t ≤ T} E*[α^max_t (1 − W_t) C_t]`.
Source: [[corr-wf14-inventory]] 074 / invariant-final.md Statement 4 (both displays), D7 (`Reg_T = Harm_T + Omit_T`)
Kind: C (`harm_le_detection` + `omit_le_detection`)
Fidelity: exact
Hyps: (a) only -/
theorem reg_le_detection (T : ℕ) (βmin αmax : ℕ → Ω → ℝ) (hk : ∀ t ≤ T, ∀ ω, S.kappa t ω = true)
    (hβ : ∀ t ≤ T, S.detectionLB βmin t) (hβm : ∀ t ≤ T, S.Fpre.Meas t (βmin t))
    (hα : ∀ t ≤ T, S.detectionUB αmax t) (hαm : ∀ t ≤ T, S.Fpre.Meas t (αmax t)) :
    expect S.μ (S.Reg T) ≤
      (∑ t ∈ range (T + 1), expect S.μ (fun ω => (1 - βmin t ω) * (indB (S.wrong t) ω * S.H t ω))) +
        ∑ t ∈ range (T + 1), expect S.μ (fun ω => αmax t ω * ((1 - indB (S.wrong t) ω) * S.C t ω)) := by
  have e : S.Reg T = fun ω => S.Harm T ω + S.Omit T ω := funext (S.Reg_eq_Harm_add_Omit T)
  rw [e, Found.CorrThreeStep.expect_add]
  exact add_le_add (S.harm_le_detection T βmin hk hβ hβm) (S.omit_le_detection T αmax hk hα hαm)

/-- **Universal defiance**: `Harm_T = ∑_{t ≤ T} W_t H_t` and `Omit_T = 0` pointwise.
Source: [[corr-wf14-inventory]] 074 / invariant-final.md Statement 4 ("Under universal defiance")
Kind: L
Fidelity: exact -/
theorem defiance (T : ℕ) (hk : ∀ t ≤ T, ∀ ω, S.kappa t ω = false) (ω : Ω) :
    S.Harm T ω = ∑ t ∈ range (T + 1), indB (S.wrong t) ω * S.H t ω ∧ S.Omit T ω = 0 := by
  constructor
  · unfold Harm
    refine sum_congr rfl fun t ht => ?_
    unfold harm
    rw [indB_true (S.executed_of_not_kappa t ω (hk t (Nat.lt_succ_iff.1 (mem_range.1 ht)) ω)), mul_one]
  · unfold Omit
    refine sum_eq_zero fun t ht => ?_
    unfold omission
    rw [indB_true (S.executed_of_not_kappa t ω (hk t (Nat.lt_succ_iff.1 (mem_range.1 ht)) ω))]
    ring

/-- **The boundedness corollary is a tail statement, recorded as such**: if the per-round bounds are
summable then `sup_T E*[Harm_T]` is finite. Not a D6 guarantee (no constant); listed to show the shape.
Source: [[corr-wf14-inventory]] 074, 2-020 / invariant-final.md Statement 4 ("a tail statement about a series")
Kind: L
Fidelity: exact (recorded, not headlined) -/
theorem harm_bounded_of_summable (βmin : ℕ → Ω → ℝ) (hk : ∀ t ω, S.kappa t ω = true)
    (hβ : ∀ t, S.detectionLB βmin t) (hmeas : ∀ t, S.Fpre.Meas t (βmin t))
    (hs : Summable fun t => expect S.μ (fun ω => (1 - βmin t ω) * (indB (S.wrong t) ω * S.H t ω)))
    (hnn : ∀ t, 0 ≤ expect S.μ (fun ω => (1 - βmin t ω) * (indB (S.wrong t) ω * S.H t ω))) :
    ∀ T, expect S.μ (S.Harm T) ≤
      ∑' t, expect S.μ (fun ω => (1 - βmin t ω) * (indB (S.wrong t) ω * S.H t ω)) := by
  intro T
  exact (S.harm_le_detection T βmin (fun t _ => hk t) (fun t _ => hβ t) (fun t _ => hmeas t)).trans
    (hs.sum_le_tsum _ (fun t _ => hnn t))

end ShutdownProc

end Cleanroom.Corrigibility.CorrTrajectory
