import Cleanroom.Corrigibility.CorrIndifference.Indifference
import Mathlib.Tactic.FinCases

/-!
# Armstrong 2015 Theorem 4.1 (T11) and the Arbital θ-offset (T12)

Armstrong's value-change indifference (eq. 6): a `u`-maximiser that will transition to `v`
maximises `v + E(u | u → u) − E(v | u → v)` after the transition and `u` if the signal is
blocked. On the two-period model (`O = Bool × Y`, `true` = switch) this is *literally* the §3
indifferent utility with `U_N = u`, `U_S = v`, `Press = {switch} × Y`, so Theorem 4.1 and Lemmas
4.2–4.4 are `EU_indiffU_eq_vN` and `EU_indiffU_US_invariant` read on this carrier: "acts as a
pure `u`-maximiser" is maximisation of the *stay-conditional* value `E(u | stay ; a)`, i.e.
under the dogmatic kernel (finding F9); Lemma 4.3's indifference to `v`-only actions is
Theorem 6. The Arbital `θ`-offset: `max_a (E[U_Y | a] + θ) = max_a E[U_X | a]` with
`θ := max_a E[U_X | a] − max_a E[U_Y | a]`, and objection (b) as the two-stage value
`M_X(a₁)`, independent of `U_Y` — the max-form twin of T6(b).

Source: [[corr-refs-inventory]] 014 (armstrong-2015-motivated-value-selection l. 168–214),
012 (arbital-utility-indifference l. 97–168); corr-core-020.
-/

namespace Cleanroom.Corrigibility.CorrIndifference

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep SoaresModel

set_option linter.unusedSectionVars false

/-! ## T11. Armstrong 2015 Theorem 4.1 -/

namespace Armstrong2015

variable {A Y : Type*} [Fintype Y] [DecidableEq Y]

/-- **The two-period model:** after action `a`, the transition `T ∈ {stay, switch}` (`false`/`true`)
and the period-2 state `y` are drawn from `t a : Distr (Bool × Y)`; the period-2 "action" is
trivial (`A₂ = Unit`) — Armstrong's utilities are functions of the period-2 state. `Press` is the
switch event.
Source: [[corr-refs-inventory]] 014 / armstrong-2015 eq. (6) and Theorem 4.1
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
def twoPeriod (t : A → Distr (Bool × Y)) : SoaresModel (Bool × Y) A Unit where
  Press := ({true} : Finset Bool) ×ˢ (univ : Finset Y)
  p := t

/-- A period-2 utility `u : A → Y → ℝ` as a Soares utility (ignores the transition bit and the
trivial final action).
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def lift (u : A → Y → ℝ) : A → Bool × Y → Unit → ℝ := fun a bo _ => u a bo.2

/-- **Armstrong's meta-utility (eq. 6) is the §3 indifferent utility:** `u` on stay,
`v − E(v | switch ; a) + E(u | stay ; a)` on switch — pointwise equal to
`indiffU (lift u) (lift v)` on `twoPeriod t` (the `f`-term is `vN − vS = E(u | stay) − E(v | switch)`).
Source: [[corr-refs-inventory]] 014 / armstrong-2015 eq. (6); corr-core-020
Kind: L
Fidelity: exact -/
theorem meta_eq_indiffU (t : A → Distr (Bool × Y)) (u v : A → Y → ℝ) (a : A) (b : Bool) (y : Y) :
    (twoPeriod t).indiffU (lift u) (lift v) a (b, y) () =
      if b then v a y + ((twoPeriod t).vN (lift u) a - (twoPeriod t).vS (lift v) a) else u a y := by
  simp only [indiffU, SoaresModel.f, twoPeriod, lift, mem_product, mem_singleton, mem_univ,
    and_true]

/-- **Theorem 4.1 / Lemmas 4.2–4.3 as one identity:** `E[meta ; a] = E(u | stay ; a)` for every
`a` and every `v` — the agent's ordering on `A` is the ordering of the *stay-conditional* value
of `u`. "Acts as a pure `u`-maximiser" is true only in this sense (finding F9); the
independence from `v` is Lemma 4.3 = Theorem 6 (`EU_indiffU_US_invariant`).
Source: [[corr-refs-inventory]] 014 / armstrong-2015 Theorem 4.1, Lemmas 4.2–4.4
Kind: L
Fidelity: exact (the identity; the source's "pure `u`-maximiser" is weaker than it sounds, F9)
Hyps: (a) `ha` keeps `vN` the conditional value; unused by the proof -/
theorem EU_meta_eq_stayValue (t : A → Distr (Bool × Y)) (u v : A → Y → ℝ) (a : A)
    (ha : (twoPeriod t).pressMass a < 1) :
    (twoPeriod t).EU ((twoPeriod t).indiffU (lift u) (lift v)) a = (twoPeriod t).vN (lift u) a := by
  have _ := ha
  exact (twoPeriod t).EU_indiffU_eq_vN _ _ a

/-- **Lemma 4.3 (indifference to `v`-only actions) is Theorem 6's invariance** on this carrier.
Source: [[corr-refs-inventory]] 014 / armstrong-2015 Lemma 4.3 (corr-refs-014 flag: "the property is the bug")
Kind: L
Fidelity: exact -/
theorem EU_meta_v_invariant (t : A → Distr (Bool × Y)) (u v v' : A → Y → ℝ) (a : A) :
    (twoPeriod t).EU ((twoPeriod t).indiffU (lift u) (lift v)) a =
      (twoPeriod t).EU ((twoPeriod t).indiffU (lift u) (lift v')) a :=
  (twoPeriod t).EU_indiffU_US_invariant _ _ _ a

end Armstrong2015

/-! ## T12. The Arbital θ-offset -/

namespace Arbital

variable {A : Type*} [Fintype A] [Nonempty A]

/-- **The offset `θ := max_a E[U_X | a] − max_a E[U_Y | a]`**, over the conditional expectations
`EX EY : A → ℝ` (the report's `U_X`, `U_Y` do not depend on `S`).
Source: [[corr-refs-inventory]] 012 / arbital-utility-indifference §"Naive indifference"
Kind: D
Fidelity: exact -/
noncomputable def theta (EX EY : A → ℝ) : ℝ :=
  univ.sup' univ_nonempty EX - univ.sup' univ_nonempty EY

/-- **The offset equalises the maxima:** `max_a (E[U_Y | a] + θ) = max_a E[U_X | a]`.
Source: [[corr-refs-inventory]] 012 / arbital-utility-indifference (the display after `θ`)
Kind: L
Fidelity: exact -/
theorem sup_add_theta (EX EY : A → ℝ) :
    univ.sup' univ_nonempty (fun a => EY a + theta EX EY) = univ.sup' univ_nonempty EX := by
  unfold theta
  apply le_antisymm
  · rw [sup'_le_iff]; intro a _
    have := le_sup' EY (mem_univ a); linarith
  · obtain ⟨a, -, ha⟩ := exists_mem_eq_sup' (univ_nonempty (α := A)) EY
    have hle : EY a + (univ.sup' univ_nonempty EX - univ.sup' univ_nonempty EY) ≤
        univ.sup' univ_nonempty
          (fun a => EY a + (univ.sup' univ_nonempty EX - univ.sup' univ_nonempty EY)) :=
      le_sup' (fun a => EY a + (univ.sup' univ_nonempty EX - univ.sup' univ_nonempty EY))
        (mem_univ a)
    linarith

variable {A₁ A₂ : Type*} [Fintype A₂] [Nonempty A₂]

/-- **Objection (b), the two-stage recomputed offset:** after `a₁`, `θ(a₁)` is recomputed from
the reachable maxima `M_X(a₁) := max_{a₂} E[U_X | a₁, a₂]`, `M_Y(a₁)`; the agent then maximises
`U_X` on `¬s` and `U_Y + θ(a₁)` on `s`, and with `U_X, U_Y` independent of `s` and `s ⊥ a₂` given
`a₁`, its first-stage value is `(1 − p_s(a₁)) M_X(a₁) + p_s(a₁) (M_Y(a₁) + θ(a₁))`.
Source: [[corr-refs-inventory]] 012 / arbital-utility-indifference (b) ("recalculated `θ`s")
Kind: D
Fidelity: variant: the two-stage value stated as an inlined formula over the reachable maxima,
not as the `EU` of a `twoObs` model (the independence assumptions are what make the conditional
expectations functions of `(a₁, a₂)` alone; audit r2, N-2) -/
noncomputable def twoStageValue (EX EY : A₁ → A₂ → ℝ) (ps : A₁ → ℝ) (a₁ : A₁) : ℝ :=
  (1 - ps a₁) * univ.sup' univ_nonempty (EX a₁) +
    ps a₁ * univ.sup' univ_nonempty (fun a₂ => EY a₁ a₂ + theta (EX a₁) (EY a₁))

/-- **The two-stage value is `M_X(a₁)`, independent of `U_Y` and of `p_s`:** the max-form twin of
Theorem 6's `U_S`-invariance — the recomputed offset makes the press branch worth exactly the
silence branch's maximum, so nothing about `U_Y` (or about the press probability) reaches the
first-stage choice.
Source: [[corr-refs-inventory]] 012 / arbital-utility-indifference (b)
Kind: L
Fidelity: variant: over the inlined `twoStageValue`, not `twoObs` (audit r2, N-2)
Hyps: (a) -/
theorem twoStageValue_eq (EX EY : A₁ → A₂ → ℝ) (ps : A₁ → ℝ) (a₁ : A₁) :
    twoStageValue EX EY ps a₁ = univ.sup' univ_nonempty (EX a₁) := by
  unfold twoStageValue; rw [sup_add_theta]; ring

/-- **Invariance in `U_Y`:** two `U_Y`'s give the same two-stage value at every `a₁`.
Source: [[corr-refs-inventory]] 012 / arbital-utility-indifference (b)
Kind: L
Fidelity: exact -/
theorem twoStageValue_EY_invariant (EX EY EY' : A₁ → A₂ → ℝ) (ps : A₁ → ℝ) (a₁ : A₁) :
    twoStageValue EX EY ps a₁ = twoStageValue EX EY' ps a₁ := by
  rw [twoStageValue_eq, twoStageValue_eq]

/-- **Witness (`Fin 2 × Fin 2`):** with `E[U_X | a₁, a₂] = ![![3, 1], ![2, 5]]` and press
probabilities `(1/2, 1/2)`, the first-stage values are `(3, 5)` for `U_Y` with maxima `(10, 0)`
and again `(3, 5)` after lowering `U_Y` to `(0, −10)`; the choice (`a₁ = 1`) is unchanged.
Source: [[corr-refs-inventory]] 012 (mandate T12 witness)
Kind: N+
Fidelity: exact
Hyps: (a) -/
theorem witness :
    let EX : Fin 2 → Fin 2 → ℝ := fun a₁ a₂ => if a₁ = 0 then (if a₂ = 0 then 3 else 1)
      else (if a₂ = 0 then 2 else 5)
    let EY : Fin 2 → Fin 2 → ℝ := fun a₁ _ => if a₁ = 0 then 10 else 0
    let EY' : Fin 2 → Fin 2 → ℝ := fun a₁ _ => if a₁ = 0 then 0 else -10
    let ps : Fin 2 → ℝ := fun _ => 1 / 2
    twoStageValue EX EY ps 0 = 3 ∧ twoStageValue EX EY ps 1 = 5 ∧
      twoStageValue EX EY' ps 0 = 3 ∧ twoStageValue EX EY' ps 1 = 5 := by
  intro EX EY EY' ps
  have h0 : univ.sup' univ_nonempty (EX 0) = 3 := by
    apply le_antisymm
    · rw [sup'_le_iff]; intro a _; fin_cases a <;> simp [EX]
    · exact le_sup'_of_le (EX 0) (mem_univ 0) (by simp [EX])
  have h1 : univ.sup' univ_nonempty (EX 1) = 5 := by
    apply le_antisymm
    · rw [sup'_le_iff]; intro a _; fin_cases a <;> simp [EX] <;> norm_num
    · exact le_sup'_of_le (EX 1) (mem_univ 1) (by simp [EX])
  simp only [twoStageValue_eq, h0, h1, and_self]

end Arbital

end Cleanroom.Corrigibility.CorrIndifference
