import Cleanroom.Corrigibility.CorrIndifference.Soares

/-!
# The two-observation instance `O = {Pr, ¬Pr}` (§2.1's setting)

`corr-three-step`'s `Obs` carries no `Fintype` instance (it never sums over observations); this
module supplies one (infrastructure, in this package's namespace) and the Soares model with
`O = Obs`, `Press = {press}`, where `vN(a₁)` is literally `max_{a₂} U_N(a₁, ¬Pr, a₂)` (eq. 7).
-/

namespace Cleanroom.Corrigibility.CorrIndifference

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep

set_option linter.unusedSectionVars false

/-- `Obs` is finite, with `univ = {press, silent}` definitionally (infrastructure; an instance on
`corr-three-step`'s type, which it does not provide).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
instance instFintypeObs : Fintype Obs := ⟨{Obs.press, Obs.silent}, fun x => by cases x <;> simp⟩

/-- Sums over `Obs` expand to two terms. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma Obs.sum_eq (f : Obs → ℝ) : ∑ o, f o = f .press + f .silent := by
  rw [show (univ : Finset Obs) = {Obs.press, Obs.silent} from rfl, sum_pair (by decide)]

namespace SoaresModel

variable {A₁ A₂ : Type*} [Fintype A₂] [Nonempty A₂]

/-- The two-point observation distribution with press probability `q`.
Source: [[corr-refs-inventory]] 002 / soares-2015 §2.1 (`O = {Pr, ¬Pr}`)
Kind: D
Fidelity: exact -/
noncomputable def obsPoint (q : ℝ) (hq : q ∈ Set.Icc (0 : ℝ) 1) : Distr Obs where
  mass o := match o with
    | .press => q
    | .silent => 1 - q
  nonneg o := by cases o <;> simp <;> linarith [hq.1, hq.2]
  sum_eq_one := by rw [Obs.sum_eq]; simp

/-- **The §2.1 model:** `O = Obs`, `Press = {press}`, press probability `q a₁`.
Source: [[corr-refs-inventory]] 002 / soares-2015 §2.1
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def twoObs (q : A₁ → ℝ) (hq : ∀ a, q a ∈ Set.Icc (0 : ℝ) 1) :
    SoaresModel Obs A₁ A₂ where
  Press := {Obs.press}
  p a := obsPoint (q a) (hq a)

/-- The press mass of `twoObs` is `q a₁`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] lemma twoObs_pressMass (q : A₁ → ℝ) (hq : ∀ a, q a ∈ Set.Icc (0 : ℝ) 1) (a : A₁) :
    (twoObs (A₂ := A₂) q hq).pressMass a = q a := by
  rw [pressMass_eq_sum]; simp [twoObs, obsPoint]

/-- **`vN` in §2.1 is the silent best value:** with `O = {Pr, ¬Pr}` and `q a₁ < 1`,
`vN(a₁) = max_{a₂} U_N(a₁, ¬Pr, a₂)` — the source's eq. (7) definition, recovered from the
quotient of record.
Source: [[corr-refs-inventory]] 002 / soares-2015 §2.1 eq. (7)
Kind: L
Fidelity: exact -/
theorem twoObs_vN (q : A₁ → ℝ) (hq : ∀ a, q a ∈ Set.Icc (0 : ℝ) 1) (UN : A₁ → Obs → A₂ → ℝ)
    (a : A₁) (h : q a < 1) : (twoObs (A₂ := A₂) q hq).vN UN a = best UN a .silent := by
  have hc : ({Obs.press} : Finset Obs)ᶜ = {Obs.silent} := by decide
  unfold vN branchSum
  rw [twoObs_pressMass]
  simp only [twoObs, hc, sum_singleton, obsPoint]
  have : (1 : ℝ) - q a ≠ 0 := by linarith
  field_simp

/-- `twoObs`'s press set is `{press}`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma twoObs_Press (q : A₁ → ℝ) (hq : ∀ a, q a ∈ Set.Icc (0 : ℝ) 1) :
    (twoObs (A₂ := A₂) q hq).Press = {Obs.press} := rfl

/-- **On `O = {Pr, ¬Pr}` with every action silent-capable, the ceiling is attained by a `vN`, so
the honest action is a global optimum at the equal-value choice:** with every `q a < 1` and
`c_high = silentMax` (the source's (10)), some action `a₀` has `vN(a₀) = silentMax` and
`E[U ; a] ≤ E[U ; a₀]` for every `a` (with `E[U ; a₀] = silentMax`, `EU_mixU_eq_of_vN_eq`). So on
the source's own carrier, when every action can be silent, the sentence "(10) averts any
incentives to steer" is true in the global, weak sense — the honest action is never strictly
beaten, though certain-press actions tie it — and its failure is pairwise (F2). **`hq1` is
load-bearing** (audit r2, B-1): (10)'s maximum ranges over every first action, certain-press ones
included; when only a certain-press action carries it, that cell is unreachable, its `vN` is the
junk `0`, no `vN` attains the ceiling, and the honest action is strictly beaten on this carrier
too (`Witnesses.strict_cause_steering_twoObs`). The ceiling at which the weak reading holds with
no such condition is `max vN` (`vNmax_is_global_optimum`).
Source: [[corr-refs-inventory]] 004 / soares-2015 eq. (10), the sentence after it (audit r1, NB-1; audit r2, B-1)
Kind: C
Fidelity: exact (the source's two-observation setting, every action silent-capable)
Hyps: (a) `hq1` (every action silent-capable, `q a < 1`; load-bearing, see above) -/
theorem twoObs_honest_is_global_optimum [Fintype A₁] [Nonempty A₁] [DecidableEq A₂]
    (q : A₁ → ℝ) (hq : ∀ a, q a ∈ Set.Icc (0 : ℝ) 1) (hq1 : ∀ a, q a < 1)
    (UN : A₁ → Obs → A₂ → ℝ) {Sh : Finset A₂} (hSh : Sh.Nonempty) {clow : ℝ}
    (hP : (twoObs (A₂ := A₂) q hq).Pressᶜ.Nonempty)
    (hc : clow < (twoObs (A₂ := A₂) q hq).silentMax UN hP) :
    ∃ a₀, (twoObs (A₂ := A₂) q hq).vN UN a₀ = (twoObs (A₂ := A₂) q hq).silentMax UN hP ∧
      ∀ a, (twoObs (A₂ := A₂) q hq).EU
          ((twoObs (A₂ := A₂) q hq).mixU UN Sh ((twoObs (A₂ := A₂) q hq).silentMax UN hP) clow) a ≤
        (twoObs (A₂ := A₂) q hq).EU
          ((twoObs (A₂ := A₂) q hq).mixU UN Sh ((twoObs (A₂ := A₂) q hq).silentMax UN hP) clow) a₀ := by
  obtain ⟨a₀, o, ho, hmax⟩ := (twoObs (A₂ := A₂) q hq).exists_eq_silentMax UN hP
  have hnp : o ∉ ({Obs.press} : Finset Obs) := by
    rw [← twoObs_Press (A₂ := A₂) q hq]; exact mem_compl.mp ho
  have hos : o = Obs.silent := by cases o <;> simp_all
  subst hos
  have hv : (twoObs (A₂ := A₂) q hq).vN UN a₀ = (twoObs (A₂ := A₂) q hq).silentMax UN hP := by
    rw [twoObs_vN q hq UN a₀ (hq1 a₀), hmax]
  exact ⟨a₀, hv, fun a => (twoObs (A₂ := A₂) q hq).EU_mixU_le_of_vN_eq UN hSh hc
    (fun a o ho => (twoObs (A₂ := A₂) q hq).best_le_silentMax UN hP a ho) hv a⟩

end SoaresModel

end Cleanroom.Corrigibility.CorrIndifference
