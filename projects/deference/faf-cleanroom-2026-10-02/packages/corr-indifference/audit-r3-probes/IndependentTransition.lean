import Cleanroom.Corrigibility.CorrIndifference.Transition

/-!
# Audit r3 (fidelity) probe: under Armstrong 2015's own assumption the "stay-conditional" value
is the plain value.

Armstrong 2015 §4 assumes the transition signal "passes through some stochastic process, that is
almost certain to let the signal through … but has some infinitesimal chance of blocking it":
`u → u` is an exogenous blocking event, independent of the period-2 state and of the action
(Armstrong 2010 §3 wants it to be a quantum measurement; Fallenstein 2014 makes the same point).
When the transition bit factors out of `t a`, `vN (lift u) a = E[u | stay ; a]` is the plain
expectation `∑_y p_y(y) u(a, y) = E[u ; a]`, so Theorem 4.1's "acts as a pure `u` maximiser" is
exact in the source's setting; F9's "not `E(u ; a)`" holds only for the package's general kernel
`t : A → Distr (Bool × Y)`, where the transition may be correlated with the state (the Soares-style
news-management case). Not imported by the library.
-/

namespace Cleanroom.Corrigibility.CorrIndifference.AuditR3

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep SoaresModel Armstrong2015

variable {A Y : Type*} [Fintype Y] [DecidableEq Y]

/-- If `t a` factors as `p_b(b) · p_y(y)` (transition bit independent of the state), then both the
stay-conditional value and the plain value of `u` are `∑_y p_y(y) u(a, y)`; `p_b(false) ≠ 0` keeps
the quotient the conditional value. -/
theorem vN_lift_eq_EU_of_independent (t : A → Distr (Bool × Y)) (pb : A → Bool → ℝ)
    (py : A → Y → ℝ) (hfac : ∀ a b y, (t a).mass (b, y) = pb a b * py a y)
    (hpy : ∀ a, ∑ y, py a y = 1) (u : A → Y → ℝ) (a : A) (hstay : pb a false ≠ 0) :
    (twoPeriod t).vN (lift u) a = ∑ y, py a y * u a y ∧
      (twoPeriod t).EU (lift u) a = ∑ y, py a y * u a y := by
  have hbest : ∀ b y, best (lift u) a (b, y) = u a y := fun b y =>
    best_eq_of_const (fun _ => rfl)
  have hrow : ∀ b, ∑ y, pb a b * py a y * u a y = pb a b * ∑ y, py a y * u a y := fun b => by
    rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
  have hsum : pb a true + pb a false = 1 := by
    have h := (t a).sum_eq_one
    rw [Fintype.sum_prod_type, Fintype.sum_bool] at h
    simp only [hfac] at h
    rw [← mul_sum, ← mul_sum, hpy a, mul_one, mul_one] at h
    exact h
  have hpm : (twoPeriod t).pressMass a = pb a true := by
    rw [pressMass_eq_sum]
    change ∑ o ∈ ({true} : Finset Bool) ×ˢ (univ : Finset Y), (t a).mass o = _
    rw [sum_product, sum_singleton]
    simp only [hfac]
    rw [← mul_sum, hpy a, mul_one]
  have hcompl : (({true} : Finset Bool) ×ˢ (univ : Finset Y))ᶜ =
      ({false} : Finset Bool) ×ˢ univ := by
    ext ⟨b, y⟩; cases b <;> simp
  have hbs : (twoPeriod t).branchSum (lift u) a (twoPeriod t).Pressᶜ =
      pb a false * ∑ y, py a y * u a y := by
    change ∑ o ∈ (({true} : Finset Bool) ×ˢ (univ : Finset Y))ᶜ,
      (t a).mass o * best (lift u) a o = _
    rw [hcompl, sum_product, sum_singleton, ← hrow]
    exact sum_congr rfl fun y _ => by rw [hfac, hbest]
  have hfac' : ∀ b y, ((twoPeriod t).p a).mass (b, y) = pb a b * py a y := fun b y => hfac a b y
  have hEU : (twoPeriod t).EU (lift u) a = ∑ y, py a y * u a y := by
    unfold EU
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [hfac', hbest]
    rw [hrow, hrow, ← add_mul, hsum, one_mul]
  refine ⟨?_, hEU⟩
  unfold vN
  rw [hbs, hpm, show (1 : ℝ) - pb a true = pb a false by linarith]
  field_simp

end Cleanroom.Corrigibility.CorrIndifference.AuditR3
