import Cleanroom.Corrigibility.CorrLandscape.Map
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# `corr-landscape` — `Regret`: Proposition R′ and its tightness (T15, load-bearing 2; extension E1)

`landscape-final.md` S6 / P6 ([[corr-wf14b-inventory]] 064): if the agent's legitimacy credence is
within `δ` of the objective posterior on every positive-mass signal (`covered`), then

  `ℓ*(r_m̂) − ℓ*(r*) ≤ (c + h) δ + |k̂ − k|`.

Proof as the source's: a flipped signal costs `(c + h)|π*(s) − q_k|` times its mass; a flip forces
`|π*(s) − q_k| ≤ δ + |k̂ − k|/(c + h)`; the masses sum to at most one. Corollary at `δ = 0`, `k̂ = k`:
regret `0`.

**Tightness (extension E1).** On a one-signal law the bound is *attained* exactly: `π*(s) = q_k̂ − δ`,
`π̂(s) = q_k̂`, `k̂ ≥ k` gives regret `= (c + h) δ + |k̂ − k|` (`regret_attained`; worked `c = 1`,
`h = 4`, `k = k̂ = 0`, `δ = 1/10`: regret `1/2`). On the other side (`k̂ < k`, where the rule's strict `<`
puts the extremal instance just below the threshold) the bound is approached: for every `η > 0` an
instance with regret `= (c + h) δ + |k̂ − k| − η` (`regret_approached`, stated for `k̂ ≤ k`, so it covers
the source's own `k̂ = k` instance). The "only if" is also in Lean: for `k̂ < k` **every** covered instance
has regret strictly below the bound (`regret_lt_of_lt`, through the strict per-signal bound `excess_lt`).
Together: the supremum of the regret over instances at tolerance `δ` is `(c + h) δ + |k̂ − k|`, attained
iff `k̂ ≥ k` (or trivially at `δ = 0 = |k̂ − k|`). The source's "`0.500` vs `0.505`" is the approached side.
-/

namespace Cleanroom.Corrigibility.CorrLandscape

open FactoredSpaces Cleanroom.Found.CorrThreeStep
open Finset hiding expect

set_option linter.unusedSectionVars false

namespace Regret

open Map

variable {S : Type} [Fintype S] [DecidableEq S]

/-- `qk_sub` (supporting lemma): `q_k̂ − q_k = (k − k̂)/(c + h)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma qk_sub {c h : ℝ} (k kh : ℝ) (hch : 0 < c + h) : qk c h kh - qk c h k = (k - kh) / (c + h) := by
  unfold qk; field_simp; ring

/-- `abs_qk_sub` (supporting lemma): `|q_k̂ − q_k| = |k̂ − k|/(c + h)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma abs_qk_sub {c h : ℝ} (k kh : ℝ) (hch : 0 < c + h) :
    |qk c h kh - qk c h k| = |kh - k| / (c + h) := by
  rw [qk_sub k kh hch, abs_div, abs_of_pos hch, abs_sub_comm]

/-- **The per-signal excess** of the conditioned decision over the Bayes decision is at most
`P*(s) ((c + h) δ + |k̂ − k|)` (P6's "a flipped signal costs `(c+h)|π*(s) − q_k|`, and a flip forces
`|π*(s) − q_k| ≤ δ + |k̂ − k|/(c + h)`").
Source: [[corr-wf14b-inventory]] 064 / landscape-final.md P6
Kind: P
Fidelity: exact -/
lemma excess_le (μ : Distr (S × Bool)) (πh : S → ℝ) {c h : ℝ} (k kh δ : ℝ) (hch : 0 < c + h)
    (hδ : 0 ≤ δ) (s : S) (hcov : 0 < sigMass μ s → |πh s - piStar μ s| ≤ δ) :
    cost μ c h k (conditionedRule πh kh c h s) s - cost μ c h k (bayesRule μ c h k s) s ≤
      sigMass μ s * ((c + h) * δ + |kh - k|) := by
  have hRHS : 0 ≤ sigMass μ s * ((c + h) * δ + |kh - k|) :=
    mul_nonneg (sigMass_nonneg μ s) (add_nonneg (mul_nonneg hch.le hδ) (abs_nonneg _))
  rcases (sigMass_nonneg μ s).lt_or_eq with hpos | hzero
  · have hc := hcov hpos
    have hleg : legMass μ s = piStar μ s * sigMass μ s := by
      rw [piStar, div_mul_cancel₀ _ hpos.ne']
    have key := cost_true_sub_false μ k hch s
    have hq := abs_qk_sub k kh hch
    have hqq : |kh - k| / (c + h) * (c + h) = |kh - k| := div_mul_cancel₀ _ hch.ne'
    have a1 := abs_le.1 hc
    have a2 := le_abs_self (qk c h kh - qk c h k)
    have a3 := neg_abs_le (qk c h kh - qk c h k)
    by_cases h1 : πh s < qk c h kh <;> by_cases h2 : legMass μ s < qk c h k * sigMass μ s
    · have hb1 : conditionedRule πh kh c h s = true := by simp [conditionedRule, h1]
      have hb2 : bayesRule μ c h k s = true := by simp [bayesRule, h2]
      rw [hb1, hb2, sub_self]; exact hRHS
    · -- the conditioned rule resists, Bayes accepts: `π* ≥ q_k`
      have hb1 : conditionedRule πh kh c h s = true := by simp [conditionedRule, h1]
      have hb2 : bayesRule μ c h k s = false := by simp [bayesRule, h2]
      rw [hb1, hb2, key, hleg]
      have e1 : (c + h) * (piStar μ s - qk c h k) ≤ (c + h) * δ + |kh - k| := by
        have : piStar μ s - qk c h k ≤ δ + |kh - k| / (c + h) := by
          rw [← hq]; linarith
        calc (c + h) * (piStar μ s - qk c h k) ≤ (c + h) * (δ + |kh - k| / (c + h)) :=
              mul_le_mul_of_nonneg_left this hch.le
          _ = (c + h) * δ + |kh - k| := by rw [mul_add, mul_comm (c + h) (|kh - k| / (c + h)), hqq]
      calc (c + h) * (piStar μ s * sigMass μ s - qk c h k * sigMass μ s)
          = sigMass μ s * ((c + h) * (piStar μ s - qk c h k)) := by ring
        _ ≤ sigMass μ s * ((c + h) * δ + |kh - k|) := mul_le_mul_of_nonneg_left e1 hpos.le
    · -- the conditioned rule accepts, Bayes resists: `π* < q_k`
      have hb1 : conditionedRule πh kh c h s = false := by simp [conditionedRule, h1]
      have hb2 : bayesRule μ c h k s = true := by simp [bayesRule, h2]
      rw [hb1, hb2, ← neg_sub, key, hleg]
      rw [not_lt] at h1
      have e1 : (c + h) * (qk c h k - piStar μ s) ≤ (c + h) * δ + |kh - k| := by
        have : qk c h k - piStar μ s ≤ δ + |kh - k| / (c + h) := by
          rw [← hq]; linarith
        calc (c + h) * (qk c h k - piStar μ s) ≤ (c + h) * (δ + |kh - k| / (c + h)) :=
              mul_le_mul_of_nonneg_left this hch.le
          _ = (c + h) * δ + |kh - k| := by rw [mul_add, mul_comm (c + h) (|kh - k| / (c + h)), hqq]
      calc -((c + h) * (piStar μ s * sigMass μ s - qk c h k * sigMass μ s))
          = sigMass μ s * ((c + h) * (qk c h k - piStar μ s)) := by ring
        _ ≤ sigMass μ s * ((c + h) * δ + |kh - k|) := mul_le_mul_of_nonneg_left e1 hpos.le
    · have hb1 : conditionedRule πh kh c h s = false := by simp [conditionedRule, h1]
      have hb2 : bayesRule μ c h k s = false := by simp [bayesRule, h2]
      rw [hb1, hb2, sub_self]; exact hRHS
  · rw [cost_eq_zero_of_sigMass_eq_zero μ c h k _ hzero.symm,
      cost_eq_zero_of_sigMass_eq_zero μ c h k _ hzero.symm, sub_self]
    exact hRHS

/-- **Proposition R′**: covered at tolerance `δ`, the conditioned agent's regret against the objective
Bayes rule is at most `(c + h) δ + |k̂ − k|`.
Source: [[corr-wf14b-inventory]] 064 / landscape-final.md S6 Proposition R′, P6, Statement 6
Kind: P
Fidelity: exact
Hyps: (a) `0 < c + h` (where `q_k` is defined), `0 ≤ δ` -/
theorem regret_le (μ : Distr (S × Bool)) (πh : S → ℝ) {c h : ℝ} (k kh δ : ℝ) (hch : 0 < c + h)
    (hδ : 0 ≤ δ) (hcov : covered πh μ δ) :
    loss μ (conditionedRule πh kh c h) c h k - loss μ (bayesRule μ c h k) c h k ≤
      (c + h) * δ + |kh - k| := by
  unfold loss
  rw [← sum_sub_distrib]
  calc ∑ s, (cost μ c h k (conditionedRule πh kh c h s) s - cost μ c h k (bayesRule μ c h k s) s)
      ≤ ∑ s, sigMass μ s * ((c + h) * δ + |kh - k|) :=
        sum_le_sum fun s _ => excess_le μ πh k kh δ hch hδ s (hcov s)
    _ = (c + h) * δ + |kh - k| := by rw [← sum_mul, sum_sigMass, one_mul]

/-- **Corollary**: at `δ = 0` and `k̂ = k` the regret is `0` (Statement 2 restated through R′).
Source: [[corr-wf14b-inventory]] 064 / landscape-final.md S6 ("At `δ = 0, k̂ = k` the conditioned rule
*is* the Bayes rule")
Kind: C
Fidelity: exact
Hyps: (a) only -/
theorem regret_zero (μ : Distr (S × Bool)) (πh : S → ℝ) {c h : ℝ} (k : ℝ) (hch : 0 < c + h)
    (hcov : covered πh μ 0) :
    loss μ (conditionedRule πh k c h) c h k - loss μ (bayesRule μ c h k) c h k = 0 := by
  rw [loss_conditioned_eq_bayes_of_covered_zero μ πh c h k hcov, sub_self]

/-! ## Tightness (extension E1): the one-signal instance -/

/-- A one-signal law: a push with legitimizing mass `p` and non-legitimizing mass `1 − p`.
Source: [[corr-wf14b-inventory]] 064 / landscape-final.md P6 ("tightness at `c = 1, h = 4`")
Kind: D
Fidelity: n/a (witness) -/
noncomputable def oneSignal (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) : Distr (Unit × Bool) where
  mass x := if x.2 then p else 1 - p
  nonneg x := by rcases x with ⟨-, b⟩; cases b <;> simp <;> linarith [hp.1, hp.2]
  sum_eq_one := by simp [Fintype.sum_prod_type, Fintype.sum_bool]

/-- `oneSignal` masses. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma oneSignal_mass (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    legMass (oneSignal p hp) () = p ∧ nonlegMass (oneSignal p hp) () = 1 - p ∧
      sigMass (oneSignal p hp) () = 1 ∧ piStar (oneSignal p hp) () = p := by
  simp [oneSignal, legMass, nonlegMass, sigMass, piStar]

/-- **Tightness, attained**: for `k ≤ k̂`, `0 ≤ δ`, with `0 ≤ q_k̂ − δ ≤ 1` and the flip forced
(`0 < δ ∨ k < k̂`), the one-signal law with `π* = q_k̂ − δ` and the credence `π̂ = q_k̂` is covered at
tolerance `δ` and the regret **equals** `(c + h) δ + |k̂ − k|`: Proposition R′'s bound is attained, not
merely approached.
Source: [[corr-wf14b-inventory]] 064 / landscape-final.md P6 (tightness); mandate T15 (extension E1)
Kind: N+
Fidelity: stronger: equality where the source reports `0.500` against `0.505`
Hyps: (a) only -/
theorem regret_attained {c h : ℝ} (k kh δ : ℝ) (hch : 0 < c + h) (hk : k ≤ kh) (hδ : 0 ≤ δ)
    (hflip : 0 < δ ∨ k < kh) (hp0 : 0 ≤ qk c h kh - δ) (hp1 : qk c h kh - δ ≤ 1) :
    covered (fun _ => qk c h kh) (oneSignal (qk c h kh - δ) ⟨hp0, hp1⟩) δ ∧
      loss (oneSignal (qk c h kh - δ) ⟨hp0, hp1⟩) (conditionedRule (fun _ => qk c h kh) kh c h) c h k -
        loss (oneSignal (qk c h kh - δ) ⟨hp0, hp1⟩) (bayesRule (oneSignal (qk c h kh - δ) ⟨hp0, hp1⟩) c h k)
          c h k = (c + h) * δ + |kh - k| := by
  obtain ⟨m1, m2, m3, m4⟩ := oneSignal_mass (qk c h kh - δ) ⟨hp0, hp1⟩
  have hq := qk_sub k kh hch
  constructor
  · intro s _
    rw [m4]
    simp [abs_of_nonneg hδ]
  · have hb1 : conditionedRule (fun _ => qk c h kh) kh c h () = false := by
      simp [conditionedRule]
    have hb2 : bayesRule (oneSignal (qk c h kh - δ) ⟨hp0, hp1⟩) c h k () = true := by
      simp only [bayesRule, m1, m3, mul_one, decide_eq_true_eq]
      have : qk c h kh - qk c h k ≤ 0 := by
        rw [hq]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hch.le
      rcases hflip with hδ' | hk'
      · linarith
      · have : qk c h kh - qk c h k < 0 := by
          rw [hq]; exact div_neg_of_neg_of_pos (by linarith) hch
        linarith
    simp only [loss, Fintype.sum_unique, hb1, hb2, cost, Bool.false_eq_true, ↓reduceIte, m1, m2, m3]
    rw [abs_of_nonneg (by linarith : 0 ≤ kh - k)]
    unfold qk at *
    field_simp
    ring

/-- **The worked instance**: `c = 1`, `h = 4`, `k = k̂ = 0`, `δ = 1/10` — regret exactly `1/2`.
Source: [[corr-wf14b-inventory]] 064 / landscape-final.md P6 ("regret `0.500` against bound `0.505`");
mandate T15 ("Worked: … regret `1/2`")
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem regret_attained_worked :
    loss (oneSignal (1 / 10) ⟨by norm_num, by norm_num⟩) (conditionedRule (fun _ => (1 / 5 : ℝ)) 0 1 4) 1 4 0 -
        loss (oneSignal (1 / 10) ⟨by norm_num, by norm_num⟩)
          (bayesRule (oneSignal (1 / 10) ⟨by norm_num, by norm_num⟩) 1 4 0) 1 4 0 = 1 / 2 := by
  have hb1 : ∀ u : Unit, conditionedRule (fun _ => (1 / 5 : ℝ)) 0 1 4 u = false := by
    intro u; simp [conditionedRule, qk]; norm_num
  have hb2 : ∀ u : Unit, bayesRule (oneSignal (1 / 10) ⟨by norm_num, by norm_num⟩) 1 4 0 u = true := by
    intro u; simp [bayesRule, qk, legMass, sigMass, nonlegMass, oneSignal]; norm_num
  simp only [loss, Fintype.sum_unique, hb1, hb2, cost]
  simp [legMass, nonlegMass, sigMass, oneSignal]
  norm_num

/-- **Tightness, approached (the `k̂ ≤ k` side)**: for `k̂ ≤ k` and every `η > 0` small enough that the
instance is a law and the flip is forced, the one-signal law with `π̂ = q_k̂ − η/(c + h)` and
`π* = π̂ + δ` is covered at tolerance `δ` and has regret **exactly** `(c + h) δ + |k̂ − k| − η`. So the
supremum over instances is the bound; for `k̂ < k` it is not attained (`regret_lt_of_lt`) because the
conditioned rule resists only at `π̂ < q_k̂` (strictly). At `k̂ = k` this is the source's own instance
(`c = 1`, `h = 4`, `π̂` just below `q_k`: `0.500` against `0.505`).
Source: [[corr-wf14b-inventory]] 064 / landscape-final.md P6 ("`π̂` just below `q_k`: regret `0.500`
against bound `0.505`"); mandate T15 (two-sided form)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem regret_approached {c h : ℝ} (k kh δ η : ℝ) (hch : 0 < c + h) (hk : kh ≤ k) (hδ : 0 ≤ δ)
    (hη : 0 < η) (hηle : η / (c + h) ≤ δ + (k - kh) / (c + h))
    (hp0 : 0 ≤ qk c h kh - η / (c + h) + δ) (hp1 : qk c h kh - η / (c + h) + δ ≤ 1) :
    covered (fun _ => qk c h kh - η / (c + h)) (oneSignal (qk c h kh - η / (c + h) + δ) ⟨hp0, hp1⟩) δ ∧
      loss (oneSignal (qk c h kh - η / (c + h) + δ) ⟨hp0, hp1⟩)
          (conditionedRule (fun _ => qk c h kh - η / (c + h)) kh c h) c h k -
        loss (oneSignal (qk c h kh - η / (c + h) + δ) ⟨hp0, hp1⟩)
          (bayesRule (oneSignal (qk c h kh - η / (c + h) + δ) ⟨hp0, hp1⟩) c h k) c h k =
      (c + h) * δ + |kh - k| - η := by
  obtain ⟨m1, m2, m3, m4⟩ := oneSignal_mass (qk c h kh - η / (c + h) + δ) ⟨hp0, hp1⟩
  have hq := qk_sub k kh hch
  have hηpos : 0 < η / (c + h) := div_pos hη hch
  constructor
  · intro s _
    rw [m4]
    simp [abs_of_nonneg hδ]
  · have hb1 : conditionedRule (fun _ => qk c h kh - η / (c + h)) kh c h () = true := by
      simp [conditionedRule]; linarith
    have hb2 : bayesRule (oneSignal (qk c h kh - η / (c + h) + δ) ⟨hp0, hp1⟩) c h k () = false := by
      simp only [bayesRule, m1, m3, mul_one, decide_eq_false_iff_not, not_lt]
      linarith
    simp only [loss, Fintype.sum_unique, hb1, hb2, cost, Bool.false_eq_true, ↓reduceIte, m1, m2, m3]
    rw [abs_of_nonpos (by linarith : kh - k ≤ 0)]
    unfold qk at *
    field_simp
    ring

/-! ## The "only if": for `k̂ < k` the bound is never attained -/

/-- **The per-signal excess is strict for `k̂ < k`** on every positive-mass signal: a resist-flip has
`π* − q_k < δ + (k − k̂)/(c+h)` (strict through `π̂ < q_k̂`), an accept-flip has
`(c+h)(q_k − π*) ≤ (k̂ − k) + (c+h)δ < (k − k̂) + (c+h)δ`, and no flip gives `0 < P*(s)·bound`.
Source: [[corr-wf14b-inventory]] 064 / landscape-final.md P6 (the tightness discussion); audit r1,
adversarial N1 ("the 'only if' is prose")
Kind: P
Fidelity: exact -/
lemma excess_lt (μ : Distr (S × Bool)) (πh : S → ℝ) {c h : ℝ} (k kh δ : ℝ) (hch : 0 < c + h)
    (hδ : 0 ≤ δ) (hk : kh < k) (s : S) (hpos : 0 < sigMass μ s) (hc : |πh s - piStar μ s| ≤ δ) :
    cost μ c h k (conditionedRule πh kh c h s) s - cost μ c h k (bayesRule μ c h k s) s <
      sigMass μ s * ((c + h) * δ + |kh - k|) := by
  have habs : |kh - k| = k - kh := by rw [abs_of_neg (by linarith : kh - k < 0)]; ring
  have hRHS : 0 < sigMass μ s * ((c + h) * δ + |kh - k|) :=
    mul_pos hpos (by rw [habs]; nlinarith [mul_nonneg hch.le hδ])
  have hleg : legMass μ s = piStar μ s * sigMass μ s := by
    rw [piStar, div_mul_cancel₀ _ hpos.ne']
  have key := cost_true_sub_false μ k hch s
  have hq := qk_sub k kh hch
  have a1 := abs_le.1 hc
  by_cases h1 : πh s < qk c h kh <;> by_cases h2 : legMass μ s < qk c h k * sigMass μ s
  · have hb1 : conditionedRule πh kh c h s = true := by simp [conditionedRule, h1]
    have hb2 : bayesRule μ c h k s = true := by simp [bayesRule, h2]
    rw [hb1, hb2, sub_self]; exact hRHS
  · -- resist-flip: strict through `π̂ < q_k̂`
    have hb1 : conditionedRule πh kh c h s = true := by simp [conditionedRule, h1]
    have hb2 : bayesRule μ c h k s = false := by simp [bayesRule, h2]
    rw [hb1, hb2, key, hleg, habs]
    have e1 : (c + h) * (piStar μ s - qk c h k) < (c + h) * δ + (k - kh) := by
      have hqq : (c + h) * (qk c h kh - qk c h k) = k - kh := by
        rw [hq, mul_div_cancel₀ _ hch.ne']
      have : piStar μ s - qk c h k < δ + (qk c h kh - qk c h k) := by linarith
      nlinarith [mul_lt_mul_of_pos_left this hch]
    calc (c + h) * (piStar μ s * sigMass μ s - qk c h k * sigMass μ s)
        = sigMass μ s * ((c + h) * (piStar μ s - qk c h k)) := by ring
      _ < sigMass μ s * ((c + h) * δ + (k - kh)) := mul_lt_mul_of_pos_left e1 hpos
  · -- accept-flip: `(c+h)(q_k − π*) ≤ (k̂ − k) + (c+h)δ < (k − k̂) + (c+h)δ`
    have hb1 : conditionedRule πh kh c h s = false := by simp [conditionedRule, h1]
    have hb2 : bayesRule μ c h k s = true := by simp [bayesRule, h2]
    rw [hb1, hb2, ← neg_sub, key, hleg, habs]
    rw [not_lt] at h1
    have e1 : (c + h) * (qk c h k - piStar μ s) < (c + h) * δ + (k - kh) := by
      have hqq : (c + h) * (qk c h k - qk c h kh) = kh - k := by
        have := qk_sub kh k hch
        rw [this, mul_div_cancel₀ _ hch.ne']
      have : qk c h k - piStar μ s ≤ δ + (qk c h k - qk c h kh) := by linarith
      nlinarith [mul_le_mul_of_nonneg_left this hch.le]
    calc -((c + h) * (piStar μ s * sigMass μ s - qk c h k * sigMass μ s))
        = sigMass μ s * ((c + h) * (qk c h k - piStar μ s)) := by ring
      _ < sigMass μ s * ((c + h) * δ + (k - kh)) := mul_lt_mul_of_pos_left e1 hpos
  · have hb1 : conditionedRule πh kh c h s = false := by simp [conditionedRule, h1]
    have hb2 : bayesRule μ c h k s = false := by simp [bayesRule, h2]
    rw [hb1, hb2, sub_self]; exact hRHS

/-- Some signal has positive mass. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma exists_sigMass_pos (μ : Distr (S × Bool)) : ∃ s, 0 < sigMass μ s := by
  by_contra hcon
  push_neg at hcon
  have h0 : ∑ s, sigMass μ s = 0 :=
    sum_eq_zero fun s _ => le_antisymm (hcon s) (sigMass_nonneg μ s)
  rw [sum_sigMass] at h0
  exact one_ne_zero h0

/-- **Proposition R′ is never attained for `k̂ < k`**: every covered instance has regret strictly below
`(c + h) δ + |k̂ − k|`. With `regret_attained` (attained for `k̂ ≥ k`) and `regret_approached` (approached
for `k̂ ≤ k`) this closes the two-sided form: the supremum is the bound, attained iff `k̂ ≥ k`.
Source: [[corr-wf14b-inventory]] 064 / landscape-final.md P6; mandate T15 (extension E1); audit r1,
adversarial N1
Kind: P
Fidelity: stronger: the "only if" of attainment, which the source and the first version left as prose
Hyps: (a) `0 < c + h`, `0 ≤ δ`, `k̂ < k` -/
theorem regret_lt_of_lt (μ : Distr (S × Bool)) (πh : S → ℝ) {c h : ℝ} (k kh δ : ℝ) (hch : 0 < c + h)
    (hδ : 0 ≤ δ) (hk : kh < k) (hcov : covered πh μ δ) :
    loss μ (conditionedRule πh kh c h) c h k - loss μ (bayesRule μ c h k) c h k <
      (c + h) * δ + |kh - k| := by
  unfold loss
  rw [← sum_sub_distrib]
  obtain ⟨s₀, hs₀⟩ := exists_sigMass_pos μ
  calc ∑ s, (cost μ c h k (conditionedRule πh kh c h s) s - cost μ c h k (bayesRule μ c h k s) s)
      < ∑ s, sigMass μ s * ((c + h) * δ + |kh - k|) := by
        refine sum_lt_sum (fun s _ => excess_le μ πh k kh δ hch hδ s (hcov s)) ⟨s₀, mem_univ _, ?_⟩
        exact excess_lt μ πh k kh δ hch hδ hk s₀ hs₀ (hcov s₀ hs₀)
    _ = (c + h) * δ + |kh - k| := by rw [← sum_mul, sum_sigMass, one_mul]

end Regret

end Cleanroom.Corrigibility.CorrLandscape
