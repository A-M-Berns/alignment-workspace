import Cleanroom.Corrigibility.LegitNegStatic.SealedBlind

/-!
# Cluster A, A2 and A2c: `L`-indistinguishability, the inferability converse, disclosure

Package `legit-neg-static`, targets 10–11. Sources: `clusters/A/NEGATIVES.md` A2, A2c;
`clusters/A/VERIFY.md` "A2: narrowed" (V6), "A2c: narrowed" (V3); [[corr-legit-neg-inventory]]
items 007, 008; [[corr-legit-neg-2-inventory]] item 2-010.

**Information structure.** A world-model is `θ = (P_θ, O_θ)`: a `Problem` (prior `π_θ`,
standard `Q_θ = u`, legitimacy) and the evaluators' observation map `O_θ : S → Obs`. An
`L`-world evaluation is any rule `V s c = Φ (O s) c` with `Φ` fixed across world-models. The
agent's own day-`n` state is *not* part of `O` unless `Obs` is chosen to carry it (V6's
narrowing, made visible by `O` being a parameter: `A2_V6_credence_in_O`).
-/

namespace Cleanroom.Corrigibility.LegitNegStatic

open Finset

/-- A world-model: a decision problem (prior, standard, legitimacy) together with the
legitimate evaluators' observation map.
Source: [[corr-legit-neg-inventory]] item 007
Kind: D
Fidelity: exact -/
structure WorldModel (S A Obs : Type) [Fintype S] [Fintype A] where
  P : Problem S A
  O : S → Obs

/-- An `L`-world evaluation: the vector `V s c = Φ (O s) c` computed from what is observable on
the `L`-terminals.
Source: [[corr-legit-neg-inventory]] item 007
Kind: D
Fidelity: exact -/
def lworldEval {S A Obs : Type} (Φ : Obs → A → ℚ) (O : S → Obs) : S → A → ℚ :=
  fun s c => Φ (O s) c

/-- `L`-indistinguishability of two world-models: agreement on `π|_L`, `Q|_{L×A}` and `O|_L`.
Source: [[corr-legit-neg-inventory]] item 007
Kind: D
Fidelity: exact -/
def LIndist {S A Obs : Type} [Fintype S] [Fintype A] (θ₁ θ₂ : WorldModel S A Obs)
    (ℓ : S → Bool) : Prop :=
  (∀ s, ℓ s = true → θ₁.P.prior s = θ₂.P.prior s) ∧
  (∀ s, ℓ s = true → ∀ a, θ₁.P.u s a = θ₂.P.u s a) ∧
  (∀ s, ℓ s = true → θ₁.O s = θ₂.O s)

section Necessity

variable {S A Obs : Type} [Fintype S] [Fintype A]

/-- `L`-indistinguishable models have the same `π(L)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mass_eq_of_LIndist {θ₁ θ₂ : WorldModel S A Obs} {ℓ : S → Bool} (h : LIndist θ₁ θ₂ ℓ) :
    θ₁.P.mass ℓ = θ₂.P.mass ℓ := by
  unfold Problem.mass
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : ℓ s = true
  · rw [h.1 s hs]
  · simp [Bool.not_eq_true] at hs; simp [hs]

/-- **A2, necessity (a congruence).** Under sealing, `L`-indistinguishable world-models give
every `L`-world evaluation the same `P1` scores — `P1` reads only `π|_L`, `O|_L` and `Φ`.
Honestly kind `L`: the content is that `J₁` factors through `(π|_L, O|_L, Φ)`. Note that the
`Q|_L` clause of `LIndist` is not used: it is what makes S1 an `L`-world evaluation (via an
`O` that reveals `Q` on `L`), not what the congruence needs.
Source: [[corr-legit-neg-inventory]] item 007 (A2 necessity)
Kind: L
Fidelity: exact; narrowed per V6: the agent's state is outside `O` unless `Obs` carries it
Hyps: (a) all -/
theorem P1_lworld_eq_of_LIndist {θ₁ θ₂ : WorldModel S A Obs} {ℓ : S → Bool}
    (h₁ : θ₁.P.SealedBy ℓ) (h₂ : θ₂.P.SealedBy ℓ) (h : LIndist θ₁ θ₂ ℓ) (Φ : Obs → A → ℚ)
    (c : A) :
    θ₁.P.P1 (liftV (lworldEval Φ θ₁.O)) c = θ₂.P.P1 (liftV (lworldEval Φ θ₂.O)) c := by
  rw [θ₁.P.P1_liftV_of_SealedBy h₁, θ₂.P.P1_liftV_of_SealedBy h₂]
  unfold Problem.J1 lworldEval
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hs : ℓ s = true
  · rw [h.1 s hs, h.2.2 s hs]
  · simp [Bool.not_eq_true] at hs; simp [hs]

/-- **A2, necessity for the choices.** `L`-indistinguishable models make P1 choose identically
under every `L`-world evaluation, and P2 likewise (exclusion convention).
Source: [[corr-legit-neg-inventory]] item 007
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem argmax_P1_lworld_eq_of_LIndist {θ₁ θ₂ : WorldModel S A Obs} {ℓ : S → Bool}
    (h₁ : θ₁.P.SealedBy ℓ) (h₂ : θ₂.P.SealedBy ℓ) (h : LIndist θ₁ θ₂ ℓ) (Φ : Obs → A → ℚ) :
    argmax (θ₁.P.P1 (liftV (lworldEval Φ θ₁.O))) = argmax (θ₂.P.P1 (liftV (lworldEval Φ θ₂.O))) :=
  argmax_congr (P1_lworld_eq_of_LIndist h₁ h₂ h Φ)

/-- `argmaxOpt_P2_lworld_eq_of_LIndist`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem argmaxOpt_P2_lworld_eq_of_LIndist {θ₁ θ₂ : WorldModel S A Obs} {ℓ : S → Bool}
    (h₁ : θ₁.P.SealedBy ℓ) (h₂ : θ₂.P.SealedBy ℓ) (h : LIndist θ₁ θ₂ ℓ) (Φ : Obs → A → ℚ) :
    argmaxOpt (θ₁.P.P2 (liftV (lworldEval Φ θ₁.O)))
      = argmaxOpt (θ₂.P.P2 (liftV (lworldEval Φ θ₂.O))) := by
  have : θ₁.P.P2 (liftV (lworldEval Φ θ₁.O)) = θ₂.P.P2 (liftV (lworldEval Φ θ₂.O)) :=
    funext fun c => by
      unfold Problem.P2
      rw [θ₁.P.PL_eq_mass_of_SealedBy h₁, θ₂.P.PL_eq_mass_of_SealedBy h₂, mass_eq_of_LIndist h,
        P1_lworld_eq_of_LIndist h₁ h₂ h Φ c]
  rw [this]

end Necessity

/-! ### Fixture A2: the action-belief mismatch -/

open Problem

/-- Fixture A2's world-model `θ₁` (harmless on `b`): `incautionInstance (1/2) (1/10) (1/2) 0`
with a constant observation.
Source: NEGATIVES A2 "Fixture A2"
Kind: D
Fidelity: exact -/
def A2_theta1 : WorldModel (Fin 2) (Fin 2) Unit :=
  ⟨incautionInstance (1/2) (1/10) (1/2) 0 (by norm_num) (by norm_num), fun _ => ()⟩

/-- Fixture A2's world-model `θ₂` (full harm on `b`): `incautionInstance (1/2) (1/10) (1/2) 1`
with the same constant observation.
Source: NEGATIVES A2 "Fixture A2"
Kind: D
Fidelity: exact -/
def A2_theta2 : WorldModel (Fin 2) (Fin 2) Unit :=
  ⟨incautionInstance (1/2) (1/10) (1/2) 1 (by norm_num) (by norm_num), fun _ => ()⟩

/-- Fixture A2's Bayesian S2 evaluators in closed form (`run.py`, `evaluator_scores`): with
issuance weight `q`, legitimate values `x` (safe) and `x + δ` (risky), and prior `r` on the
harmful hypothesis (harm `1`), `V(safe) = (1 − q) x + q` and `V(risky) = (1 − q)(x + δ) + q (1 − r)`.
The same under both models, since the signal is.
Source: NEGATIVES A2 "Fixture A2"
Kind: D
Fidelity: exact -/
def A2_PhiOf (q δ x r : ℚ) : Unit → Fin 2 → ℚ :=
  fun _ c => ![(1 - q) * x + q, (1 - q) * (x + δ) + q * (1 - r)] c

/-- Fixture A2's evaluators at `q = 1/2`, `δ = 1/10`, `x = 1/2`, `r = 1/100`: the vector
`(3/4, 159/200)` (safe, risky), now a consequence of the formula (`A2_Phi_eq`).
Source: NEGATIVES A2 "Fixture A2"
Kind: D
Fidelity: exact -/
def A2_Phi : Unit → Fin 2 → ℚ := A2_PhiOf (1/2) (1/10) (1/2) (1/100)

/-- `A2_Phi` is the hard number pair the fixture prints, derived from the prior `r = 1/100`.
Source: NEGATIVES A2 "Fixture A2"
Kind: L
Fidelity: exact -/
theorem A2_Phi_eq : A2_Phi = fun _ c => ![3/4, 159/200] c := by
  funext u c; fin_cases c <;> simp [A2_Phi, A2_PhiOf] <;> norm_num

/-- **A2, N+ witness (fixture A2).** `θ₁` and `θ₂` are `L`-indistinguishable (`O` constant on
`L`, so the witness is not vacuous by injectivity); both proposals pick `risky` in both models;
yet under `θ₂` the agent's own standard `W` prefers `safe` by `9/20`. The action-belief mismatch
in its sharpest form.
Source: [[corr-legit-neg-inventory]] item 007 (fixture A2)
Kind: N+
Fidelity: exact -/
theorem A2_witness :
    LIndist A2_theta1 A2_theta2 legG ∧
    argmax (A2_theta1.P.P1 (liftV (lworldEval A2_Phi A2_theta1.O))) = {1} ∧
    argmax (A2_theta2.P.P1 (liftV (lworldEval A2_Phi A2_theta2.O))) = {1} ∧
    argmax (A2_theta2.P.W A2_theta2.P.u) = {0} ∧
    A2_theta2.P.W A2_theta2.P.u 0 - A2_theta2.P.W A2_theta2.P.u 1 = 9/20 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro s hs; fin_cases s <;> simp_all [legG, A2_theta1, A2_theta2, incautionInstance]
  · intro s hs a; fin_cases s <;> fin_cases a <;> simp_all [legG, A2_theta1, A2_theta2, incautionInstance]
  · intro s _; rfl
  · apply argmax_eq_singleton_of_lt; intro b hb
    have hb0 : b = 0 := by fin_cases b <;> simp_all
    subst hb0
    simp [A2_theta1, incautionInstance, P1, lworldEval, A2_Phi, A2_PhiOf]; norm_num
  · apply argmax_eq_singleton_of_lt; intro b hb
    have hb0 : b = 0 := by fin_cases b <;> simp_all
    subst hb0
    simp [A2_theta2, incautionInstance, P1, lworldEval, A2_Phi, A2_PhiOf]; norm_num
  · apply argmax_eq_singleton_of_lt; intro b hb
    have hb1 : b = 1 := by fin_cases b <;> simp_all
    subst hb1
    simp [A2_theta2, incautionInstance, W, EU]; norm_num
  · simp [A2_theta2, incautionInstance, W, EU]; norm_num

/-- V6's evaluators: `Obs = ℚ` is the agent's day-`n` credence in the harm, taken at face value
in place of the prior `r` of `A2_PhiOf` (issuance weight `1/2`): `V(safe) = 3/4`,
`V(risky) = 3/10 + (1/2)(1 − cred)`.
Source: VERIFY A V6
Kind: D
Fidelity: exact -/
def A2_PhiV6 : ℚ → Fin 2 → ℚ := fun cred => A2_PhiOf (1/2) (1/10) (1/2) cred ()

/-- **A2, V6 variant.** If the agent's credence is part of `O` (and trusted), the harm is
inferable: the two world-models that carry credence `1` and `1/100` on the same problem are
*not* `L`-indistinguishable (`O` differs on `L`), and with credence `1` the evaluators pick
`safe`, with credence `1/100` they pick `risky`. This is why the necessity theorem needs the
agent's state outside `O` — `O` is a parameter.
Source: VERIFY A "A2: narrowed" (V6); finding 5
Kind: N+
Fidelity: variant: the agent's state inside `O` -/
theorem A2_V6_credence_in_O :
    let P := incautionInstance (1/2) (1/10) (1/2) 1 (by norm_num) (by norm_num)
    ¬ LIndist (⟨P, fun _ => (1 : ℚ)⟩ : WorldModel (Fin 2) (Fin 2) ℚ) ⟨P, fun _ => (1/100 : ℚ)⟩ legG ∧
    argmax (P.P1 (liftV (lworldEval A2_PhiV6 (fun _ => 1)))) = {0} ∧
    argmax (P.P1 (liftV (lworldEval A2_PhiV6 (fun _ => 1/100)))) = {1} := by
  intro P
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := h.2.2 0 (by simp [legG])
    norm_num at this
  · apply argmax_eq_singleton_of_lt; intro b hb
    have hb1 : b = 1 := by fin_cases b <;> simp_all
    subst hb1
    simp [P, incautionInstance, P1, lworldEval, A2_PhiV6, A2_PhiOf]; norm_num
  · apply argmax_eq_singleton_of_lt; intro b hb
    have hb0 : b = 0 := by fin_cases b <;> simp_all
    subst hb0
    simp [P, incautionInstance, P1, lworldEval, A2_PhiV6, A2_PhiOf]; norm_num

/-! ### The inferability converse -/

namespace Problem

variable {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)

/-- `m_b = E_π[Q(·, b) | ¬L]`, the issuance-time `¬L`-conditional quality of `b` (the
*definition*, not a free hypothesis: a converse with `m_b` free would be a squeeze).
Source: [[corr-legit-neg-inventory]] item 007 (converse)
Kind: D
Fidelity: exact -/
def condNotL (ℓ : S → Bool) (Q : S → A → ℚ) (b : A) : ℚ :=
  (∑ s, P.prior s * ind (!ℓ s) * Q s b) / P.mass (fun s => !ℓ s)

/-- The inferable evaluators' vector `V s b = π(L) · Q s b + π(¬L) · m_b`.
Source: [[corr-legit-neg-inventory]] item 007 (converse)
Kind: D
Fidelity: exact -/
def inferableVec (ℓ : S → Bool) (Q : S → A → ℚ) : S → A → ℚ :=
  fun s b => P.mass ℓ * Q s b + P.mass (fun s => !ℓ s) * P.condNotL ℓ Q b

/-- `π(¬L) · m_b = ∑_{¬L} π Q(·, b)` — including at `π(¬L) = 0`, where both sides are `0`
(the `¬L` sum vanishes because every `¬L` state has prior `0`; `0 · junk = 0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma mass_mul_condNotL (ℓ : S → Bool) (Q : S → A → ℚ) (b : A) :
    P.mass (fun s => !ℓ s) * P.condNotL ℓ Q b = ∑ s, P.prior s * ind (!ℓ s) * Q s b := by
  unfold condNotL
  by_cases h : P.mass (fun s => !ℓ s) = 0
  · rw [h, zero_mul]
    symm
    refine Finset.sum_eq_zero fun s _ => ?_
    by_cases hs : (!ℓ s) = true
    · rw [P.prior_eq_zero_of_mass_eq_zero h s hs]; ring
    · simp at hs; simp [hs]
  · rw [mul_div_cancel₀ _ h]

/-- **A2, converse (load-bearing 2).** Under `SealedBy ℓ`, if the evaluators report
`π(L) Q s b + π(¬L) m_b` on `L`, then `J₁ b = π(L) · W b` exactly, for every `b` — with no
positivity hypothesis (at `π(¬L) = 0` the `m_b` term is `0 · junk = 0`, see
`mass_mul_condNotL`).
Source: [[corr-legit-neg-inventory]] item 007 (A2 converse)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem P1_inferable_eq_mass_mul_W {ℓ : S → Bool} (h : P.SealedBy ℓ) (Q : S → A → ℚ) (b : A) :
    P.P1 (liftV (P.inferableVec ℓ Q)) b = P.mass ℓ * P.W Q b := by
  rw [P.P1_liftV_of_SealedBy h]
  unfold J1 inferableVec
  have hsplit := P.W_split Q ℓ b
  have hm := P.mass_mul_condNotL ℓ Q b
  have hL : ∑ s, P.prior s * ind (ℓ s) * (P.mass ℓ * Q s b + P.mass (fun s => !ℓ s) * P.condNotL ℓ Q b)
      = P.mass ℓ * (∑ s, P.prior s * ind (ℓ s) * Q s b)
        + (P.mass (fun s => !ℓ s) * P.condNotL ℓ Q b) * P.mass ℓ := by
    unfold mass
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hL, hm, hsplit]; ring

/-- **A2, converse for the choices.** With `0 < π(L)`, inferable evaluators make P1 (and, by
A0, P2) choose `argmax W`.
Source: [[corr-legit-neg-inventory]] item 007; item 014 (A6 sufficiency)
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem argmax_P1_inferable_eq_argmax_W {ℓ : S → Bool} (h : P.SealedBy ℓ) (hpos : 0 < P.mass ℓ)
    (Q : S → A → ℚ) : argmax (P.P1 (liftV (P.inferableVec ℓ Q))) = argmax (P.W Q) := by
  rw [argmax_congr (P.P1_inferable_eq_mass_mul_W h Q)]
  have : (fun b => P.mass ℓ * P.W Q b) = fun b => P.W Q b * P.mass ℓ := funext fun b => mul_comm _ _
  rw [this, argmax_mul_pos _ hpos]

/-- `argmaxOpt_P2_inferable_eq_argmax_W`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem argmaxOpt_P2_inferable_eq_argmax_W {ℓ : S → Bool} (h : P.SealedBy ℓ)
    (hpos : 0 < P.mass ℓ) (Q : S → A → ℚ) :
    argmaxOpt (P.P2 (liftV (P.inferableVec ℓ Q))) = argmax (P.W Q) := by
  rw [P.argmaxOpt_P2_eq_argmax_P1_of_SealedBy h hpos, P.argmax_P1_inferable_eq_argmax_W h hpos]

/-! ### A2c: the disclosure incentive -/

/-- **A2c, general lemma.** Under `SealedBy ℓ`, an option `a_d` whose own `L`-branch score is
pointwise at most `a_s`'s is never strictly preferred to `a_s` by P1: `P1 a_d ≤ P1 a_s`, so
`a_d ∈ argmax → a_s ∈ argmax`. (Disclosure lowers only the discloser's own `L`-score.)
Source: [[corr-legit-neg-inventory]] item 008 (A2c)
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem P1_le_of_dominated_on_L {ℓ : S → Bool} (h : P.SealedBy ℓ) (V : MenuVec S A) (ad as : A)
    (hV : ∀ s, ℓ s = true → V s ad ad ≤ V s as as) : P.P1 V ad ≤ P.P1 V as := by
  unfold P1
  refine Finset.sum_le_sum fun s _ => ?_
  rw [h s ad, h s as]
  by_cases hs : ℓ s = true
  · simp only [hs, ind_true, mul_one]; exact mul_le_mul_of_nonneg_left (hV s hs) (P.prior_nonneg s)
  · simp [Bool.not_eq_true] at hs; simp [hs]

/-- `mem_argmax_of_dominated_on_L`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_argmax_of_dominated_on_L {ℓ : S → Bool} (h : P.SealedBy ℓ) (V : MenuVec S A)
    (ad as : A) (hV : ∀ s, ℓ s = true → V s ad ad ≤ V s as as) (had : ad ∈ argmax (P.P1 V)) :
    as ∈ argmax (P.P1 V) := by
  rw [mem_argmax] at had ⊢
  intro b; exact (had b).trans (P.P1_le_of_dominated_on_L h V ad as hV)

end Problem

/-- The disclosure instance's evaluators (fixture A2c): menu `0 = risky+silent`,
`1 = risky+disclose`, `2 = safe`; belief in the harm `r` unless disclosed (then `1`):
`V = ((1−q)(x+δ) + q(1−r), (1−q)(x+δ), (1−q)x + q)` on `g`.
Source: NEGATIVES A2c
Kind: D
Fidelity: exact -/
def discV (q δ x r : ℚ) : Fin 2 → Fin 3 → ℚ :=
  fun _ a => ![(1 - q) * (x + δ) + q * (1 - r), (1 - q) * (x + δ), (1 - q) * x + q] a

/-- The sealed disclosure instance: states `g, b` with `π(b) = q`, `L = {g}`, three options.
`u` is the standard `Q` of the incaution family extended to the three options
(`silent`/`disclose` both `x + δ` on `g`, `1 − harm` on `b`).
Source: NEGATIVES A2c
Kind: D
Fidelity: exact -/
def disclosureSealed (q δ x harm : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Problem (Fin 2) (Fin 3) where
  prior := ![1 - q, q]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> linarith
  prior_sum := by simp
  leg := fun s _ => decide (s = 0)
  u := fun s a => ![![x + δ, x + δ, x], ![1 - harm, 1 - harm, 1]] s a

/-- The coverage-barrier instance: omission voids every world, `leg s silent = false` for all
`s` (option-dependent legitimacy: this leaves `Sealed`).
Source: NEGATIVES A2c (the barrier)
Kind: D
Fidelity: exact -/
def disclosureBarrier (q δ x harm : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : Problem (Fin 2) (Fin 3) where
  prior := ![1 - q, q]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> linarith
  prior_sum := by simp
  leg := fun s a => decide (s = 0) && !decide (a = 0)
  u := fun s a => ![![x + δ, x + δ, x], ![1 - harm, 1 - harm, 1]] s a

/-- **A2c, sealed instance (N+).** With `q = 1/2`, `δ = 1/10`, `x = 1/2`, `r = 1/100` the
evaluators' scores are `(159/200, 3/10, 3/4)` and both proposals pick `risky+silent`: sealing
gives a strict incentive against disclosure.
Source: [[corr-legit-neg-inventory]] item 008 (A2c)
Kind: N+
Fidelity: exact -/
theorem A2c_sealed_silent :
    let P := disclosureSealed (1/2) (1/10) (1/2) 1 (by norm_num) (by norm_num)
    discV (1/2) (1/10) (1/2) (1/100) 0 = ![159/200, 3/10, 3/4] ∧
    argmax (P.P1 (liftV (discV (1/2) (1/10) (1/2) (1/100)))) = {0} ∧
    argmaxOpt (P.P2 (liftV (discV (1/2) (1/10) (1/2) (1/100)))) = {0} := by
  intro P
  have hs : P.SealedBy legG := fun _ _ => rfl
  have h1 : argmax (P.P1 (liftV (discV (1/2) (1/10) (1/2) (1/100)))) = {0} := by
    apply argmax_eq_singleton_of_lt; intro b hb
    fin_cases b
    · exact absurd rfl hb
    · simp [P, disclosureSealed, Problem.P1, discV]; norm_num
    · simp [P, disclosureSealed, Problem.P1, discV]; norm_num
  refine ⟨?_, h1, ?_⟩
  · funext a; fin_cases a <;> simp [discV] <;> norm_num
  · rw [P.argmaxOpt_P2_eq_argmax_P1_of_SealedBy hs ?_, h1]
    simp [P, disclosureSealed, Problem.mass, legG]; norm_num

/-- **A2c, the coverage barrier (exclusion convention of record).** With omission voiding every
world: P1 picks `safe` (`P1 silent = 0`), and P2 under exclusion picks `safe` (`silent` is not
a candidate; VERIFY A V3). The barrier works for both proposals.
Source: [[corr-legit-neg-inventory]] item 008; VERIFY A "A2c: narrowed" (V3)
Kind: N+
Fidelity: exact (exclusion convention) -/
theorem A2c_barrier_safe :
    let P := disclosureBarrier (1/2) (1/10) (1/2) 1 (by norm_num) (by norm_num)
    P.P1 (liftV (discV (1/2) (1/10) (1/2) (1/100))) 0 = 0 ∧
    argmax (P.P1 (liftV (discV (1/2) (1/10) (1/2) (1/100)))) = {2} ∧
    P.P2 (liftV (discV (1/2) (1/10) (1/2) (1/100))) 0 = none ∧
    argmaxOpt (P.P2 (liftV (discV (1/2) (1/10) (1/2) (1/100)))) = {2} := by
  intro P
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [P, disclosureBarrier, Problem.P1]
  · apply argmax_eq_singleton_of_lt; intro b hb
    fin_cases b
    · simp [P, disclosureBarrier, Problem.P1, discV]; norm_num
    · simp [P, disclosureBarrier, Problem.P1, discV]; norm_num
    · exact absurd rfl hb
  · simp [P, disclosureBarrier, Problem.P2, Problem.PL, Problem.mass]
  · ext a
    simp only [mem_argmaxOpt, Finset.mem_singleton]
    constructor
    · rintro ⟨y, hy, hmax⟩
      fin_cases a
      · simp [P, disclosureBarrier, Problem.P2, Problem.PL, Problem.mass] at hy
      · exfalso
        have h2 := hmax 2 (3/4) (by simp [P, disclosureBarrier, Problem.P2, Problem.PL, Problem.mass, Problem.P1, discV]; norm_num)
        simp [P, disclosureBarrier, Problem.P2, Problem.PL, Problem.mass, Problem.P1, discV] at hy
        norm_num at hy; linarith
      · rfl
    · rintro rfl
      refine ⟨3/4, by simp [P, disclosureBarrier, Problem.P2, Problem.PL, Problem.mass, Problem.P1, discV]; norm_num, ?_⟩
      intro b y hy
      fin_cases b
      · simp [P, disclosureBarrier, Problem.P2, Problem.PL, Problem.mass] at hy
      · simp [P, disclosureBarrier, Problem.P2, Problem.PL, Problem.mass, Problem.P1, discV] at hy
        norm_num at hy; linarith
      · simp [P, disclosureBarrier, Problem.P2, Problem.PL, Problem.mass, Problem.P1, discV] at hy
        norm_num at hy; linarith

/-- **A2c, the barrier under the 1-at-null variant** (`_li`). Under `P2li`, `silent` scores `1`
(the junk top value) and wins: the inversion the source headlined holds *only* under this
convention, which `main.tex:1610` permits ignoring (VERIFY A V3; finding 6).
Source: [[corr-legit-neg-inventory]] item 008 (A2c P2 inversion)
Kind: N+
Fidelity: variant: the inversion holds only under the 1-at-null convention (main.tex:1610, "the reader is welcome to ignore") -/
theorem A2c_barrier_inverted_li :
    let P := disclosureBarrier (1/2) (1/10) (1/2) 1 (by norm_num) (by norm_num)
    P.P2li (liftV (discV (1/2) (1/10) (1/2) (1/100))) 0 = 1 ∧
    argmax (P.P2li (liftV (discV (1/2) (1/10) (1/2) (1/100)))) = {0} := by
  intro P
  refine ⟨?_, ?_⟩
  · simp [P, disclosureBarrier, Problem.P2li, Problem.PL, Problem.mass]
  · apply argmax_eq_singleton_of_lt; intro b hb
    fin_cases b
    · exact absurd rfl hb
    · simp [P, disclosureBarrier, Problem.P2li, Problem.PL, Problem.mass, Problem.P1, discV]; norm_num
    · simp [P, disclosureBarrier, Problem.P2li, Problem.PL, Problem.mass, Problem.P1, discV]; norm_num

end Cleanroom.Corrigibility.LegitNegStatic
