import Cleanroom.Corrigibility.LegitNegStatic.Readouts
import Cleanroom.Corrigibility.LegitNegStatic.Toys

/-!
# Cluster A, A0–A1: the sealed regime's shared argmax and `¬L`-blindness

Package `legit-neg-static`, targets 8–9. Sources: `clusters/A/NEGATIVES.md` A0, A1;
`clusters/A/VERIFY.md` "A0: survives", "A1: narrowed" (V1, V2); [[corr-legit-neg-inventory]]
items 005, 006. Everything is stated over the `Problem` of record with `SealedBy ℓ`
(`Problem.lean`); the sealed displays `J₁`, `J₂` are the proposals `P1`, `P2` of the lifted
vector (`Proposals.lean`, `P1_liftV_of_SealedBy`).

**Register.** The yardstick `W` is unconstrained expected utility with correctly learned values
(`Problem.W`'s docstring); every theorem below named `regret` is a distance from *that*
yardstick, which is not a failure by Abram's concerns. Names carry the property (`blind`,
`regret_le`, `argmax_eq`), never a verdict.
-/

namespace Cleanroom.Corrigibility.LegitNegStatic

open Finset

/-- A strict maximiser is the unique element of the argmax.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmax_eq_singleton_of_lt {A : Type} [Fintype A] [DecidableEq A] {f : A → ℚ} (a : A)
    (h : ∀ b, b ≠ a → f b < f a) : argmax f = {a} := by
  ext c
  simp only [mem_argmax, Finset.mem_singleton]
  constructor
  · intro hc
    by_contra hne
    exact absurd (hc a) (not_le.2 (h c hne))
  · intro hc b
    rw [hc]
    by_cases hb : b = a
    · rw [hb]
    · exact (h b hb).le

/-- On a two-option menu, `argmax f = {1}` iff `f 0 < f 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmax_fin2_eq_one_iff (f : Fin 2 → ℚ) : argmax f = {1} ↔ f 0 < f 1 := by
  constructor
  · intro h
    have h0 : (0 : Fin 2) ∉ argmax f := by rw [h]; simp
    rw [mem_argmax] at h0
    simp only [Fin.forall_fin_two, le_refl, true_and, not_le] at h0
    exact h0
  · intro h
    exact argmax_eq_singleton_of_lt 1 fun b hb => by
      have : b = 0 := by fin_cases b <;> simp_all
      subst this; exact h

/-- `argmax_fin2_eq_zero_iff`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma argmax_fin2_eq_zero_iff (f : Fin 2 → ℚ) : argmax f = {0} ↔ f 1 < f 0 := by
  constructor
  · intro h
    have h1 : (1 : Fin 2) ∉ argmax f := by rw [h]; simp
    rw [mem_argmax] at h1
    simp only [Fin.forall_fin_two, le_refl, and_true, not_le] at h1
    exact h1
  · intro h
    exact argmax_eq_singleton_of_lt 0 fun b hb => by
      have : b = 1 := by fin_cases b <;> simp_all
      subst this; exact h

namespace Problem

variable {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)

/-! ## A0. P1 and P2 under sealing: same exact argmax, different units -/

/-- **A0 (i).** Under `SealedBy ℓ` with `0 < π(L)`, `argmaxOpt P2 = argmax P1` for *every* menu
vector (selection-dependent ones included): `P2 = P1 / π(L)` with a common positive factor.
Stated over `argmaxOpt`, so `P2`'s partiality is not assumed away.
Source: [[corr-legit-neg-inventory]] item 005 (A0)
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem argmaxOpt_P2_eq_argmax_P1_of_SealedBy {ℓ : S → Bool} (h : P.SealedBy ℓ)
    (hpos : 0 < P.mass ℓ) (V : MenuVec S A) : argmaxOpt (P.P2 V) = argmax (P.P1 V) := by
  have hne : ∀ a, P.PL a ≠ 0 := fun a => by
    rw [P.PL_eq_mass_of_SealedBy h]; exact hpos.ne'
  have hV : P.P2 V = fun a => some (P.P1 V a / P.mass ℓ) := funext fun a => by
    rw [P.P2_of_ne V a (hne a), P.PL_eq_mass_of_SealedBy h]
  rw [hV, argmaxOpt_some, argmax_div_pos _ hpos]

/-- **A0 (ii), ε-units.** An option `ε`-optimal in `P1` units is `ε / π(L)`-optimal in `P2`
units (the workspace's `R_U = p · R_auth`, recalled, not new).
Source: [[corr-legit-neg-inventory]] item 005 (A0)
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem eps_optimal_transfer {ℓ : S → Bool} (h : P.SealedBy ℓ) (hpos : 0 < P.mass ℓ)
    (V : MenuVec S A) (a : A) (ε : ℚ) (ha : ∀ b, P.P1 V b - ε ≤ P.P1 V a) :
    ∀ b, P.P1 V b / P.PL b - ε / P.mass ℓ ≤ P.P1 V a / P.PL a := by
  intro b
  rw [P.PL_eq_mass_of_SealedBy h, P.PL_eq_mass_of_SealedBy h, ← sub_div]
  exact (div_le_div_iff_of_pos_right hpos).2 (ha b)

/-- **A0 (iii), `π(L) = 0`, P1.** Every option scores `0`: the whole menu ties.
Source: [[corr-legit-neg-inventory]] item 005 (A0)
Kind: L
Fidelity: exact -/
theorem argmax_P1_eq_univ_of_mass_zero {ℓ : S → Bool} (h : P.SealedBy ℓ) (h0 : P.mass ℓ = 0)
    (V : MenuVec S A) : argmax (P.P1 V) = univ := by
  have : ∀ a, P.P1 V a = 0 := fun a =>
    P.P1_eq_zero_of_PL_eq_zero V a (by rw [P.PL_eq_mass_of_SealedBy h]; exact h0)
  rw [argmax_congr this, argmax_const]

/-- **A0 (iii), `π(L) = 0`, P2 (exclusion convention of record).** No option is a candidate:
the argmax is empty.
Source: [[corr-legit-neg-2-inventory]] item 2-003
Kind: L
Fidelity: exact (exclusion convention) -/
theorem argmaxOpt_P2_eq_empty_of_mass_zero {ℓ : S → Bool} (h : P.SealedBy ℓ)
    (h0 : P.mass ℓ = 0) (V : MenuVec S A) : argmaxOpt (P.P2 V) = ∅ :=
  argmaxOpt_none _ fun a => P.P2_of_eq V a (by rw [P.PL_eq_mass_of_SealedBy h]; exact h0)

/-- **A0 (iii), `π(L) = 0`, the 1-at-null variant.** `P2li` ties the whole menu at the top.
Variant theorem: FAF's `conditionalQuote` junk value read indicator-wise (ARGUMENT in the
source); not the convention of record.
Source: [[corr-legit-neg-inventory]] item 005 (A0, LI convention clause)
Kind: L
Fidelity: variant: 1-at-null convention -/
theorem argmax_P2li_eq_univ_of_mass_zero_li {ℓ : S → Bool} (h : P.SealedBy ℓ)
    (h0 : P.mass ℓ = 0) (V : MenuVec S A) : argmax (P.P2li V) = univ := by
  have : ∀ a, P.P2li V a = 1 := fun a => by
    unfold P2li; rw [if_pos (by rw [P.PL_eq_mass_of_SealedBy h]; exact h0)]
  rw [argmax_congr this, argmax_const]

/-! ## A1. `¬L`-blindness and the sharp bound -/

/-- **A1 (i), blindness (general form).** `P1` of `S1 Q` reads `Q` only on legitimate
terminals: two standards agreeing there give the same `P1`, hence the same argmax — under any
yardstick. Under `SealedBy ℓ` "legitimate terminals" are the `L`-states. Honestly a congruence
(`P1_congr`): kind L, though the mandate pre-labelled A1 (i) as P.
Source: [[corr-legit-neg-inventory]] item 006 (A1 (i)); VERIFY A cross-cutting caveat
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem P1_S1_congr_of_agree_on_leg {Q Q' : S → A → ℚ}
    (hQ : ∀ s a, P.leg s a = true → Q s a = Q' s a) (a : A) :
    P.P1 (S1 Q) a = P.P1 (S1 Q') a :=
  P.P1_congr a fun s hs => hQ s a hs

/-- `argmax_P1_S1_blind`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem argmax_P1_S1_blind {Q Q' : S → A → ℚ}
    (hQ : ∀ s a, P.leg s a = true → Q s a = Q' s a) :
    argmax (P.P1 (S1 Q)) = argmax (P.P1 (S1 Q')) :=
  argmax_congr (P.P1_S1_congr_of_agree_on_leg hQ)

/-- `argmaxOpt_P2_S1_blind`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem argmaxOpt_P2_S1_blind {Q Q' : S → A → ℚ}
    (hQ : ∀ s a, P.leg s a = true → Q s a = Q' s a) :
    argmaxOpt (P.P2 (S1 Q)) = argmaxOpt (P.P2 (S1 Q')) := by
  have : P.P2 (S1 Q) = P.P2 (S1 Q') := funext fun a => by
    unfold P2; rw [P.P1_S1_congr_of_agree_on_leg hQ]
  rw [this]

/-- **A1 (i), sealed form.** Under `SealedBy ℓ`, standards agreeing on `L` give the same
choices: the void-terminal values of `Q` never enter. A congruence (kind L).
Source: [[corr-legit-neg-inventory]] item 006 (A1 (i))
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem argmax_P1_S1_blind_of_SealedBy {ℓ : S → Bool} (h : P.SealedBy ℓ) {Q Q' : S → A → ℚ}
    (hQ : ∀ s, ℓ s = true → ∀ a, Q s a = Q' s a) :
    argmax (P.P1 (S1 Q)) = argmax (P.P1 (S1 Q')) :=
  P.argmax_P1_S1_blind fun s a hs => hQ s (by rw [← h s a]; exact hs) a

/-- Under `SealedBy ℓ`, `P1 (S1 Q) c` is the `L`-part of the standard `W Q c`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P1_S1_eq_Lpart_of_SealedBy {ℓ : S → Bool} (h : P.SealedBy ℓ) (Q : S → A → ℚ) (c : A) :
    P.P1 (S1 Q) c = ∑ s, P.prior s * ind (ℓ s) * Q s c := by
  unfold P1
  exact Finset.sum_congr rfl fun s _ => by simp [h s c]

/-- **A1 (ii), the bound.** Under `SealedBy ℓ` with `0 ≤ Q ≤ D`, a `P1`-maximiser under S1 has
`W`-regret at most `D · π(¬L)` against every option: the `L`-part of the regret is `≤ 0` by
optimality and the `¬L`-part is `≤ D · π(¬L)` by the range. **Under the yardstick `W`**
(unconstrained EU); the hypothesis `0 ≤ Q ≤ D` is (a)-grade modelling — with `Q` unbounded
below the bound is false.
Source: [[corr-legit-neg-inventory]] item 006 (A1 (ii))
Kind: P
Fidelity: exact
Hyps: (a) all; the range `0 ≤ Q ≤ D` is the modelling assumption of the source -/
theorem W_regret_le_of_mem_argmax_P1_S1 {ℓ : S → Bool} (h : P.SealedBy ℓ) {Q : S → A → ℚ}
    {D : ℚ} (hQ0 : ∀ s a, 0 ≤ Q s a) (hQD : ∀ s a, Q s a ≤ D) {a : A}
    (ha : a ∈ argmax (P.P1 (S1 Q))) (b : A) :
    P.W Q b - P.W Q a ≤ D * P.mass (fun s => !ℓ s) := by
  have hb := mem_argmax.1 ha b
  rw [P.P1_S1_eq_Lpart_of_SealedBy h, P.P1_S1_eq_Lpart_of_SealedBy h] at hb
  rw [P.W_split Q ℓ b, P.W_split Q ℓ a]
  have hN : (∑ s, P.prior s * ind (!ℓ s) * Q s b) - ∑ s, P.prior s * ind (!ℓ s) * Q s a
      ≤ D * P.mass (fun s => !ℓ s) := by
    rw [← Finset.sum_sub_distrib]
    unfold mass
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have hp := P.prior_nonneg s
    have hi := ind_nonneg (!ℓ s)
    have key : 0 ≤ P.prior s * ind (!ℓ s) * (D - (Q s b - Q s a)) :=
      mul_nonneg (mul_nonneg hp hi) (by linarith [hQ0 s a, hQD s b])
    nlinarith [key]
  linarith

/-- **A1 (ii), P2 form.** The same bound for a `P2`-maximiser (exclusion convention), via A0.
Source: [[corr-legit-neg-inventory]] item 006
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem W_regret_le_of_mem_argmaxOpt_P2_S1 {ℓ : S → Bool} (h : P.SealedBy ℓ) (hpos : 0 < P.mass ℓ)
    {Q : S → A → ℚ} {D : ℚ} (hQ0 : ∀ s a, 0 ≤ Q s a) (hQD : ∀ s a, Q s a ≤ D) {a : A}
    (ha : a ∈ argmaxOpt (P.P2 (S1 Q))) (b : A) :
    P.W Q b - P.W Q a ≤ D * P.mass (fun s => !ℓ s) := by
  rw [P.argmaxOpt_P2_eq_argmax_P1_of_SealedBy h hpos] at ha
  exact P.W_regret_le_of_mem_argmax_P1_S1 h hQ0 hQD ha b

/-- **A1 (iv), shift-type S3 keeps the argmax** (VERIFY A, V1): a common per-state shift
cancels under sealing, so `P1 (shiftS3 k)` and `P1 (S1 u)` have the same argmax, and the bound
of (ii) transfers.
Source: VERIFY A "A1: narrowed (i)" (shift-type)
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem argmax_P1_shiftS3_eq_of_SealedBy {ℓ : S → Bool} (h : P.SealedBy ℓ) (k : S → ℚ) :
    argmax (P.P1 (P.shiftS3 k)) = argmax (P.P1 (S1 P.u)) := by
  have : ∀ a, P.P1 (P.shiftS3 k) a = P.P1 (S1 P.u) a + (-(∑ s, P.prior s * ind (ℓ s) * k s)) := by
    intro a
    unfold P1 shiftS3
    rw [← sub_eq_add_neg, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [h s a, S1_apply]; ring
  rw [argmax_congr this, argmax_add_const]

/-- `W_regret_le_of_mem_argmax_P1_shiftS3`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem W_regret_le_of_mem_argmax_P1_shiftS3 {ℓ : S → Bool} (h : P.SealedBy ℓ) (k : S → ℚ)
    {D : ℚ} (hQ0 : ∀ s a, 0 ≤ P.u s a) (hQD : ∀ s a, P.u s a ≤ D) {a : A}
    (ha : a ∈ argmax (P.P1 (P.shiftS3 k))) (b : A) :
    P.W P.u b - P.W P.u a ≤ D * P.mass (fun s => !ℓ s) := by
  rw [P.argmax_P1_shiftS3_eq_of_SealedBy h] at ha
  exact P.W_regret_le_of_mem_argmax_P1_S1 h hQ0 hQD ha b

/-! ### T2 on a known branch (A1 (v); positive boundary of target 17) -/

/-- `P1` in the singleton cell `{s}`: the point mass reads the diagonal at `s`, gated by its
legitimacy.
Source: NEGATIVES A1 "T2 (branch known)"
Kind: L
Fidelity: exact -/
theorem restrict_singleton_P1 [DecidableEq S] (s : S) (hs : 0 < P.prior s) (V : MenuVec S A)
    (a : A) : (P.restrict {s} (by simpa using hs)).P1 V a = ind (P.leg s a) * V s a a := by
  unfold P1
  simp only [restrict_prior, restrict_leg, P.cellprior_singleton s hs]
  simp [ite_mul, Finset.sum_ite_eq']

/-- **A1 (v), T2 on a known-void branch.** If `s ∉ L` (sealed), `P1` in the cell `{s}` ties the
whole menu at `0` for every vector — the full-range harm included; and a common window value
(any `V` at all) does not break the tie, trivially: `P1` is identically `0` on the cell.
Source: [[corr-legit-neg-inventory]] item 006 (A1 (iv), T2 clause); VERIFY A V2
Kind: L
Fidelity: exact -/
theorem argmax_P1_restrict_void_eq_univ [DecidableEq S] {ℓ : S → Bool} (h : P.SealedBy ℓ)
    (s : S) (hs : 0 < P.prior s) (hv : ℓ s = false) (V : MenuVec S A) :
    argmax ((P.restrict {s} (by simpa using hs)).P1 V) = univ := by
  have : ∀ a, (P.restrict {s} (by simpa using hs)).P1 V a = 0 := fun a => by
    rw [P.restrict_singleton_P1 s hs V a, h s a, hv]; simp
  rw [argmax_congr this, argmax_const]

/-- **T2 on a known-legitimate branch is exact** (positive boundary, target 17): if `s ∈ L`,
`P1` in the cell `{s}` is the vector `V s · ·` itself.
Source: [[corr-legit-neg-inventory]] item 014 (A6 positive boundary)
Kind: L
Fidelity: exact -/
theorem restrict_singleton_P1_of_leg [DecidableEq S] {ℓ : S → Bool} (h : P.SealedBy ℓ)
    (s : S) (hs : 0 < P.prior s) (hl : ℓ s = true) (V : MenuVec S A) (a : A) :
    (P.restrict {s} (by simpa using hs)).P1 V a = V s a a := by
  rw [P.restrict_singleton_P1 s hs V a, h s a, hl]; simp

end Problem

/-! ## Instances and witnesses (cluster A fixtures A0, A1; VERIFY V1) -/

open Problem

section Incaution

variable (q δ x harm : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1)

/-- On `incautionInstance`, `P1 (S1 u)` of `risky` exceeds that of `safe` by `(1 − q) δ`.
Source: NEGATIVES A1 "The family"
Kind: L
Fidelity: exact -/
theorem incaution_P1_diff :
    (incautionInstance q δ x harm h0 h1).P1 (S1 (incautionInstance q δ x harm h0 h1).u) 1
      - (incautionInstance q δ x harm h0 h1).P1 (S1 (incautionInstance q δ x harm h0 h1).u) 0
      = (1 - q) * δ := by
  simp [incautionInstance, P1]; ring

/-- On `incautionInstance`, `W safe − W risky = q · harm − (1 − q) δ` (with `harm = 1`: the
source's gap `q − (1 − q) δ`).
Source: NEGATIVES A1 "The family"
Kind: L
Fidelity: exact -/
theorem incaution_W_gap :
    (incautionInstance q δ x harm h0 h1).W (incautionInstance q δ x harm h0 h1).u 0
      - (incautionInstance q δ x harm h0 h1).W (incautionInstance q δ x harm h0 h1).u 1
      = q * harm - (1 - q) * δ := by
  simp [incautionInstance, W, EU, Fin.sum_univ_two]; ring

/-- On `incautionInstance` with `q < 1` and `0 < δ`, `risky` is the strict `P1`-maximiser
(and, by A0, the strict `P2`-maximiser).
Source: NEGATIVES A1 "The family"
Kind: N+
Fidelity: exact -/
theorem incaution_argmax_risky (hq : q < 1) (hδ : 0 < δ) :
    argmax ((incautionInstance q δ x harm h0 h1).P1 (S1 (incautionInstance q δ x harm h0 h1).u))
      = {1} := by
  apply argmax_eq_singleton_of_lt
  intro b hb
  have hb0 : b = 0 := by fin_cases b <;> simp_all
  subst hb0
  have := incaution_P1_diff q δ x harm h0 h1
  have : 0 < (1 - q) * δ := mul_pos (by linarith) hδ
  linarith

/-- The `¬L`-mass of `incautionInstance` is `q`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma incaution_mass_notL :
    (incautionInstance q δ x harm h0 h1).mass (fun s => !legG s) = q := by
  simp [incautionInstance, mass, legG, Fin.sum_univ_two]

end Incaution

/-- **A0, N+ witness.** On `incautionInstance (1/2) (1/10) (1/2) 1` under S1 the scores are not
constant and both proposals pick `risky`: `argmax P1 = argmaxOpt P2 = {risky}`.
Source: [[corr-legit-neg-inventory]] item 005 (A0); fixture A1 (`q = 1/2`)
Kind: N+
Fidelity: exact -/
theorem A0_witness :
    let P := incautionInstance (1/2) (1/10) (1/2) 1 (by norm_num) (by norm_num)
    argmax (P.P1 (S1 P.u)) = {1} ∧ argmaxOpt (P.P2 (S1 P.u)) = {1} := by
  intro P
  have h1 : argmax (P.P1 (S1 P.u)) = {1} :=
    incaution_argmax_risky (1/2) (1/10) (1/2) 1 (by norm_num) (by norm_num)
      (by norm_num : (1/2 : ℚ) < 1) (by norm_num : (0 : ℚ) < 1/10)
  refine ⟨h1, ?_⟩
  rw [P.argmaxOpt_P2_eq_argmax_P1_of_SealedBy (incautionInstance_SealedBy _ _ _ _ _ _) ?_, h1]
  simp [P, incautionInstance, mass, legG]
  norm_num

/-- **A0 (ii), the exact factor.** With `π(L) = 1/100` and `V_g = (1/2, 1)`
(`incautionInstance (99/100) (1/2) (1/2) _`): `R_U = 1/200` and `R_auth = 1/2 = R_U / π(L)`.
Source: [[corr-legit-neg-inventory]] item 005 (A0 ε-units instance)
Kind: N+
Fidelity: exact -/
theorem A0_eps_units :
    let P := incautionInstance (99/100) (1/2) (1/2) 1 (by norm_num) (by norm_num)
    P.P1 (S1 P.u) 1 - P.P1 (S1 P.u) 0 = 1/200 ∧
      P.P1 (S1 P.u) 1 / P.PL 1 - P.P1 (S1 P.u) 0 / P.PL 0 = 1/2 := by
  intro P
  constructor
  · simp [P, incautionInstance, P1]; norm_num
  · simp [P, incautionInstance, P1, PL, mass]; norm_num

/-- **A1 (iii), sharpness, parametric in `q`.** For every `π(¬L) = q < 1` and every `ε > 0`
there is `δ > 0` (with `harm = 1`, `x = 1/2`, `x + δ ≤ 1`) at which `risky` is the strict
`P1`-maximiser and the `W`-regret exceeds `D · π(¬L) − ε = q − ε`: the sup of the regret is
`D · π(¬L)` for every `q < 1`, approached as `δ → 0`, so as `π(¬L) → 1` the chosen option can be
worse by almost the whole value range.
Source: [[corr-legit-neg-inventory]] item 006 (A1 sharpness); NEGATIVES A1 headline
Kind: P
Fidelity: exact -/
theorem A1_sharp_all_q (q : ℚ) (h0 : 0 ≤ q) (hq : q < 1) (ε : ℚ) (hε : 0 < ε) :
    ∃ δ : ℚ, 0 < δ ∧ (1/2 : ℚ) + δ ≤ 1 ∧
      argmax ((incautionInstance q δ (1/2) 1 h0 hq.le).P1
        (S1 (incautionInstance q δ (1/2) 1 h0 hq.le).u)) = {1} ∧
      (incautionInstance q δ (1/2) 1 h0 hq.le).W (incautionInstance q δ (1/2) 1 h0 hq.le).u 0
        - (incautionInstance q δ (1/2) 1 h0 hq.le).W (incautionInstance q δ (1/2) 1 h0 hq.le).u 1
        > q - ε := by
  have hδ0 : 0 < min (ε/2) (1/2) := lt_min (by linarith) (by norm_num)
  refine ⟨min (ε/2) (1/2), hδ0, ?_, ?_, ?_⟩
  · have := min_le_right (ε/2) (1/2); linarith
  · exact incaution_argmax_risky _ _ _ _ _ _ hq hδ0
  · rw [incaution_W_gap]
    have h1 : min (ε/2) (1/2) ≤ ε/2 := min_le_left _ _
    have hqδ : 0 ≤ q * min (ε/2) (1/2) := mul_nonneg h0 hδ0.le
    nlinarith [h1, hqδ, hε]

/-- **A1 (iii), sharpness, the `q = 1/2` instance.** For every `ε > 0` there is an instance of
the family with `harm = 1`, `0 < δ`, `q < 1`, `x + δ ≤ 1`, in which `risky` is the strict
maximiser and the `W`-regret exceeds `D · π(¬L) − ε = q − ε` (`A1_sharp_all_q` at `q = 1/2`).
Source: [[corr-legit-neg-inventory]] item 006 (A1 sharpness)
Kind: N+
Fidelity: exact (one `q`; the parametric headline is `A1_sharp_all_q`) -/
theorem A1_sharp (ε : ℚ) (hε : 0 < ε) :
    ∃ (q δ : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1), q < 1 ∧ 0 < δ ∧ (1/2 : ℚ) + δ ≤ 1 ∧
      argmax ((incautionInstance q δ (1/2) 1 h0 h1).P1
        (S1 (incautionInstance q δ (1/2) 1 h0 h1).u)) = {1} ∧
      (incautionInstance q δ (1/2) 1 h0 h1).W (incautionInstance q δ (1/2) 1 h0 h1).u 0
        - (incautionInstance q δ (1/2) 1 h0 h1).W (incautionInstance q δ (1/2) 1 h0 h1).u 1
        > q - ε := by
  refine ⟨1/2, min (ε/2) (1/2), by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, ?_⟩
  · exact lt_min (by linarith) (by norm_num)
  · have := min_le_right (ε/2) (1/2); linarith
  · exact incaution_argmax_risky _ _ _ _ _ _ (by norm_num) (lt_min (by linarith) (by norm_num))
  · rw [incaution_W_gap]
    have := min_le_left (ε/2) (1/2)
    have h := min_le_right (ε/2) (1/2)
    nlinarith [h, this]

/-- **A1 (iii), the tie attains the bound.** At `δ = 0` both options are `P1`-maximisers and the
`W`-regret of `risky` is exactly `q = D · π(¬L)`.
Source: [[corr-legit-neg-inventory]] item 006 (A1 "attained at ties")
Kind: N+
Fidelity: exact -/
theorem A1_tie_attains (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    argmax ((incautionInstance q 0 (1/2) 1 h0 h1).P1 (S1 (incautionInstance q 0 (1/2) 1 h0 h1).u))
      = univ ∧
    (incautionInstance q 0 (1/2) 1 h0 h1).W (incautionInstance q 0 (1/2) 1 h0 h1).u 0
      - (incautionInstance q 0 (1/2) 1 h0 h1).W (incautionInstance q 0 (1/2) 1 h0 h1).u 1
      = q := by
  constructor
  · ext a; simp only [mem_argmax, Finset.mem_univ, iff_true]
    intro b; fin_cases a <;> fin_cases b <;> simp [incautionInstance, P1]
  · rw [incaution_W_gap]; ring

/-- VERIFY A's V1 instance: two legitimate states with weights `2/5`, `3/5` (`π(¬L) = 0`),
`Q = ((1, 0), (49/100, 1/2))`.
Source: VERIFY A V1
Kind: D
Fidelity: exact -/
def ordinalWitness : Problem (Fin 2) (Fin 2) where
  prior := ![2/5, 3/5]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> norm_num
  prior_sum := by simp [Fin.sum_univ_two]; norm_num
  leg := fun _ _ => true
  u := fun s a => ![![1, 0], ![49/100, 1/2]] s a

/-- **A1 (iv), ordinal S3 breaks the bound** (VERIFY A, V1): on `ordinalWitness`, sealed with
`L = everything` (`π(¬L) = 0`), the rank scores pick `b` while `W` prefers `a` by `197/500`.
An `L`-world distortion, hence also the exception to A6's positive boundary.
Source: VERIFY A "A1: narrowed (i)" (ordinal); finding 3
Kind: N+
Fidelity: exact -/
theorem A1_ordinal_breaks_bound :
    ordinalWitness.SealedBy (fun _ => true) ∧
    ordinalWitness.mass (fun _ => !true) = 0 ∧
    argmax (ordinalWitness.P1 ordinalWitness.ordinalS3) = {1} ∧
    ordinalWitness.W ordinalWitness.u 0 - ordinalWitness.W ordinalWitness.u 1 = 197/500 := by
  refine ⟨fun _ _ => rfl, by simp [ordinalWitness, mass], ?_, ?_⟩
  · apply argmax_eq_singleton_of_lt
    intro b hb
    have hb0 : b = 0 := by fin_cases b <;> simp_all
    subst hb0
    simp [ordinalWitness, P1, ordinalS3, Fin.sum_univ_two, Fin.forall_fin_two]
    norm_num
  · simp [ordinalWitness, W, EU, Fin.sum_univ_two]; norm_num

end Cleanroom.Corrigibility.LegitNegStatic
