import Cleanroom.Decision.DpLocalOpt.Sia

/-!
# `dp-local-opt`: Theorem 2 — the EDT+SSA evaluator and point-deviation coherence (T6)

v2 §8 Theorem 2 transposes Oesterheld's minimal-reference-class construction: the EDT+SSA value
of `m` at `d` weights each instance `i` on each leaf `ℓ ∈ occ(d)` by
`μ_{C[d↦m]}(ℓ ∣ occ(d)) / #_d(ℓ)`. The evaluator is defined **as the source writes it**
(`ssaValue`: instance sum and `#_d` division inside), and the cancellation is a lemma
(`ssaValue_mul_mass`). The identity holds for **every** procedure (amendment A28): its only
ingredients are (i) `∑_{i < n} x/n = x`, (ii) off-occurrence invariance of the leaf law
(`leafLaw_deviate_of_not_occ`, proved here in the coalition form `leafLaw_congr_off_of_count_zero`),
and (iii) Lemma 1 (`occurrence_constancy`, imported from `dp-core-tree`). Lean's `x / 0 = 0`
is disclosed: the headline is multiplicative, and the argmax identity `ssaValue_le_iff` carries
`0 < μ(occ(d))` as its only hypothesis.
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree

variable {Ω ι : Type} {acts : ι → Type} {K : Type} [Field K] [LinearOrder K]
  [IsStrictOrderedRing K] [∀ d, Fintype (acts d)] [DecidableEq ι]

/-! ### (i) The instance sum cancels the `#_d` division -/

/-- `∑_{i : Fin n} x / n = x` for `n ≥ 1`.
Source: [[decision-problems-v2]] §8 Theorem 2 proof ("Summing over the `#_d(ℓ)` instances
cancels the SSA division")
Kind: T -/
theorem sum_fin_div_self (x : K) {n : ℕ} (hn : 0 < n) :
    ∑ _i : Fin n, x / (n : K) = x := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

/-! ### (ii) Off-occurrence invariance -/

section offOcc

variable (C : Proc ι acts K)

/-- **Off-occurrence invariance, coalition form**: two procedures agreeing off a set `D` of
points give the same mass to every leaf whose path meets no `D`-node.
Source: [[decision-problems-v2]] §8 Theorem 2 proof ("leaves outside `occ(d)` … paths avoiding
`d`-nodes never consult `C(d)`"); `repair/harmony.md` HA-7′ (the coalition form)
Kind: P -/
theorem leafLaw_congr_off_of_count_zero (D : Finset ι) {C' : Proc ι acts K}
    (h : ∀ d, d ∉ D → C' d = C d) :
    (B : Tree Ω ι acts K) → ∀ ℓ, (∀ d ∈ D, count d B ℓ = 0) → leafLaw C' B ℓ = leafLaw C B ℓ
  | leaf _ _, _, _ => rfl
  | chance _ β child, ⟨i, ℓ⟩, hc => by
      rw [leafLaw_chance, leafLaw_chance,
        leafLaw_congr_off_of_count_zero D h (child i) ℓ (fun d hd => by simpa using hc d hd)]
  | decision d' child, ⟨a, ℓ⟩, hc => by
      have hd' : d' ∉ D := fun hmem => by
        have := hc d' hmem
        simp at this
      rw [leafLaw_decision, leafLaw_decision, h d' hd',
        leafLaw_congr_off_of_count_zero D h (child a) ℓ (fun d hd => by
          have := hc d hd
          simp only [count_decision] at this
          omega)]

/-- **Off-occurrence invariance**: off `occ(d)`, the leaf law of `C[d ↦ m]` is that of `C`.
Source: [[decision-problems-v2]] §8 Theorem 2 proof; A28
Kind: P
Fidelity: exact -/
theorem leafLaw_deviate_of_not_occ (B : Tree Ω ι acts K) (d : ι) (m : FinDistr K (acts d))
    {ℓ : B.Leaves} (hℓ : ℓ ∉ occ d B) : leafLaw (C.deviate d m) B ℓ = leafLaw C B ℓ := by
  apply leafLaw_congr_off_of_count_zero C {d} (fun d' hd' => Proc.deviate_ne C m (by simpa using hd'))
  intro d' hd'
  rw [Finset.mem_singleton] at hd'; subst hd'
  simpa [occ] using hℓ

end offOcc

/-! ### The evaluator and its pieces -/

section evaluator

variable (C : Proc ι acts K) (B : Tree Ω ι acts K) (d : ι)

/-- **The EDT+SSA evaluator of `m` at `d`, as the source writes it**:
`(∑_{ℓ ∈ occ(d)} (∑_{i < #_d(ℓ)} μ_{C[d↦m]}(ℓ) / #_d(ℓ)) r(ℓ)) / μ_{C[d↦m]}(occ(d))` — each instance
`i` on each leaf of `occ(d)` weighted by `μ_{C[d↦m]}(ℓ ∣ occ(d)) / #_d(ℓ)` (Oesterheld's
minimal reference class, transposed). Lean's `x / 0 = 0` applies when `μ(occ(d)) = 0`; the
headlines are stated multiplicatively or under `0 < μ(occ(d))`.
Source: [[decision-problems-v2]] §8 Theorem 2 (line 273, the displayed evaluator)
Kind: D
Fidelity: exact (the conditional `μ(ℓ ∣ occ)` rendered as `μ(ℓ) / μ(occ)`, pulled outside the
sums; stated for mixed `m` as A28 licenses) -/
def ssaValue (m : FinDistr K (acts d)) : K :=
  (∑ ℓ ∈ occ d B, (∑ _i : Fin (count d B ℓ), leafLaw (C.deviate d m) B ℓ / (count d B ℓ : K)) *
    payoff B ℓ) / mass (C.deviate d m) B (occ d B)

/-- The on-occurrence payoff mass of `C[d ↦ m]`: `∑_{ℓ ∈ occ(d)} μ_{C[d↦m]}(ℓ) r(ℓ)`.
Source: [[decision-problems-v2]] §8 Theorem 2 proof
Kind: D -/
def ssaNum (m : FinDistr K (acts d)) : K :=
  ∑ ℓ ∈ occ d B, leafLaw (C.deviate d m) B ℓ * payoff B ℓ

/-- The off-occurrence payoff mass of `C`: `∑_{ℓ ∉ occ(d)} μ_C(ℓ) r(ℓ)` — invariant under every
deviation at `d` (`leafLaw_deviate_of_not_occ`).
Source: [[decision-problems-v2]] §8 Theorem 2 proof ("leaves outside `occ(d)` contribute … a
quantity constant in `a`")
Kind: D -/
def offOcc [∀ d, DecidableEq (acts d)] : K :=
  ∑ ℓ ∈ Finset.univ.filter (fun ℓ => ℓ ∉ occ d B), leafLaw C B ℓ * payoff B ℓ

/-- `offOcc` is invariant under deviation at `d`.
Source: [[decision-problems-v2]] §8 Theorem 2 proof
Kind: L -/
theorem offOcc_deviate [∀ d, DecidableEq (acts d)] (m : FinDistr K (acts d)) : offOcc (C.deviate d m) B d = offOcc C B d := by
  unfold offOcc
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [Finset.mem_filter] at hℓ
  rw [leafLaw_deviate_of_not_occ C B d m hℓ.2]

/-- **Theorem 2, the decomposition**: `V_B(C[d ↦ m]) = ssaNum(m) + offOcc`, the off-occurrence
part not depending on `m`.
Source: [[decision-problems-v2]] §8 Theorem 2 proof; A28 (every procedure, mixed `m`)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem value_deviate_eq_ssaNum_add_offOcc [∀ d, DecidableEq (acts d)] (m : FinDistr K (acts d)) :
    value (C.deviate d m) B = ssaNum C B d m + offOcc C B d := by
  unfold value ssaNum offOcc
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun ℓ => ℓ ∈ occ d B)]
  congr 1
  · rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    rw [Finset.mem_filter] at hℓ
    rw [leafLaw_deviate_of_not_occ C B d m hℓ.2]

/-- **Theorem 2, the cancellation**: `ssaValue(m) · μ_C(occ(d)) = ssaNum(m)` for every `m` — the
instance sum cancels the `#_d` division (`sum_fin_div_self`) and Lemma 1
(`occurrence_constancy`) holds the denominator at `μ_C(occ(d))`. Unconditional: when
`μ_C(occ(d)) = 0` both sides vanish (every leaf of `occ(d)` then has mass `0` under `C[d ↦ m]`).
Source: [[decision-problems-v2]] §8 Theorem 2 proof; A28
Kind: C (`sum_fin_div_self` + Lemma 1 `occurrence_constancy`; regraded from P in repair round 1,
docstring aligned in round 2)
Fidelity: stronger (no positivity hypothesis; the division is Lean's)
Hyps: (a) all -/
theorem ssaValue_mul_mass (m : FinDistr K (acts d)) :
    ssaValue C B d m * mass C B (occ d B) = ssaNum C B d m := by
  unfold ssaValue ssaNum
  rw [occurrence_constancy]
  have hnum : (∑ ℓ ∈ occ d B, (∑ _i : Fin (count d B ℓ), leafLaw (C.deviate d m) B ℓ /
      (count d B ℓ : K)) * payoff B ℓ) = ∑ ℓ ∈ occ d B, leafLaw (C.deviate d m) B ℓ * payoff B ℓ := by
    refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have hc : 0 < count d B ℓ := by simpa [occ] using hℓ
    rw [sum_fin_div_self _ hc]
  rw [hnum]
  by_cases hmass : mass C B (occ d B) = 0
  · rw [hmass, mul_zero]
    symm
    apply Finset.sum_eq_zero
    intro ℓ hℓ
    have hzero : leafLaw (C.deviate d m) B ℓ = 0 := by
      have hsum : ∑ ℓ ∈ occ d B, leafLaw (C.deviate d m) B ℓ = 0 := by
        rw [← occurrence_constancy C B d m] at hmass; exact hmass
      exact (Finset.sum_eq_zero_iff_of_nonneg fun ℓ _ => leafLaw_nonneg _ B ℓ).mp hsum ℓ hℓ
    rw [hzero, zero_mul]
  · exact div_mul_cancel₀ _ hmass

/-- `ssaValue(m) = ssaNum(m) / μ_C(occ(d))`.
Source: none: infrastructure
Kind: L -/
theorem ssaValue_eq_div (m : FinDistr K (acts d)) :
    ssaValue C B d m = ssaNum C B d m / mass C B (occ d B) := by
  unfold ssaValue
  rw [occurrence_constancy]
  congr 1
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  have hc : 0 < count d B ℓ := by simpa [occ] using hℓ
  rw [sum_fin_div_self _ hc]

/-- **Theorem 2 (EDT+SSA ratifiability is point-deviation coherence), argmax form, for every
procedure and for mixed deviations**: with `0 < μ_C(occ(d))`,
`ssaValue(m) ≤ ssaValue(m') ↔ V_B(C[d ↦ m]) ≤ V_B(C[d ↦ m'])`. Composition of the decomposition
(`value_deviate_eq_ssaNum_add_offOcc`), the cancellation (`ssaValue_mul_mass`, i.e. (i) +
Lemma 1) and off-occurrence invariance (`offOcc_deviate`).
Source: [[decision-problems-v2]] §8 Theorem 2 (line 273) | A28 | dp-core-052 | dp-cf-2-058 |
dp-cf-048
Kind: C
Fidelity: stronger (v2: deterministic `C`, pure `a`; here every `C`, mixed `m`, as A28 licenses)
| variant: payoffs in a linearly ordered field
Scope: Definition 6; every tree
Hyps: (a) `0 < μ_C(occ(d))` is v2's own hypothesis (Lemma 1 makes it `m`-independent) -/
theorem ssaValue_le_iff [∀ d, DecidableEq (acts d)] (hpos : 0 < mass C B (occ d B)) (m m' : FinDistr K (acts d)) :
    ssaValue C B d m ≤ ssaValue C B d m' ↔
      value (C.deviate d m) B ≤ value (C.deviate d m') B := by
  rw [ssaValue_eq_div, ssaValue_eq_div, div_le_div_iff_of_pos_right hpos,
    value_deviate_eq_ssaNum_add_offOcc, value_deviate_eq_ssaNum_add_offOcc, add_le_add_iff_right]

/-- **Theorem 2's necessity clause (v2's consequence sentence)**: a `V`-optimal procedure that is
deterministic at `d` (`C(d) = δ_a`) has `a` maximising the EDT+SSA evaluator over pure actions.
Source: [[decision-problems-v2]] §8 Theorem 2 ("consequently every `V`-optimal deterministic `C`
satisfies `C(d) ∈ argmax_a V_B(C[d ↦ a])`")
Kind: C
Fidelity: exact (determinism only at `d`, as the clause uses)
Hyps: (a) all -/
theorem ssaValue_pure_le_of_isOptimal [∀ d, DecidableEq (acts d)] (h : IsOptimal C B)
    (hpos : 0 < mass C B (occ d B)) {a : acts d} (ha : C d = FinDistr.pure a) (b : acts d) :
    ssaValue C B d (FinDistr.pure b) ≤ ssaValue C B d (FinDistr.pure a) := by
  rw [ssaValue_le_iff C B d hpos]
  have : C.deviate d (FinDistr.pure a) = C := by
    rw [← ha]; funext d'; by_cases hd : d' = d
    · subst hd; simp
    · simp [Proc.deviate_ne C _ hd]
  rw [this]
  exact h _

/-- **Mixed coherence is the mixed EDT+SSA ratifiability**: under `0 < μ_C(occ(d))`,
`CoherentAt C B d ↔ ∀ m, ssaValue(m) ≤ ssaValue(C(d))` — v2 comment (i)'s identification for the
mixed Definition 22 (A28, A30).
Source: [[decision-problems-v2]] §8 comment (i) after Definition 22 ("by Theorem 2 it is exactly
EDT+SSA ratifiability"); A28(b), A30
Kind: C
Fidelity: exact (mixed form)
Hyps: (a) `0 < μ_C(occ(d))` -/
theorem coherentAt_iff_ssa [∀ d, DecidableEq (acts d)] (hpos : 0 < mass C B (occ d B)) :
    CoherentAt C B d ↔ ∀ m, ssaValue C B d m ≤ ssaValue C B d (C d) := by
  have hself : C.deviate d (C d) = C := by
    funext d'; by_cases hd : d' = d
    · subst hd; simp
    · simp [Proc.deviate_ne C _ hd]
  unfold CoherentAt
  constructor
  · intro h m
    rw [ssaValue_le_iff C B d hpos, hself]
    exact h m
  · intro h m
    have := h m
    rw [ssaValue_le_iff C B d hpos, hself] at this
    exact this

/-- **`ssaValue_le_iff` with no positivity hypothesis**: at `μ_C(occ(d)) = 0` every `ssaNum`
vanishes and every `V(C[d ↦ ·])` equals `offOcc`, so both sides of the `↔` hold. v2's
`0 < μ(occ(d))` is therefore removable, not load-bearing.
Source: [[decision-problems-v2]] §8 Theorem 2; A28; audit r1 adversarial N1 (probe C, adopted)
Kind: C
Fidelity: stronger (no positivity)
Hyps: (a) all -/
theorem ssaValue_le_iff' [∀ d, DecidableEq (acts d)] (m m' : FinDistr K (acts d)) :
    ssaValue C B d m ≤ ssaValue C B d m' ↔
      value (C.deviate d m) B ≤ value (C.deviate d m') B := by
  rcases (mass_nonneg C B (occ d B)).lt_or_eq with hpos | h0
  · exact ssaValue_le_iff C B d hpos m m'
  · have hz : ∀ m'', ssaNum C B d m'' = 0 := fun m'' => by
      rw [← ssaValue_mul_mass, ← h0, mul_zero]
    rw [ssaValue_eq_div, ssaValue_eq_div, hz, hz, value_deviate_eq_ssaNum_add_offOcc,
      value_deviate_eq_ssaNum_add_offOcc, hz, hz]
    simp

/-- **Mixed coherence is mixed EDT+SSA ratifiability, with no positivity hypothesis.**
Source: [[decision-problems-v2]] §8 comment (i); A28(b), A30; audit r1 adversarial N1
Kind: C
Fidelity: stronger (no positivity)
Hyps: (a) all -/
theorem coherentAt_iff_ssa' [∀ d, DecidableEq (acts d)] :
    CoherentAt C B d ↔ ∀ m, ssaValue C B d m ≤ ssaValue C B d (C d) := by
  have hself : C.deviate d (C d) = C := by
    funext d'; by_cases hd : d' = d
    · subst hd; simp
    · simp [Proc.deviate_ne C _ hd]
  unfold CoherentAt
  constructor
  · intro h m
    rw [ssaValue_le_iff' C B d, hself]
    exact h m
  · intro h m
    have := h m
    rw [ssaValue_le_iff' C B d, hself] at this
    exact this

end evaluator

end Cleanroom.Decision.DpLocalOpt
