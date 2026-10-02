import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Mul
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# DReST: usefulness and neutrality (Targets 12, 13, 27)

Abstract environment (Thornley et al., "Towards shutdownable agents via stochastic choice",
App. D): `k ≥ 1` selectable lengths, a policy is a length distribution `p ∈ stdSimplex` and a
vector `ρ : Fin k → ℝ`, `0 ≤ ρ l ≤ 1`, the fraction of the maximum conditional coin value
`E_π(C | L = l) / max_Π`. **(c) disclosed**: the paper's `E_π(C|L=l)` and `Pr_π{L = l}` are taken
as independently controllable and every `(p, ρ)` as achievable (true in its gridworlds).

* `usefulness p ρ = ∑ p l ρ l` (Def D.3; the `0/0` case is excluded by taking the ratio as
  primitive).
* `neutrality p = ∑ negMulLog (p l)` (Def D.4 with natural log: a positive constant times the
  paper's `log₂` entropy, changing no argmax; **(c)** stand-in for FAF's `measureEntropy`).
  `neutrality_le_uniform`, `neutrality_eq_uniform_iff` (Jensen on `strictConcaveOn_negMulLog`).
* `F n k lam mu p ρ = ∑_{i<n} mu^i ∑_l p l ρ l (1 − (1−lam) p l)^i` — the expected DReST return of an
  `n`-mini-episode meta-episode under the paper's own reading (lengths i.i.d. from `p`, since
  the agent cannot distinguish mini-episodes), with `mu = lam^{−1/k}` the per-round rescaling.
  Its derivation from the enumerated meta-episode (sum over length sequences of probability ×
  return) is `DrestDerivation.lean` (`F_eq_metaReturn`, repair round 1): for `∑ p = 1`, `F` is
  exactly the enumerated expected return, so the refutations below hold for DReST's own Def D.2
  (`lemma_D2_false_enumerated`, `theorem_5_1_neutrality_false_enumerated`). Until that file
  existed `F` was a (c); both round-1 auditors had reproduced the enumeration numerically for
  `n ≤ 8`.
* **Usefulness half** (`F_strictMono_rho`, `usefulness_eq_one_of_isMaxOn`): `F` is strictly
  increasing in each `ρ l` with `p l > 0`, so every maximiser has `ρ l = 1` where `p l > 0` and
  `usefulness = 1`.
* **Neutrality half refuted** (`lemma_D2_false`, `theorem_5_1_neutrality_false`): at
  `lam = 1/4`, `k = 2`, `mu = 2`, `ρ ≡ 1`, `n = 8`: `F(1/4, 3/4) − F(1/2, 1/2) = 13191189/4194304 > 0`
  (exact dyadic arithmetic, `norm_num`). So Lemma D.2 ("equalizing probabilities increases
  expected return") is false as stated, and no maximiser of `F 8` on the simplex is uniform.
* **The repair** (Target 27, `repaired_return_le_uniform`): without the per-round rescaling the
  return is `∑_l φ(p l)` with `φ` concave, and uniform is optimal for every `n` (strictness for
  `n ≥ 2` not proved).
* **Joint maximisation** (`theorem_5_1_neutrality_false_joint`): the theorem quantifies over
  policies `(p, ρ)`; a joint maximiser has `ρ = 1` on the support of `p` (`usefulness_eq_one_of_isMaxOn`),
  so `p` maximises the `ρ ≡ 1` slice and is not uniform (audit round 1, fidelity non-blocking 7).
-/

namespace Cleanroom.Lit.LitShutdownPrefs

namespace Drest

open Finset

variable {k : ℕ}

/-- **usefulness** of the policy `(p, ρ)`: the expected fraction of available coins collected,
`∑ l, p l · ρ l`.
Source: DReST Def D.3 (l. 372), with the ratio `E_π(C|L=l)/max_Π` taken as the primitive `ρ l`
(the `0/0` case is thereby excluded); [[lit-shutdown-prefs-mandate]] Target 12
Kind: D
Fidelity: variant: (c) `ρ` primitive; every `(p, ρ)` achievable -/
def usefulness (p ρ : Fin k → ℝ) : ℝ := ∑ l, p l * ρ l

/-- **neutrality** of the length distribution `p`: its Shannon entropy in nats,
`∑ l, −p l · log (p l)`.
Source: DReST Def D.4 (l. 394); [[lit-shutdown-prefs-mandate]] Target 12
Kind: D
Fidelity: variant: (c) `Real.negMulLog` (natural log) stands in for FAF's
`ProbabilityTheory.measureEntropy` and for the paper's `log₂` — a positive constant factor -/
noncomputable def neutrality (p : Fin k → ℝ) : ℝ := ∑ l, Real.negMulLog (p l)

/-- The uniform length distribution.
Source: DReST App. D ("maximally neutral if and only if … `Pr_π{L = x} = 1/k`")
Kind: D -/
noncomputable def uniform (k : ℕ) : Fin k → ℝ := fun _ => 1 / k

/-- **Maximally neutral**: every selectable length has probability `1/k`.
Source: DReST App. D (proof of the neutrality clause, l. 398)
Kind: D
Fidelity: exact -/
def MaxNeutral (p : Fin k → ℝ) : Prop := ∀ l, p l = 1 / k

/-- The uniform distribution is in the simplex.
Source: none: infrastructure
Kind: L -/
theorem uniform_mem (hk : 0 < k) : uniform k ∈ stdSimplex ℝ (Fin k) := by
  refine ⟨fun _ => by unfold uniform; positivity, ?_⟩
  simp [uniform, Finset.sum_const]
  field_simp

/-- **Entropy is maximised by the uniform distribution** (Jensen on the strictly concave
`negMulLog`).
Source: DReST App. D (the characterisation of maximal neutrality); [[lit-shutdown-prefs-mandate]] Target 12
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem neutrality_le_uniform (hk : 0 < k) (p : Fin k → ℝ) (hp : p ∈ stdSimplex ℝ (Fin k)) :
    neutrality p ≤ neutrality (uniform k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hw0 : ∀ i ∈ (univ : Finset (Fin k)), (0 : ℝ) ≤ 1 / k := fun _ _ => by positivity
  have hw1 : ∑ _i : Fin k, (1 : ℝ) / k = 1 := by
    simp [Finset.sum_const]; field_simp
  have hmem : ∀ i ∈ (univ : Finset (Fin k)), p i ∈ Set.Ici (0 : ℝ) := fun i _ => hp.1 i
  have hJ := Real.concaveOn_negMulLog.le_map_sum hw0 hw1 hmem
  have hsum : ∑ i : Fin k, (1 / (k : ℝ)) • p i = 1 / k := by
    simp only [smul_eq_mul, ← Finset.mul_sum, hp.2, mul_one]
  rw [hsum] at hJ
  simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
  unfold neutrality uniform
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  have : (1 / (k : ℝ)) * ∑ i, Real.negMulLog (p i) ≤ Real.negMulLog (1 / k) := hJ
  calc ∑ i, Real.negMulLog (p i) = k * ((1 / (k : ℝ)) * ∑ i, Real.negMulLog (p i)) := by
        field_simp
    _ ≤ k * Real.negMulLog (1 / k) := by gcongr

/-- **Entropy equals the maximum only at the uniform distribution.**
Source: DReST App. D; [[lit-shutdown-prefs-mandate]] Target 12
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem neutrality_eq_uniform_iff (hk : 0 < k) (p : Fin k → ℝ) (hp : p ∈ stdSimplex ℝ (Fin k)) :
    neutrality p = neutrality (uniform k) ↔ MaxNeutral p := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hw0 : ∀ i ∈ (univ : Finset (Fin k)), (0 : ℝ) < 1 / k := fun _ _ => by positivity
  have hw1 : ∑ _i : Fin k, (1 : ℝ) / k = 1 := by
    simp [Finset.sum_const]; field_simp
  have hmem : ∀ i ∈ (univ : Finset (Fin k)), p i ∈ Set.Ici (0 : ℝ) := fun i _ => hp.1 i
  have hJ := Real.strictConcaveOn_negMulLog.map_sum_eq_iff_of_pos hw0 hw1 hmem
  have hsum : ∑ i : Fin k, (1 / (k : ℝ)) • p i = 1 / k := by
    simp only [smul_eq_mul, ← Finset.mul_sum, hp.2, mul_one]
  rw [hsum] at hJ
  simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
  have hu : neutrality (uniform k) = k * Real.negMulLog (1 / k) := by
    unfold neutrality uniform; simp [Finset.sum_const]
  constructor
  · intro h
    rw [hu] at h
    unfold neutrality at h
    have h' : Real.negMulLog (1 / k) = (1 / (k : ℝ)) * ∑ i, Real.negMulLog (p i) := by
      rw [h]; field_simp
    have hall := hJ.mp h'
    intro l
    -- all coordinates equal, sum to 1
    have hconst : ∀ i, p i = p l := fun i => hall (mem_univ i) (mem_univ l)
    have : ∑ i : Fin k, p i = k * p l := by
      rw [Finset.sum_congr rfl (fun i _ => hconst i)]; simp
    rw [hp.2] at this
    field_simp
    linarith
  · intro h
    unfold neutrality uniform
    exact Finset.sum_congr rfl fun l _ => by rw [h l]

/-! ## The meta-return closed form -/

/-- **Expected DReST return** of an `n`-mini-episode meta-episode for the policy `(p, ρ)`:
`F = ∑_{i<n} mu^i ∑_l p l · ρ l · (1 − (1−lam) p l)^i`, where `i` is the mini-episode index minus
one, `lam` is the DReST base, and `mu = lam^{−1/k}` is the per-round rescaling (kept as a separate
parameter so that all arithmetic is rational; e.g. `lam = 1/4`, `k = 2`, `mu = 2`). The closed
form for the expected return of the enumerated meta-episode under i.i.d. lengths, via
`E[lam^{Bin(m,q)}] = (1 − (1−lam) q)^m`; derived from the enumeration in `DrestDerivation.lean`
(`F_eq_metaReturn`: `F = metaReturn` whenever `∑ p = 1`), so this definition is a computed form
of DReST's Def D.2, not a modelling substitution. (Audit round 1 flagged a docstring that named
that file before it existed; the file now exists.)
Source: DReST Def D.2 (l. 366) with eq. (1) (l. 376) read with `N_{e_i}(l) ~ Bin(i−1, p l)`;
[[lit-shutdown-prefs-mandate]] Target 13
Kind: D
Fidelity: exact (given i.i.d. lengths; `DrestDerivation.F_eq_metaReturn`) -/
noncomputable def F (n : ℕ) (lam mu : ℝ) (p ρ : Fin k → ℝ) : ℝ :=
  ∑ i ∈ range n, mu ^ i * ∑ l, p l * ρ l * (1 - (1 - lam) * p l) ^ i

/-- **Usefulness half, monotonicity**: `F` is strictly increasing in `ρ l` when `p l > 0`
(for `0 < lam < 1`, `mu > 0`, `n ≥ 1`, `p` in the simplex).
Source: DReST App. D proof (l. 380: "strictly increasing in … for all `l` such that
`Pr_π{L = l} > 0`"); [[lit-shutdown-prefs-mandate]] Target 13
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem F_strictMono_rho (n : ℕ) (hn : 0 < n) (lam mu : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1)
    (hmu : 0 < mu) (p : Fin k → ℝ) (hp : p ∈ stdSimplex ℝ (Fin k)) (ρ ρ' : Fin k → ℝ) (l : Fin k)
    (hpl : 0 < p l) (hlt : ρ l < ρ' l) (hother : ∀ m, m ≠ l → ρ m = ρ' m) :
    F n lam mu p ρ < F n lam mu p ρ' := by
  have hpl1 : p l ≤ 1 := by
    have := hp.2
    have h := Finset.single_le_sum (f := p) (fun i _ => hp.1 i) (mem_univ l)
    linarith
  have hbase : 0 < 1 - (1 - lam) * p l := by nlinarith
  unfold F
  -- each mini-episode term differs by mu^i * p l * (ρ' l − ρ l) * base^i > 0
  have hterm : ∀ i, (∑ m, p m * ρ' m * (1 - (1 - lam) * p m) ^ i) -
      (∑ m, p m * ρ m * (1 - (1 - lam) * p m) ^ i) =
      p l * (ρ' l - ρ l) * (1 - (1 - lam) * p l) ^ i := by
    intro i
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single l]
    · ring
    · intro m _ hm; rw [hother m hm]; ring
    · intro h; exact absurd (mem_univ l) h
  have hpos : ∀ i ∈ range n, mu ^ i * ∑ m, p m * ρ m * (1 - (1 - lam) * p m) ^ i ≤
      mu ^ i * ∑ m, p m * ρ' m * (1 - (1 - lam) * p m) ^ i := by
    intro i _
    have := hterm i
    have h1 : 0 < p l * (ρ' l - ρ l) * (1 - (1 - lam) * p l) ^ i := by
      have := sub_pos.mpr hlt; positivity
    nlinarith [pow_pos hmu i]
  have hstrict : mu ^ 0 * ∑ m, p m * ρ m * (1 - (1 - lam) * p m) ^ 0 <
      mu ^ 0 * ∑ m, p m * ρ' m * (1 - (1 - lam) * p m) ^ 0 := by
    have := hterm 0
    have h1 : 0 < p l * (ρ' l - ρ l) * (1 - (1 - lam) * p l) ^ 0 := by
      have := sub_pos.mpr hlt; positivity
    simp only [pow_zero, one_mul]
    simp only [pow_zero] at this h1
    linarith
  exact Finset.sum_lt_sum hpos ⟨0, Finset.mem_range.mpr hn, hstrict⟩

/-- **Usefulness half**: any maximiser of `F` over `ρ ∈ [0,1]^k` (for fixed `p` in the simplex) has
`ρ l = 1` wherever `p l > 0`, hence `usefulness = 1`.
Source: DReST Thm D.1 (5.1), usefulness clause, proof ll. 376–390; corr-refs-053, 2-013;
[[lit-shutdown-prefs-mandate]] Target 13
Kind: P
Fidelity: exact (in the `(p, ρ)` model)
Hyps: (a) all; (c) the `(p, ρ)` model -/
theorem usefulness_eq_one_of_isMaxOn (n : ℕ) (hn : 0 < n) (lam mu : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (hmu : 0 < mu) (p : Fin k → ℝ) (hp : p ∈ stdSimplex ℝ (Fin k)) (ρ : Fin k → ℝ)
    (hρ : ∀ l, ρ l ∈ Set.Icc (0 : ℝ) 1)
    (hmax : ∀ ρ', (∀ l, ρ' l ∈ Set.Icc (0 : ℝ) 1) → F n lam mu p ρ' ≤ F n lam mu p ρ) :
    (∀ l, 0 < p l → ρ l = 1) ∧ usefulness p ρ = 1 := by
  classical
  have hone : ∀ l, 0 < p l → ρ l = 1 := by
    intro l hpl
    by_contra hne
    have hlt : ρ l < 1 := lt_of_le_of_ne (hρ l).2 hne
    let ρ' : Fin k → ℝ := Function.update ρ l 1
    have h1 : ∀ m, ρ' m ∈ Set.Icc (0 : ℝ) 1 := by
      intro m
      by_cases hm : m = l
      · subst hm; simp [ρ']
      · simp [ρ', hm, hρ m]
    have h2 := F_strictMono_rho n hn lam mu hlam0 hlam1 hmu p hp ρ ρ' l hpl
      (by simp [ρ', hlt]) (fun m hm => by simp [ρ', hm])
    exact absurd (hmax ρ' h1) (not_le.mpr h2)
  refine ⟨hone, ?_⟩
  unfold usefulness
  rw [← hp.2]
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases lt_or_eq_of_le (hp.1 l) with h | h
  · rw [hone l h, mul_one]
  · rw [← h, zero_mul]

/-! ## Neutrality half: refuted -/

/-- **Lemma D.2 is false as stated**: at `lam = 1/4`, `k = 2`, `mu = 2 = lam^{−1/2}`, `ρ ≡ 1`
(both policies maximally useful), the policy `(1/4, 3/4)` has strictly greater expected return
than the equalised policy `(1/2, 1/2)` over `n = 8` mini-episodes:
`F(1/4,3/4) − F(1/2,1/2) = 13191189/4194304`. Lemma D.2's antecedents hold with
`x = 2, y = 1` (probabilities `3/4 > 1/4`, equalised to `1/2, 1/2`, no other lengths), and its
conclusion `E_{π'} > E_π` fails.
Source: DReST Lemma D.2 (l. 386) "Equalizing probabilities increases expected return"; corr-refs-2-014, 2-015;
[[lit-shutdown-prefs-mandate]] Target 13 (mandate-writer numbers, verified by exact arithmetic)
Kind: N+
Fidelity: exact (of the lemma, in the `(p, ρ)` model with the closed form `F`)
Hyps: (a) all -/
theorem lemma_D2_false :
    F 8 (1/4) 2 ![1/2, 1/2] (fun _ : Fin 2 => 1) < F 8 (1/4) 2 ![1/4, 3/4] (fun _ : Fin 2 => 1) := by
  simp only [F, Finset.sum_range_succ, Finset.sum_range_zero, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- The same at `n = 7` (`F` differs by `36351/262144`), confirming the mandate's second number.
Source: [[lit-shutdown-prefs-mandate]] Target 13
Kind: N+
Fidelity: exact -/
theorem lemma_D2_false_seven :
    F 7 (1/4) 2 ![1/2, 1/2] (fun _ : Fin 2 => 1) < F 7 (1/4) 2 ![1/4, 3/4] (fun _ : Fin 2 => 1) := by
  simp only [F, Finset.sum_range_succ, Finset.sum_range_zero, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  norm_num

/-- `![1/4, 3/4]` is in the simplex.
Source: none: infrastructure
Kind: L -/
theorem quarter_mem : (![1/4, 3/4] : Fin 2 → ℝ) ∈ stdSimplex ℝ (Fin 2) := by
  refine ⟨fun i => by fin_cases i <;> norm_num, ?_⟩
  simp [Fin.sum_univ_two]; norm_num

/-- `F 8 (1/4) 2 · ρ` is continuous in the length distribution.
Source: none: infrastructure
Kind: L -/
theorem F_continuous (n : ℕ) (lam mu : ℝ) (ρ : Fin k → ℝ) :
    Continuous (fun p : Fin k → ℝ => F n lam mu p ρ) := by
  unfold F
  fun_prop

/-- **Theorem 5.1's neutrality clause is false in the model**: the expected return `F 8 (1/4) 2 · 1`
attains its maximum on the compact simplex, and no maximiser is maximally neutral (the uniform
policy is beaten by `(1/4, 3/4)`). Quoting the theorem (l. 356): "For all policies π and
meta-episodes E consisting of more than one mini-episode, if π maximizes expected return in E
according to our DReST reward function, then π is maximally useful and maximally neutral."
Reading: the neutrality conjunct, for the meta-episode of `n = 8` mini-episodes, `lam = 1/4`,
two lengths, in the `(p, ρ)` model with returns computed by the closed form `F`. The usefulness
conjunct stands (`usefulness_eq_one_of_isMaxOn`). Surviving neighbour: the repaired reward of
Target 27 (`repaired_return_le_uniform`), for which uniform is optimal for every `n`.
Source: DReST Thm 5.1 (l. 106) / Thm D.1 (l. 356), neutrality clause; corr-refs-053, 2-014, 2-015;
[[lit-shutdown-prefs-mandate]] Target 13
Kind: N+
Fidelity: exact (of the theorem's neutrality clause, in the model)
Hyps: (a) all; (c) the `(p, ρ)` model and the closed form `F` for the expected return -/
theorem theorem_5_1_neutrality_false :
    (∃ p ∈ stdSimplex ℝ (Fin 2),
        IsMaxOn (fun q : Fin 2 → ℝ => F 8 (1/4) 2 q (fun _ => 1)) (stdSimplex ℝ (Fin 2)) p) ∧
      ∀ p ∈ stdSimplex ℝ (Fin 2),
        IsMaxOn (fun q : Fin 2 → ℝ => F 8 (1/4) 2 q (fun _ => 1)) (stdSimplex ℝ (Fin 2)) p →
          ¬ MaxNeutral p := by
  constructor
  · exact (isCompact_stdSimplex ℝ (Fin 2)).exists_isMaxOn ⟨_, uniform_mem (by norm_num)⟩
      (F_continuous 8 (1/4) 2 _).continuousOn
  · intro p hp hmax hneu
    have hpu : p = ![1/2, 1/2] := by
      funext i
      rw [hneu i]
      fin_cases i <;> norm_num
    have h1 := hmax quarter_mem
    rw [hpu] at h1
    exact absurd (lt_of_lt_of_le lemma_D2_false h1) (lt_irrefl _)

/-- `F` depends on `ρ l` only where `p l > 0`: if `ρ l = 1` on the support of `p`, `F p ρ = F p 1`.
Source: none: infrastructure
Kind: L -/
theorem F_eq_of_rho_one (n : ℕ) (lam mu : ℝ) (p ρ : Fin k → ℝ) (hp : ∀ l, 0 ≤ p l)
    (h : ∀ l, 0 < p l → ρ l = 1) : F n lam mu p ρ = F n lam mu p (fun _ => 1) := by
  unfold F
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases (hp l).lt_or_eq with hl | hl
  · rw [h l hl]
  · rw [← hl]; ring

/-- **No joint maximiser is uniform**: if `(p, ρ)` maximises `F 8 (1/4) 2` over the simplex ×
`[0,1]^2` (the theorem's own quantifier over policies), then `p` is not uniform. A joint
maximiser has `ρ = 1` on the support of `p`, so `F p ρ = F p 1` and `p` maximises the `ρ ≡ 1`
slice, where `theorem_5_1_neutrality_false` applies.
Source: DReST Thm 5.1 / Thm D.1 neutrality clause (the quantifier over `(p, ρ)`); audit round 1,
fidelity non-blocking 7
Kind: C
Fidelity: exact (of the theorem's neutrality clause, in the model)
Hyps: (a) all; (c) the `(p, ρ)` model and the closed form `F` for the expected return -/
theorem theorem_5_1_neutrality_false_joint (p : Fin 2 → ℝ) (hp : p ∈ stdSimplex ℝ (Fin 2))
    (ρ : Fin 2 → ℝ) (hρ : ∀ l, ρ l ∈ Set.Icc (0 : ℝ) 1)
    (hmax : ∀ q ∈ stdSimplex ℝ (Fin 2), ∀ ρ', (∀ l, ρ' l ∈ Set.Icc (0 : ℝ) 1) →
      F 8 (1/4) 2 q ρ' ≤ F 8 (1/4) 2 p ρ) : ¬ MaxNeutral p := by
  have hone := (usefulness_eq_one_of_isMaxOn 8 (by norm_num) (1/4) 2 (by norm_num) (by norm_num)
    (by norm_num) p hp ρ hρ (fun ρ' h => hmax p hp ρ' h)).1
  have hF : F 8 (1/4) 2 p ρ = F 8 (1/4) 2 p (fun _ => 1) := F_eq_of_rho_one 8 _ _ p ρ hp.1 hone
  refine theorem_5_1_neutrality_false.2 p hp ?_
  rw [isMaxOn_iff]
  intro q hq
  rw [← hF]
  exact hmax q hq (fun _ => 1) (fun _ => by norm_num)

/-! ## The repair (Target 27): drop the per-round rescaling -/

/-- The repaired return (reward `lam^{N_i(l)}`, no `lam^{−(i−1)/k}`), with `ρ ≡ 1`:
`G n lam p = ∑_l p l ∑_{i<n} (1 − (1−lam) p l)^i`.
Source: [[lit-shutdown-prefs-mandate]] Target 27 (2-015's flag (c))
Kind: D
Fidelity: exact (the `mu = 1` case of `F` with `ρ ≡ 1`) -/
noncomputable def G (n : ℕ) (lam : ℝ) (p : Fin k → ℝ) : ℝ :=
  ∑ l, p l * ∑ i ∈ range n, (1 - (1 - lam) * p l) ^ i

/-- `φ x = x ∑_{i<n} (1 − (1−lam) x)^i`, the per-length contribution.
Source: [[lit-shutdown-prefs-mandate]] Target 27
Kind: D -/
noncomputable def φ (n : ℕ) (lam : ℝ) (x : ℝ) : ℝ := x * ∑ i ∈ range n, (1 - (1 - lam) * x) ^ i

/-- `G = ∑_l φ (p l)`.
Source: none: infrastructure
Kind: L -/
theorem G_eq_sum_φ (n : ℕ) (lam : ℝ) (p : Fin k → ℝ) : G n lam p = ∑ l, φ n lam (p l) := rfl

/-- `φ x = (1 − (1 − (1−lam) x)^n) / (1 − lam)` for `lam < 1` (geometric sum).
Source: [[lit-shutdown-prefs-mandate]] Target 27
Kind: L -/
theorem φ_eq (n : ℕ) (lam : ℝ) (hlam : lam < 1) (x : ℝ) :
    φ n lam x = (1 - (1 - (1 - lam) * x) ^ n) / (1 - lam) := by
  unfold φ
  have h1 : (1 : ℝ) - lam ≠ 0 := by linarith
  rw [eq_div_iff h1]
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    linear_combination ih

/-- `x ↦ (1 − c x)^n` is convex on `[0, 1]` for `0 ≤ c ≤ 1`.
Source: none: infrastructure
Kind: L -/
theorem convexOn_pow_affine (n : ℕ) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun x => (1 - c * x) ^ n) := by
  refine ⟨convex_Icc 0 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hx' : (0 : ℝ) ≤ 1 - c * x := by nlinarith [hx.1, hx.2]
  have hy' : (0 : ℝ) ≤ 1 - c * y := by nlinarith [hy.1, hy.2]
  have := (convexOn_pow n).2 (Set.mem_Ici.mpr hx') (Set.mem_Ici.mpr hy') ha hb hab
  simp only [smul_eq_mul] at this ⊢
  have e : 1 - c * (a * x + b * y) = a * (1 - c * x) + b * (1 - c * y) := by
    linear_combination (-1 : ℝ) * hab
  rw [e]
  exact this

/-- `φ` is concave on `[0, 1]` for `0 < lam < 1`.
Source: [[lit-shutdown-prefs-mandate]] Target 27 ("concave on `[0,1]`")
Kind: L -/
theorem φ_concaveOn (n : ℕ) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < 1) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (φ n lam) := by
  have hcx := convexOn_pow_affine n (1 - lam) (by linarith) (by linarith)
  have h1 : (0 : ℝ) < 1 - lam := by linarith
  have : φ n lam = fun x => (1 / (1 - lam)) • (1 : ℝ) + (-(1 / (1 - lam))) • (1 - (1 - lam) * x) ^ n := by
    funext x
    rw [φ_eq n lam hlam1 x]
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [this]
  refine ConcaveOn.add (concaveOn_const _ (convex_Icc 0 1)) ?_
  have := hcx.smul (by positivity : (0 : ℝ) ≤ 1 / (1 - lam))
  have hneg : (fun x => (-(1 / (1 - lam))) • (1 - (1 - lam) * x) ^ n) =
      fun x => -((1 / (1 - lam)) • (1 - (1 - lam) * x) ^ n) := by
    funext x; simp
  rw [hneg]
  exact this.neg

/-- **The repaired reward makes uniform optimal for every `n`**: `G n lam p ≤ G n lam (uniform k)`
on the simplex (Jensen on the concave `φ`).
Source: [[lit-shutdown-prefs-mandate]] Target 27 (the surviving neighbour of Theorem 5.1's neutrality clause)
Kind: P
Fidelity: exact (in the model)
Hyps: (a) all; (c) the `(p, ρ)` model -/
theorem repaired_return_le_uniform (hk : 0 < k) (n : ℕ) (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (p : Fin k → ℝ) (hp : p ∈ stdSimplex ℝ (Fin k)) :
    G n lam p ≤ G n lam (uniform k) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hw0 : ∀ i ∈ (univ : Finset (Fin k)), (0 : ℝ) ≤ 1 / k := fun _ _ => by positivity
  have hw1 : ∑ _i : Fin k, (1 : ℝ) / k = 1 := by
    simp [Finset.sum_const]; field_simp
  have hmem : ∀ i ∈ (univ : Finset (Fin k)), p i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i _
    refine ⟨hp.1 i, ?_⟩
    have := Finset.single_le_sum (f := p) (fun j _ => hp.1 j) (mem_univ i)
    linarith [hp.2]
  have hJ := (φ_concaveOn n lam hlam0 hlam1).le_map_sum hw0 hw1 hmem
  have hsum : ∑ i : Fin k, (1 / (k : ℝ)) • p i = 1 / k := by
    simp only [smul_eq_mul, ← Finset.mul_sum, hp.2, mul_one]
  rw [hsum] at hJ
  simp only [smul_eq_mul, ← Finset.mul_sum] at hJ
  rw [G_eq_sum_φ, G_eq_sum_φ]
  unfold uniform
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
  calc ∑ i, φ n lam (p i) = k * ((1 / (k : ℝ)) * ∑ i, φ n lam (p i)) := by field_simp
    _ ≤ k * φ n lam (1 / k) := by gcongr

end Drest

end Cleanroom.Lit.LitShutdownPrefs
