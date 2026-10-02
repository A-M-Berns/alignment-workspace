import Cleanroom.Corrigibility.LegitNegPricing.Scoring

/-!
# Cross-branch reflection: C7 (located assessors, same law iff) and C6 (sealed caution)

Package `legit-neg-pricing`, targets 21 and 26 (`stretch`). Sources: `clusters/C/NEGATIVES.md`
C7, C6, `clusters/C/VERIFY.md` "C7: survives, with the fixture narrowed" (V3), "C6: survives",
`clusters/C/fixtures/verify_C.py` V3, `c06_sealed_caution.py`, pinned by
[[corr-legit-neg-inventory]] items 040, 039 and [[corr-legit-neg-2-inventory]] item 2-016.

C7's abstract form needs no probability hypotheses (`reflection_iff` is an identity about two
weight vectors); the bridge to the `Problem` of record is stated for a sealed legitimacy event
`ℓ` and an information map `info : S → I`, with the located reports as a free vector `k` and the
true conditional `trueK` as the `Hcond` it should equal. Positivity is where it matters: every
`k` is the true report of *some* standard (`trueK_of_realise`), which is what turns "for all
`k`" into "for all payoffs". The original C7 fixture's flip depends on an imaged report at a
zero-mass cell (V3) and is recorded in the findings, not formalised; the witness is V3's
positivity instance. Exclusion convention for P2/P5.
-/

namespace Cleanroom.Corrigibility.LegitNegPricing

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

/-! ### C7, abstract -/

/-- **C7 (abstract)**: two weight vectors on a finite information set give the same aggregate
for every report `k` iff they are equal — indicator payoffs separate them. No positivity or
normalisation is needed.
Source: [[corr-legit-neg-inventory]] item 040 (C7, the proposition)
Kind: P
Fidelity: exact (stronger: no hypotheses on the weights)
Hyps: (a) none -/
theorem reflection_iff {I : Type} [Fintype I] [DecidableEq I] (pL pN : I → ℚ) :
    (∀ k : I → ℚ, ∑ i, pL i * k i = ∑ i, pN i * k i) ↔ pL = pN := by
  constructor
  · intro h
    funext j
    have := h fun i => if j = i then 1 else 0
    simpa [Finset.sum_ite_eq] using this
  · rintro rfl k; rfl

/-- **Likelihood-ratio reweighting is exact under positivity**: if every cell carrying `¬L` mass
also carries `L` mass (`pN i ≠ 0 → pL i ≠ 0`), reweighting each located report by `pN i / pL i`
recovers the `¬L` law's aggregate; the hypothesis is exactly positivity.
Source: [[corr-legit-neg-inventory]] item 040 (C7, escape (2)); VERIFY C V3
Kind: P
Fidelity: exact
Hyps: (a) positivity -/
theorem reweighting_exact {I : Type} [Fintype I] (pL pN : I → ℚ) (hpos : ∀ i, pN i ≠ 0 → pL i ≠ 0)
    (k : I → ℚ) : ∑ i, pL i * (pN i / pL i) * k i = ∑ i, pN i * k i := by
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : pN i = 0
  · simp [h]
  · rw [mul_div_cancel₀ _ (hpos i h)]

/-- `ind_and`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ind_and (a b : Bool) : ind (a && b) = ind a * ind b := by
  cases a <;> cases b <;> simp [ind]

/-! ### C7, the bridge to the `Problem` of record -/

section Bridge

variable {S A I : Type} [Fintype S] [Fintype A] [Fintype I] [DecidableEq I]
  (P : Problem S A) (ℓ : S → Bool) (info : S → I)

/-- `π(L ∧ info = i)`.
Source: [[corr-legit-neg-inventory]] item 040 (C7)
Kind: D
Fidelity: exact -/
def massLI (i : I) : ℚ := P.mass fun s => ℓ s && decide (info s = i)

/-- `π(¬L ∧ info = i)`.
Source: [[corr-legit-neg-inventory]] item 040 (C7)
Kind: D
Fidelity: exact -/
def massNI (i : I) : ℚ := P.mass fun s => !ℓ s && decide (info s = i)

/-- `P(info = i | L)` (junk at `π(L) = 0`).
Source: [[corr-legit-neg-inventory]] item 040 (C7)
Kind: D
Fidelity: exact -/
def condL (i : I) : ℚ := massLI P ℓ info i / P.mass ℓ

/-- `P(info = i | ¬L)` (junk at `π(¬L) = 0`).
Source: [[corr-legit-neg-inventory]] item 040 (C7)
Kind: D
Fidelity: exact -/
def condN (i : I) : ℚ := massNI P ℓ info i / P.mass fun s => !ℓ s

/-- The located cross-branch report: the humans at a terminal in state `s` report `k (info s)`
for every option (the same number, by construction of the fixture).
Source: [[corr-legit-neg-inventory]] item 040 (C7)
Kind: D
Fidelity: exact -/
def locatedK (k : I → ℚ) : MenuVec S A := fun s _ _ => k (info s)

/-- The true located report for option `a`: `𝔼[u_a | ¬L, info = i]` (junk at a zero-mass cell —
positivity is where it is a real conditional).
Source: [[corr-legit-neg-inventory]] item 040 (C7)
Kind: D
Fidelity: exact -/
def trueK (a : A) (i : I) : ℚ := P.Hcond (fun s => !ℓ s && decide (info s = i)) a

/-- Grouping a sum over states by the information cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_by_info (f : S → ℚ) (k : I → ℚ) :
    ∑ s, f s * k (info s) = ∑ i, (∑ s, f s * ind (decide (info s = i))) * k i := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [ind_decide, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- **C7, the `L` side**: under `SealedBy ℓ`, `K̄ a` of a located report is `∑_i P(i | L) k i`.
Source: [[corr-legit-neg-inventory]] item 040 (C7, first display)
Kind: L
Fidelity: exact -/
theorem Kbar_located (hS : P.SealedBy ℓ) (k : I → ℚ) (a : A) :
    P.Kbar (locatedK info k) a = ∑ i, condL P ℓ info i * k i := by
  unfold Problem.Kbar locatedK
  rw [P.PL_eq_mass_of_SealedBy hS]
  have e : ∀ s, P.prior s * ind (P.leg s a) * k (info s) = (P.prior s * ind (ℓ s)) * k (info s) :=
    fun s => by rw [hS s a]
  simp only [e]
  rw [sum_by_info info (fun s => P.prior s * ind (ℓ s)) k]
  unfold condL massLI Problem.mass
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_mul_eq_mul_div]
  have : (∑ s, P.prior s * ind (ℓ s) * ind (decide (info s = i)))
      = ∑ s, P.prior s * ind (ℓ s && decide (info s = i)) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ind_and]; ring
  rw [this]

/-- **C7, the `¬L` side**: the `¬L` part of `H a` is `∑_i π(¬L ∧ i) · trueK a i` — no positivity
needed (a zero-mass cell contributes `0 · junk = 0`).
Source: [[corr-legit-neg-inventory]] item 040 (C7, second display)
Kind: L
Fidelity: exact -/
theorem Hpart_located (a : A) :
    ∑ s, P.prior s * ind (!ℓ s) * P.u s a = ∑ i, massNI P ℓ info i * trueK P ℓ info a i := by
  have key : ∀ i, massNI P ℓ info i * trueK P ℓ info a i
      = ∑ s, P.prior s * ind (!ℓ s && decide (info s = i)) * P.u s a := by
    intro i
    unfold massNI trueK Problem.Hcond
    by_cases h : P.mass (fun s => !ℓ s && decide (info s = i)) = 0
    · rw [h, zero_mul]
      symm
      refine Finset.sum_eq_zero fun s _ => ?_
      by_cases hs : (!ℓ s && decide (info s = i)) = true
      · rw [P.prior_eq_zero_of_mass_eq_zero h s hs]; ring
      · simp only [Bool.not_eq_true] at hs; simp [hs]
    · rw [mul_div_cancel₀ _ h]
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have e : ∀ i, P.prior s * ind (!ℓ s && decide (info s = i)) * P.u s a
      = (P.prior s * ind (!ℓ s) * P.u s a) * ind (decide (info s = i)) := by
    intro i; rw [ind_and]; ring
  simp only [e]
  rw [← Finset.mul_sum]
  simp only [ind_decide]
  rw [Finset.sum_ite_eq]
  simp

/-- `sum_sub_mul_eq`: supporting lemma (no headline).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_sub_mul_eq (k : I → ℚ) :
    ∑ i, (condL P ℓ info i - condN P ℓ info i) * k i
      = ∑ i, condL P ℓ info i * k i - ∑ i, condN P ℓ info i * k i := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **C7, the reflection gap**: under `SealedBy ℓ`, on the defined value of
`P5 (locatedK k) (S1 u) a`, `P5 − (L-part + π(¬L) ∑_i P(i | ¬L) k i) = π(¬L) ∑_i (P(i | L) − P(i | ¬L)) k i`.
Source: [[corr-legit-neg-inventory]] item 040 (C7)
Kind: L
Fidelity: exact -/
theorem reflection_gap (hS : P.SealedBy ℓ) (k : I → ℚ) (a : A) :
    (P.P1 (S1 P.u) a + (1 - P.PL a) * P.Kbar (locatedK info k) a)
        - (P.P1 (S1 P.u) a + P.mass (fun s => !ℓ s) * ∑ i, condN P ℓ info i * k i)
      = P.mass (fun s => !ℓ s) * ∑ i, (condL P ℓ info i - condN P ℓ info i) * k i := by
  rw [Kbar_located P ℓ info hS k a, P.PL_eq_mass_of_SealedBy hS, ← P.mass_not,
    sum_sub_mul_eq P ℓ info k]
  ring

/-- **C7 (headline)**: under sealing with `0 < π(¬L)`, the located P5 value equals the
`¬L`-law aggregate `L-part + π(¬L) ∑_i P(i | ¬L) k i` for **every** report vector `k` iff the
information has the same law under `L` and `¬L` (`P(· | L) = P(· | ¬L)` on `I`).
Source: [[corr-legit-neg-inventory]] item 040 (C7); NEGATIVES C7 proof ("`k = 1_{I₀}` separates")
Kind: P
Fidelity: exact
Hyps: (a) sealing, `0 < π(¬L)` -/
theorem P5_located_eq_forall_iff (hS : P.SealedBy ℓ) (a : A) (hN : P.mass (fun s => !ℓ s) ≠ 0) :
    (∀ k : I → ℚ, P.P1 (S1 P.u) a + (1 - P.PL a) * P.Kbar (locatedK info k) a
        = P.P1 (S1 P.u) a + P.mass (fun s => !ℓ s) * ∑ i, condN P ℓ info i * k i)
      ↔ condL P ℓ info = condN P ℓ info := by
  rw [← reflection_iff]
  constructor
  · intro h k
    have hg := reflection_gap P ℓ info hS k a
    rw [sub_eq_zero.2 (h k), sum_sub_mul_eq] at hg
    have h2 := (mul_eq_zero.1 hg.symm).resolve_left hN
    exact sub_eq_zero.1 h2
  · intro h k
    have hg := reflection_gap P ℓ info hS k a
    rw [sum_sub_mul_eq, h k, sub_self, mul_zero] at hg
    exact sub_eq_zero.1 hg

/-- **`H` is the `¬L`-law aggregate of the true reports**: under sealing with `0 < π(¬L)`,
`H a = P1 (S1 u) a + π(¬L) ∑_i P(i | ¬L) trueK a i`. Hence, with `P5_located_eq_forall_iff`,
the located P5 of the *true* reports is `H` for every standard iff the laws agree — provided
every `k` is realised as some standard's true reports (`trueK_of_realise`).
Source: [[corr-legit-neg-inventory]] item 040 (C7)
Kind: C
Fidelity: exact
Hyps: (a) sealing, `0 < π(¬L)` -/
theorem H_eq_located_true (hS : P.SealedBy ℓ) (a : A) (hN : P.mass (fun s => !ℓ s) ≠ 0) :
    P.H a = P.P1 (S1 P.u) a + P.mass (fun s => !ℓ s) * ∑ i, condN P ℓ info i * trueK P ℓ info a i := by
  have hsplit : P.H a = (∑ s, P.prior s * ind (ℓ s) * P.u s a)
      + ∑ s, P.prior s * ind (!ℓ s) * P.u s a := P.W_split P.u ℓ a
  have hL : P.P1 (S1 P.u) a = ∑ s, P.prior s * ind (ℓ s) * P.u s a := by
    unfold Problem.P1
    exact Finset.sum_congr rfl fun s _ => by rw [hS s a, S1_apply]
  rw [hsplit, hL, Hpart_located P ℓ info a, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  unfold condN
  field_simp

/-- **Positivity realises every report**: if every cell carries `¬L` mass, then for every `k`
the standard `u'` that equals `k (info s)` on the `¬L` states has `trueK = k` — so "for every
`k`" in `P5_located_eq_forall_iff` is "for every standard" under positivity.
Source: [[corr-legit-neg-inventory]] item 040 (C7, "for all payoffs"); VERIFY C V3
Kind: L
Fidelity: exact
Hyps: (a) positivity on every cell -/
theorem trueK_of_realise (a : A) (hpos : ∀ i, massNI P ℓ info i ≠ 0) (k : I → ℚ) :
    let P' : Problem S A :=
      { prior := P.prior, prior_nonneg := P.prior_nonneg, prior_sum := P.prior_sum, leg := P.leg
        u := fun s b => if ℓ s then P.u s b else k (info s) }
    trueK P' ℓ info a = k := by
  intro P'
  funext i
  unfold trueK Problem.Hcond
  have hm : P'.mass (fun s => !ℓ s && decide (info s = i)) = massNI P ℓ info i := rfl
  rw [hm]
  rw [div_eq_iff (hpos i)]
  unfold massNI Problem.mass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [P']
  cases ℓ s <;> by_cases hi : info s = i <;> simp [ind, hi] <;> ring

end Bridge

/-! ### V3: the positivity instance -/

/-- V3's problem: states `m₁L, m₁N, m₂L, m₂N` (`3/8, 1/8, 1/8, 3/8`), sealed (`L` on the even
states), `safe` worth `1/2` everywhere, `risky` worth `1/2` on `L`, `1` at `m₁N`, `0` at `m₂N`.
Source: [[corr-legit-neg-2-inventory]] item 2-016 (V3); `verify_C.py:59-75`
Kind: D
Fidelity: exact -/
def v3 : Problem (Fin 4) (Fin 2) where
  prior := ![3/8, 1/8, 1/8, 3/8]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> norm_num
  prior_sum := by simp [Fin.sum_univ_four]; norm_num
  leg := fun s _ => decide (s.val % 2 = 0)
  u := fun s a => ![![1/2, 1/2], ![1/2, 1], ![1/2, 1/2], ![1/2, 0]] s a

/-- V3's exact located reports: the assessors at `m_iL` report the true `¬L` outcome at `m_iN`.
Source: [[corr-legit-neg-2-inventory]] item 2-016 (V3, `exactK`)
Kind: D
Fidelity: exact -/
def v3K : MenuVec (Fin 4) (Fin 2) := fun s _ c => ![![1/2, 1], ![1/2, 1], ![1/2, 0], ![1/2, 0]] s c

/-- **V3 (N+ for C7's iff)**: every assessor exactly right, positivity everywhere
(`P(L | m₁) = 3/4`, `P(L | m₂) = 1/4`), and P5 still takes `risky` (`5/8 > 1/2`) while `H`
prefers `safe` (`3/8 < 1/2`): regret `1/8`; accurate P3 picks `safe`; likelihood-ratio
reweighting of the reports is exact here. Exclusion convention.
Source: [[corr-legit-neg-2-inventory]] item 2-016 (V3); VERIFY C "C7"
Kind: N+
Fidelity: exact -/
theorem V3_witness :
    v3.P5 v3K (S1 v3.u) 1 = some (5/8) ∧ v3.P5 v3K (S1 v3.u) 0 = some (1/2)
    ∧ argmaxOpt (v3.P5 v3K (S1 v3.u)) = {1}
    ∧ argmax v3.H = {0} ∧ v3.H 0 - v3.H 1 = 1/8
    ∧ argmax (v3.P3 (S1 v3.u) 1 (S1 v3.u)) = {0}
    ∧ (massLI v3 (fun s => decide (s.val % 2 = 0)) (fun s => decide (s.val < 2)) true = 3/8
        ∧ massNI v3 (fun s => decide (s.val % 2 = 0)) (fun s => decide (s.val < 2)) true = 1/8
        ∧ massLI v3 (fun s => decide (s.val % 2 = 0)) (fun s => decide (s.val < 2)) false = 1/8
        ∧ massNI v3 (fun s => decide (s.val % 2 = 0)) (fun s => decide (s.val < 2)) false = 3/8)
    ∧ (3/4 : ℚ) * ((1/4) / (3/4)) * 1 + (1/4) * ((3/4) / (1/4)) * 0 = (1/4) * 1 + (3/4) * 0 := by
  have hPL : ∀ a, v3.PL a = 1/2 := by
    intro a; simp [v3, Problem.PL, Problem.mass, Fin.sum_univ_four]; norm_num
  have hP1 : ∀ a, v3.P1 (S1 v3.u) a = ![1/4, 1/4] a := by
    intro a; fin_cases a <;> simp [v3, Problem.P1, Fin.sum_univ_four] <;> norm_num
  have hK : ∀ a, v3.Kbar v3K a = ![1/2, 3/4] a := by
    intro a; fin_cases a <;> simp [v3, v3K, Problem.Kbar, Problem.PL, Problem.mass, Fin.sum_univ_four] <;> norm_num
  have hP5 : ∀ a, v3.P5 v3K (S1 v3.u) a = some (![1/2, 5/8] a) := by
    intro a
    rw [P5_of_ne _ _ _ _ (by rw [hPL]; norm_num), hP1, hK, hPL]
    fin_cases a <;> simp <;> norm_num
  have hH : ∀ a, v3.H a = ![1/2, 3/8] a := by
    intro a; fin_cases a <;> simp [v3, Problem.H, Problem.W, EU, Fin.sum_univ_four] <;> norm_num
  refine ⟨by rw [hP5]; rfl, by rw [hP5]; rfl, ?_, ?_, ?_, ?_, ?_, by norm_num⟩
  · rw [argmaxOpt_eq_argmax_of_forall_some hP5, argmax_fin2_eq_one_iff]; norm_num
  · rw [argmax_fin2_eq_zero_iff, hH, hH]; norm_num
  · rw [hH, hH]; norm_num
  · rw [argmax_fin2_eq_zero_iff]
    simp [v3, Problem.P3, Fin.sum_univ_four]; norm_num
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [massLI, massNI, v3, Problem.mass, Fin.sum_univ_four] <;> norm_num

/-! ### C6: sealed caution -/

/-- C6's sealed problem: `g` legitimate, `b` void, equiprobable; `care` worth `1/2` on both
branches; `harm` gains `1/10` on `L` (`3/5`) and loses `1/2` on the void branch (`0`).
Source: [[corr-legit-neg-inventory]] item 039 (C6); `c06_sealed_caution.py`
Kind: D
Fidelity: exact -/
def c6 : Problem (Fin 2) (Fin 2) where
  prior := ![1/2, 1/2]
  prior_nonneg := by intro s; fin_cases s <;> simp
  prior_sum := by simp [Fin.sum_univ_two]; norm_num
  leg := fun s _ => decide (s = 0)
  u := fun s a => ![![1/2, 3/5], ![1/2, 0]] s a

/-- C6's accurate cross-branch assessors (`K` = the void-branch truth) and located ones (`K`
extrapolated from `g`).
Source: [[corr-legit-neg-inventory]] item 039 (C6)
Kind: D
Fidelity: exact -/
def c6Kacc : MenuVec (Fin 2) (Fin 2) := fun _ _ c => ![1/2, 0] c

/-- `c6Kloc`: the located assessors' report (see `c6Kacc`).
Source: [[corr-legit-neg-inventory]] item 039 (C6)
Kind: D
Fidelity: exact -/
def c6Kloc : MenuVec (Fin 2) (Fin 2) := fun _ _ c => ![1/2, 3/5] c

/-- **C6**: under S1, `P1` (`1/4` vs `3/10`) and `P2` (`1/2` vs `3/5`) choose `harm`; `P3` with
accurate void grades refuses iff `λ > 1/5` (tie at `1/5`); `P4a` refuses; `P4b(κ, κ')` refuses
iff `κ'/(1 − κ) > 1/5` (`κ < 1`); `P5` refuses with accurate assessors and chooses `harm` with
located ones; under `S2` both `P1` and `P2` refuse. Exclusion convention.
Source: [[corr-legit-neg-inventory]] item 039 (C6); `c06_sealed_caution.py`
Kind: N+
Fidelity: exact (parametric in `λ` and `(κ, κ')`) -/
theorem C6_sealed_caution (lam κ κ' : ℚ) (hκ : κ < 1) :
    argmax (c6.P1 (S1 c6.u)) = {1}
    ∧ argmaxOpt (c6.P2 (S1 c6.u)) = {1}
    ∧ (argmax (c6.P3 (S1 c6.u) lam (S1 c6.u)) = {0} ↔ 1/5 < lam)
    ∧ (argmax (c6.P3 (S1 c6.u) lam (S1 c6.u)) = univ ↔ lam = 1/5)
    ∧ argmaxLex (c6.P4a (S1 c6.u) (S1 c6.u)) = {0}
    ∧ (argmax (c6.P4b (S1 c6.u) κ κ' (S1 c6.u)) = {0} ↔ 1/5 < κ' / (1 - κ))
    ∧ argmaxOpt (c6.P5 c6Kacc (S1 c6.u)) = {0}
    ∧ argmaxOpt (c6.P5 c6Kloc (S1 c6.u)) = {1}
    ∧ argmax (c6.P1 c6.S2) = {0}
    ∧ argmaxOpt (c6.P2 c6.S2) = {0} := by
  have hPL : ∀ a, c6.PL a = 1/2 := by
    intro a; simp [c6, Problem.PL, Problem.mass] <;> norm_num
  have hP1 : ∀ a, c6.P1 (S1 c6.u) a = ![1/4, 3/10] a := by
    intro a; fin_cases a <;> simp [c6, Problem.P1] <;> norm_num
  have hP3 : ∀ a, c6.P3 (S1 c6.u) lam (S1 c6.u) a = ![1/4 + lam / 4, 3/10] a := by
    intro a; fin_cases a <;> simp [c6, Problem.P3, Fin.sum_univ_two] <;> ring
  have hP3one : ∀ a, c6.P3 (S1 c6.u) 1 (S1 c6.u) a = ![1/2, 3/10] a := by
    intro a; fin_cases a <;> simp [c6, Problem.P3, Fin.sum_univ_two] <;> norm_num
  have hP4b : ∀ a, c6.P4b (S1 c6.u) κ κ' (S1 c6.u) a
      = ![(κ + (1 - κ) / 2) / 2 + κ' / 4, (κ + (1 - κ) * 3/5) / 2] a := by
    intro a; fin_cases a <;> simp [c6, Problem.P4b, Fin.sum_univ_two] <;> ring
  have hH : ∀ a, c6.H a = ![1/2, 3/10] a := by
    intro a; fin_cases a <;> simp [c6, Problem.H, Problem.W, EU, Fin.sum_univ_two] <;> norm_num
  have hKacc : ∀ a, c6.Kbar c6Kacc a = ![1/2, 0] a := by
    intro a; fin_cases a <;> simp [c6, c6Kacc, Problem.Kbar, Problem.PL, Problem.mass, Fin.sum_univ_two] <;> norm_num
  have hKloc : ∀ a, c6.Kbar c6Kloc a = ![1/2, 3/5] a := by
    intro a; fin_cases a <;> simp [c6, c6Kloc, Problem.Kbar, Problem.PL, Problem.mass, Fin.sum_univ_two] <;> norm_num
  have hP5acc : ∀ a, c6.P5 c6Kacc (S1 c6.u) a = some (![1/2, 3/10] a) := by
    intro a; rw [P5_of_ne _ _ _ _ (by rw [hPL]; norm_num), hP1, hKacc, hPL]
    fin_cases a <;> simp <;> norm_num
  have hP5loc : ∀ a, c6.P5 c6Kloc (S1 c6.u) a = some (![1/2, 3/5] a) := by
    intro a; rw [P5_of_ne _ _ _ _ (by rw [hPL]; norm_num), hP1, hKloc, hPL]
    fin_cases a <;> simp <;> norm_num
  have hne : ∀ a, c6.PL a ≠ 0 := fun a => by rw [hPL]; norm_num
  have hg : 0 < 1 - κ := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_one_iff, hP1, hP1]; norm_num
  · rw [argmaxOpt_P2_eq_argmax_div _ _ hne, argmax_fin2_eq_one_iff]
    simp only [hP1, hPL]; norm_num
  · rw [argmax_fin2_eq_zero_iff, hP3, hP3]; simp; constructor <;> intro h <;> linarith
  · rw [argmax_fin2_eq_univ_iff, hP3, hP3]; simp; constructor <;> intro h <;> linarith
  · refine finset_fin2_ext ?_ ?_ <;>
      simp only [mem_argmaxLex, mem_singleton, Fin.forall_fin_two, Problem.P4a,
        Prod.Lex.toLex_le_toLex, hPL, hP3one] <;> norm_num
  · rw [argmax_fin2_eq_zero_iff, hP4b, hP4b]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [lt_div_iff₀ hg]
    constructor <;> intro h <;> nlinarith
  · rw [argmaxOpt_eq_argmax_of_forall_some hP5acc, argmax_fin2_eq_zero_iff]; norm_num
  · rw [argmaxOpt_eq_argmax_of_forall_some hP5loc, argmax_fin2_eq_one_iff]; norm_num
  · rw [argmax_fin2_eq_zero_iff, P1_S2_eq, P1_S2_eq, hH, hH, hPL, hPL]; norm_num
  · rw [argmaxOpt_eq_argmax_of_forall_some fun a => P2_S2_eq c6 a (hne a), argmax_fin2_eq_zero_iff,
      hH, hH]; norm_num

end Cleanroom.Corrigibility.LegitNegPricing
