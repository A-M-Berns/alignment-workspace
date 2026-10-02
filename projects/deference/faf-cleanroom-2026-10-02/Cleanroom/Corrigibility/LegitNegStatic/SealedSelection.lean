import Cleanroom.Corrigibility.LegitNegStatic.SealedBlind

/-!
# Cluster A, A3 and A3b: the cross-branch reflection gap and local-linear estimators

Package `legit-neg-static`, targets 12–13. Sources: `clusters/A/NEGATIVES.md` A3, A3b;
`clusters/A/VERIFY.md` "A3: narrowed", "A3b: survives (with a count correction)" (V4);
[[corr-legit-neg-inventory]] items 009, 010; [[corr-legit-neg-2-inventory]] item 2-009.

Framing (VERIFY A3): the failing evaluators answer the `k`-fixed counterfactual or the
posterior-given-`L` question (readings D2′/D4 of `SealedDefense.lean`), not S2 as `RUN.md` §3
defines it; the failure is of the *pairing* of P1/P2's aggregation with such evaluators.
-/

namespace Cleanroom.Corrigibility.LegitNegStatic

open Finset

/-- `ind_and`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma ind_and (a b : Bool) : ind (a && b) = ind a * ind b := by cases a <;> cases b <;> simp [ind]

namespace Problem

variable {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)

/-- `E[h | E] = (∑ π [E] h) / π(E)` over `Finset.sum` (no `MeasureTheory`); junk `… / 0` at
`π(E) = 0`, which every theorem excludes by hypothesis.
Source: [[corr-legit-neg-inventory]] item 009
Kind: D
Fidelity: exact -/
def condExp (E : S → Bool) (h : S → ℚ) : ℚ := (∑ s, P.prior s * ind (E s) * h s) / P.mass E

/-- `Cov(h, 1_E) = E[h · 1_E] − E[h] · π(E)`.
Source: [[corr-legit-neg-inventory]] item 009
Kind: D
Fidelity: exact -/
def cov (E : S → Bool) (h : S → ℚ) : ℚ :=
  (∑ s, P.prior s * ind (E s) * h s) - (∑ s, P.prior s * h s) * P.mass E

/-- `sum_split`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sum_split (E : S → Bool) (h : S → ℚ) :
    ∑ s, P.prior s * h s
      = (∑ s, P.prior s * ind (E s) * h s) + ∑ s, P.prior s * ind (!E s) * h s := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  cases E s <;> simp [ind]

/-- **A3, the identity (load-bearing 3).** For `0 < π(L) < 1` and any `h`,
`E[h | ¬L] − E[h | L] = −Cov(h, 1_L) / (π(L) · π(¬L))`. Hypotheses, not junk: at `π(L) ∈ {0, 1}`
the right-hand side divides by zero.
Source: [[corr-legit-neg-inventory]] item 009 (A3)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem condExp_gap_eq_neg_cov_div (E : S → Bool) (h : S → ℚ) (hL : 0 < P.mass E)
    (hN : 0 < P.mass (fun s => !E s)) :
    P.condExp (fun s => !E s) h - P.condExp E h
      = - P.cov E h / (P.mass E * P.mass (fun s => !E s)) := by
  unfold condExp cov
  rw [P.sum_split E h]
  have hN' : P.mass (fun s => !E s) = 1 - P.mass E := P.mass_not E
  have h1 : (1 - P.mass E) ≠ 0 := by rw [← hN']; exact hN.ne'
  rw [hN']
  field_simp
  ring

end Problem

/-! ### A3 in threshold form over the selection model -/

open Problem

/-- The `N`-state with the same adversary strength as a given state: `(k, L) ↦ (k, N)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def smN : Fin 4 → Fin 4 := ![1, 1, 3, 3]

/-- The harm profile `h = (hW, hS)` read on the selection model's states.
Source: [[corr-legit-neg-2-inventory]] item 2-009
Kind: D
Fidelity: exact -/
def smH (hW hS : ℚ) : Fin 4 → ℚ := fun s => ![hW, hS] (smK s)

/-- The `k`-known issuance-weighted evaluators (reading D2′): on an `L`-state,
`V s a = π(L) · Q s a + (1 − π(L)) · Q (k, N) a`, with `π(L) = (aW + aS)/2`.
Source: [[corr-legit-neg-2-inventory]] item 2-009
Kind: D
Fidelity: exact -/
def smVk (aW aS x hW hS δ : ℚ) : Fin 4 → Fin 2 → ℚ := fun s a =>
  (aW + aS) / 2 * smQ x δ hW hS s a + (1 - (aW + aS) / 2) * smQ x δ hW hS (smN s) a

/-- The Bayesian-posterior evaluators (reading D4): on an `L`-state, the `¬L` term is the
posterior over `k` given `L`: `P(W | L) = aW/(aW + aS)`, `P(S | L) = aS/(aW + aS)`.
Source: [[corr-legit-neg-2-inventory]] item 2-009
Kind: D
Fidelity: exact -/
def smVb (aW aS x hW hS δ : ℚ) : Fin 4 → Fin 2 → ℚ := fun s a =>
  (aW + aS) / 2 * smQ x δ hW hS s a
    + (1 - (aW + aS) / 2) * (aW / (aW + aS) * smQ x δ hW hS 1 a + aS / (aW + aS) * smQ x δ hW hS 3 a)

section Threshold

variable (aW aS x hW hS δ : ℚ) (hW0 : 0 ≤ aW) (hW1 : aW ≤ 1) (hS0 : 0 ≤ aS) (hS1 : aS ≤ 1)

/-- `π(L) = (aW + aS)/2` on the selection model.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sm_mass_L : (selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1).mass smL = (aW + aS) / 2 := by
  simp [selectionModel, selectionModelWith, mass, smL, Fin.sum_univ_four]; ring

/-- `π(¬L) = 1 − (aW + aS)/2`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sm_mass_N :
    (selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1).mass (fun s => !smL s) = 1 - (aW + aS) / 2 := by
  simp [selectionModel, selectionModelWith, mass, smL, Fin.sum_univ_four]; ring

/-- `E[h | L] = (aW hW + aS hS)/(aW + aS)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sm_condExp_L (hpos : 0 < aW + aS) :
    (selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1).condExp smL (smH hW hS)
      = (aW * hW + aS * hS) / (aW + aS) := by
  unfold condExp
  rw [sm_mass_L]
  have hne : aW + aS ≠ 0 := hpos.ne'
  have hne2 : (aW + aS) / 2 ≠ 0 := by intro h; apply hne; linarith
  rw [div_eq_div_iff hne2 hne]
  simp [selectionModel, selectionModelWith, smL, smH, smK, Fin.sum_univ_four]
  ring

/-- `E[h | ¬L] = ((1 − aW) hW + (1 − aS) hS)/(2 − aW − aS)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sm_condExp_N (hpos : 0 < 2 - aW - aS) :
    (selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1).condExp (fun s => !smL s) (smH hW hS)
      = ((1 - aW) * hW + (1 - aS) * hS) / (2 - aW - aS) := by
  unfold condExp
  rw [sm_mass_N]
  have h2 : 2 - aW - aS ≠ 0 := hpos.ne'
  have h1 : 1 - (aW + aS) / 2 ≠ 0 := by intro h; apply h2; linarith
  rw [div_eq_div_iff h1 h2]
  simp [selectionModel, selectionModelWith, smL, smH, smK, Fin.sum_univ_four]
  ring

/-- **A3 threshold form, the agent's side (`k` known).** With `π(L) = (aW + aS)/2 =: p`,
`J₁ risky − J₁ safe = p · (p δ − (1 − p) · E[h | L])`.
Source: [[corr-legit-neg-2-inventory]] item 2-009
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem sm_P1_diff_k (hpos : 0 < aW + aS) :
    let P := selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1
    P.P1 (liftV (smVk aW aS x hW hS δ)) 1 - P.P1 (liftV (smVk aW aS x hW hS δ)) 0
      = (aW + aS) / 2 * ((aW + aS) / 2 * δ - (1 - (aW + aS) / 2) * ((aW * hW + aS * hS) / (aW + aS))) := by
  intro P
  simp [P, selectionModel, selectionModelWith, P1, smVk, smQ, smL, smK, smN, Fin.sum_univ_four]
  field_simp
  ring

/-- **A3 threshold form, the Bayesian evaluators give the same score difference** (hence the same
argmax): `∑_k P(k | L) h(k) = E[h | L]`.
Source: [[corr-legit-neg-2-inventory]] item 2-009
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem sm_P1_diff_b_eq_k (hpos : 0 < aW + aS) :
    let P := selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1
    P.P1 (liftV (smVb aW aS x hW hS δ)) 1 - P.P1 (liftV (smVb aW aS x hW hS δ)) 0
      = P.P1 (liftV (smVk aW aS x hW hS δ)) 1 - P.P1 (liftV (smVk aW aS x hW hS δ)) 0 := by
  intro P
  simp [P, selectionModel, selectionModelWith, P1, smVk, smVb, smQ, smL, smK, smN, Fin.sum_univ_four]
  field_simp
  ring

/-- **A3 threshold form, the standard's side.** `W risky − W safe = p δ − (1 − p) · E[h | ¬L]`.
Source: [[corr-legit-neg-2-inventory]] item 2-009
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem sm_W_diff (hpos : 0 < 2 - aW - aS) :
    let P := selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1
    P.W P.u 1 - P.W P.u 0
      = (aW + aS) / 2 * δ - (1 - (aW + aS) / 2) * (((1 - aW) * hW + (1 - aS) * hS) / (2 - aW - aS)) := by
  intro P
  simp [P, selectionModel, selectionModelWith, W, EU, smQ, smL, smK, Fin.sum_univ_four]
  field_simp
  ring

/-- **A3, the window.** With `p = π(L) ∈ (0, 1)`: the proposals strictly choose `risky` iff
`δ > (1 − p)/p · E[h | L]`, and the standard strictly prefers `safe` iff
`δ < (1 − p)/p · E[h | ¬L]`; the agent errs exactly for `δ` in the window between them, with
`W`-regret `(1 − p) E[h | ¬L] − p δ` there.
Source: [[corr-legit-neg-2-inventory]] item 2-009
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem sm_window (hpos : 0 < aW + aS) (hpos' : 0 < 2 - aW - aS) :
    let P := selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1
    let p := (aW + aS) / 2
    let EhL := (aW * hW + aS * hS) / (aW + aS)
    let EhN := ((1 - aW) * hW + (1 - aS) * hS) / (2 - aW - aS)
    (argmax (P.P1 (liftV (smVk aW aS x hW hS δ))) = {1} ↔ (1 - p) * EhL < p * δ) ∧
    (argmax (P.W P.u) = {0} ↔ p * δ < (1 - p) * EhN) ∧
    P.W P.u 0 - P.W P.u 1 = (1 - p) * EhN - p * δ := by
  intro P p EhL EhN
  have hk := sm_P1_diff_k aW aS x hW hS δ hW0 hW1 hS0 hS1 hpos
  have hw := sm_W_diff aW aS x hW hS δ hW0 hW1 hS0 hS1 hpos'
  simp only at hk hw
  have hp : 0 < p := by simp only [p]; linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_one_iff]
    constructor
    · intro h
      have : 0 < p * (p * δ - (1 - p) * EhL) := by simp only [p, EhL]; linarith
      have := (mul_pos_iff_of_pos_left hp).1 this
      linarith
    · intro h
      have : 0 < p * (p * δ - (1 - p) * EhL) := mul_pos hp (by linarith)
      simp only [p, EhL] at this; linarith
  · rw [argmax_fin2_eq_zero_iff]
    simp only [p, EhN]
    constructor <;> intro h <;> linarith
  · simp only [p, EhN]; linarith

/-- **The window for P2.** Under sealing with `π(L) = (aW + aS)/2 > 0`, P2's choice is P1's (A0),
so `sm_window`'s first clause holds for `argmaxOpt (P2 ·)` verbatim.
Source: [[corr-legit-neg-2-inventory]] item 2-009
Kind: L
Fidelity: exact; exclusion convention -/
theorem sm_window_P2 (hpos : 0 < aW + aS) :
    argmaxOpt ((selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1).P2 (liftV (smVk aW aS x hW hS δ)))
      = argmax ((selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1).P1 (liftV (smVk aW aS x hW hS δ))) :=
  (selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1).argmaxOpt_P2_eq_argmax_P1_of_SealedBy
    (selectionModelWith_SealedBy _ _ _ _ _ _ _) (by rw [sm_mass_L]; linarith) _

end Threshold

/-- The A3 instance: `aW = 9/10`, `aS = 1/10`, `x = 1/2`, `h = (0, 1)`, parametric in `δ`.
Source: NEGATIVES A3 "Fixture A3"
Kind: D
Fidelity: exact -/
def A3P (δ : ℚ) : Problem (Fin 4) (Fin 2) :=
  selectionModel (9/10) (1/10) (1/2) 0 1 δ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **A3, the instance.** `aW = 9/10`, `aS = 1/10`, `h = (0, 1)`: `E[h | L] = 1/10`,
`E[h | ¬L] = 9/10`, the window is `(1/10, 9/10)`, and the regret at `δ = 1/2` is `1/5`.
Source: [[corr-legit-neg-inventory]] item 009 (fixture A3)
Kind: N+
Fidelity: exact -/
theorem A3_instance :
    (A3P (1/2)).condExp smL (smH 0 1) = 1/10 ∧
    (A3P (1/2)).condExp (fun s => !smL s) (smH 0 1) = 9/10 ∧
    (∀ δ : ℚ, argmax ((A3P δ).P1 (liftV (smVk (9/10) (1/10) (1/2) 0 1 δ))) = {1} ↔ 1/10 < δ) ∧
    (∀ δ : ℚ, argmax ((A3P δ).W (A3P δ).u) = {0} ↔ δ < 9/10) ∧
    (A3P (1/2)).W (A3P (1/2)).u 0 - (A3P (1/2)).W (A3P (1/2)).u 1 = 1/5 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold A3P
    rw [sm_condExp_L (9/10) (1/10) (1/2) 0 1 (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · unfold A3P
    rw [sm_condExp_N (9/10) (1/10) (1/2) 0 1 (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
    norm_num
  · intro δ
    unfold A3P
    have := (sm_window (9/10) (1/10) (1/2) 0 1 δ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
    rw [this]; constructor <;> intro h <;> linarith
  · intro δ
    unfold A3P
    have := (sm_window (9/10) (1/10) (1/2) 0 1 δ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2.1
    rw [this]; constructor <;> intro h <;> linarith
  · unfold A3P
    have := (sm_window (9/10) (1/10) (1/2) 0 1 (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2.2
    rw [this]; norm_num

/-- **A3, the unbounded family.** With `aW = 1 − e`, `aS = e`, `h = (0, 1)`: `E[h | L] = e`,
`E[h | ¬L] = 1 − e`, and the ratio `(1 − e)/e` exceeds any `M` for a suitable `e ∈ (0, 1)`.
Source: [[corr-legit-neg-2-inventory]] item 2-009 (family)
Kind: P
Fidelity: exact -/
theorem A3_family_unbounded (M : ℚ) :
    ∃ e : ℚ, 0 < e ∧ e < 1 ∧ ∃ (h0 : 0 ≤ 1 - e) (h1 : 1 - e ≤ 1) (h2 : 0 ≤ e) (h3 : e ≤ 1),
      (selectionModel (1 - e) e (1/2) 0 1 0 h0 h1 h2 h3).condExp smL (smH 0 1) = e ∧
      (selectionModel (1 - e) e (1/2) 0 1 0 h0 h1 h2 h3).condExp (fun s => !smL s) (smH 0 1) = 1 - e ∧
      M < (1 - e) / e := by
  have hm0 : 0 ≤ max M 0 := le_max_right M 0
  have hm : 0 < max M 0 + 2 := by linarith
  have hm' : max M 0 + 2 ≠ 0 := hm.ne'
  set e : ℚ := 1 / (max M 0 + 2) with he
  have hprod : e * (max M 0 + 2) = 1 := by rw [he]; field_simp
  have he0 : 0 < e := by rw [he]; exact div_pos one_pos hm
  have he1 : e < 1 := by nlinarith
  refine ⟨e, he0, he1, by linarith, by linarith, he0.le, he1.le, ?_, ?_, ?_⟩
  · rw [sm_condExp_L _ _ _ _ _ _ _ _ _ _ (by linarith)]; ring
  · rw [sm_condExp_N _ _ _ _ _ _ _ _ _ _ (by linarith)]
    have h1 : (2 : ℚ) - (1 - e) - e = 1 := by ring
    rw [h1]; ring
  · have h1 : (1 - e) / e = max M 0 + 1 := by
      rw [he]; field_simp; ring
    rw [h1]; have := le_max_left M 0; linarith

/-- **A3, support failure** (the instance of A3b (2)): `aS = 0` makes `E[h | L] = 0` for both
`hS ∈ {0, 1}` while `E[h | ¬L]` differs — two harm profiles that agree on all `L`-supported
information and differ on `¬L` mass.
Source: [[corr-legit-neg-2-inventory]] item 2-009 (support failure)
Kind: N+
Fidelity: exact -/
theorem A3_support_failure :
    (∀ hS : ℚ, (selectionModel (9/10) 0 (1/2) 0 hS 0 (by norm_num) (by norm_num) le_rfl (by norm_num)).condExp smL (smH 0 hS) = 0) ∧
    (selectionModel (9/10) 0 (1/2) 0 0 0 (by norm_num) (by norm_num) le_rfl (by norm_num)).condExp (fun s => !smL s) (smH 0 0) = 0 ∧
    (selectionModel (9/10) 0 (1/2) 0 1 0 (by norm_num) (by norm_num) le_rfl (by norm_num)).condExp (fun s => !smL s) (smH 0 1) = 10/11 := by
  refine ⟨fun hS => ?_, ?_, ?_⟩
  · rw [sm_condExp_L (9/10) 0 (1/2) 0 hS 0 (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)]; ring
  · rw [sm_condExp_N (9/10) 0 (1/2) 0 0 0 (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)]; ring
  · rw [sm_condExp_N (9/10) 0 (1/2) 0 1 0 (by norm_num) (by norm_num) le_rfl (by norm_num) (by norm_num)]; norm_num

/-- **A3's identity, N+ witness.** On `A3P (1/2)` (`π(L) = 1/2`, `h = (0, 0, 1, 1)`, non-constant):
`Cov(h, 1_L) = −1/5`, `E[h | ¬L] − E[h | L] = 4/5 = −Cov / (π(L) π(¬L)) = (1/5)/(1/4)`, and the
identity's full hypothesis package is discharged.
Source: [[corr-legit-neg-inventory]] item 009 (A3); audit r1 adversarial N7
Kind: N+
Fidelity: exact -/
theorem condExp_gap_instance :
    (A3P (1/2)).cov smL (smH 0 1) = -1/5 ∧
    (A3P (1/2)).condExp (fun s => !smL s) (smH 0 1) - (A3P (1/2)).condExp smL (smH 0 1) = 4/5 ∧
    - (A3P (1/2)).cov smL (smH 0 1)
        / ((A3P (1/2)).mass smL * (A3P (1/2)).mass (fun s => !smL s)) = 4/5 ∧
    (A3P (1/2)).condExp (fun s => !smL s) (smH 0 1) - (A3P (1/2)).condExp smL (smH 0 1)
      = - (A3P (1/2)).cov smL (smH 0 1)
          / ((A3P (1/2)).mass smL * (A3P (1/2)).mass (fun s => !smL s)) := by
  have hL : (A3P (1/2)).mass smL = 1/2 := by
    rw [show A3P (1/2) = selectionModel (9/10) (1/10) (1/2) 0 1 (1/2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) from rfl, sm_mass_L]; norm_num
  have hN : (A3P (1/2)).mass (fun s => !smL s) = 1/2 := by
    rw [show A3P (1/2) = selectionModel (9/10) (1/10) (1/2) 0 1 (1/2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) from rfl, sm_mass_N]; norm_num
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [A3P, selectionModel, selectionModelWith, cov, mass, smL, smH, smK, Fin.sum_univ_four]
    norm_num
  · have h := A3_instance
    rw [h.2.1, h.1]; norm_num
  · simp [A3P, selectionModel, selectionModelWith, cov, mass, smL, smH, smK, Fin.sum_univ_four]
    norm_num
  · exact (A3P (1/2)).condExp_gap_eq_neg_cov_div smL (smH 0 1) (by rw [hL]; norm_num)
      (by rw [hN]; norm_num)

/-! ### A3b: local-linear `L`-world estimators over evaluator-information atoms -/

section A3b

variable {J : ℕ}

/-- The local-linear `L`-world estimator `Φ_c(g) = ∑_j a_j c_j g_j` over atoms `j : Fin J`, with
`a_j = π(L ∩ G_j)`.
Source: [[corr-legit-neg-inventory]] item 010
Kind: D
Fidelity: exact -/
def Phi (a c g : Fin J → ℚ) : ℚ := ∑ j, a j * c j * g j

/-- The target `E[g · 1_{¬L}] = ∑_j b_j g_j` with `b_j = π(¬L ∩ G_j)`.
Source: [[corr-legit-neg-inventory]] item 010
Kind: D
Fidelity: exact -/
def Eg (b g : Fin J → ℚ) : ℚ := ∑ j, b j * g j

/-- **A3b (1).** `Φ_c` is exact for every `g` iff `a_j c_j = b_j` for every atom (indicator test
functions one way, linearity the other).
Source: [[corr-legit-neg-inventory]] item 010 (1)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem Phi_exact_iff (a b c : Fin J → ℚ) :
    (∀ g, Phi a c g = Eg b g) ↔ ∀ j, a j * c j = b j := by
  constructor
  · intro h j
    have := h (fun i => if i = j then 1 else 0)
    unfold Phi Eg at this
    simpa [Finset.sum_ite_eq'] using this
  · intro h g
    unfold Phi Eg
    exact Finset.sum_congr rfl fun j _ => by rw [h j]

/-- **A3b (2).** An exact estimator exists iff every atom with no `L`-mass has no `¬L`-mass
(absolute continuity); then `c_j = b_j / a_j` on supported atoms.
Source: [[corr-legit-neg-inventory]] item 010 (2)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem exists_Phi_exact_iff (a b : Fin J → ℚ) :
    (∃ c, ∀ g, Phi a c g = Eg b g) ↔ ∀ j, a j = 0 → b j = 0 := by
  constructor
  · rintro ⟨c, hc⟩ j hj
    have := (Phi_exact_iff a b c).1 hc j
    rw [hj, zero_mul] at this; exact this.symm
  · intro h
    refine ⟨fun j => if a j = 0 then 0 else b j / a j, (Phi_exact_iff a b _).2 fun j => ?_⟩
    by_cases hj : a j = 0
    · simp [hj, h j hj]
    · simp [hj, mul_div_cancel₀ _ hj]

/-- **A3b (3), unweighted.** The constant reweighting `c ≡ π(¬L)/π(L)` is exact for every `g` iff
`a_j π(¬L) = b_j π(L)` for every atom (`b_j / a_j` constant across supported atoms).
Source: [[corr-legit-neg-inventory]] item 010 (3)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem Phi_unweighted_exact_iff (a b : Fin J → ℚ) {pL pN : ℚ} (hpL : pL ≠ 0) :
    (∀ g, Phi a (fun _ => pN / pL) g = Eg b g) ↔ ∀ j, a j * pN = b j * pL := by
  rw [Phi_exact_iff]
  constructor
  · intro h j
    have := h j
    field_simp at this
    linarith
  · intro h j
    have := h j
    field_simp
    linarith

/-- **A3b (3), independence.** With `π(L) + π(¬L) = 1`, `a_j π(¬L) = b_j π(L)` for all `j` iff
`π(L ∩ G_j) = π(L) · π(G_j)` for all `j`, i.e. `L ⊥ 𝒢`.
Source: [[corr-legit-neg-inventory]] item 010 (3)
Kind: L
Fidelity: exact -/
theorem indep_iff (a b : Fin J → ℚ) {pL pN : ℚ} (h : pL + pN = 1) :
    (∀ j, a j * pN = b j * pL) ↔ ∀ j, a j = pL * (a j + b j) := by
  have hN : pN = 1 - pL := by linarith
  subst hN
  constructor <;> intro hj j <;> have := hj j <;> linarith

end A3b

/-! ### The bridge from the `Problem` to the atom masses -/

namespace Problem

variable {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)

/-- `π(E ∩ G_j)` for the atom `G_j = atom⁻¹ {j}` of an evaluator-information partition.
Source: [[corr-legit-neg-inventory]] item 010
Kind: D
Fidelity: exact -/
def atomMass {J : ℕ} (E : S → Bool) (atom : S → Fin J) (j : Fin J) : ℚ :=
  P.mass (fun s => E s && decide (atom s = j))

/-- For a `𝒢`-measurable `g` (a function of the atom), `∑ π [E] g(atom) = ∑_j π(E ∩ G_j) g_j`:
`Eg b g` *is* `E[g · 1_{¬L}]` when `b = atomMass (¬L)`, and `Phi a c g` is the estimator's
aggregate under `π · 1_L`.
Source: [[corr-legit-neg-inventory]] item 010
Kind: L
Fidelity: exact -/
theorem sum_atom {J : ℕ} (E : S → Bool) (atom : S → Fin J) (g : Fin J → ℚ) :
    ∑ s, P.prior s * ind (E s) * g (atom s) = ∑ j, P.atomMass E atom j * g j := by
  unfold atomMass mass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single (atom s)]
  · simp
  · intro j _ hj; simp [Ne.symm hj]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The atom masses of an event sum to its mass: `∑_j π(E ∩ G_j) = π(E)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem atomMass_sum {J : ℕ} (E : S → Bool) (atom : S → Fin J) :
    ∑ j, P.atomMass E atom j = P.mass E := by
  have := P.sum_atom E atom (fun _ => 1)
  simp only [mul_one] at this
  exact this.symm

/-- **A3b (3) over the `Problem` of record.** With `a_j = π(L ∩ G_j)`, `b_j = π(¬L ∩ G_j)` and
`π(L)`, `π(¬L)` the problem's own masses (so `pL`, `pN` of `Phi_unweighted_exact_iff` and
`indep_iff` are pinned, not free), the constant reweighting `c ≡ π(¬L)/π(L)` is exact for every
`g` iff `π(L ∩ G_j) = π(L) · π(G_j)` on every atom, `π(G_j) = a_j + b_j`: `L ⊥ 𝒢`.
Source: [[corr-legit-neg-inventory]] item 010 (3)
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem unweighted_exact_iff_indep {J : ℕ} (ℓ : S → Bool) (atom : S → Fin J)
    (hpos : 0 < P.mass ℓ) :
    (∀ g, Phi (P.atomMass ℓ atom) (fun _ => P.mass (fun s => !ℓ s) / P.mass ℓ) g
        = Eg (P.atomMass (fun s => !ℓ s) atom) g)
      ↔ ∀ j, P.atomMass ℓ atom j
          = P.mass ℓ * (P.atomMass ℓ atom j + P.atomMass (fun s => !ℓ s) atom j) := by
  rw [Phi_unweighted_exact_iff _ _ hpos.ne', indep_iff _ _ (by rw [P.mass_not]; ring)]

end Problem

/-! ### A3b witnesses (`J = 2`; three configurations, not the enumeration) -/

/-- **A3b, independent configuration.** `a = (1/6, 1/6)`, `b = (1/3, 1/3)`: `π(L) = 1/3`, the
unweighted estimator `c ≡ 2` is exact.
Source: [[corr-legit-neg-inventory]] item 010; VERIFY A V4
Kind: N+
Fidelity: exact -/
theorem A3b_independent :
    ∀ g, Phi (![1/6, 1/6] : Fin 2 → ℚ) (fun _ => (2/3 : ℚ) / (1/3)) g = Eg ![1/3, 1/3] g := by
  rw [Phi_unweighted_exact_iff _ _ (by norm_num)]
  intro j; fin_cases j <;> simp <;> norm_num

/-- **A3b, dependent configuration.** `a = (1/10, 1/5)`, `b = (3/10, 2/5)`: supported, so an
exact estimator exists (`c = (3, 2)`), but the unweighted one is biased.
Source: [[corr-legit-neg-inventory]] item 010; VERIFY A V4
Kind: N+
Fidelity: exact -/
theorem A3b_dependent :
    (∃ c, ∀ g, Phi (![1/10, 1/5] : Fin 2 → ℚ) c g = Eg ![3/10, 2/5] g) ∧
    ¬ (∀ g, Phi (![1/10, 1/5] : Fin 2 → ℚ) (fun _ => (7/10 : ℚ) / (3/10)) g = Eg ![3/10, 2/5] g) := by
  constructor
  · rw [exists_Phi_exact_iff]; intro j; fin_cases j <;> simp
  · rw [Phi_unweighted_exact_iff _ _ (by norm_num)]
    intro h; have := h 0; simp at this; norm_num at this

/-- **A3b, unsupported configuration.** `a = (0, 1/2)`, `b = (1/4, 1/4)`: an atom with no
`L`-mass carries `¬L`-mass, so no exact estimator exists.
Source: [[corr-legit-neg-inventory]] item 010; VERIFY A V4
Kind: N+
Fidelity: exact -/
theorem A3b_unsupported :
    ¬ ∃ c, ∀ g, Phi (![0, 1/2] : Fin 2 → ℚ) c g = Eg ![1/4, 1/4] g := by
  rw [exists_Phi_exact_iff]
  intro h; have := h 0 (by simp); norm_num at this

end Cleanroom.Corrigibility.LegitNegStatic
