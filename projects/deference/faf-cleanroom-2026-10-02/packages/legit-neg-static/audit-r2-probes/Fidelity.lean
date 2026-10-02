import Cleanroom.Corrigibility.LegitNegStatic.SealedDefense

/-!
# Audit round 2, lens `fidelity`: probes for `legit-neg-static`

Not imported by the library. Elaborated with `scripts/lean-check`.

1. `probe1_choice_level_necessity`: the narrowed headline `readLocal_exact_iff` proves its
   "only if" for *score* equality (`J₁ = W` on every atom-profile standard). The source's
   narrowed A5 is about *choices* ("escapes A3"). This probe shows the choice-level "only if"
   also holds on a two-option menu with `π(L) > 0`: if some atom has `a_j · cw_j ≠ b_j`, a
   standard with an atom-profile `¬L` part makes the local-linear reading's argmax differ
   from `argmax W`. So the ledger's "equality of scores, hence of choices" can be strengthened
   to an iff at the level of choices (this probe is the missing direction).
2. `probe2_bayes_k_argmax_eq`: the mandate's "prove the equality of argmax sets" for the
   Bayesian vs `k`-known evaluators, as an explicit argmax equality (the package proves the
   stronger equality of score differences, `sm_P1_diff_b_eq_k`, but does not state the argmax
   corollary).
3. `probe3_sealed_gated_EU_inverts`: finding 13 and the report scope the gated plain-EU
   inversion to "void-heavy priors under action-dependent legitimacy" (`voidHeavy` is B's
   toy, where `a₁` voids in `b`). The inversion also occurs on a *sealed* void-heavy problem:
   `π(b) = 9/10`, `L = {g}`, `Q(g, ·) = (0, 0)`, `Q(b, ·) = (0, 1)`, `n = (0, 1)`, `ϖ = 2 > D = 1`.
   Ungated: `9/10 − 2 < 0` excludes the violator; gated: `9/10 − 2/10 = 7/10 > 0` picks it.
   So the qualifier "under action-dependent legitimacy" is not needed; what matters is that
   the score accrues value on void worlds.
-/

namespace Cleanroom.Corrigibility.LegitNegStatic

open Finset Problem

/-- The indicator profile of atom `j₀`. -/
def indJ {J : ℕ} (j₀ : Fin J) : Fin J → ℚ := fun j => if j = j₀ then 1 else 0

lemma Phi_indJ {J : ℕ} (a c : Fin J → ℚ) (j₀ : Fin J) : Phi a c (indJ j₀) = a j₀ * c j₀ := by
  unfold Phi indJ
  simp [Finset.sum_ite_eq']

lemma Eg_indJ {J : ℕ} (b : Fin J → ℚ) (j₀ : Fin J) : Eg b (indJ j₀) = b j₀ := by
  unfold Eg indJ
  simp [Finset.sum_ite_eq']

/-- The `L`-part of a standard that is the constant `x` on `L` is `x · π(L)`. -/
lemma Lpart_const {S A' : Type} [Fintype S] [Fintype A'] (P : Problem S A') (ℓ : S → Bool)
    (x : ℚ) (y : S → ℚ) :
    (∑ s, P.prior s * ind (ℓ s) * (if ℓ s = true then x else y s)) = x * P.mass ℓ := by
  unfold Problem.mass
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  cases hs : ℓ s <;> simp [ind] <;> ring

/-- **Probe 1.** Choice-level necessity of exact weights, two-option menu. -/
theorem probe1_choice_level_necessity {S : Type} [Fintype S] (P : Problem S (Fin 2))
    {ℓ : S → Bool} (h : P.SealedBy ℓ) (hpos : 0 < P.mass ℓ) {J : ℕ} (atom : S → Fin J)
    (cw : Fin J → ℚ) (j₀ : Fin J)
    (hne : P.atomMass ℓ atom j₀ * cw j₀ ≠ P.atomMass (fun s => !ℓ s) atom j₀) :
    ∃ (Q : S → Fin 2 → ℚ) (g : Fin 2 → Fin J → ℚ), AtomProfile ℓ atom Q g ∧
      argmax (P.P1 (liftV (readLocal atom cw Q g))) ≠ argmax (P.W Q) := by
  set a := P.atomMass ℓ atom j₀ * cw j₀ with ha
  set b := P.atomMass (fun s => !ℓ s) atom j₀ with hb
  set m := P.mass ℓ with hm
  set t : ℚ := (a + b) / (2 * m) with ht
  have hm0 : m ≠ 0 := hpos.ne'
  have htm : t * m = (a + b) / 2 := by rw [ht]; field_simp
  let Q : S → Fin 2 → ℚ := fun s c => if c = 1 then (if ℓ s = true then -t else indJ j₀ (atom s)) else 0
  let g : Fin 2 → Fin J → ℚ := fun c => if c = 1 then indJ j₀ else 0
  have hprof : AtomProfile ℓ atom Q g := by
    intro s c hs
    simp only [Q, g]
    by_cases hc : c = 1 <;> simp [hc, hs]
  refine ⟨Q, g, hprof, ?_⟩
  -- the four scores
  have hP1_0 : P.P1 (liftV (readLocal atom cw Q g)) 0 = 0 := by
    rw [P.P1_readLocal h]
    simp only [Q, g]
    simp [Phi]
  have hW_0 : P.W Q 0 = 0 := by
    rw [P.W_eq_Lpart_add_Eg ℓ atom Q g hprof]
    simp only [Q, g]
    simp [Eg]
  have hP1_1 : P.P1 (liftV (readLocal atom cw Q g)) 1 = (a - b) / 2 := by
    rw [P.P1_readLocal h]
    simp only [Q, g, if_true]
    rw [Lpart_const P ℓ (-t) _, Phi_indJ, ← ha, ← hm]
    linarith [htm]
  have hW_1 : P.W Q 1 = (b - a) / 2 := by
    rw [P.W_eq_Lpart_add_Eg ℓ atom Q g hprof]
    simp only [Q, g, if_true]
    rw [Lpart_const P ℓ (-t) _, Eg_indJ, ← hb, ← hm]
    linarith [htm]
  intro heq
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- a < b: P1 picks 0 strictly, W picks 1 strictly
    have h1 : argmax (P.P1 (liftV (readLocal atom cw Q g))) = {0} := by
      rw [argmax_fin2_eq_zero_iff, hP1_0, hP1_1]; linarith
    have h2 : argmax (P.W Q) = {1} := by
      rw [argmax_fin2_eq_one_iff, hW_0, hW_1]; linarith
    rw [h1, h2] at heq
    exact absurd heq (by decide)
  · have h1 : argmax (P.P1 (liftV (readLocal atom cw Q g))) = {1} := by
      rw [argmax_fin2_eq_one_iff, hP1_0, hP1_1]; linarith
    have h2 : argmax (P.W Q) = {0} := by
      rw [argmax_fin2_eq_zero_iff, hW_0, hW_1]; linarith
    rw [h1, h2] at heq
    exact absurd heq (by decide)

/-- **Probe 2.** The Bayesian and `k`-known evaluators have the same argmax (explicit form of
the mandate's "prove the equality of argmax sets"), from `sm_P1_diff_b_eq_k`. -/
theorem probe2_bayes_k_argmax_eq (aW aS x hW hS δ : ℚ) (hW0 : 0 ≤ aW) (hW1 : aW ≤ 1)
    (hS0 : 0 ≤ aS) (hS1 : aS ≤ 1) (hpos : 0 < aW + aS) :
    argmax ((selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1).P1 (liftV (smVb aW aS x hW hS δ)))
      = argmax ((selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1).P1 (liftV (smVk aW aS x hW hS δ))) := by
  have hd := sm_P1_diff_b_eq_k aW aS x hW hS δ hW0 hW1 hS0 hS1 hpos
  simp only at hd
  set P := selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1
  set c := P.P1 (liftV (smVb aW aS x hW hS δ)) 0 - P.P1 (liftV (smVk aW aS x hW hS δ)) 0
  have hshift : ∀ a, P.P1 (liftV (smVb aW aS x hW hS δ)) a
      = P.P1 (liftV (smVk aW aS x hW hS δ)) a + c :=
    Fin.forall_fin_two.2 ⟨by simp only [c]; ring, by simp only [c]; linarith⟩
  rw [argmax_congr hshift, argmax_add_const]

/-- A sealed void-heavy problem: `π(b) = 9/10`, `L = {g}`, `Q(g, ·) = (0, 0)`, `Q(b, ·) = (0, 1)`. -/
def sealedVoidHeavy : Problem (Fin 2) (Fin 2) where
  prior := ![1/10, 9/10]
  prior_nonneg := by intro s; fin_cases s <;> simp <;> norm_num
  prior_sum := by simp [Fin.sum_univ_two]; norm_num
  leg := fun s _ => decide (s = 0)
  u := fun s a => ![![0, 0], ![0, 1]] s a

/-- **Probe 3.** The gated plain-EU rule score inverts on a *sealed* void-heavy problem too. -/
theorem probe3_sealed_gated_EU_inverts :
    sealedVoidHeavy.SealedBy legG ∧
    (∀ s a, 0 ≤ sealedVoidHeavy.u s a) ∧ (∀ s a, sealedVoidHeavy.u s a ≤ 1) ∧
    argmax (fun a => sealedVoidHeavy.W sealedVoidHeavy.u a - 2 * ((![0, 1] : Fin 2 → ℕ) a : ℚ)) = {0} ∧
    argmax (gatedEUrule sealedVoidHeavy sealedVoidHeavy.u 2 ![0, 1]) = {1} := by
  refine ⟨fun _ _ => rfl, ?_, ?_, ?_, ?_⟩
  · intro s a; fin_cases s <;> fin_cases a <;> simp [sealedVoidHeavy]
  · intro s a; fin_cases s <;> fin_cases a <;> simp [sealedVoidHeavy]
  · rw [argmax_fin2_eq_zero_iff]
    simp [sealedVoidHeavy, W, EU, Fin.sum_univ_two]; norm_num
  · rw [argmax_fin2_eq_one_iff]
    simp [gatedEUrule, sealedVoidHeavy, W, EU, PL, mass, Fin.sum_univ_two]; norm_num

end Cleanroom.Corrigibility.LegitNegStatic

namespace Cleanroom.Corrigibility.LegitNegStatic

/-- **Probe 4.** A3b (3) as worded in NEGATIVES ("exact for every `g` iff `ρ` is constant, i.e.
iff `L ⊥ 𝒢`") and in item 010 / mandate target 13 ("iff `b_j/a_j` is constant across supported
atoms iff `L ⊥ atom`") needs absolute continuity for its middle clause: `a = (1/2, 0)`,
`b = (1/4, 1/4)` has `ρ` constant on its single supported atom, yet the unweighted estimator
`c ≡ π(¬L)/π(L) = 1` is not exact and `L ⊥ 𝒢` fails. The package's condition
(`Phi_unweighted_exact_iff`: `a_j π(¬L) = b_j π(L)` on every atom) is the correct one; the
source's middle clause is an imprecision not recorded in the findings file. -/
theorem probe4_rho_const_not_exact :
    ¬ (∀ g, Phi (![1/2, 0] : Fin 2 → ℚ) (fun _ => (1/2 : ℚ) / (1/2)) g = Eg ![1/4, 1/4] g) ∧
    ¬ (∀ j, (![1/2, 0] : Fin 2 → ℚ) j
        = 1/2 * ((![1/2, 0] : Fin 2 → ℚ) j + (![1/4, 1/4] : Fin 2 → ℚ) j)) := by
  constructor
  · rw [Phi_unweighted_exact_iff _ _ (by norm_num)]
    intro h; have := h 0; norm_num at this
  · intro h; have := h 1; norm_num at this

end Cleanroom.Corrigibility.LegitNegStatic
