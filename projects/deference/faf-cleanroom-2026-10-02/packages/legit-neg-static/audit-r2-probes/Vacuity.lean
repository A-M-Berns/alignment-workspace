import Cleanroom.Corrigibility.LegitNegStatic.SealedDefense
import Cleanroom.Corrigibility.LegitNegStatic.BlindnessChar

/-!
# `legit-neg-static`, audit round 2, adversarial lens: probes

Not imported by the library. Elaborated with `scripts/lean-check`. Each probe is evidence for
one item of `legit-neg-static-audit-r2-adversarial.md`.

- Probe 1: target 15's theorem is mandated for "the rule-scored P1 (or P2, or plain EU)"; the
  package has the P1 and plain-EU forms and no P2 form. Here the P2 form is defined. (a) For P2
  the gated and ungated rule terms *coincide* wherever P2 is defined, so finding 13's
  gated/ungated distinction is invisible to P2. (b) Under the exclusion convention the naive
  P2 clause is **false**: when every compliant option has `P(L | ·) = 0`, the declared violator
  is the unique `argmaxOpt`. (c) Under sealing with `π(L) > 0` the P2 clause holds, in twelve
  lines from the package's own lemmas — the missing statement is cheap.
- Probe 2: NEGATIVES A3's escape (i) — D2′ reweighted by `ρ = b/a = (1/9, 9)` on the *dependent*
  A3 instance — is not instantiated in the package (`readD2'_escapes_of_indep` covers only
  `aW = aS`; `argmax_readLocal_eq_argmax_W_of_exact` is general). Here it is: the general
  theorem's hypothesis package is inhabited on a structure where the unweighted D2′ fails, so
  the narrowed A5 headline's `ρ` clause is exercised non-degenerately (N+).
- Probe 3: A1's bound `W_regret_le_of_mem_argmax_P1_S1` asks `0 ≤ Q ≤ D` on every terminal;
  the proof uses the range only off `L`. The strengthening with the range hypotheses restricted
  to `ℓ s = false` is proved here from the same lemmas (a free improvement, not an error).
-/

namespace Cleanroom.Corrigibility.LegitNegStatic.AuditR2

open Finset Cleanroom.Corrigibility.LegitNegStatic Cleanroom.Corrigibility.LegitNegStatic.Problem

/-! ## Probe 1: the P2 form of the rule term -/

/-- The rule-scored P2 under the exclusion convention: `P1 V a / P(L | a) − ϖ · n a`, `none` at
`P(L | a) = 0`. -/
def P2rule {S A : Type} [Fintype S] [Fintype A] (P : Problem S A) (ϖ : ℚ) (n : A → ℕ)
    (V : MenuVec S A) (a : A) : Option ℚ :=
  if P.PL a = 0 then none else some (P.P1 V a / P.PL a - ϖ * (n a : ℚ))

/-- (a) For P2, gating is invisible: `P2 (ruleScore ϖ n V) a = P2rule P ϖ n V a` for every `a`
(the `[leg]`-gated penalty `ϖ n a · P(L | a)` is divided by the same `P(L | a)`). -/
theorem probe1_P2_gated_eq_ungated {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)
    (ϖ : ℚ) (n : A → ℕ) (V : MenuVec S A) (a : A) :
    P.P2 (ruleScore ϖ n V) a = P2rule P ϖ n V a := by
  unfold P2 P2rule
  split_ifs with h
  · rfl
  · congr 1
    have hg := P.P1ruleGated_eq ϖ n V a
    unfold P1ruleGated at hg
    rw [hg, sub_div, mul_div_assoc, div_self h, mul_one]

/-- The exclusion-edge instance: the compliant `a₀` is void everywhere, the violator `a₁` is
legitimate everywhere, `u ≡ 0` (so `0 ≤ V ≤ D` with `D = 0 < ϖ = 2`). -/
def nullCompliant : Problem (Fin 2) (Fin 2) where
  prior := ![1/2, 1/2]
  prior_nonneg := by intro s; fin_cases s <;> simp
  prior_sum := by simp; norm_num
  leg := fun _ a => decide (a = 1)
  u := fun _ _ => 0

/-- (b) On `nullCompliant` with `n = (0, 1)`, `ϖ = 2`: the ungated P1 form excludes the violator
(`ruleScore_ungated_excludes` applies), but the P2 form under the exclusion convention *selects*
it — `a₀` is `none`, so `a₁` with score `0/1 − 2 = −2` is the unique candidate. The mandate's
"(or P2)" clause needs a defined compliant option (e.g. sealing with `π(L) > 0`). -/
theorem probe1_P2_exclusion_picks_violator :
    (1 : Fin 2) ∉ argmax (nullCompliant.P1rule 2 ![0, 1] (S1 nullCompliant.u)) ∧
    argmaxOpt (P2rule nullCompliant 2 ![0, 1] (S1 nullCompliant.u)) = {1} := by
  constructor
  · exact nullCompliant.ruleScore_ungated_excludes (ϖ := 2) (D := 0) le_rfl (by norm_num)
      ![0, 1] (S1 nullCompliant.u) (fun s a => by simp [nullCompliant])
      (fun s a => by simp [nullCompliant]) 0 (by simp) 1 (by simp)
  · have h0 : P2rule nullCompliant 2 ![0, 1] (S1 nullCompliant.u) 0 = none := by
      simp [P2rule, nullCompliant, PL, mass]
    have h1 : P2rule nullCompliant 2 ![0, 1] (S1 nullCompliant.u) 1 = some (-2) := by
      simp [P2rule, nullCompliant, PL, mass, P1, Fin.sum_univ_two]; norm_num
    ext a
    simp only [mem_argmaxOpt, Finset.mem_singleton]
    constructor
    · rintro ⟨x, hx, -⟩
      fin_cases a
      · simp [h0] at hx
      · rfl
    · rintro rfl
      refine ⟨-2, h1, ?_⟩
      intro b y hy
      fin_cases b <;> simp [h0, h1] at hy
      linarith

/-- (c) The P2 clause of target 15 under sealing with `π(L) > 0`: from the package's lemmas. -/
theorem probe1_P2rule_excludes_of_sealed {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)
    {ℓ : S → Bool} (h : P.SealedBy ℓ) (hpos : 0 < P.mass ℓ) {ϖ D : ℚ} (hD : 0 ≤ D) (hϖ : D < ϖ)
    (n : A → ℕ) (V : MenuVec S A) (hV0 : ∀ s a, 0 ≤ V s a a) (hVD : ∀ s a, V s a a ≤ D) (a₀ : A)
    (h0 : n a₀ = 0) (a : A) (ha : 1 ≤ n a) : a ∉ argmaxOpt (P2rule P ϖ n V) := by
  have hne : ∀ b, P.PL b ≠ 0 := fun b => by rw [P.PL_eq_mass_of_SealedBy h]; exact hpos.ne'
  have hV : P2rule P ϖ n V = fun b => some (P.P1 V b / P.mass ℓ - ϖ * (n b : ℚ)) :=
    funext fun b => by simp [P2rule, P.PL_eq_mass_of_SealedBy h, hpos.ne']
  rw [hV, argmaxOpt_some, mem_argmax]
  intro hh
  have h₀ := hh a₀
  rw [h0] at h₀
  have hle : P.P1 V a ≤ D * P.PL a := P.P1_le_mul_PL a fun s _ => hVD s a
  rw [P.PL_eq_mass_of_SealedBy h] at hle
  have hnn : 0 ≤ P.P1 V a₀ := P.P1_nonneg a₀ fun s _ => hV0 s a₀
  have hn : (1 : ℚ) ≤ n a := by exact_mod_cast ha
  have hϖpos : 0 < ϖ := lt_of_le_of_lt hD hϖ
  have h1 : ϖ ≤ ϖ * (n a : ℚ) := by nlinarith
  have hdiv : P.P1 V a / P.mass ℓ ≤ D := (div_le_iff₀ hpos).2 hle
  have hdiv0 : 0 ≤ P.P1 V a₀ / P.mass ℓ := div_nonneg hnn hpos.le
  simp only [Nat.cast_zero, mul_zero, sub_zero] at h₀
  linarith

/-! ## Probe 2: A3's escape (i), the `ρ`-reweighted D2′ on the dependent instance -/

/-- On `A3P δ` (`aW = 9/10`, `aS = 1/10`: `a = (9/20, 1/20)`, `b = (1/20, 9/20)`, so
`ρ = b/a = (1/9, 9)`, NEGATIVES A3 escape (i)), the local-linear reading with weights `ρ` has
exact weights, hence chooses `argmax W` for *every* `δ`; at `δ = 1/2` it picks `safe` where the
unweighted D2′ picks `risky` (`A5_A3_cells`). The hypothesis package of
`argmax_readLocal_eq_argmax_W_of_exact` is inhabited on a dependent structure. -/
theorem probe2_rho_reweighted_escapes :
    (∀ δ : ℚ, argmax ((A3P δ).P1 (liftV (readLocal smK ![1/9, 9] (smQ (1/2) δ 0 1)
        (fun a k => smQ (1/2) δ 0 1 (smNof k) a)))) = argmax ((A3P δ).W (A3P δ).u)) ∧
    argmax ((A3P (1/2)).P1 (liftV (readLocal smK ![1/9, 9] (smQ (1/2) (1/2) 0 1)
        (fun a k => smQ (1/2) (1/2) 0 1 (smNof k) a)))) = {0} ∧
    argmax ((A3P (1/2)).P1 (liftV (readD2' (9/10) (1/10) (1/2) 0 1 (1/2)))) = {1} := by
  have hall : ∀ δ : ℚ, argmax ((A3P δ).P1 (liftV (readLocal smK ![1/9, 9] (smQ (1/2) δ 0 1)
        (fun a k => smQ (1/2) δ 0 1 (smNof k) a)))) = argmax ((A3P δ).W (A3P δ).u) := by
    intro δ
    obtain ⟨ha, hb⟩ := sm_atomMass (9/10) (1/10) (1/2) 0 1 δ (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
    have hc : ∀ j, (A3P δ).atomMass smL smK j * (![1/9, 9] : Fin 2 → ℚ) j
        = (A3P δ).atomMass (fun s => !smL s) smK j := by
      intro j
      show (selectionModel (9/10) (1/10) (1/2) 0 1 δ _ _ _ _).atomMass smL smK j * _
        = (selectionModel (9/10) (1/10) (1/2) 0 1 δ _ _ _ _).atomMass (fun s => !smL s) smK j
      rw [ha, hb]
      fin_cases j <;> simp <;> norm_num
    have hg := (readD2'_eq_mass_mul_readLocal (9/10) (1/10) (1/2) 0 1 δ (by norm_num)).2
    have hpos : 0 < (A3P δ).mass smL := by
      show (0 : ℚ) < (selectionModel (9/10) (1/10) (1/2) 0 1 δ _ _ _ _).mass smL
      rw [sm_mass_L]; norm_num
    exact ((A3P δ).argmax_readLocal_eq_argmax_W_of_exact
      (selectionModelWith_SealedBy (9/10) (1/10) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) _) hpos smK _ hc _ _ hg).1
  refine ⟨hall, ?_, ?_⟩
  · rw [hall (1/2)]
    exact (A3_instance.2.2.2.1 (1/2)).2 (by norm_num)
  · exact (A3_instance.2.2.1 (1/2)).2 (by norm_num)

/-! ## Probe 3: A1's bound with the range only off `L` -/

/-- The bound of `W_regret_le_of_mem_argmax_P1_S1` with `0 ≤ Q ≤ D` required only on `¬L`
states: the same proof, with one case split. -/
theorem probe3_regret_bound_range_off_L {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)
    {ℓ : S → Bool} (h : P.SealedBy ℓ) {Q : S → A → ℚ} {D : ℚ}
    (hQ0 : ∀ s a, ℓ s = false → 0 ≤ Q s a) (hQD : ∀ s a, ℓ s = false → Q s a ≤ D) {a : A}
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
    by_cases hs : ℓ s = true
    · simp [hs, ind]
    · have hs' : ℓ s = false := by simpa using hs
      have hp := P.prior_nonneg s
      have key : 0 ≤ P.prior s * (D - (Q s b - Q s a)) :=
        mul_nonneg hp (by linarith [hQ0 s a hs', hQD s b hs'])
      simp only [hs', Bool.not_false, ind_true, mul_one]
      nlinarith [key]
  linarith

end Cleanroom.Corrigibility.LegitNegStatic.AuditR2
