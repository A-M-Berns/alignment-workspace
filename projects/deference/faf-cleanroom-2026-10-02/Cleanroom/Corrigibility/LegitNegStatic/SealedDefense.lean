import Cleanroom.Corrigibility.LegitNegStatic.SealedInfo
import Cleanroom.Corrigibility.LegitNegStatic.SealedSelection

/-!
# Cluster A, A4–A6: inexpressible and lent protection, the ungated rule term, the readings
D1–D4′, and what the defense must accomplish

Package `legit-neg-static`, targets 14–17. Sources: `clusters/A/NEGATIVES.md` A4, A5, A6;
`clusters/A/VERIFY.md` "A4: survives", "A5: narrowed", "A6: narrowed" (V1, V5);
[[corr-legit-neg-inventory]] items 011–014; [[corr-legit-neg-2-inventory]] items 2-011, 2-012.

Scope: the finite shadow only. The workspace (`alignment-workspace`) is out of scope; the
attribution "Anson's rules are learned" is ATTRIBUTION-UNVETTED (findings). The "narrow
updatelessness" reading and the anger analogy are ARGUMENT in the source and not targets.
-/

namespace Cleanroom.Corrigibility.LegitNegStatic

open Finset Problem

/-! ## A4 (a): protection of `C_n` is inexpressible under sealing -/

namespace Problem

variable {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)

/-- **A4a / A4a′ (the honest content).** Under `SealedBy ℓ` no term of any proposal depends on
the option through `P(L | ·)`: `P(L | a) = P(L | a')` for all `a, a'`, and `J₁ a = π(L) · (J₁ a / π(L))`
with the same `π(L)` for every option. This is the whole of "protection of `C_n` is
inexpressible" and of its dual "no steering toward `¬C_n`"; it is not dressed as more.
Source: [[corr-legit-neg-inventory]] item 011 (A4a, A4a′)
Kind: L
Fidelity: exact -/
theorem PL_const_of_SealedBy {ℓ : S → Bool} (h : P.SealedBy ℓ) (a a' : A) : P.PL a = P.PL a' := by
  rw [P.PL_eq_mass_of_SealedBy h, P.PL_eq_mass_of_SealedBy h]

/-- Updateless evaluators (the prior-weighted value, constant across `L`-states) make `J₁` a
positive multiple of `W`: the escape of A3 (ii) and A4b, in general form.
Source: [[corr-legit-neg-inventory]] item 009 (escape ii), item 011 (escape)
Kind: L
Fidelity: exact -/
theorem P1_updateless_eq_mass_mul_W {ℓ : S → Bool} (h : P.SealedBy ℓ) (Q : S → A → ℚ) (a : A) :
    P.P1 (liftV (fun _ c => P.W Q c)) a = P.mass ℓ * P.W Q a := by
  rw [P.P1_liftV_of_SealedBy h, P.J1_const]

/-- `argmax_P1_updateless_eq_argmax_W`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem argmax_P1_updateless_eq_argmax_W {ℓ : S → Bool} (h : P.SealedBy ℓ) (hpos : 0 < P.mass ℓ)
    (Q : S → A → ℚ) : argmax (P.P1 (liftV (fun _ c => P.W Q c))) = argmax (P.W Q) := by
  rw [argmax_congr (P.P1_updateless_eq_mass_mul_W h Q)]
  have : (fun a => P.mass ℓ * P.W Q a) = fun a => P.W Q a * P.mass ℓ := funext fun a => mul_comm _ _
  rw [this, argmax_mul_pos _ hpos]

end Problem

/-! ## A4 (b): lent protection over the selection model -/

section Lent

variable (aW aS lam ε : ℚ) (hW0 : 0 ≤ aW) (hW1 : aW ≤ 1) (hS0 : 0 ≤ aS) (hS1 : aS ≤ 1)

/-- The lent-protection problem: A3's adversary model with the standard `smQprot lam ε`
(`idle` protects `L'` iff the adversary is weak; `protect` always, at cost `ε`).
Source: [[corr-legit-neg-inventory]] item 011 (A4b)
Kind: D
Fidelity: exact -/
def lentProblem : Problem (Fin 4) (Fin 2) :=
  selectionModelWith aW aS hW0 hW1 hS0 hS1 (smQprot lam ε)

/-- **A4b, the gain given `C`.** With pointwise-correct legitimate evaluators (`V = Q` on `L`),
`J₁ protect − J₁ idle = π(L) · (λ · P(S | C) − ε)` with `P(S | C) = aS/(aW + aS)`.
Source: [[corr-legit-neg-2-inventory]] item 2-012
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem lent_P1_diff (hpos : 0 < aW + aS) :
    let P := lentProblem aW aS lam ε hW0 hW1 hS0 hS1
    P.P1 (liftV (smQprot lam ε)) 1 - P.P1 (liftV (smQprot lam ε)) 0
      = (aW + aS) / 2 * (lam * (aS / (aW + aS)) - ε) := by
  intro P
  simp [P, lentProblem, selectionModelWith, P1, smQprot, smL, smK, Fin.sum_univ_four]
  field_simp
  ring

/-- **A4b, the gain over all worlds.** `W protect − W idle = λ · P(S) − ε = λ/2 − ε`.
Source: [[corr-legit-neg-2-inventory]] item 2-012
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem lent_W_diff :
    let P := lentProblem aW aS lam ε hW0 hW1 hS0 hS1
    P.W P.u 1 - P.W P.u 0 = lam * (1/2) - ε := by
  intro P
  simp [P, lentProblem, selectionModelWith, W, EU, smQprot, smL, smK, Fin.sum_univ_four]
  ring

/-- **A4b, the under-protection window (parametric iff).** The proposals strictly idle iff
`λ P(S | C) < ε`, and `W` strictly protects iff `ε < λ P(S)`; under-protection is exactly
`ε ∈ (λ P(S | C), λ P(S))`.
Source: [[corr-legit-neg-2-inventory]] item 2-012; [[corr-legit-neg-inventory]] item 011
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem lent_window (hpos : 0 < aW + aS) :
    let P := lentProblem aW aS lam ε hW0 hW1 hS0 hS1
    (argmax (P.P1 (liftV (smQprot lam ε))) = {0} ↔ lam * (aS / (aW + aS)) < ε) ∧
    (argmax (P.W P.u) = {1} ↔ ε < lam * (1/2)) := by
  intro P
  have hk := lent_P1_diff aW aS lam ε hW0 hW1 hS0 hS1 hpos
  have hw := lent_W_diff aW aS lam ε hW0 hW1 hS0 hS1
  simp only at hk hw
  have hp : 0 < (aW + aS) / 2 := by linarith
  constructor
  · rw [argmax_fin2_eq_zero_iff]
    constructor
    · intro h
      have : (aW + aS) / 2 * (lam * (aS / (aW + aS)) - ε) < 0 := by linarith
      have := (mul_neg_iff).1 this
      rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
      · linarith
      · linarith
    · intro h
      have : (aW + aS) / 2 * (lam * (aS / (aW + aS)) - ε) < 0 :=
        mul_neg_of_pos_of_neg hp (by linarith)
      linarith
  · rw [argmax_fin2_eq_one_iff]
    constructor <;> intro h <;> linarith

end Lent

/-- **A4b, the instance.** `λ = 1`, `ε = 3/10`, `aW = 9/10`, `aS = 1/10`: the gain is `−1/5`
given `C` and `+1/5` unconditionally; the proposals idle, `W` protects; the window is
`(1/10, 1/2)`.
Source: [[corr-legit-neg-inventory]] item 011 (fixture A4b)
Kind: N+
Fidelity: exact -/
theorem A4b_instance :
    let P := lentProblem (9/10) (1/10) 1 (3/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    P.P1 (liftV (smQprot 1 (3/10))) 1 - P.P1 (liftV (smQprot 1 (3/10))) 0 = (1/2) * (-1/5) ∧
    P.W P.u 1 - P.W P.u 0 = 1/5 ∧
    argmax (P.P1 (liftV (smQprot 1 (3/10)))) = {0} ∧ argmax (P.W P.u) = {1} := by
  intro P
  have hk := lent_P1_diff (9/10) (1/10) 1 (3/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hw := lent_W_diff (9/10) (1/10) 1 (3/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hwin := lent_window (9/10) (1/10) 1 (3/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only at hk hw hwin
  refine ⟨by rw [hk]; norm_num, by rw [hw]; norm_num, ?_, ?_⟩
  · rw [hwin.1]; norm_num
  · rw [hwin.2]; norm_num

/-- **A4b, N− (independent threat).** With `aW = aS = 1/2` the threat is independent of `C_n`,
`P(S | C) = P(S)`, and both the proposals and `W` protect at `ε = 3/10`.
Source: [[corr-legit-neg-inventory]] item 011 (A4b N−)
Kind: N-
Fidelity: exact -/
theorem A4b_independent_threat :
    let P := lentProblem (1/2) (1/2) 1 (3/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    argmax (P.P1 (liftV (smQprot 1 (3/10)))) = {1} ∧ argmax (P.W P.u) = {1} := by
  intro P
  have hk := lent_P1_diff (1/2) (1/2) 1 (3/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hwin := lent_window (1/2) (1/2) 1 (3/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp only at hk hwin
  refine ⟨?_, by rw [hwin.2]; norm_num⟩
  rw [argmax_fin2_eq_one_iff]
  norm_num at hk
  linarith

/-- **A4b, the escape.** Updateless evaluators (the prior-weighted value of protection) make
the proposals protect, matching `W`.
Source: [[corr-legit-neg-inventory]] item 011 (A4b escape)
Kind: N+
Fidelity: exact -/
theorem A4b_updateless_escape :
    let P := lentProblem (9/10) (1/10) 1 (3/10) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    argmax (P.P1 (liftV (fun _ c => P.W P.u c))) = {1} := by
  intro P
  rw [P.argmax_P1_updateless_eq_argmax_W (selectionModelWith_SealedBy _ _ _ _ _ _ _) ?_]
  · exact (A4b_instance).2.2.2
  · rw [show P.mass smL = (9/10 + 1/10) / 2 from by
      simp [P, lentProblem, selectionModelWith, mass, smL, Fin.sum_univ_four]; ring]
    norm_num

/-! ## The workspace escape in finite shadow: a committed, ungated rule term -/

namespace Problem

variable {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)

/-- The rule-scored vector `V s a c − ϖ · n c`, with `n : A → ℕ` the agent's own count of
declared violations.
Source: [[corr-legit-neg-inventory]] item 012
Kind: D
Fidelity: exact -/
def ruleScore {S A : Type} (ϖ : ℚ) (n : A → ℕ) (V : MenuVec S A) : MenuVec S A :=
  fun s a c => V s a c - ϖ * (n c : ℚ)

/-- **The ungated rule-scored P1**: `∑ s, π s · ([leg s a] · V s a a − ϖ · n a)`, the penalty
charged on *every* state, legitimate or void (no `[leg]` factor on it).
Source: [[corr-legit-neg-inventory]] item 012; [[corr-legit-neg-2-inventory]] item 2-024
Kind: D
Fidelity: exact -/
def P1rule (ϖ : ℚ) (n : A → ℕ) (V : MenuVec S A) (a : A) : ℚ :=
  ∑ s, P.prior s * (ind (P.leg s a) * V s a a - ϖ * (n a : ℚ))

/-- `P1rule_eq`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P1rule_eq (ϖ : ℚ) (n : A → ℕ) (V : MenuVec S A) (a : A) :
    P.P1rule ϖ n V a = P.P1 V a - ϖ * (n a : ℚ) := by
  unfold P1rule P1
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, P.prior_sum, one_mul, mul_assoc]

/-- **The gated variant**: the penalty inside the `[leg]` factor, `P1 (ruleScore ϖ n V) a`
`= P1 V a − ϖ · n a · P(L | a)`. An `L`-world evaluation (it factors through the vector).
Source: [[corr-legit-neg-inventory]] item 012 (the trap)
Kind: D
Fidelity: exact -/
def P1ruleGated (ϖ : ℚ) (n : A → ℕ) (V : MenuVec S A) (a : A) : ℚ := P.P1 (ruleScore ϖ n V) a

/-- `P1ruleGated_eq`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma P1ruleGated_eq (ϖ : ℚ) (n : A → ℕ) (V : MenuVec S A) (a : A) :
    P.P1ruleGated ϖ n V a = P.P1 V a - ϖ * (n a : ℚ) * P.PL a := by
  unfold P1ruleGated P1 ruleScore PL mass
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **Target 15, branchwise dominance.** If `ϖ > D ≥ 0`, `0 ≤ V ≤ D` on the diagonal, and some
option has `n = 0`, then no option with `n ≥ 1` is in the argmax of the ungated rule-scored
`P1` — for every prior, every legitimacy structure and every menu vector.
Source: [[corr-legit-neg-inventory]] item 012; [[corr-legit-neg-2-inventory]] item 2-024
Kind: P
Fidelity: exact
Hyps: (a) all; the range `0 ≤ V ≤ D` is the modelling assumption -/
theorem ruleScore_ungated_excludes {ϖ D : ℚ} (hD : 0 ≤ D) (hϖ : D < ϖ) (n : A → ℕ)
    (V : MenuVec S A) (hV0 : ∀ s a, 0 ≤ V s a a) (hVD : ∀ s a, V s a a ≤ D) (a₀ : A)
    (h0 : n a₀ = 0) (a : A) (ha : 1 ≤ n a) : a ∉ argmax (P.P1rule ϖ n V) := by
  rw [mem_argmax]; intro h
  have h₀ := h a₀
  rw [P.P1rule_eq, P.P1rule_eq, h0] at h₀
  have hle : P.P1 V a ≤ D * P.PL a := P.P1_le_mul_PL a fun s _ => hVD s a
  have hPL := P.mass_le_one (fun s => P.leg s a)
  have hnn : 0 ≤ P.P1 V a₀ := P.P1_nonneg a₀ fun s _ => hV0 s a₀
  have hn : (1 : ℚ) ≤ n a := by exact_mod_cast ha
  have : ϖ * (n a : ℚ) ≥ ϖ := by nlinarith
  have hDPL : D * P.PL a ≤ D := by
    have := P.PL a; unfold PL at *; nlinarith [P.mass_nonneg (fun s => P.leg s a)]
  simp only [Nat.cast_zero, mul_zero, sub_zero] at h₀
  linarith

/-- The same for the plain (ungated) expected-utility rule score `W Q a − ϖ n a`.
Source: [[corr-legit-neg-inventory]] item 012
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem ruleScore_EU_excludes {ϖ D : ℚ} (hD : 0 ≤ D) (hϖ : D < ϖ) (n : A → ℕ) (Q : S → A → ℚ)
    (hQ0 : ∀ s a, 0 ≤ Q s a) (hQD : ∀ s a, Q s a ≤ D) (a₀ : A) (h0 : n a₀ = 0) (a : A)
    (ha : 1 ≤ n a) : a ∉ argmax (fun a => P.W Q a - ϖ * (n a : ℚ)) := by
  rw [mem_argmax]; intro h
  have h₀ := h a₀
  rw [h0] at h₀
  have hW : P.W Q a ≤ D := by
    unfold W EU
    calc ∑ s, P.prior s * Q s a ≤ ∑ s, P.prior s * D :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hQD s a) (P.prior_nonneg s)
      _ = D := by rw [← Finset.sum_mul, P.prior_sum, one_mul]
  have hW0 : 0 ≤ P.W Q a₀ := Finset.sum_nonneg fun s _ => mul_nonneg (P.prior_nonneg s) (hQ0 s a₀)
  have hn : (1 : ℚ) ≤ n a := by exact_mod_cast ha
  have : ϖ * (n a : ℚ) ≥ ϖ := by nlinarith
  simp only [Nat.cast_zero, mul_zero, sub_zero] at h₀
  linarith

/-- **The gated variant also excludes violators whenever `π(L) > 0` under sealing** (finding 13:
under sealing gating is inert for the argmax — it multiplies every option's penalty by the same
constant).
Source: finding 13 of [[legit-neg-static-findings]]
Kind: P
Fidelity: exact -/
theorem ruleScore_gated_excludes_of_mass_pos {ℓ : S → Bool} (h : P.SealedBy ℓ)
    (hpos : 0 < P.mass ℓ) {ϖ D : ℚ} (hD : 0 ≤ D) (hϖ : D < ϖ) (n : A → ℕ) (V : MenuVec S A)
    (hV0 : ∀ s a, 0 ≤ V s a a) (hVD : ∀ s a, V s a a ≤ D) (a₀ : A) (h0 : n a₀ = 0) (a : A)
    (ha : 1 ≤ n a) : a ∉ argmax (P.P1ruleGated ϖ n V) := by
  rw [mem_argmax]; intro hh
  have h₀ := hh a₀
  rw [P.P1ruleGated_eq, P.P1ruleGated_eq, h0, P.PL_eq_mass_of_SealedBy h,
    P.PL_eq_mass_of_SealedBy h] at h₀
  have hle : P.P1 V a ≤ D * P.PL a := P.P1_le_mul_PL a fun s _ => hVD s a
  rw [P.PL_eq_mass_of_SealedBy h] at hle
  have hnn : 0 ≤ P.P1 V a₀ := P.P1_nonneg a₀ fun s _ => hV0 s a₀
  have hn : (1 : ℚ) ≤ n a := by exact_mod_cast ha
  have hϖpos : 0 < ϖ := lt_of_le_of_lt hD hϖ
  have h1 : ϖ * 1 ≤ ϖ * (n a : ℚ) := mul_le_mul_of_nonneg_left hn hϖpos.le
  have h2 : ϖ * 1 * P.mass ℓ ≤ ϖ * (n a : ℚ) * P.mass ℓ := mul_le_mul_of_nonneg_right h1 hpos.le
  have h3 : D * P.mass ℓ < ϖ * P.mass ℓ := mul_lt_mul_of_pos_right hϖ hpos
  simp only [Nat.cast_zero, mul_zero, zero_mul, sub_zero, mul_one] at h₀ h2
  linarith

end Problem

/-- The gated tie witness: `a₀` legitimate everywhere, `a₁` void everywhere, `u ≡ 0`.
Source: finding 13
Kind: D
Fidelity: exact -/
def gatedTieWitness : Problem (Fin 2) (Fin 2) where
  prior := ![1/2, 1/2]
  prior_nonneg := by intro s; fin_cases s <;> simp
  prior_sum := by simp; norm_num
  leg := fun _ a => decide (a = 0)
  u := fun _ _ => 0

/-- **Target 15, N− for the gated variant.** On `gatedTieWitness` with `n = (0, 1)`, `ϖ = 2`:
the ungated rule score excludes the violator `a₁` (`argmax = {a₀}`), while the gated one ties the
whole menu at `0` (`a₁`'s penalty is gated away by `P(L | a₁) = 0`, and `a₀` scores `0`). A tie,
not an inversion: within `0 ≤ V ≤ D` no strict inversion exists (finding 13).
Source: finding 13; [[corr-legit-neg-inventory]] item 012 (the trap)
Kind: N-
Fidelity: exact; weaker than the mandate's expected witness (tie only) -/
theorem ruleScore_gated_tie_witness :
    argmax (gatedTieWitness.P1rule 2 ![0, 1] (S1 gatedTieWitness.u)) = {0} ∧
    argmax (gatedTieWitness.P1ruleGated 2 ![0, 1] (S1 gatedTieWitness.u)) = univ := by
  constructor
  · rw [argmax_fin2_eq_zero_iff, P1rule_eq, P1rule_eq]
    simp [gatedTieWitness, P1]
  · have : ∀ a, gatedTieWitness.P1ruleGated 2 ![0, 1] (S1 gatedTieWitness.u) a = 0 := by
      intro a; rw [P1ruleGated_eq]; fin_cases a <;> simp [gatedTieWitness, P1, PL, mass]
    rw [argmax_congr this, argmax_const]

/-- **A2's pair closes under a declared violation.** With `risky` declared (`n = (0, 1)`) and
`ϖ = 2 > 1`, both `L`-indistinguishable models of fixture A2 choose `safe` under the ungated
rule-scored `P1` (the evaluators' vector `(3/4, 159/200)` lies in `[0, 1]`).
Source: [[corr-legit-neg-inventory]] item 012 (A2 pair)
Kind: N+
Fidelity: exact -/
theorem A2_pair_closes_under_rule :
    argmax (A2_theta1.P.P1rule 2 ![0, 1] (liftV (lworldEval A2_Phi A2_theta1.O))) = {0} ∧
    argmax (A2_theta2.P.P1rule 2 ![0, 1] (liftV (lworldEval A2_Phi A2_theta2.O))) = {0} := by
  have key : ∀ (P : Problem (Fin 2) (Fin 2)) (V : MenuVec (Fin 2) (Fin 2)),
      (∀ s a, 0 ≤ V s a a) → (∀ s a, V s a a ≤ 1) → argmax (P.P1rule 2 ![0, 1] V) = {0} := by
    intro P V h0 h1
    have hne := argmax_nonempty (P.P1rule 2 ![0, 1] V)
    have h1' := P.ruleScore_ungated_excludes (ϖ := 2) (D := 1) (by norm_num) (by norm_num) ![0, 1] V h0 h1 0
      (by simp) 1 (by simp)
    ext a; simp only [Finset.mem_singleton]
    constructor
    · intro ha; fin_cases a
      · rfl
      · exact absurd ha h1'
    · rintro rfl
      obtain ⟨b, hb⟩ := hne
      fin_cases b
      · exact hb
      · exact absurd hb h1'
  constructor <;> apply key <;> intro s a <;> fin_cases a <;> simp [lworldEval, A2_Phi, A2_PhiOf] <;> norm_num

/-- The `[leg]`-gated plain-EU rule score `W Q a − ϖ · n a · P(L | a)`: the gated analogue of the
score in `ruleScore_EU_excludes` (the mandate's "gating the term by `[leg]`" applied to plain EU).
Source: [[corr-legit-neg-inventory]] item 012 (trap); audit r1 adversarial N1
Kind: D
Fidelity: exact -/
def gatedEUrule {S A : Type} [Fintype S] [Fintype A] (P : Problem S A) (Q : S → A → ℚ) (ϖ : ℚ)
    (n : A → ℕ) (a : A) : ℚ :=
  P.W Q a - ϖ * (n a : ℚ) * P.PL a

/-- The void-heavy instance: `π(b) = 9/10`; `a₀` legitimate everywhere with `u ≡ 0`; `a₁` void in
`b` with `u ≡ 1` (so `P(L | a₁) = 1/10`). `0 ≤ u ≤ 1`.
Source: [[corr-legit-neg-inventory]] item 012 (trap: "fails on void-heavy priors")
Kind: D
Fidelity: exact -/
def voidHeavy : Problem (Fin 2) (Fin 2) := toyB 0 1 0 1 (9/10) (by norm_num) (by norm_num)

/-- **The mandate's N− for the gate, on the plain-EU form.** With `ϖ = 2 > D = 1`, `n = (0, 1)`
and `0 ≤ u ≤ 1`, the ungated EU rule score excludes the violator `a₁` (`1 − 2 < 0`) while the
`[leg]`-gated one picks it strictly (`1 − 2 · (1/10) = 4/5 > 0`): gating fails on a void-heavy
prior under action-dependent legitimacy, exactly as the mandate's trap says. Contrast
`ruleScore_gated_excludes_of_mass_pos`: for the `P1` form gating is inert under sealing, because
`P1` is itself `[leg]`-gated (finding 13, scoped to the `P1` form by audit r1).
Source: [[corr-legit-neg-inventory]] item 012 (trap); audit r1 adversarial N1
Kind: N+
Fidelity: exact (the mandate's requested gate-failure witness, on the gated plain-EU score, not
the gated `P1` score; a strict flip, so non-degenerate) -/
theorem ruleScore_EU_gated_inverts :
    argmax (fun a => voidHeavy.W voidHeavy.u a - 2 * ((![0, 1] : Fin 2 → ℕ) a : ℚ)) = {0} ∧
    argmax (gatedEUrule voidHeavy voidHeavy.u 2 ![0, 1]) = {1} ∧
    (∀ s a, 0 ≤ voidHeavy.u s a) ∧ (∀ s a, voidHeavy.u s a ≤ 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_zero_iff]
    simp [voidHeavy, toyB, W, EU, Fin.sum_univ_two]
  · rw [argmax_fin2_eq_one_iff]
    simp [gatedEUrule, voidHeavy, toyB, W, EU, PL, mass, Fin.sum_univ_two]; norm_num
  · intro s a; fin_cases s <;> fin_cases a <;> simp [voidHeavy, toyB]
  · intro s a; fin_cases s <;> fin_cases a <;> simp [voidHeavy, toyB]

/-! ## A5: the readings D1–D4′ -/

/-- **D1** (conditional on the option): S1 on the diagonal, the outcome score.
Source: [[corr-legit-neg-inventory]] item 013
Kind: D
Fidelity: exact -/
def readD1 {S A : Type} (Q : S → A → ℚ) : MenuVec S A := S1 Q

/-- **D1, unselected options**: the realized vector with every unselected option at `1` (the
1-at-null convention applied to a refuted "`c` selected"). Degenerate by design.
Source: [[corr-legit-neg-inventory]] item 013
Kind: D
Fidelity: variant: 1-at-null convention -/
def readD1unselected {S A : Type} (Q : S → A → ℚ) (sel : A) [DecidableEq A] : S → A → ℚ :=
  fun s c => if c = sel then Q s sel else 1

/-- **D1-unselected is degenerate**: with `Q ≤ 1` the selected option is weakly worst in its own
realized vector, so selection-blindness fails and the regret comparator is vacuous.
Source: [[corr-legit-neg-inventory]] item 013 (D1 unselected row)
Kind: L
Fidelity: exact (N− by design) -/
theorem readD1unselected_selected_worst {S A : Type} [DecidableEq A] (Q : S → A → ℚ)
    (hQ : ∀ s c, Q s c ≤ 1) (sel : A) (s : S) (c : A) :
    readD1unselected Q sel s sel ≤ readD1unselected Q sel s c := by
  unfold readD1unselected
  simp only [if_true]
  split_ifs with h
  · exact le_rfl
  · exact hQ s sel

/-- **D2** (counterfactual with `L` held): the standard on `L`, selection-independent — the same
numbers as D1 on the diagonal.
Source: [[corr-legit-neg-inventory]] item 013
Kind: D
Fidelity: exact -/
def readD2 {S A : Type} (Q : S → A → ℚ) : S → A → ℚ := fun s c => Q s c

namespace Problem

variable {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)

/-- **D3** (issuance-time proposition): the prior expectation `E_π[Q(·, c)] = W Q c`, constant
across `L`-states.
Source: [[corr-legit-neg-inventory]] item 013
Kind: D
Fidelity: exact -/
def readD3 (Q : S → A → ℚ) : S → A → ℚ := fun _ c => P.W Q c

/-- **D4′** (policy-level, prior) reduces to D3 by definition.
Source: [[corr-legit-neg-inventory]] item 013 (D4′ row: "reduces to D3")
Kind: D
Fidelity: exact -/
abbrev readD4' (Q : S → A → ℚ) : S → A → ℚ := P.readD3 Q

/-- **D3 escapes A1 and A3**: under sealing with `π(L) > 0`, `J₁` of D3 is `π(L) · W`, so the
choice is `argmax W` for every `Q`.
Source: [[corr-legit-neg-inventory]] item 013 (D3 row)
Kind: L
Fidelity: exact -/
theorem argmax_readD3_eq_argmax_W {ℓ : S → Bool} (h : P.SealedBy ℓ) (hpos : 0 < P.mass ℓ)
    (Q : S → A → ℚ) : argmax (P.P1 (liftV (P.readD3 Q))) = argmax (P.W Q) :=
  P.argmax_P1_updateless_eq_argmax_W h hpos Q

end Problem

/-- **D2′** (counterfactual flipping `L`, `k` held) and **D4** (policy-level, posterior) over
the selection model: the `k`-known issuance-weighted vector `smVk`; D4 reduces to D2′.
Source: [[corr-legit-neg-inventory]] item 013 (D2′, D4 rows)
Kind: D
Fidelity: exact -/
abbrev readD2' (aW aS x hW hS δ : ℚ) : Fin 4 → Fin 2 → ℚ := smVk aW aS x hW hS δ

/-- **A5, the A1-instance cells.** On `incautionInstance (1/2) (1/10) (1/2) 1`: D1 and D2 pick
`risky`; D3 picks `safe = argmax W`.
Source: [[corr-legit-neg-inventory]] item 013 (fixture A5)
Kind: N+
Fidelity: exact -/
theorem A5_A1_cells :
    let P := incautionInstance (1/2) (1/10) (1/2) 1 (by norm_num) (by norm_num)
    argmax (P.P1 (readD1 P.u)) = {1} ∧
    argmax (P.P1 (liftV (readD2 P.u))) = {1} ∧
    argmax (P.P1 (liftV (P.readD3 P.u))) = {0} ∧ argmax (P.W P.u) = {0} := by
  intro P
  have hW : argmax (P.W P.u) = {0} := by
    rw [argmax_fin2_eq_zero_iff]; simp [P, incautionInstance, W, EU]; norm_num
  refine ⟨?_, ?_, ?_, hW⟩
  · exact incaution_argmax_risky (1/2) (1/10) (1/2) 1 (by norm_num) (by norm_num)
      (by norm_num : (1/2 : ℚ) < 1) (by norm_num : (0 : ℚ) < 1/10)
  · rw [argmax_fin2_eq_one_iff]; simp [P, incautionInstance, P1, readD2]; norm_num
  · rw [P.argmax_readD3_eq_argmax_W (incautionInstance_SealedBy _ _ _ _ _ _) ?_, hW]
    simp [P, incautionInstance, mass, legG]; norm_num

/-- **A5, the A3-instance cells.** On the selection model with `δ = 1/2`: D2′ (= D4) fails —
picks `risky` while `W` prefers `safe` — and D3 (= D4′) escapes.
Source: [[corr-legit-neg-inventory]] item 013 (A3 instance row)
Kind: N+
Fidelity: exact -/
theorem A5_A3_cells :
    let P := selectionModel (9/10) (1/10) (1/2) 0 1 (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    argmax (P.P1 (liftV (readD2' (9/10) (1/10) (1/2) 0 1 (1/2)))) = {1} ∧
    argmax (P.W P.u) = {0} ∧
    argmax (P.P1 (liftV (P.readD3 P.u))) = {0} := by
  intro P
  have h := A3_instance
  refine ⟨(h.2.2.1 (1/2)).2 (by norm_num), (h.2.2.2.1 (1/2)).2 (by norm_num), ?_⟩
  rw [P.argmax_readD3_eq_argmax_W (selectionModelWith_SealedBy _ _ _ _ _ _ _) ?_]
  · exact (h.2.2.2.1 (1/2)).2 (by norm_num)
  · rw [sm_mass_L]; norm_num

/-! ### The narrowed headline (VERIFY A5): the readings as the `c`-weights of A3b

The `ρ` clause of VERIFY's narrowed A5 is A3b (1) applied to a *local-linear reading*: evaluators
at a legitimate state in atom `G_j` report the standard's own value plus `c_j` times the harm on
their atom. Over the `Problem` of record that reading is `readLocal`; the bridge to the abstract
`(a, b, c)` of `Phi_exact_iff` is `P1_readLocal` (its `J₁` is the `L`-part of `W` plus
`Phi a c g`) and `W_eq_Lpart_add_Eg` (`W` is the `L`-part plus `Eg b g`). D2′ is this reading at
the constant weight `π(¬L)/π(L)` (`readD2'_eq_mass_mul_readLocal`), so it escapes for every harm
profile iff `L ⊥ k` (`readD2'_weights_exact_iff`). The *direct* clause (D3/D4′, and A2's inferable
vector) is not in this family: its `¬L` term is the one number `E[g · 1_{¬L}]` on every atom, not
`c_j g_j`, and it escapes by `argmax_readD3_eq_argmax_W` / `argmax_P1_inferable_eq_argmax_W`. -/

/-- **The local-linear reading** with atom weights `cw` over the `Problem` of record: at a
legitimate state `s` in atom `atom s` the evaluators report `Q s c + cw (atom s) · g c (atom s)`,
the standard's own value plus a locally weighted estimate of option `c`'s harm on their atom
(`g c : Fin J → ℚ`, the harm profile across atoms). D3 is *not* of this form (see the section
docstring).
Source: VERIFY A "A5: narrowed"; [[corr-legit-neg-inventory]] item 010
Kind: D
Fidelity: exact -/
def readLocal {S A : Type} {J : ℕ} (atom : S → Fin J) (cw : Fin J → ℚ) (Q : S → A → ℚ)
    (g : A → Fin J → ℚ) : S → A → ℚ :=
  fun s c => Q s c + cw (atom s) * g c (atom s)

/-- The harm profile `g` is the standard off `L`: `Q s c = g c (atom s)` on every void state
(`Q`'s `¬L` part is `𝒢`-measurable, as A3b assumes).
Source: [[corr-legit-neg-inventory]] item 010
Kind: D
Fidelity: exact -/
def AtomProfile {S A : Type} (ℓ : S → Bool) {J : ℕ} (atom : S → Fin J) (Q : S → A → ℚ)
    (g : A → Fin J → ℚ) : Prop :=
  ∀ s c, ℓ s = false → Q s c = g c (atom s)

namespace Problem

variable {S A : Type} [Fintype S] [Fintype A] (P : Problem S A)

/-- **Bridge, first half.** Under sealing, `J₁` of the local-linear reading is the `L`-part of
`W Q` plus the estimator's aggregate `Phi a cw (g c)` with `a_j = π(L ∩ G_j)`.
Source: VERIFY A "A5: narrowed"; [[corr-legit-neg-inventory]] item 010
Kind: L
Fidelity: exact -/
theorem P1_readLocal {ℓ : S → Bool} (h : P.SealedBy ℓ) {J : ℕ} (atom : S → Fin J)
    (cw : Fin J → ℚ) (Q : S → A → ℚ) (g : A → Fin J → ℚ) (c : A) :
    P.P1 (liftV (readLocal atom cw Q g)) c
      = (∑ s, P.prior s * ind (ℓ s) * Q s c) + Phi (P.atomMass ℓ atom) cw (g c) := by
  rw [P.P1_liftV_of_SealedBy h]
  unfold J1 readLocal Phi
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  exact (P.sum_atom ℓ atom (fun j => cw j * g c j)).trans
    (Finset.sum_congr rfl fun j _ => by ring)

/-- **Bridge, second half.** When the standard off `L` is the atom profile `g`, `W Q c` is the
`L`-part plus the prior's `¬L`-integral `Eg b (g c)` with `b_j = π(¬L ∩ G_j)`.
Source: VERIFY A "A5: narrowed"; [[corr-legit-neg-inventory]] item 010
Kind: L
Fidelity: exact -/
theorem W_eq_Lpart_add_Eg (ℓ : S → Bool) {J : ℕ} (atom : S → Fin J) (Q : S → A → ℚ)
    (g : A → Fin J → ℚ) (hg : AtomProfile ℓ atom Q g) (c : A) :
    P.W Q c = (∑ s, P.prior s * ind (ℓ s) * Q s c)
      + Eg (P.atomMass (fun s => !ℓ s) atom) (g c) := by
  rw [P.W_split Q ℓ c]
  congr 1
  unfold Eg
  rw [← P.sum_atom (fun s => !ℓ s) atom (g c)]
  refine Finset.sum_congr rfl fun s _ => ?_
  cases hs : ℓ s
  · rw [hg s c hs]
  · simp [ind]

/-- **A5, narrowed headline (VERIFY A5), the `ρ` clause over the `Problem` of record.** Under
sealing, the local-linear reading with atom weights `cw` reproduces the yardstick — `J₁ = W Q`
for every standard `Q` whose `¬L` part is an atom profile, i.e. it escapes A1–A3 for *every* harm
profile — iff `π(L ∩ G_j) · cw_j = π(¬L ∩ G_j)` on every atom: its `¬L` term is integrated
against the prior's `¬L` law. The abstract content is A3b (1), `Phi_exact_iff`; the bridge is
`P1_readLocal` and `W_eq_Lpart_add_Eg`. The direct clause (D3/D4′) is `argmax_readD3_eq_argmax_W`,
not an instance of this family. The source's original "exactly when not conditioned on `L`" is
not proved (finding 7). `Nonempty A` is needed only for the forward direction (a test standard
must be evaluated at some option).
Source: VERIFY A "A5: narrowed"; [[corr-legit-neg-inventory]] item 010
Kind: C
Fidelity: exact (the narrowed statement; equality of scores, hence of choices)
Hyps: (a) all -/
theorem readLocal_exact_iff [Nonempty A] {ℓ : S → Bool} (h : P.SealedBy ℓ) {J : ℕ}
    (atom : S → Fin J) (cw : Fin J → ℚ) :
    (∀ (Q : S → A → ℚ) (g : A → Fin J → ℚ), AtomProfile ℓ atom Q g →
        ∀ c, P.P1 (liftV (readLocal atom cw Q g)) c = P.W Q c)
      ↔ ∀ j, P.atomMass ℓ atom j * cw j = P.atomMass (fun s => !ℓ s) atom j := by
  rw [← Phi_exact_iff]
  constructor
  · intro hx g₀
    obtain ⟨c₀⟩ := ‹Nonempty A›
    have hprof : AtomProfile ℓ atom (fun s (_ : A) => if ℓ s then (0 : ℚ) else g₀ (atom s))
        (fun (_ : A) => g₀) :=
      fun s _ hs => by simp [hs]
    have := hx _ _ hprof c₀
    rw [P.P1_readLocal h, P.W_eq_Lpart_add_Eg ℓ atom _ _ hprof] at this
    exact add_left_cancel this
  · intro hx Q g hg c
    rw [P.P1_readLocal h, P.W_eq_Lpart_add_Eg ℓ atom Q g hg, hx (g c)]

/-- **The escape.** With exact weights, the local-linear reading makes P1 and P2 choose
`argmax W` for every standard whose `¬L` part is an atom profile.
Source: VERIFY A "A5: narrowed"
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem argmax_readLocal_eq_argmax_W_of_exact {ℓ : S → Bool} (h : P.SealedBy ℓ)
    (hpos : 0 < P.mass ℓ) {J : ℕ} (atom : S → Fin J) (cw : Fin J → ℚ)
    (hc : ∀ j, P.atomMass ℓ atom j * cw j = P.atomMass (fun s => !ℓ s) atom j)
    (Q : S → A → ℚ) (g : A → Fin J → ℚ) (hg : AtomProfile ℓ atom Q g) :
    argmax (P.P1 (liftV (readLocal atom cw Q g))) = argmax (P.W Q) ∧
    argmaxOpt (P.P2 (liftV (readLocal atom cw Q g))) = argmax (P.W Q) := by
  have hP1 : ∀ c, P.P1 (liftV (readLocal atom cw Q g)) c = P.W Q c := fun c => by
    rw [P.P1_readLocal h, P.W_eq_Lpart_add_Eg ℓ atom Q g hg, (Phi_exact_iff _ _ _).2 hc (g c)]
  refine ⟨argmax_congr hP1, ?_⟩
  rw [P.argmaxOpt_P2_eq_argmax_P1_of_SealedBy h hpos, argmax_congr hP1]

/-- **A5 narrowed, the absolute-continuity clause.** Some local-linear reading escapes for every
harm profile iff no atom carries `¬L`-mass without `L`-mass; the weights are then
`ρ_j = π(¬L ∩ G_j) / π(L ∩ G_j)` on supported atoms (D2′ reweighted by `ρ`; A3b (2)).
Source: VERIFY A "A5: narrowed"; [[corr-legit-neg-inventory]] item 010 (2)
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem exists_readLocal_exact_iff [Nonempty A] {ℓ : S → Bool} (h : P.SealedBy ℓ) {J : ℕ}
    (atom : S → Fin J) :
    (∃ cw : Fin J → ℚ, ∀ (Q : S → A → ℚ) (g : A → Fin J → ℚ), AtomProfile ℓ atom Q g →
        ∀ c, P.P1 (liftV (readLocal atom cw Q g)) c = P.W Q c)
      ↔ ∀ j, P.atomMass ℓ atom j = 0 → P.atomMass (fun s => !ℓ s) atom j = 0 := by
  rw [← exists_Phi_exact_iff]
  exact exists_congr fun cw => (P.readLocal_exact_iff h atom cw).trans (Phi_exact_iff _ _ _).symm

end Problem

/-- `(k, N)`, the void state of adversary strength `k` (`W ↦ 1`, `S ↦ 3`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def smNof : Fin 2 → Fin 4 := ![1, 3]

/-- **D2′ is the local-linear reading at the constant weight `π(¬L)/π(L)`**, scaled by `π(L)`:
on the selection model with `p = π(L) = (aW + aS)/2 ≠ 0`, `smVk s a = p · readLocal smK (π(¬L)/π(L)) Q g s a`
with `g a k = Q (k, N) a`, and `Q`'s `¬L` part is that atom profile.
Source: [[corr-legit-neg-2-inventory]] item 2-009; VERIFY A "A5: narrowed"
Kind: L
Fidelity: exact -/
theorem readD2'_eq_mass_mul_readLocal (aW aS x hW hS δ : ℚ) (hp : (aW + aS) / 2 ≠ 0) :
    (∀ s a, readD2' aW aS x hW hS δ s a
        = (aW + aS) / 2 * readLocal smK (fun _ => (1 - (aW + aS) / 2) / ((aW + aS) / 2))
            (smQ x δ hW hS) (fun a k => smQ x δ hW hS (smNof k) a) s a) ∧
    AtomProfile smL smK (smQ x δ hW hS) (fun a k => smQ x δ hW hS (smNof k) a) := by
  constructor
  · intro s a
    have hN : smNof (smK s) = smN s := by fin_cases s <;> rfl
    have hs : aW + aS ≠ 0 := fun h => hp (by rw [h]; norm_num)
    unfold readD2' smVk readLocal
    dsimp only
    rw [hN]
    field_simp
  · intro s a hs
    fin_cases s <;> simp [smL] at hs ⊢ <;> rfl

section D2prime

variable (aW aS x hW hS δ : ℚ) (hW0 : 0 ≤ aW) (hW1 : aW ≤ 1) (hS0 : 0 ≤ aS) (hS1 : aS ≤ 1)

/-- The selection model's atom masses over `k`: `a = (aW/2, aS/2)`, `b = ((1 − aW)/2, (1 − aS)/2)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma sm_atomMass :
    (∀ j, (selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1).atomMass smL smK j = ![aW / 2, aS / 2] j) ∧
    (∀ j, (selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1).atomMass (fun s => !smL s) smK j
      = ![(1 - aW) / 2, (1 - aS) / 2] j) := by
  constructor <;> intro j <;> fin_cases j <;>
    simp [selectionModel, selectionModelWith, atomMass, mass, smL, smK, Fin.sum_univ_four]

/-- **D2′ escapes A3 for every harm profile iff `L ⊥ k`.** The `c`-weights criterion for D2′'s
constant weight `π(¬L)/π(L)` on the selection model's atoms `k ∈ {W, S}` holds iff `aW = aS`
(A3b (3): the constant reweighting is exact iff `L` is independent of the atoms).
Source: VERIFY A "A5: narrowed"; [[corr-legit-neg-inventory]] item 010 (3)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem readD2'_weights_exact_iff (hpos : 0 < aW + aS) :
    (∀ j, (selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1).atomMass smL smK j
          * ((1 - (aW + aS) / 2) / ((aW + aS) / 2))
        = (selectionModel aW aS x hW hS δ hW0 hW1 hS0 hS1).atomMass (fun s => !smL s) smK j)
      ↔ aW = aS := by
  obtain ⟨ha, hb⟩ := sm_atomMass aW aS x hW hS δ hW0 hW1 hS0 hS1
  simp only [ha, hb]
  have hp : (aW + aS) / 2 ≠ 0 := by intro h; linarith
  constructor
  · intro h
    have h0 := h 0
    simp at h0
    field_simp at h0
    nlinarith [h0]
  · rintro rfl j
    have haW : aW ≠ 0 := fun h => hp (by rw [h]; norm_num)
    fin_cases j <;> simp <;> field_simp

/-- **D2′ escapes when `L ⊥ k`**: with `aW = aS`, D2′'s choice is `argmax W` for every
`x, hW, hS, δ` (the window of `sm_window` is empty).
Source: VERIFY A "A5: narrowed"; [[corr-legit-neg-2-inventory]] item 2-009
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem readD2'_escapes_of_indep (hpos : 0 < aW) :
    let P := selectionModel aW aW x hW hS δ hW0 hW1 hW0 hW1
    argmax (P.P1 (liftV (readD2' aW aW x hW hS δ))) = argmax (P.W P.u) := by
  intro P
  have hp : (aW + aW) / 2 ≠ 0 := by intro h; linarith
  obtain ⟨hV, hg⟩ := readD2'_eq_mass_mul_readLocal aW aW x hW hS δ hp
  have hc := (readD2'_weights_exact_iff aW aW x hW hS δ hW0 hW1 hW0 hW1 (by linarith)).2 rfl
  have hesc := (P.argmax_readLocal_eq_argmax_W_of_exact (selectionModelWith_SealedBy _ _ _ _ _ _ _)
    (by rw [sm_mass_L]; linarith) smK _ hc _ _ hg).1
  have hscale : ∀ c, P.P1 (liftV (readD2' aW aW x hW hS δ)) c
      = P.P1 (liftV (readLocal smK (fun _ => (1 - (aW + aW) / 2) / ((aW + aW) / 2))
          (smQ x δ hW hS) (fun a k => smQ x δ hW hS (smNof k) a))) c * ((aW + aW) / 2) := by
    intro c
    unfold P1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [liftV_apply, liftV_apply, hV s c]; ring
  rw [argmax_congr hscale, argmax_mul_pos _ (by linarith)]
  exact hesc

/-- **A3's window is non-empty as soon as `E[h | L] < E[h | ¬L]`**: some `δ` makes D2′ strictly
pick `risky` while `W` strictly picks `safe` (`δ` at the midpoint of `sm_window`'s window).
Source: [[corr-legit-neg-2-inventory]] item 2-009
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem sm_window_nonempty (hpos : 0 < aW + aS) (hpos' : 0 < 2 - aW - aS)
    (hlt : (aW * hW + aS * hS) / (aW + aS)
      < ((1 - aW) * hW + (1 - aS) * hS) / (2 - aW - aS)) :
    ∃ δ₀ : ℚ, argmax ((selectionModel aW aS x hW hS δ₀ hW0 hW1 hS0 hS1).P1
        (liftV (readD2' aW aS x hW hS δ₀))) = {1} ∧
      argmax ((selectionModel aW aS x hW hS δ₀ hW0 hW1 hS0 hS1).W
        (selectionModel aW aS x hW hS δ₀ hW0 hW1 hS0 hS1).u) = {0} := by
  obtain ⟨δ₀, hδ⟩ : ∃ δ₀ : ℚ, δ₀ = (1 - (aW + aS) / 2)
      * ((aW * hW + aS * hS) / (aW + aS) + ((1 - aW) * hW + (1 - aS) * hS) / (2 - aW - aS))
      / (aW + aS) := ⟨_, rfl⟩
  have hne1 : aW + aS ≠ 0 := hpos.ne'
  have hne2 : 2 - aW - aS ≠ 0 := hpos'.ne'
  have hp1 : 0 < 1 - (aW + aS) / 2 := by linarith
  have key : (aW + aS) / 2 * δ₀ = (1 - (aW + aS) / 2)
      * ((aW * hW + aS * hS) / (aW + aS) + ((1 - aW) * hW + (1 - aS) * hS) / (2 - aW - aS))
      / 2 := by
    rw [hδ]; field_simp
  have hgap := mul_pos hp1 (sub_pos.2 hlt)
  have hw := sm_window aW aS x hW hS δ₀ hW0 hW1 hS0 hS1 hpos hpos'
  simp only at hw
  refine ⟨δ₀, hw.1.2 ?_, hw.2.1.2 ?_⟩
  · rw [key]; nlinarith [hgap]
  · rw [key]; nlinarith [hgap]

/-- **D2′ fails whenever `L` and `k` are dependent.** With `aW ≠ aS` (both in `[0, 1]`) there are
a harm profile `(hW, hS) ∈ {(1, 0), (0, 1)}` and a `δ` at which D2′ strictly picks `risky` while
`W` strictly picks `safe`: `E[h | L] < E[h | ¬L]` for the profile that loads the harm on the
strength `L` under-represents.
Source: VERIFY A "A5: narrowed"; [[corr-legit-neg-2-inventory]] item 2-009
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem readD2'_fails_of_dep (hne : aW ≠ aS) :
    ∃ hW' hS' δ' : ℚ, argmax ((selectionModel aW aS x hW' hS' δ' hW0 hW1 hS0 hS1).P1
        (liftV (readD2' aW aS x hW' hS' δ'))) = {1} ∧
      argmax ((selectionModel aW aS x hW' hS' δ' hW0 hW1 hS0 hS1).W
        (selectionModel aW aS x hW' hS' δ' hW0 hW1 hS0 hS1).u) = {0} := by
  have hpos : 0 < aW + aS := by
    rcases (add_nonneg hW0 hS0).lt_or_eq with h | h
    · exact h
    · exact absurd (by linarith : aW = aS) hne
  have hpos' : 0 < 2 - aW - aS := by
    rcases (by linarith : (0 : ℚ) ≤ 2 - aW - aS).lt_or_eq with h | h
    · exact h
    · exact absurd (by linarith : aW = aS) hne
  have hne1 : aW + aS ≠ 0 := hpos.ne'
  have hne2 : 2 - aW - aS ≠ 0 := hpos'.ne'
  rcases lt_or_gt_of_ne hne with h | h
  · refine ⟨1, 0, ?_⟩
    apply sm_window_nonempty aW aS x 1 0 hW0 hW1 hS0 hS1 hpos hpos'
    apply lt_of_sub_pos
    have hdiff : ((1 - aW) * 1 + (1 - aS) * 0) / (2 - aW - aS) - (aW * 1 + aS * 0) / (aW + aS)
        = (aS - aW) / ((2 - aW - aS) * (aW + aS)) := by
      field_simp; ring
    rw [hdiff]
    exact div_pos (by linarith) (mul_pos hpos' hpos)
  · refine ⟨0, 1, ?_⟩
    apply sm_window_nonempty aW aS x 0 1 hW0 hW1 hS0 hS1 hpos hpos'
    apply lt_of_sub_pos
    have hdiff : ((1 - aW) * 0 + (1 - aS) * 1) / (2 - aW - aS) - (aW * 0 + aS * 1) / (aW + aS)
        = (aW - aS) / ((2 - aW - aS) * (aW + aS)) := by
      field_simp; ring
    rw [hdiff]
    exact div_pos (by linarith) (mul_pos hpos' hpos)

/-- **D2′ escapes A3 for every harm profile iff `L ⊥ k`** — at the level of choices. With
`π(L) > 0`: D2′'s choice is `argmax W` for every `hW, hS, δ` iff `aW = aS`. The `⟸` is
`readD2'_escapes_of_indep` (through the `c`-weights criterion `readD2'_weights_exact_iff`), the
`⟹` is `readD2'_fails_of_dep`. Positivity is needed: at `aW = aS = 0` the weights are exact
vacuously but `P1 ≡ 0` ties the menu while `W` does not.
Source: VERIFY A "A5: narrowed"; [[corr-legit-neg-2-inventory]] item 2-009
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem readD2'_escapes_iff (hpos : 0 < aW + aS) :
    (∀ hW' hS' δ' : ℚ, argmax ((selectionModel aW aS x hW' hS' δ' hW0 hW1 hS0 hS1).P1
          (liftV (readD2' aW aS x hW' hS' δ')))
        = argmax ((selectionModel aW aS x hW' hS' δ' hW0 hW1 hS0 hS1).W
          (selectionModel aW aS x hW' hS' δ' hW0 hW1 hS0 hS1).u))
      ↔ aW = aS := by
  constructor
  · intro hall
    by_contra hne
    obtain ⟨hW', hS', δ', h1, h0⟩ := readD2'_fails_of_dep aW aS x hW0 hW1 hS0 hS1 hne
    have := hall hW' hS' δ'
    rw [h1, h0] at this
    exact absurd this (by decide)
  · rintro rfl hW' hS' δ'
    exact readD2'_escapes_of_indep aW x hW' hS' δ' hW0 hW1 (by linarith)

end D2prime

/-! ## A6: sufficiency, non-dispensability, the issuance-weight identity, the positive boundary -/

/-- **A6, sufficiency.** If the consulted `L`-world numbers aggregate to `π(L) · W b` — which the
inferable vector does (`P1_inferable_eq_mass_mul_W`, where the composition lives) — P1 and P2
choose `argmax W` (the A2 converse restated; from its hypothesis this is one `argmax_mul_pos`
plus A0, hence kind L).
Source: [[corr-legit-neg-inventory]] item 014 (sufficiency)
Kind: L
Fidelity: exact
Hyps: (a) all -/
theorem A6_sufficiency {S A : Type} [Fintype S] [Fintype A] (P : Problem S A) {ℓ : S → Bool}
    (h : P.SealedBy ℓ) (hpos : 0 < P.mass ℓ) (Q : S → A → ℚ) (V : S → A → ℚ)
    (hV : ∀ b, P.P1 (liftV V) b = P.mass ℓ * P.W Q b) :
    argmax (P.P1 (liftV V)) = argmax (P.W Q) ∧ argmaxOpt (P.P2 (liftV V)) = argmax (P.W Q) := by
  have h1 : argmax (P.P1 (liftV V)) = argmax (P.W Q) := by
    rw [argmax_congr hV]
    have : (fun b => P.mass ℓ * P.W Q b) = fun b => P.W Q b * P.mass ℓ := funext fun b => mul_comm _ _
    rw [this, argmax_mul_pos _ hpos]
  exact ⟨h1, by rw [P.argmaxOpt_P2_eq_argmax_P1_of_SealedBy h hpos, h1]⟩

/-- Evaluators on the legitimate state `g` who weight the `¬L` consequence by `w`:
`V_w a = (1 − w) Q(g, a) + w Q(b, a)` (two-state instances).
Source: [[corr-legit-neg-2-inventory]] item 2-011
Kind: D
Fidelity: exact -/
def weightedVec (w : ℚ) (Q : Fin 2 → Fin 2 → ℚ) : Fin 2 → Fin 2 → ℚ :=
  fun _ a => (1 - w) * Q 0 a + w * Q 1 a

/-- **A6, the issuance-weight identity (item 2-011).** On `incautionInstance`, `J₁ a = π(g) · EU_{(1−w, w)} a`:
the choice tracks expected utility under the prior `(1 − w, w)` the evaluators use, whatever
that prior is.
Source: [[corr-legit-neg-2-inventory]] item 2-011
Kind: L
Fidelity: exact -/
theorem P1_weighted_eq_mass_mul_EU (q δ x harm w : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (a : Fin 2) :
    let P := incautionInstance q δ x harm h0 h1
    P.P1 (liftV (weightedVec w P.u)) a = (1 - q) * EU ![1 - w, w] P.u a := by
  intro P
  simp [P, incautionInstance, P1, weightedVec, EU]

/-- `argmax_P1_weighted_eq_argmax_EU`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem argmax_P1_weighted_eq_argmax_EU (q δ x harm w : ℚ) (h0 : 0 ≤ q) (h1 : q < 1) :
    let P := incautionInstance q δ x harm h0 h1.le
    argmax (P.P1 (liftV (weightedVec w P.u))) = argmax (EU ![1 - w, w] P.u) := by
  intro P
  rw [argmax_congr (fun a => P1_weighted_eq_mass_mul_EU q δ x harm w h0 h1.le a)]
  have : (fun a => (1 - q) * EU ![1 - w, w] P.u a) = fun a => EU ![1 - w, w] P.u a * (1 - q) :=
    funext fun a => mul_comm _ _
  rw [this, argmax_mul_pos _ (by linarith)]

/-- **A6, the weight threshold (non-dispensability of the ex-ante weight, strengthened).** On
`incautionInstance (9/10) (1/5) (1/2) (1/20)`, evaluators using weight `w` pick `safe` strictly
iff `w > δ/(δ + harm) = 4/5`, and `risky` strictly iff `w < 4/5`. Hence weights `0` and `1/2`
pick `risky`, the issuance weight `9/10` picks `safe`.
Source: [[corr-legit-neg-inventory]] item 014 (ingredient 3); VERIFY A "A6" (any weight above 4/5)
Kind: P
Fidelity: exact (stronger than the source's three points) -/
theorem A6_weight_threshold (w : ℚ) :
    let P := incautionInstance (9/10) (1/5) (1/2) (1/20) (by norm_num) (by norm_num)
    (argmax (P.P1 (liftV (weightedVec w P.u))) = {0} ↔ 4/5 < w) ∧
    (argmax (P.P1 (liftV (weightedVec w P.u))) = {1} ↔ w < 4/5) := by
  intro P
  constructor
  · rw [argmax_fin2_eq_zero_iff]; simp [P, incautionInstance, P1, weightedVec]
    constructor <;> intro h <;> nlinarith
  · rw [argmax_fin2_eq_one_iff]; simp [P, incautionInstance, P1, weightedVec]
    constructor <;> intro h <;> nlinarith

/-- `A6_weight_points`: supporting lemma (no headline; see the file docstring).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem A6_weight_points :
    let P := incautionInstance (9/10) (1/5) (1/2) (1/20) (by norm_num) (by norm_num)
    argmax (P.P1 (liftV (weightedVec 0 P.u))) = {1} ∧
    argmax (P.P1 (liftV (weightedVec (1/2) P.u))) = {1} ∧
    argmax (P.P1 (liftV (weightedVec (9/10) P.u))) = {0} := by
  intro P
  exact ⟨(A6_weight_threshold 0).2.2 (by norm_num), (A6_weight_threshold (1/2)).2.2 (by norm_num),
    (A6_weight_threshold (9/10)).1.2 (by norm_num)⟩

/-- **A6, V5: the yardstick's prior decides the right weight.** With the agent's `π(¬L) = 1/2`
and the humans' ex-ante `μ(¬L) = 9/10` (`δ = 1/5`, `harm = 1/20`): `W_π` prefers `risky`, `W_μ`
prefers `safe`; the agent's issuance weight tracks `W_π`, the humans' weight tracks `W_μ`.
The required weight is that of whichever ex-ante prior defines the standard (finding 8).
Source: VERIFY A "A6: narrowed (i)" (V5); [[corr-legit-neg-2-inventory]] item 2-011
Kind: N+
Fidelity: exact -/
theorem A6_V5_yardstick_prior :
    let P := incautionInstance (1/2) (1/5) (1/2) (1/20) (by norm_num) (by norm_num)
    argmax (P.W P.u) = {1} ∧ argmax (EU ![1/10, 9/10] P.u) = {0} ∧
    argmax (P.P1 (liftV (weightedVec (1/2) P.u))) = {1} ∧
    argmax (P.P1 (liftV (weightedVec (9/10) P.u))) = {0} := by
  intro P
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [argmax_fin2_eq_one_iff]; simp [P, incautionInstance, W, EU]; norm_num
  · rw [argmax_fin2_eq_zero_iff]; simp [P, incautionInstance, EU]; norm_num
  · rw [argmax_fin2_eq_one_iff]; simp [P, incautionInstance, P1, weightedVec]; norm_num
  · rw [argmax_fin2_eq_zero_iff]; simp [P, incautionInstance, P1, weightedVec]; norm_num

/-- **A6, the positive boundary.** Under `SealedBy ℓ` with `0 < π(L)`: `P(L | ·)` is constant
(no steering, no news management), P1 and P2 share the argmax for every vector, and T2 with the
branch known to be in `L` is exact for every vector — ordinal S3 included: the third conjunct
holds for every `V`. V1's exception concerns the *vector*, not T2 exactness: the ordinal-S3 vector
is not the standard, so its T1 choice distorts `W` even at `π(¬L) = 0`
(`A1_ordinal_breaks_bound`).
Source: [[corr-legit-neg-inventory]] item 014 (positive boundary); VERIFY A "A6, narrowing (ii)"
Kind: L
Fidelity: exact (ordinal S3 excepted, as V1 narrows) -/
theorem A6_positive_boundary {S A : Type} [Fintype S] [Fintype A] [DecidableEq S] (P : Problem S A)
    {ℓ : S → Bool} (h : P.SealedBy ℓ) (hpos : 0 < P.mass ℓ) :
    (∀ a a', P.PL a = P.PL a') ∧
    (∀ V : MenuVec S A, argmaxOpt (P.P2 V) = argmax (P.P1 V)) ∧
    (∀ (s : S) (hs : 0 < P.prior s), ℓ s = true → ∀ (V : MenuVec S A) (a : A),
      (P.restrict {s} (by simpa using hs)).P1 V a = V s a a) :=
  ⟨P.PL_const_of_SealedBy h, fun V => P.argmaxOpt_P2_eq_argmax_P1_of_SealedBy h hpos V,
    fun s hs hl V a => P.restrict_singleton_P1_of_leg h s hs hl V a⟩

end Cleanroom.Corrigibility.LegitNegStatic
