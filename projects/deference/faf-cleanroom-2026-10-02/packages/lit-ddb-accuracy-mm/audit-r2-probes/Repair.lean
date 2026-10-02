import Cleanroom.Lit.LitDdbAccuracyMm

/-!
# lit-ddb-accuracy-mm — audit round 2 (adversarial), probe: the repair

Not imported by the library. Elaborated with `scripts/lean-check`.

Round 1's blocking issues were the class of `EpistemicValueOn` (B1) and two degenerate refutation
witnesses (B2). This probe attacks the repair:

1. `IsGspOn.valueDirectedOn` (the former (b), now derived) is not an equivalence in disguise: the
   derived predicate `ValueDirectedOn` is strictly weaker than `IsGspOn` (absolute loss is
   value-directed but not gsp on the range), and it is not trivially true (negated Brier fails it).
   So deriving it from gsp has content, and the class `IsGsp` alone is the right one.
2. The refutation of the transcriber's `(x − t)` integrand (`xt_rule_thm79_refuted`) checks Theorem
   7.9's monotonicity hypothesis only at the attained true values `k ∈ {0, 2}`
   (`ValueDirectedOn Xxt`). Here it is checked for every true value `k ≥ 0` (per side). And the
   reading matters: read *across* sides ("`I(x, y)` strictly increasing as `|x − y|` increases",
   no side restriction), the hypothesis fails for the transcriber's rule at `k = 1` — but it also
   fails for DDB's own `(t − k)` family with the same non-uniform `λ = (1 + t) dt`, a member that is
   gsp on the range (proved below). So the cross-side reading would make Theorem 7.9 false for its
   own family, and the per-side reading (value-directedness) is the only tenable one.
3. `mm34_backward_refuted`'s `StrictAgree unif3 G3` is a real constraint, not a vacuity of the
   guard or of the antecedent: the guard is positive, the antecedent is inhabited, and a nearby
   non-twin frame with agent beliefs `(7/10, 2/10, 1/10)` fails it. On the tie menu `{ftf, fft}`
   the principal is also indifferent, so the valuing failure is purely world-dependent
   tie-breaking, which is the reading under attack.
4. Degenerate boundaries of the range-restricted class (documented, not flaws): for a constant
   variable every rule is `IsGspOn` and Total Trust holds, so the range form of Theorem 3.2 says
   nothing there — consistently.
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm.AuditR2

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples
  Cleanroom.Lit.LitDdbAccuracyMm Cleanroom.Lit.LitDdbAccuracyMm.MM

noncomputable section

/-! ## 1. The derived value-directedness is strictly weaker than gsp on the range -/

/-- Absolute loss `|x − k|`, written with `max` so that `norm_num` evaluates it. -/
def absRule : Rule := fun x k => max (x - k) (k - x)

/-- Absolute loss is value-directed on all of `ℝ` (hence on every value range). -/
theorem absRule_valueDirected (X : Fin 2 → ℝ) : ValueDirected X absRule := by
  intro w e₁ e₂
  constructor
  · rintro ⟨h12, h2⟩
    simp only [absRule]
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    linarith
  · rintro ⟨h2, h21⟩
    simp only [absRule]
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    linarith

theorem absRule_valueDirectedOn : ValueDirectedOn Xxt absRule :=
  (absRule_valueDirected Xxt).valueDirectedOn

/-- Absolute loss is not gsp on the range of `Xxt = (0, 2)`: under `πxt = (3/4, 1/4)` the
estimate `0` (in the range) beats the mean `1/2`: `E(I(0)) = 1/2 < 3/4 = E(I(1/2))`. -/
theorem absRule_not_isGspOn : ¬ IsGspOn Xxt absRule := by
  intro h
  have he : E πxt Xxt = 1 / 2 := xt_values.1
  have := h πxt πxt_mem 0 ⟨0, by norm_num [Xxt]⟩ ⟨1, by norm_num [Xxt]⟩ (by rw [he]; norm_num)
  rw [he] at this
  simp only [expInacc, Fin.sum_univ_two, πxt, Xxt, absRule, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons] at this
  norm_num [max_def] at this

/-- So the converse of `IsGspOn.valueDirectedOn` fails: the derivation has content. -/
theorem valueDirectedOn_not_imp_isGspOn :
    ∃ I : Rule, ValueDirectedOn Xxt I ∧ ¬ IsGspOn Xxt I :=
  ⟨absRule, absRule_valueDirectedOn, absRule_not_isGspOn⟩

/-- `ValueDirectedOn` is not trivially true: negated Brier fails clause 1 at `e₁ = 0 < e₂ = 1 ≤
X 1 = 2`. -/
theorem negBrier_not_valueDirectedOn : ¬ ValueDirectedOn Xxt (fun x k => -(x - k) ^ 2) := by
  intro h
  have := (h 1 0 1).1 ⟨0, by norm_num [Xxt]⟩ (by norm_num) (by norm_num [Xxt])
  norm_num [Xxt] at this

/-! ## 2. Theorem 7.9's monotonicity hypothesis: every true value, and the reading -/

/-- The transcriber's rule in closed form. -/
theorem xtRule_closed (x k : ℝ) :
    xtRule x k = x ^ 2 / 2 + x ^ 3 / 6 - x * k - x * k ^ 2 / 2 + k ^ 2 / 2 + k ^ 3 / 3 := by
  unfold xtRule Fxt; ring

/-- The increment factorises with the sign of `x₂ − x₁`. -/
theorem xtRule_sub (x₁ x₂ k : ℝ) :
    xtRule x₂ k - xtRule x₁ k =
      (x₂ - x₁) * ((x₂ + x₁) / 2 + (x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2) / 6 - k - k ^ 2 / 2) := by
  unfold xtRule Fxt; ring

/-- Above the true value `k ≥ 0`, `xtRule` is strictly increasing in the estimate. -/
theorem xtRule_incr_above {k x₁ x₂ : ℝ} (hk : 0 ≤ k) (h1 : k ≤ x₁) (h12 : x₁ < x₂) :
    xtRule x₁ k < xtRule x₂ k := by
  have h2 : k < x₂ := by linarith
  have a1 : k ^ 2 ≤ x₁ ^ 2 := by nlinarith
  have a2 : k ^ 2 ≤ x₁ * x₂ := by nlinarith
  have a3 : k ^ 2 ≤ x₂ ^ 2 := by nlinarith
  have hb : 0 < (x₂ + x₁) / 2 + (x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2) / 6 - k - k ^ 2 / 2 := by linarith
  rw [← sub_pos, xtRule_sub]
  exact mul_pos (by linarith) hb

/-- Below the true value `k`, on nonnegative estimates, `xtRule` is strictly decreasing in the
estimate (so strictly increasing in `|x − k|`). -/
theorem xtRule_decr_below {k x₁ x₂ : ℝ} (h0 : 0 ≤ x₁) (h12 : x₁ < x₂) (h2 : x₂ ≤ k) :
    xtRule x₂ k < xtRule x₁ k := by
  have a1 : x₁ ^ 2 ≤ k ^ 2 := by nlinarith
  have a2 : x₁ * x₂ ≤ k ^ 2 := by nlinarith
  have a3 : x₂ ^ 2 ≤ k ^ 2 := by nlinarith
  have hb : (x₂ + x₁) / 2 + (x₂ ^ 2 + x₁ * x₂ + x₁ ^ 2) / 6 - k - k ^ 2 / 2 < 0 := by linarith
  rw [← sub_neg, xtRule_sub]
  exact mul_neg_of_pos_of_neg (by linarith) hb

/-- **Per-side monotonicity for every true value in `[0, 2]`**, not only `k ∈ {0, 2}`: the
strengthening of `xtRule_valueDirectedOn` that Theorem 7.9's hypothesis (a function on
`[v₀, vₙ] × [v₀, vₙ]`) actually asks for. -/
theorem xtRule_monotone_all_k :
    ∀ k, 0 ≤ k → k ≤ 2 → ∀ x₁ x₂, 0 ≤ x₁ → x₁ < x₂ → x₂ ≤ 2 →
      (k ≤ x₁ → xtRule x₁ k < xtRule x₂ k) ∧ (x₂ ≤ k → xtRule x₂ k < xtRule x₁ k) :=
  fun k hk _ x₁ x₂ h0 h12 _ =>
    ⟨fun h1 => xtRule_incr_above hk h1 h12, fun h2 => xtRule_decr_below h0 h12 h2⟩

/-- **The cross-side reading fails for the transcriber's rule** at `k = 1`: `|3/2 − 1| = 1/2 <
51/100 = |49/100 − 1|`, yet `I(3/2, 1) = 13/48 > I(49/100, 1)`. -/
theorem xtRule_not_cross_side :
    |(3 / 2 : ℝ) - 1| < |(49 / 100 : ℝ) - 1| ∧ xtRule (49 / 100) 1 < xtRule (3 / 2) 1 := by
  constructor
  · norm_num [abs_of_nonneg, abs_of_nonpos]
  · rw [xtRule_closed, xtRule_closed]; norm_num

/-- DDB's own family with the same non-uniform `λ = (1 + t) dt`: `J(x, k) = ∫_k^x (t − k)(1 + t) dt`
in closed form. -/
def tkRule : Rule := fun x k =>
  x ^ 2 / 2 + x ^ 3 / 3 - k * x - k * x ^ 2 / 2 + k ^ 2 / 2 + k ^ 3 / 6

/-- Sanity: `J(x, x) = 0`, and `J(x, 0) = x²/2 + x³/3 = ∫_0^x t (1 + t) dt`. -/
theorem tkRule_diag (x : ℝ) : tkRule x x = 0 := by unfold tkRule; ring

theorem tkRule_zero (x : ℝ) : tkRule x 0 = x ^ 2 / 2 + x ^ 3 / 3 := by unfold tkRule; ring

/-- **The `(t − k)` member is gsp on the range of `Xxt = (0, 2)`** (a non-step member of the
family, not covered by `isGsp_stepRule`): under `ρ = (1 − p, p)`, `E_ρ(J(s)) − E_ρ(J(2p)) =
(s − 2p)² (s/3 + p/3 + 1/2)`. -/
theorem tkRule_isGspOn : IsGspOn Xxt tkRule := by
  intro ρ hρ s ⟨w₁, hw₁⟩ _ hne
  have hs0 : 0 ≤ s := by
    have : Xxt w₁ = 0 ∨ Xxt w₁ = 2 := by fin_cases w₁ <;> simp [Xxt]
    rcases this with h | h <;> linarith
  have hsum : ρ 0 + ρ 1 = 1 := by
    have := hρ.2; simpa [Fin.sum_univ_two] using this
  have hp0 : 0 ≤ ρ 1 := hρ.1 1
  have hE : E ρ Xxt = 2 * ρ 1 := by
    simp [E, Fin.sum_univ_two, Xxt]; ring
  rw [hE] at hne ⊢
  have hρ0 : ρ 0 = 1 - ρ 1 := by linarith
  have key : expInacc ρ Xxt tkRule s - expInacc ρ Xxt tkRule (2 * ρ 1) =
      (s - 2 * ρ 1) ^ 2 * (s / 3 + ρ 1 / 3 + 1 / 2) := by
    simp only [expInacc, Fin.sum_univ_two, Xxt, tkRule, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hρ0]; ring
  have hsq : 0 < (s - 2 * ρ 1) ^ 2 := by
    have : s - 2 * ρ 1 ≠ 0 := sub_ne_zero.2 hne
    positivity
  have hpos : 0 < s / 3 + ρ 1 / 3 + 1 / 2 := by linarith
  have := mul_pos hsq hpos
  linarith

/-- **The cross-side reading fails for DDB's own family too**: with `λ = (1 + t) dt`,
`J(3/2, 1) = 7/24 > J(49/100, 1)` although `|3/2 − 1| < |49/100 − 1|`. So under that reading
Theorem 7.9's hypothesis excludes a gsp member of its own family; the per-side reading
(value-directedness) is the only tenable one, and it is what `xtRule_valueDirectedOn` checks. -/
theorem tkRule_not_cross_side :
    |(3 / 2 : ℝ) - 1| < |(49 / 100 : ℝ) - 1| ∧ tkRule (49 / 100) 1 < tkRule (3 / 2) 1 := by
  constructor
  · norm_num [abs_of_nonneg, abs_of_nonpos]
  · unfold tkRule; norm_num

/-! ## 3. `StrictAgree unif3 G3` is a real constraint -/

/-- The guard of `StrictAgree` is positive on `G3` (one cell, full support). -/
theorem G3_guard_pos (ω : Fin 3) : 0 < mass unif3 (tcell G3 ω) := by
  rw [G3_tcell]; norm_num [mass, Fin.sum_univ_three, unif3, vec3_two]

/-- The antecedent is inhabited: the principal strictly prefers `ttt` to `fff` on the cell. -/
theorem G3_antecedent_inhabited : cellEU unif3 G3 0 fff3 < cellEU unif3 G3 0 ttt3 := by
  rw [G3_cellEU, G3_cellEU]; norm_num [fff3, ttt3, bvec3_zero, bvec3_one, bvec3_two, uB_true, uB_false]

/-- On the tie menu of the refutation the principal is *also* indifferent: the valuing failure is
purely the world-dependent tie-break. -/
theorem G3_principal_ties : cellEU unif3 G3 0 ftf3 = cellEU unif3 G3 0 fft3 := by
  rw [G3_cellEU, G3_cellEU]; norm_num [ftf3, fft3, bvec3_zero, bvec3_one, bvec3_two, uB_true, uB_false]

/-- A nearby non-twin frame: agent beliefs `(7/10, 2/10, 1/10)` at every world, `V = u`. -/
def pag3' : Fin 3 → ℝ := ![7 / 10, 2 / 10, 1 / 10]

theorem pag3'_mem : pag3' ∈ stdSimplex ℝ (Fin 3) :=
  simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

def G3' : GFrame (Fin 3) Bool where
  u := uB
  Pag := fun _ => pag3'
  Pag_mem := fun _ => pag3'_mem
  V := fun _ => uB
  A := univ

theorem G3'_tcell (ω : Fin 3) : tcell G3' ω = univ := by
  ext w; simp [tcell, G3']

theorem G3'_cellEU (ω : Fin 3) (c : Fin 3 → Bool) :
    cellEU unif3 G3' ω c = (uB (c 0) + uB (c 1) + uB (c 2)) / 3 := by
  simp only [cellEU]
  rw [G3'_tcell]
  simp only [Fin.sum_univ_three, unif3, G3', vec3_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem G3'_agentEU (ω : Fin 3) (a : Fin 3 → Bool) :
    G3'.agentEU ω a = 7 / 10 * uB (a 0) + 2 / 10 * uB (a 1) + 1 / 10 * uB (a 2) := by
  simp [GFrame.agentEU, G3', E, Fin.sum_univ_three, pag3', vec3_two]

/-- **Strict agreement fails on `G3'`**: the principal strictly prefers `ftt` (two `true`s) to
`tff` (one), but the agent prefers `tff` (`7/10 > 3/10`). So `strictAgree_unif3_G3` is a genuine
check of the frame, not a consequence of `V = u` with one cell. -/
theorem G3'_not_strictAgree : ¬ StrictAgree unif3 G3' := by
  intro h
  have hg : 0 < mass unif3 (tcell G3' 0) := by
    rw [G3'_tcell]; norm_num [mass, Fin.sum_univ_three, unif3, vec3_two]
  have := h ftt3 (mem_univ _) tff3 (mem_univ _) 0 hg
    (by rw [G3'_cellEU, G3'_cellEU]
        norm_num [ftt3, tff3, bvec3_zero, bvec3_one, bvec3_two, uB_true, uB_false])
  rw [G3'_agentEU, G3'_agentEU] at this
  norm_num [ftt3, tff3, bvec3_zero, bvec3_one, bvec3_two, uB_true, uB_false] at this

/-- `G3'` is clear (vacuously, one cell) and rich, like `G3`: the failure of strict agreement is
inside the hypothesis package of `typeMeasurable_valuesB_iff_strictAgree`, so by that theorem
some type-measurable behaviour on `G3'` is not valued. -/
theorem G3'_clarity : Clarity G3' := by
  intro ω ω' h; rw [G3'_tcell] at h; exact absurd (mem_univ ω') h

theorem G3'_richness : Richness G3' := fun _ _ _ _ _ => mem_univ _

theorem G3'_some_typeMeasurable_not_valued :
    ¬ ∀ B, TypeMeasurable G3' B → IsBehaviour G3' B → ValuesB unif3 G3' B := by
  rw [typeMeasurable_valuesB_iff_strictAgree unif3_mem G3'_clarity G3'_richness]
  exact G3'_not_strictAgree

/-! ## 4. Degenerate boundaries of the range-restricted class -/

/-- For a constant variable every rule is gsp on the (one-point) range. -/
theorem isGspOn_const {W : Type} [Fintype W] [DecidableEq W] (c : ℝ) (I : Rule) :
    IsGspOn (fun _ : W => c) I := by
  intro ρ hρ s ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ hne
  exfalso
  apply hne
  have : E ρ (fun _ : W => c) = c := by
    simp only [E, ← sum_mul, hρ.2, one_mul]
  rw [this]
  exact le_antisymm hw₂ hw₁

/-- And every distribution totally trusts every frame with respect to a constant variable, so the
range form of Theorem 3.2 is consistent there: both sides hold, and the theorem says nothing. -/
theorem totalTrustOn_const {W : Type} [Fintype W] [DecidableEq W] {π : W → ℝ}
    (hπ : π ∈ stdSimplex ℝ W) (F : Frame W) (c : ℝ) : TotalTrustOn (fun _ => c) π F := by
  have hE : ∀ w, E (F.P w) (fun _ : W => c) = c := fun w => by
    simp only [E, ← sum_mul, (F.P_mem w).2, one_mul]
  constructor
  · intro s
    apply sum_nonneg
    intro w _
    simp only [hE]
    split_ifs with h <;> nlinarith [hπ.1 w]
  · intro s
    apply sum_nonpos
    intro w _
    simp only [hE]
    split_ifs with h <;> nlinarith [hπ.1 w]

/-! ## 5. Two ledger evidence pointers, re-established

The ledger's Witness cells for `totalTrustOn_iff_epistemicValueOn` and `simpleTrustOn_iff_levinstein`
cite facts proved only in the round-1 probe `Vacuity.lean` (`fn46_not_totalTrustOn`,
`simpleTrust_of_forall_simpleTrustOn`), a file the report says no longer elaborates in full
against the repaired library. Both facts hold against the repaired library; here they are. -/

/-- Fn 46's witness plus Theorem 3.2 (⟹): `π21` does not totally trust `fact21` with respect to
`O₁` (the negative side of the iff, on Fact 2.1's frame). -/
theorem fn46_not_totalTrustOn : ¬ TotalTrustOn O1 π21 fact21 := by
  intro h
  have := (totalTrustOn_expInaccP_le π21_mem h (isGsp_fn46Rule O1).isGspOn).1
  have hlt := fn46_witness.2
  linarith

/-- Simple Trust with respect to every `q` (clause 1) gives the foundation's guarded
`SimpleTrust`. -/
theorem simpleTrust_of_forall_simpleTrustOn {W : Type} [Fintype W] [DecidableEq W] {π : W → ℝ}
    {F : Frame W} (h : ∀ q, SimpleTrustOn q π F) : SimpleTrust π F :=
  fun q t _ => (h q).1 t

/-- Hence fn 50 gives a `q` at which `SimpleTrustOn` fails — the negative side of Theorem 3.1. -/
theorem fn50_exists_not_simpleTrustOn : ∃ q, ¬ SimpleTrustOn q π50 fn50 := by
  by_contra hcon
  push_neg at hcon
  exact fn50_not_simpleTrust (simpleTrust_of_forall_simpleTrustOn hcon)

end

end Cleanroom.Lit.LitDdbAccuracyMm.AuditR2
