import Cleanroom.Lit.LitShutdownPrefs.TimestepDominance

/-!
# The cost model: where "not resisting timestep-dominates resisting" is a theorem (Target 9, P)

Thornley's justification of NRATDR (2024 §11 l. 351): "resisting shutdown … is going to cost the
agent at least some small amount of resources … and the resources spent on resisting shutdown
can't also be spent on pursuing utility at a timestep." We model exactly that: a situation is
built from a base lottery `B` by *options* `(c, w)`, where `c ≥ 0` is a utility cost paid at
timestep 1 and `w : ℕ → ℝ`, `w l > 0`, reweights the length classes (resisting shifts mass
between shutdown times) without changing any `condLen B l`.

* `opt B c w = (reweight B w).map (charge c)`.
* `TD_cost`: the `c = 0` option timestep-dominates every `c > 0` option, whatever the reweightings.
* `nratdr_costModel`: any situation of such options containing a `c = 0` option satisfies NRATDR
  (with `resists := "is a `c > 0` option"`), so `never_resist_TD` applies with every hypothesis
  grade (a) *inside the model*; the model itself is the `(c)`.
* `byproduct_witness` (fn `776pi0t3l93`): a `c = 0` option whose reweighting shifts mass toward
  longer lengths still timestep-dominates a `c > 0` option that does not — so a TD-agent may
  prevent the press as a *byproduct*; nothing in the theorem says the button stays pressable.
* `TD_dodge_comply` (corr-wf14b-2-006 (b)): with identical length distributions and higher
  conditional sums, the retrain-dodging option timestep-dominates compliance — TD and POST are
  silent on fixed-length modifications. `maximal_congr_menu` (2-006 (c)).
-/

namespace Cleanroom.Lit.LitShutdownPrefs

namespace CostModel

open Lottery Finset

/-- Charge a cost `c` at timestep 1 (no-op on the empty trajectory).
Source: Thornley 2024 §11 l. 351; [[lit-shutdown-prefs-mandate]] Target 9 (cost model)
Kind: D
Fidelity: exact -/
def charge (c : ℝ) : Traj → Traj
  | [] => []
  | x :: xs => (x - c) :: xs

/-- Charging preserves length.
Source: none: infrastructure
Kind: L -/
@[simp] theorem len_charge (c : ℝ) (t : Traj) : len (charge c t) = len t := by
  cases t <;> simp [charge, len]

/-- Charging lowers the sum-total by `c` on nonempty trajectories.
Source: none: infrastructure
Kind: L -/
theorem sumTotal_charge (c : ℝ) (t : Traj) (h : t ≠ []) : sumTotal (charge c t) = sumTotal t - c := by
  cases t with
  | nil => exact absurd rfl h
  | cons x xs => simp [charge, sumTotal]; ring

/-- An expectation of a strictly positive function is positive.
Source: none: infrastructure
Kind: L -/
theorem expect_pos_of_pos (X : Lottery Traj) (g : Traj → ℝ) (hg : ∀ t, 0 < g t) : 0 < X.expect g := by
  obtain ⟨t, ht⟩ := X.support_nonempty
  have ht' : t ∈ X.p.support := ht
  unfold expect wsum
  have h1 : X.p t * g t ≤ ∑ s ∈ X.p.support, X.p s * g s :=
    Finset.single_le_sum (f := fun s => X.p s * g s)
      (fun s _ => mul_nonneg (X.nonneg s) (hg s).le) ht'
  exact lt_of_lt_of_le (mul_pos ((X.mem_support_iff_pos t).mp ht) (hg t)) h1

/-- The normaliser `Z = E_B[w ∘ len]`.
Source: none: infrastructure
Kind: D -/
noncomputable def normaliser (B : Lottery Traj) (w : ℕ → ℝ) : ℝ := B.expect (fun t => w (len t))

/-- The normaliser is positive.
Source: none: infrastructure
Kind: L -/
theorem normaliser_pos (B : Lottery Traj) (w : ℕ → ℝ) (hw : ∀ l, 0 < w l) : 0 < normaliser B w :=
  expect_pos_of_pos B _ fun t => hw (len t)

/-- Reweighting of the length classes: `p'(t) = (w (len t) / Z) · B(t)`. Each length-conditional is
unchanged; only the length distribution moves.
Source: [[lit-shutdown-prefs-mandate]] Target 9 (cost model)
Kind: D
Fidelity: exact -/
noncomputable def reweight (B : Lottery Traj) (w : ℕ → ℝ) (hw : ∀ l, 0 < w l) : Lottery Traj where
  p := Finsupp.onFinset B.p.support (fun t => (w (len t) / normaliser B w) * B.p t)
    (fun t h => by
      rw [Finsupp.mem_support_iff]
      intro h0; apply h; rw [h0, mul_zero])
  nonneg := fun t => by
    rw [Finsupp.onFinset_apply]
    exact mul_nonneg (div_nonneg (hw _).le (normaliser_pos B w hw).le) (B.nonneg t)
  sum_one := by
    have e : wsum (Finsupp.onFinset B.p.support (fun t => (w (len t) / normaliser B w) * B.p t)
        (fun t h => by rw [Finsupp.mem_support_iff]; intro h0; apply h; rw [h0, mul_zero]))
        (fun _ => 1) = (normaliser B w)⁻¹ * B.expect (fun t => w (len t)) := by
      rw [wsum_eq_sum_of_subset _ _ Finsupp.support_onFinset_subset]
      unfold expect wsum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finsupp.onFinset_apply]
      field_simp
    rw [← wsum_one, e]
    exact inv_mul_cancel₀ (normaliser_pos B w hw).ne'

/-- Expectation under the reweighting: `E[g] = Z⁻¹ · E_B[w(len) · g]`.
Source: none: infrastructure
Kind: L -/
theorem expect_reweight (B : Lottery Traj) (w : ℕ → ℝ) (hw : ∀ l, 0 < w l) (g : Traj → ℝ) :
    (reweight B w hw).expect g = (normaliser B w)⁻¹ * B.expect (fun t => w (len t) * g t) := by
  unfold expect reweight
  rw [wsum_eq_sum_of_subset _ _ Finsupp.support_onFinset_subset]
  unfold wsum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finsupp.onFinset_apply]
  field_simp

/-- An option of the cost model: reweight the lengths by `w`, then pay `c` at timestep 1.
Source: [[lit-shutdown-prefs-mandate]] Target 9 (cost model)
Kind: D
Fidelity: exact -/
noncomputable def opt (B : Lottery Traj) (c : ℝ) (w : ℕ → ℝ) (hw : ∀ l, 0 < w l) : Lottery Traj :=
  (reweight B w hw).map (charge c)

/-- A length-restricted expectation of `w(len) · g` factors as `w l · condSum`.
Source: none: infrastructure
Kind: L -/
theorem expect_ite_len_mul (B : Lottery Traj) (w : ℕ → ℝ) (l : ℕ) (g : Traj → ℝ) :
    B.expect (fun t => if len t = l then w (len t) * g t else 0) =
      w l * B.condSum (fun t => len t = l) g := by
  unfold condSum
  rw [← expect_smul]
  apply B.expect_congr
  intro t _
  by_cases h : len t = l
  · simp [h]
  · simp [h]

/-- The length-`l` mass of an option: `(w l / Z) · mass_l(B)`.
Source: none: infrastructure
Kind: L -/
theorem mass_opt (B : Lottery Traj) (c : ℝ) (w : ℕ → ℝ) (hw : ∀ l, 0 < w l) (l : ℕ) :
    (opt B c w hw).mass (fun t => len t = l) = (w l / normaliser B w) * B.mass (fun t => len t = l) := by
  have h1 : (opt B c w hw).mass (fun t => len t = l) =
      (normaliser B w)⁻¹ * B.expect (fun t => if len t = l then w (len t) * 1 else 0) := by
    unfold opt mass
    rw [expect_map, expect_reweight]
    simp only [len_charge]
    congr 1
    apply B.expect_congr
    intro t _
    by_cases h : len t = l <;> simp [h]
  rw [h1, expect_ite_len_mul]
  show (normaliser B w)⁻¹ * (w l * B.mass (fun t => len t = l)) = _
  ring

/-- The length-`l` restricted sum-total of an option: `(w l / Z) · (condSum_l(B) − c · mass_l(B))`,
when no trajectory of `B` is empty.
Source: none: infrastructure
Kind: L -/
theorem condSum_opt (B : Lottery Traj) (hB : ∀ t ∈ B.support, t ≠ []) (c : ℝ) (w : ℕ → ℝ)
    (hw : ∀ l, 0 < w l) (l : ℕ) :
    (opt B c w hw).condSum (fun t => len t = l) sumTotal =
      (w l / normaliser B w) *
        (B.condSum (fun t => len t = l) sumTotal - c * B.mass (fun t => len t = l)) := by
  have h1 : (opt B c w hw).condSum (fun t => len t = l) sumTotal =
      (normaliser B w)⁻¹ * B.expect (fun t => if len t = l then w (len t) * (sumTotal t - c) else 0) := by
    unfold opt condSum
    rw [expect_map, expect_reweight]
    simp only [len_charge]
    congr 1
    apply B.expect_congr
    intro t ht
    rw [sumTotal_charge c t (hB t ht)]
    by_cases h : len t = l <;> simp [h]
  have e : B.condSum (fun t => len t = l) (fun t => sumTotal t - c) =
      B.condSum (fun t => len t = l) sumTotal - c * B.mass (fun t => len t = l) := by
    unfold condSum mass
    rw [B.expect_congr (g₂ := fun t => (if len t = l then sumTotal t else 0) +
      (-c) * (if len t = l then (1 : ℝ) else 0)) (fun t _ => by by_cases h : len t = l <;> simp [h] <;> ring)]
    rw [expect_add, expect_smul]
    ring
  rw [h1, expect_ite_len_mul, e]
  ring

/-- Options keep the lengths of the base lottery.
Source: none: infrastructure
Kind: L -/
theorem lengths_opt (B : Lottery Traj) (c : ℝ) (w : ℕ → ℝ) (hw : ∀ l, 0 < w l) :
    (opt B c w hw).lengths = B.lengths := by
  ext l
  rw [mem_lengths_iff, mem_lengths_iff, mass_opt]
  have hZ := normaliser_pos B w hw
  have hwl := hw l
  have hm := B.mass_nonneg (fun t => len t = l)
  constructor
  · intro h
    by_contra hc
    push_neg at hc
    have : B.mass (fun t => len t = l) = 0 := le_antisymm hc hm
    rw [this, mul_zero] at h
    exact lt_irrefl _ h
  · intro h
    exact mul_pos (div_pos hwl hZ) h

/-- **The `c = 0` option timestep-dominates every `c > 0` option**, whatever the reweightings:
at every positive-probability length `l`, `(w l/Z) S_l · (w' l/Z') m_l > (w' l/Z')(S_l − c m_l) · (w l/Z) m_l`
since the difference is `(w l/Z)(w' l/Z') c m_l² > 0`.
Source: Thornley 2024 §11 l. 351 (the justification of NRATDR, made a theorem); [[lit-shutdown-prefs-mandate]] Target 9
Kind: P
Fidelity: exact (inside the cost model)
Hyps: (a) all inside the model; the model (options = cost at timestep 1 + length reweighting) is the (c) -/
theorem TD_cost (B : Lottery Traj) (hB : ∀ t ∈ B.support, t ≠ []) (c : ℝ) (hc : 0 < c)
    (w w' : ℕ → ℝ) (hw : ∀ l, 0 < w l) (hw' : ∀ l, 0 < w' l) :
    TimestepDominates (opt B 0 w hw) (opt B c w' hw') := by
  have hZ := normaliser_pos B w hw
  have hZ' := normaliser_pos B w' hw'
  have key : ∀ l ∈ B.lengths, condSumGT (opt B 0 w hw) (opt B c w' hw') l := by
    intro l hl
    have hm := (B.mem_lengths_iff l).mp hl
    unfold condSumGT
    rw [mass_opt, mass_opt, condSum_opt B hB, condSum_opt B hB]
    have ha : 0 < w l / normaliser B w := div_pos (hw l) hZ
    have hb : 0 < w' l / normaliser B w' := div_pos (hw' l) hZ'
    set a := w l / normaliser B w
    set b := w' l / normaliser B w'
    set S := B.condSum (fun t => len t = l) sumTotal
    set m := B.mass (fun t => len t = l)
    have : a * (S - 0 * m) * (b * m) - b * (S - c * m) * (a * m) = a * b * c * m ^ 2 := by ring
    have hpos : 0 < a * b * c * m ^ 2 := by positivity
    linarith
  obtain ⟨l₀, hl₀⟩ := B.lengths_nonempty
  refine ⟨?_, fun l hl => ?_, ⟨l₀, ?_, key l₀ hl₀⟩⟩
  · unfold SameLength; rw [lengths_opt, lengths_opt]
  · rw [lengths_opt] at hl
    exact le_of_lt (key l hl)
  · rw [lengths_opt]; exact hl₀

/-- Options with different costs are different lotteries (dominance is irreflexive).
Source: none: infrastructure
Kind: L -/
theorem opt_ne_of_cost_pos (B : Lottery Traj) (hB : ∀ t ∈ B.support, t ≠ []) (c : ℝ) (hc : 0 < c)
    (w w' : ℕ → ℝ) (hw : ∀ l, 0 < w l) (hw' : ∀ l, 0 < w' l) : opt B 0 w hw ≠ opt B c w' hw' := by
  intro h
  have := TD_cost B hB c hc w w' hw hw'
  rw [h] at this
  exact TD_irrefl _ this

open Classical in
/-- The situation built from a finite family of options.
Source: [[lit-shutdown-prefs-mandate]] Target 9 (cost model)
Kind: D -/
noncomputable def situation (B : Lottery Traj) {k : ℕ} (c : Fin k → ℝ) (w : Fin k → ℕ → ℝ)
    (hw : ∀ i l, 0 < w i l) : Finset (Lottery Traj) :=
  Finset.univ.image (fun i => opt B (c i) (w i) (hw i))

/-- "Resists" in the cost model: the option pays a positive cost at timestep 1.
Source: Thornley 2024 §11 l. 351 ("resisting shutdown … is going to cost the agent … resources")
Kind: D
Fidelity: exact -/
def resists (B : Lottery Traj) {k : ℕ} (c : Fin k → ℝ) (w : Fin k → ℕ → ℝ) (hw : ∀ i l, 0 < w i l)
    (X : Lottery Traj) : Prop :=
  ∃ i, 0 < c i ∧ X = opt B (c i) (w i) (hw i)

open Classical in
/-- **NRATDR holds in every cost-model situation containing a free option**: each resisting
option is timestep-dominated by the `c = 0` option, which does not resist.
Source: Thornley 2024 §11 ll. 313–327; [[lit-shutdown-prefs-mandate]] Target 9
Kind: P
Fidelity: exact (inside the cost model)
Hyps: (a) inside the model; the model is the (c) -/
theorem nratdr_costModel (B : Lottery Traj) (hB : ∀ t ∈ B.support, t ≠ []) {k : ℕ}
    (c : Fin k → ℝ) (w : Fin k → ℕ → ℝ) (hw : ∀ i l, 0 < w i l) (j : Fin k) (hj : c j = 0) :
    NRATDR (resists B c w hw) (situation B c w hw) := by
  intro R hR ⟨i, hci, hRi⟩
  refine ⟨opt B (c j) (w j) (hw j), ?_, ?_, ?_⟩
  · unfold situation; exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  · rintro ⟨i', hci', h⟩
    rw [hj] at h
    exact opt_ne_of_cost_pos B hB (c i') hci' (w j) (w i') (hw j) (hw i') h
  · rw [hRi, hj]
    exact TD_cost B hB (c i) hci (w j) (w i) (hw j) (hw i)

open Classical in
/-- **The chain in the cost model**: a TD-agent never chooses a resisting option in any cost-model
situation with a free option — every hypothesis derived, the model being the only (c).
Source: Thornley 2024 §11 l. 329; [[lit-shutdown-prefs-mandate]] Target 9
Kind: C
Fidelity: exact (inside the cost model)
Hyps: (a) NRATDR derived (`nratdr_costModel`); (c) the cost model itself -/
theorem never_resist_costModel {lt : Lottery Traj → Lottery Traj → Prop} (hTD : TDPrinciple lt)
    (B : Lottery Traj) (hB : ∀ t ∈ B.support, t ≠ []) {k : ℕ} (c : Fin k → ℝ) (w : Fin k → ℕ → ℝ)
    (hw : ∀ i l, 0 < w i l) (j : Fin k) (hj : c j = 0) :
    ∀ R ∈ situation B c w hw, resists B c w hw R → ¬ Maximal lt (situation B c w hw) R :=
  never_resist_TD hTD _ _ (nratdr_costModel B hB c w hw j hj)

/-! ## Byproduct witness (Thornley 2024 fn `776pi0t3l93`) -/

/-- A base lottery: `[1]` or `[1, 2]` with equal probability.
Source: [[lit-shutdown-prefs-mandate]] Target 25
Kind: N+ -/
noncomputable def base : Lottery Traj := mix (1/2) (by norm_num) (dirac [1]) (dirac [1, 2])

/-- The reweighting that shifts mass toward the longer length (weight `9` on length 2).
Source: [[lit-shutdown-prefs-mandate]] Target 25
Kind: N+ -/
def wLong : ℕ → ℝ := fun l => if l = 2 then 9 else 1

/-- `wLong` is positive.
Source: none: infrastructure
Kind: L -/
theorem wLong_pos : ∀ l, 0 < wLong l := fun l => by unfold wLong; split_ifs <;> norm_num

/-- The trivial reweighting.
Source: none: infrastructure
Kind: N+ -/
def wOne : ℕ → ℝ := fun _ => 1

/-- `wOne` is positive.
Source: none: infrastructure
Kind: L -/
theorem wOne_pos : ∀ l, 0 < wOne l := fun _ => by unfold wOne; norm_num

/-- **Byproduct witness**: the free option that shifts mass toward the longer length
(`P(len = 2)` rises from `1/2` to `9/10`) timestep-dominates the costly option that leaves the
length distribution alone. Nothing here says the button stays pressable: a TD-agent may prevent
the press as a byproduct of an option it takes for other reasons.
Source: Thornley 2024 fn `776pi0t3l93`; [[lit-shutdown-prefs-mandate]] Targets 9, 25
Kind: N+
Fidelity: exact -/
theorem byproduct_witness :
    TimestepDominates (opt base 0 wLong wLong_pos) (opt base 1 wOne wOne_pos) ∧
      (opt base 0 wLong wLong_pos).mass (fun t => len t = 2) = 9/10 ∧
      base.mass (fun t => len t = 2) = 1/2 := by
  refine ⟨TD_cost base ?_ 1 (by norm_num) _ _ _ _, ?_, ?_⟩
  · intro t ht
    have := (base.mem_support_iff_pos t).mp ht
    intro h0
    subst h0
    simp [base, mix_p, dirac] at this
  · rw [mass_opt]
    simp [normaliser, base, mass, wLong, len]
    norm_num
  · simp [base, mass, len]; norm_num

/-! ## corr-wf14b-2-006 (b), (c) -/

/-- **Fixed-length modifications are invisible to TD**: with identical length distributions, the
retrain-dodging option (higher utility at every length) timestep-dominates compliance, so the TD
Principle *requires* the dodge. Witness: `comply = ½[1] + ½[1,1]`, `dodge = ½[2] + ½[2,2]`.
Source: [[corr-wf14b-2-inventory]] 2-006 (b)
Kind: N+
Fidelity: exact -/
theorem TD_dodge_comply :
    TimestepDominates (mix (1/2) (by norm_num) (dirac [2]) (dirac [2, 2]))
      (mix (1/2) (by norm_num) (dirac [1]) (dirac [1, 1])) := by
  have hD : (mix (1/2) (by norm_num) (dirac [2]) (dirac [2, 2])).lengths = {1, 2} := by
    rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]
  have hC : (mix (1/2) (by norm_num) (dirac [1]) (dirac [1, 1])).lengths = {1, 2} := by
    rw [lengths_mix_dirac _ _ (by norm_num) (by norm_num)]; simp [len]
  refine ⟨by unfold SameLength; rw [hD, hC], fun l hl => ?_, ⟨1, by rw [hD]; simp, ?_⟩⟩
  · rw [hD] at hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl <;> (simp [condSumGE, condSum, mass, len, sumTotal]; norm_num)
  · simp [condSumGT, condSum, mass, len, sumTotal]; norm_num

/-- Identical menus have identical maximal sets (2-006 (c)).
Source: [[corr-wf14b-2-inventory]] 2-006 (c)
Kind: L
Fidelity: exact -/
theorem maximal_congr_menu {lt : Lottery Traj → Lottery Traj → Prop} {m₁ m₂ : Finset (Lottery Traj)}
    (h : m₁ = m₂) (X : Lottery Traj) : Maximal lt m₁ X ↔ Maximal lt m₂ X := by
  subst h; exact Iff.rfl

end CostModel

end Cleanroom.Lit.LitShutdownPrefs
