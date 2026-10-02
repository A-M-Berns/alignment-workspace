import Cleanroom.Found.LiAsympCalc

/-!
# li-asymp-calc — audit round 2, adversarial lens: probes

Not imported by the library. Elaborated with `scripts/lean-check`. Each probe is evidence for
one item of `li-asymp-calc-audit-r2-adversarial.md`:

1. `g3d_witness` — a **non-degenerate** inhabitant of the full hypothesis package of
   `determinedVia_of_sentenceAffine_determined` (G3 (d)): a deductive process whose theory
   reveals the atom `0` on every day (`atomDP`), `X ≡ gridLUV`, `y ≡ 0`, and the coherent
   payout stream `τ r = 1[r ≤ 0]`. Consistent worlds exist, inconsistent worlds exist (the
   theory does work — `DeterminedVia gridLUV atomDP 0` is not the trivial `DeterminedVia
   gridLUV empty 0`), and the conclusion composes through G3 (b) to FAF's
   `LUVCombination.DeterminedViaTheory`. The package ships no witness for (d).
2. `offGrid_witness` — a non-degenerate inhabitant of `determined_mesh_ofLUV_offGrid`'s
   package: `X n = sharpLUV (1/(n+3))`, valued at the strictly decreasing off-grid rational
   `1/(n+3)` by every world, `hoff` holding for an arithmetic reason (`i (n+3) = n+1` has no
   solution `i ≤ n`), and the exact mesh conclusion instantiated through the lemma. The package
   ships no witness for the off-grid lemma.
3. `hardIndicator_const_on_unit_histories` / `not_exists_ef_hardIndicator_unit` — D3's
   quantification over **all** histories: at `t = 1` the hard indicator restricted to
   `[0,1]`-valued histories **is** an `EF` (`EF.const 0`), so the theorem's truth at `t ≥ 1`
   rests on histories with a price above `1`; for `t ∈ [0,1)` the restricted statement still
   fails, by the package's own one-price path kept inside `[0,1]`. This matches the source's
   all-histories statement (root-deference-2-002); recorded so that a dependent does not read
   D3 at the boundary as a statement about `[0,1]` markets.
4. `kronecker_witness_conclusion_trivial` — the Kronecker witness's conclusion instance
   `(∑_{n<N} (-1)^n)/(N+1) → 0` holds without Kronecker (the numerator is `0` or `1`): the
   witness certifies the *hypothesis* class (conditional, non-absolute convergence), not the
   conclusion.
-/

namespace Cleanroom.Found.LiAsympCalc.AuditR2

open LogicalInduction Filter Topology Finset

/-! ### 1. A non-degenerate witness for G3 (d) -/

/-- The deductive process revealing the atom `0` on every day. -/
def atomDP : DeductiveProcess :=
  ⟨fun _ => {LO.Propositional.Formula.atom 0}, fun _ => Finset.Subset.refl _⟩

lemma atomDP_holds {v : PCWorld} (hv : v.ConsistentWithTheory atomDP) : v 0 := by
  have h0 : ∀ φ ∈ atomDP.D 0, v.Holds φ := hv 0
  exact (PCWorld.holds_atom v 0).1 (h0 (LO.Propositional.Formula.atom 0) (by simp [atomDP]))

/-- The threshold-coherent payout stream around `0`: `1` at or below `0`, `0` above. -/
noncomputable def τgrid (r : ℚ) : ℝ := if r ≤ 0 then 1 else 0

lemma gridLUV_gt_neg {r : ℚ} (hr : r < 0) : gridLUV.gt r = (⊤ : Sentence) := by
  simp [gridLUV, hr]

lemma gridLUV_gt_pos {r : ℚ} (hr : 0 < r) :
    gridLUV.gt r = LO.Propositional.Formula.falsum := by
  simp [gridLUV, hr, not_lt.2 hr.le]

lemma gridLUV_gt_zero : gridLUV.gt 0 = LO.Propositional.Formula.atom 0 := by
  simp [gridLUV]

theorem g3d_witness (P : History) :
    (∀ n, 0 ≤ (fun _ : ℕ => (0 : ℝ)) n ∧ (fun _ : ℕ => (0 : ℝ)) n ≤ 1) ∧
      (∀ r : ℚ, AffineCombination.DeterminedViaTheory
        (fun n => AffineCombination.sentenceAffine (fun m => ((fun _ : ℕ => gridLUV) m).gt r) n)
        P atomDP (fun n => (fun _ : ℕ => τgrid) n r)) ∧
      (∀ n (r : ℚ), ((r : ℝ) < (fun _ : ℕ => (0 : ℝ)) n → (fun _ : ℕ => τgrid) n r = 1) ∧
        ((fun _ : ℕ => (0 : ℝ)) n < r → (fun _ : ℕ => τgrid) n r = 0)) ∧
      (∃ v : PCWorld, v.ConsistentWithTheory atomDP) ∧
      (∃ v : PCWorld, ¬ v.ConsistentWithTheory atomDP) ∧
      (∀ n, LUV.DeterminedVia ((fun _ : ℕ => gridLUV) n) atomDP ((fun _ : ℕ => (0 : ℝ)) n)) ∧
      LUVCombination.DeterminedViaTheory
        (fun n => LUVCombination.ofLUV ((fun _ : ℕ => gridLUV) n)) P atomDP (fun _ => 0) := by
  have hy : ∀ n, 0 ≤ (fun _ : ℕ => (0 : ℝ)) n ∧ (fun _ : ℕ => (0 : ℝ)) n ≤ 1 :=
    fun _ => ⟨le_rfl, zero_le_one⟩
  have hdet : ∀ r : ℚ, AffineCombination.DeterminedViaTheory
      (fun n => AffineCombination.sentenceAffine (fun m => ((fun _ : ℕ => gridLUV) m).gt r) n)
      P atomDP (fun n => (fun _ : ℕ => τgrid) n r) := by
    intro r n v hv
    rw [sentenceAffine_value_payout]
    show v.payout (gridLUV.gt r) = τgrid r
    unfold PCWorld.payout τgrid
    rcases lt_trichotomy r 0 with hr | rfl | hr
    · rw [gridLUV_gt_neg hr, if_pos (PCWorld.holds_top v), if_pos hr.le]
    · rw [gridLUV_gt_zero, if_pos ((PCWorld.holds_atom v 0).2 (atomDP_holds hv)), if_pos le_rfl]
    · have hf : ¬ v.Holds LO.Propositional.Formula.falsum := fun h => h
      rw [gridLUV_gt_pos hr, if_neg hf, if_neg (not_le.2 hr)]
  have hcoh : ∀ n (r : ℚ), ((r : ℝ) < (fun _ : ℕ => (0 : ℝ)) n → (fun _ : ℕ => τgrid) n r = 1) ∧
      ((fun _ : ℕ => (0 : ℝ)) n < r → (fun _ : ℕ => τgrid) n r = 0) := by
    intro n r
    show ((r : ℝ) < 0 → τgrid r = 1) ∧ ((0 : ℝ) < r → τgrid r = 0)
    unfold τgrid
    constructor
    · intro hr
      have : r < 0 := by exact_mod_cast hr
      rw [if_pos this.le]
    · intro hr
      have : 0 < r := by exact_mod_cast hr
      rw [if_neg (not_le.2 this)]
  have hDV : ∀ n, LUV.DeterminedVia ((fun _ : ℕ => gridLUV) n) atomDP ((fun _ : ℕ => (0 : ℝ)) n) :=
    determinedVia_of_sentenceAffine_determined P hy hdet hcoh
  refine ⟨hy, hdet, hcoh, ⟨fun _ => True, fun _ φ hφ => ?_⟩, ⟨fun _ => False, fun h => ?_⟩, hDV,
    DeterminedVia.determinedViaTheory_ofLUV P hDV⟩
  · simp only [atomDP, Finset.mem_singleton] at hφ
    subst hφ
    exact (PCWorld.holds_atom _ 0).2 trivial
  · exact atomDP_holds h

/-! ### 2. A non-degenerate witness for the off-grid exact mesh lemma -/

/-- The sharp threshold LUV at a rational `q`: `⌜X > r⌝` is `⊤` for `r < q`, `⊥` for `r ≥ q`. -/
def sharpLUV (q : ℚ) : LUV :=
  ⟨fun r => if r < q then (⊤ : Sentence) else LO.Propositional.Formula.falsum⟩

lemma sharpLUV_valuesAt {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (v : PCWorld) :
    v.ValuesAt (sharpLUV q) q := by
  refine ⟨by exact_mod_cast hq0, by exact_mod_cast hq1, fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · have hr' : r < q := by exact_mod_cast hr
    simp only [sharpLUV, if_pos hr']
    exact PCWorld.holds_top v
  · have hr' : q < r := by exact_mod_cast hr
    simp only [sharpLUV, if_neg (not_lt.2 hr'.le)]
    intro h
    exact h

/-- `1/(n+3)` is never a grid point `i/(n+1)` with `i ≤ n`. -/
lemma offGrid_inv (n i : ℕ) (hi : i ≤ n) :
    (i : ℝ) / ((n + 1 : ℕ) : ℝ) ≠ 1 / ((n : ℝ) + 3) := by
  intro h
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hn3 : (n : ℝ) + 3 ≠ 0 := by positivity
  rw [div_eq_div_iff hn1 hn3] at h
  push_cast at h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_pos i with hi0 | hpos
  · subst hi0
    simp only [Nat.cast_zero, zero_mul, one_mul] at h
    linarith
  · have h1 : (1 : ℝ) ≤ i := by exact_mod_cast hpos
    nlinarith [mul_nonneg (sub_nonneg.2 h1) hn]

theorem offGrid_witness (P : History) :
    (∀ n, LUV.DeterminedVia ((fun k : ℕ => sharpLUV (1 / ((k : ℚ) + 3))) n)
        DeductiveProcess.empty ((fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 3)) n)) ∧
      (∀ n (i : ℕ), i ≤ n →
        (i : ℝ) / ((n + 1 : ℕ) : ℝ) ≠ (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 3)) n) ∧
      (∀ n, (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 3)) (n + 1) <
        (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 3)) n) ∧
      AffineCombination.DeterminedViaTheory
        (fun n => (LUVCombination.ofLUV
          ((fun k : ℕ => sharpLUV (1 / ((k : ℚ) + 3))) n)).meshAffine (n + 1))
        P DeductiveProcess.empty
        (fun n => (((n + 1 : ℕ) : ℝ))⁻¹ *
          ((Finset.range (n + 1)).filter
            (fun i : ℕ => (i : ℝ) / ((n + 1 : ℕ) : ℝ) <
              (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 3)) n)).card) := by
  have hDV : ∀ n, LUV.DeterminedVia ((fun k : ℕ => sharpLUV (1 / ((k : ℚ) + 3))) n)
      DeductiveProcess.empty ((fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 3)) n) := by
    intro n v _
    have hq0 : (0 : ℚ) ≤ 1 / ((n : ℚ) + 3) := by positivity
    have hq1 : 1 / ((n : ℚ) + 3) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      linarith
    have hc : ((1 / ((n : ℚ) + 3) : ℚ) : ℝ) = 1 / ((n : ℝ) + 3) := by
      push_cast
      ring
    show v.ValuesAt (sharpLUV (1 / ((n : ℚ) + 3))) (1 / ((n : ℝ) + 3))
    rw [← hc]
    exact sharpLUV_valuesAt hq0 hq1 v
  have hoff : ∀ n (i : ℕ), i ≤ n →
      (i : ℝ) / ((n + 1 : ℕ) : ℝ) ≠ (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 3)) n :=
    fun n i hi => offGrid_inv n i hi
  refine ⟨hDV, hoff, fun n => ?_, DeterminedVia.determined_mesh_ofLUV_offGrid P hDV hoff⟩
  show (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 3) < 1 / ((n : ℝ) + 3)
  apply one_div_lt_one_div_of_lt
  · positivity
  · push_cast
    linarith

/-! ### 3. D3 at the boundary: the all-histories quantification -/

/-- At `t = 1`, on `[0,1]`-valued histories the hard indicator **is** an expressible feature
(the constant `0`). -/
theorem hardIndicator_const_on_unit_histories (n : ℕ) (φ : Sentence) :
    ∃ e : EF, ∀ V : History, (∀ m ψ, V m ψ ∈ Set.Icc (0 : ℝ) 1) →
      e.denote V = if (1 : ℝ) < V n φ then 1 else 0 := by
  refine ⟨EF.const 0, fun V hV => ?_⟩
  rw [if_neg (not_lt.2 (hV n φ).2)]
  simp

/-- For `t ∈ [0,1)` the restricted statement still fails: the package's one-price path stays
inside the `[0,1]`-valued histories. -/
theorem not_exists_ef_hardIndicator_unit {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (n : ℕ)
    (φ : Sentence) :
    ¬ ∃ e : EF, ∀ V : History, (∀ m ψ, V m ψ ∈ Set.Icc (0 : ℝ) 1) →
      e.denote V = if t < V n φ then 1 else 0 := by
  rintro ⟨e, he⟩
  classical
  let V : History := fun _ _ => 0
  let γ : ℝ → History := fun s => Function.update V n (Function.update (V n) φ s)
  have hγ : Continuous γ := continuous_pricePath V n φ
  have hunit : ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ m ψ, γ s m ψ ∈ Set.Icc (0 : ℝ) 1 := by
    intro s hs m ψ
    simp only [γ, V, Function.update_apply, ite_apply]
    split_ifs <;> first | exact hs | exact ⟨le_rfl, zero_le_one⟩
  let g : ℝ → ℝ := fun s => e.denote (γ s)
  have hg : Continuous g := (EF.continuous_denote e).comp hγ
  have hval : ∀ s ∈ Set.Icc (0 : ℝ) 1, g s = if t < s then 1 else 0 := by
    intro s hs
    simp only [g]
    rw [he (γ s) (hunit s hs)]
    simp only [γ, Function.update_self]
  have hgt : g t = 0 := by
    rw [hval t ⟨ht0, ht1.le⟩]
    simp
  have h1 : Tendsto g (𝓝[>] t) (𝓝 1) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT ht1] with s hs
    rw [hval s ⟨ht0.trans hs.1.le, hs.2⟩, if_pos hs.1]
  have h0 : Tendsto g (𝓝[>] t) (𝓝 (g t)) :=
    (hg.tendsto t).mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique h1 h0
  rw [hgt] at this
  exact one_ne_zero this

/-! ### 4. The Kronecker witness's conclusion instance is trivial -/

lemma sum_neg_one_pow (N : ℕ) :
    ∑ n ∈ range N, (-1 : ℝ) ^ n = if Even N then 0 else 1 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h : Even N
    · have h' : ¬ Even (N + 1) := by rw [Nat.even_add_one]; exact not_not.2 h
      rw [if_pos h, if_neg h', Even.neg_one_pow h]
      ring
    · have h' : Even (N + 1) := Nat.even_add_one.2 h
      rw [if_neg h, if_pos h', Odd.neg_one_pow (Nat.not_even_iff_odd.1 h)]
      ring

theorem kronecker_witness_conclusion_trivial :
    Tendsto (fun N : ℕ => (∑ n ∈ range N, (-1 : ℝ) ^ n) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
  have hb : ∀ N : ℕ, |(∑ n ∈ range N, (-1 : ℝ) ^ n) / ((N : ℝ) + 1)| ≤ 1 / ((N : ℝ) + 1) := by
    intro N
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    apply div_le_div_of_nonneg_right _ (by positivity)
    rw [sum_neg_one_pow]
    split_ifs <;> norm_num
  have hlim : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  exact squeeze_zero_norm (fun N => by rw [Real.norm_eq_abs]; exact hb N) hlim

/-! ### 5. On the grid, exact determination can hold — at a truth other than the grid-rounded one

With the atom-deciding process of §1, `DeterminedVia gridLUV atomDP 0` holds and the
precision-`(n+1)` mesh of `ofLUV gridLUV` **is** exactly `DeterminedViaTheory` — at the truth
`1/(n+1)` (every consistent world holds `⌜X > 0⌝ = atom 0`, and no other grid threshold), which
is **not** the mandate's grid-rounded truth `(n+1)⁻¹ · #{i ≤ n : i/(n+1) < 0} = 0`. So finding 9's
claim (c) fails on the grid in a second way: even where exact determination holds, the strict
`<` count is the wrong truth; the equal-threshold count decided by the theory has to be added. -/

theorem onGrid_determined_off_by_one_grid_step (P : History) :
    (∀ _n : ℕ, LUV.DeterminedVia gridLUV atomDP 0) ∧
      AffineCombination.DeterminedViaTheory
        (fun n => (LUVCombination.ofLUV gridLUV).meshAffine (n + 1)) P atomDP
        (fun n => 1 / ((n : ℝ) + 1)) ∧
      ∀ n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ≠
        (((n + 1 : ℕ) : ℝ))⁻¹ * ((Finset.range (n + 1)).filter
          (fun i : ℕ => (i : ℝ) / ((n + 1 : ℕ) : ℝ) < (0 : ℝ))).card := by
  refine ⟨fun _ v _ => gridLUV_valuesAt v, ?_, ?_⟩
  · intro n v hv
    simp only [meshAffine_ofLUV_value, LUV.expectApprox]
    have hsum : ∑ i ∈ Finset.range (n + 1),
        v.payout (gridLUV.gt ((i : ℚ) / ((n + 1 : ℕ) : ℚ))) = 1 := by
      rw [Finset.sum_eq_single 0]
      · rw [Nat.cast_zero, zero_div, gridLUV_gt_zero]
        unfold PCWorld.payout
        rw [if_pos ((PCWorld.holds_atom v 0).2 (atomDP_holds hv))]
      · intro i _ hi
        have hpos : (0 : ℚ) < (i : ℚ) / ((n + 1 : ℕ) : ℚ) := by
          have : (0 : ℚ) < i := by exact_mod_cast Nat.pos_of_ne_zero hi
          positivity
        rw [gridLUV_gt_pos hpos]
        unfold PCWorld.payout
        exact if_neg (fun h => h)
      · intro h
        exact absurd (Finset.mem_range.2 (Nat.succ_pos n)) h
    rw [hsum]
    push_cast
    ring
  · intro n h
    have hfilt : (Finset.range (n + 1)).filter
        (fun i : ℕ => (i : ℝ) / ((n + 1 : ℕ) : ℝ) < (0 : ℝ)) = ∅ := by
      apply Finset.filter_eq_empty_iff.2
      intro i _
      exact not_lt.2 (by positivity)
    rw [hfilt, Finset.card_empty, Nat.cast_zero, mul_zero] at h
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith

end Cleanroom.Found.LiAsympCalc.AuditR2
