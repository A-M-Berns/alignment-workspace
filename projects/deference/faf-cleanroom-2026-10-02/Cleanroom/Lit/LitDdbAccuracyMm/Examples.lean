import Cleanroom.Lit.LitDdbAccuracyMm.Rules

/-!
# The witnesses: fn 46, fn 50, fn 51 — and DDB's fn 51 conjecture, proved (Targets 10–12)

Exact rationals by `norm_num`, over the foundation's `Examples.fact21`/`π21`/`O1` (fn 46) and
two new three-world frames (fn 50, fn 51). Target 12 (ii): DDB write "requiring `π` to expect all
of `P`'s estimates to be more accurate than its own as measured by squared Euclidean distance
may entail New Reflection (we've been unable to find a counterexample)" — it does:
`SqEuclidDominance.newReflects`. The proof takes, on a type cell `K` with `π(K) > 0` and row
`ρ`, the variables `X = π u 𝟙_{v} − π v 𝟙_{u}` (`u, v ∈ K`), which have `E_π(X) = 0`; dominance
then forces `E_ρ(X) = 0`, i.e. `π u ρ v = π v ρ u`, which summed over `u ∈ K` is New Reflection's
product identity; `ρ(K) > 0` comes from `X = 𝟙_{v}`. The converse fails on Figure 2
(`fig2_not_sqEuclidDominance`).
-/

namespace Cleanroom.Lit.LitDdbAccuracyMm

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Found.LitDdbFrames.Examples

noncomputable section

set_option linter.unusedSectionVars false

/-! ## Target 10: fn 46 on Fact 2.1's frame -/

/-- **Fn 46, exact values.** On Fact 2.1's frame with `π = (0.17, 0.56, 0.27)` and
`O₁ = (29, −3, −13)`, fn 46's rule gives `E_π(I(π)) = 5409001/5000000` (≈ 1.0818) and
`E_π(I(P)) = 22129913/20000000` (≈ 1.1065) — DDB's rounded `1.082` and `1.107`.
Source: [[Deference Done Better]] fn 46; item 064
Kind: L
Fidelity: exact (DDB's numbers are rounded)
Hyps: (a) none -/
theorem fn46_values :
    expInacc π21 O1 fn46Rule (E π21 O1) = 5409001 / 5000000 ∧
    expInaccP π21 fact21 O1 fn46Rule = 22129913 / 20000000 := by
  obtain ⟨hE0, hE1, hE2, hEπ⟩ := fact21_E_O1
  constructor
  · unfold expInacc
    rw [hEπ]
    simp only [Fin.sum_univ_three, vec3_two, fn46Rule, mixRule, clampTerm, clamp, π21, O1]
    norm_num [min_def, max_def]
  · unfold expInaccP
    simp only [Fin.sum_univ_three]
    rw [hE0, hE1, hE2]
    simp only [fn46Rule, mixRule, clampTerm, clamp, π21, O1, vec3_two]
    norm_num [min_def, max_def]

/-- **Target 10 (fn 46).** On Fact 2.1's frame `π` expects itself to be strictly *more*
accurate about `O₁` than the expert under fn 46's gsp rule: `E_π(I(π)) < E_π(I(P))`. With
Theorem 3.2 (⟹) this gives `¬ TotalTrustOn O₁ π21 fact21` directly. DDB say that in this
example `π` trusts (hence simply trusts) `P`, so that the Levinstein class certifies nothing
about estimates of `O₁` while gsp Epistemic Value separates; **Simple Trust of `fact21` by `π21`
is not checked here** (the ledger row is `partial`; the foundation proves only
`fact21_not_totalTrust`, `fact21_not_value`).
Source: [[Deference Done Better]] §3 l. 263, fn 46; item 064
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fn46_witness :
    IsGsp O1 fn46Rule ∧ expInacc π21 O1 fn46Rule (E π21 O1) < expInaccP π21 fact21 O1 fn46Rule := by
  obtain ⟨h1, h2⟩ := fn46_values
  refine ⟨isGsp_fn46Rule O1, ?_⟩
  rw [h1, h2]; norm_num

/-! ## Target 11: fn 50 -/

/-- Fn 50's frame: rows `(0.9, 0.1, 0)`, `(0.9, 0.1, 0)`, `(0.4, 0.1, 0.5)` (duplicate rows: the
cell `[P = P₁] = {w₁, w₂}`).
Source: [[Deference Done Better]] fn 50
Kind: D
Fidelity: exact -/
def fn50 : Frame (Fin 3) :=
  mk3 ![9 / 10, 1 / 10, 0] ![9 / 10, 1 / 10, 0] ![4 / 10, 1 / 10, 5 / 10]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- Fn 50's rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fn50_P : fn50.P 0 = ![9 / 10, 1 / 10, 0] ∧ fn50.P 1 = ![9 / 10, 1 / 10, 0] ∧
    fn50.P 2 = ![4 / 10, 1 / 10, 5 / 10] := ⟨rfl, rfl, rfl⟩

/-- Fn 50's deferrer `π = P₃ = (0.4, 0.1, 0.5)`.
Source: [[Deference Done Better]] fn 50
Kind: D
Fidelity: exact -/
def π50 : Fin 3 → ℝ := ![4 / 10, 1 / 10, 5 / 10]

/-- `π50` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π50_mem : π50 ∈ stdSimplex ℝ (Fin 3) :=
  simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Fn 50, Simple Trust fails** at `(q = {w₁}, t = 0.9)`: `π(w₁ ∧ P(w₁) ≥ 0.9) = 0.4 <
0.9 · 0.5 = 0.9 · π(P(w₁) ≥ 0.9)` (the conditional is `0.8`).
Source: [[Deference Done Better]] fn 50
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fn50_not_simpleTrust : ¬ SimpleTrust π50 fn50 := by
  intro h
  obtain ⟨h0, h1, h2⟩ := fn50_P
  have hev : fn50.probEvent {0} (9 / 10) = {0, 1} := by
    ext w
    fin_cases w <;> simp [Frame.probEvent, mass, h0, h1, h2, fin3_mk_two]
    all_goals norm_num
  have := h {0} (9 / 10)
  rw [hev] at this
  norm_num [mass, π50] at this

/-- **Fn 50, New Reflection fails**: at the candidate `P₁` (cell `{w₁, w₂}`),
`π(w₁ | P = P₁) = 0.8 ≠ 0.9 = P₁(w₁ | P = P₁)`.
Source: [[Deference Done Better]] fn 50
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fn50_not_newReflects : ¬ NewReflects π50 fn50 := by
  intro h
  obtain ⟨h0, h1, h2⟩ := fn50_P
  have hc : fn50.P 0 ∈ fn50.cands π50 := fn50.P_mem_cands (by norm_num [π50])
  have hcell : fn50.cell (fn50.P 0) = {0, 1} := by
    ext w
    fin_cases w <;> simp [Frame.cell, h0, h1, h2]
  have := (h _ hc).2 0
  simp only [ind, hcell, Frame.selfMass, mass] at this
  norm_num [h0, π50] at this

/-- **Fn 50, propositional Brier dominance on every `q`**: for all 8 propositions,
`∑ w, π w (P_w(q) − 𝟙_q w)^2 ≤ ∑ w, π w (π(q) − 𝟙_q w)^2` — although `π` neither simply trusts
nor new-reflects the frame. A single fixed rule certifies no deference principle.
Source: [[Deference Done Better]] §3 l. 301, fn 50; item 065
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fn50_brier_dominance : ∀ q : Finset (Fin 3),
    ∑ w, π50 w * (mass (fn50.P w) q - ind q w) ^ 2 ≤ ∑ w, π50 w * (mass π50 q - ind q w) ^ 2 := by
  intro q
  obtain ⟨h0, h1, h2⟩ := fn50_P
  have hq : q = univ.filter (fun w => w ∈ q) := by ext; simp
  rw [hq]
  simp only [mass, ind, sum_filter, mem_filter, mem_univ, true_and]
  by_cases hq0 : (0 : Fin 3) ∈ q <;> by_cases hq1 : (1 : Fin 3) ∈ q <;>
    by_cases hq2 : (2 : Fin 3) ∈ q <;>
    simp only [Fin.sum_univ_three, vec3_two, h0, h1, h2, π50, hq0, hq1, hq2, if_true, if_false] <;>
    norm_num

/-! ## Target 12: fn 51, and the conjecture -/

/-- Fn 51's frame: rows `(0.6, 0.2, 0.2)`, `(0, 1, 0)`, `(0, 0, 1)`.
Source: [[Deference Done Better]] fn 51
Kind: D
Fidelity: exact -/
def fn51 : Frame (Fin 3) :=
  mk3 ![6 / 10, 2 / 10, 2 / 10] ![0, 1, 0] ![0, 0, 1]
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num))

/-- Fn 51's rows.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem fn51_P : fn51.P 0 = ![6 / 10, 2 / 10, 2 / 10] ∧ fn51.P 1 = ![0, 1, 0] ∧
    fn51.P 2 = ![0, 0, 1] := ⟨rfl, rfl, rfl⟩

/-- Fn 51's deferrer `π = (0.8, 0.1, 0.1)`.
Source: [[Deference Done Better]] fn 51
Kind: D
Fidelity: exact -/
def π51 : Fin 3 → ℝ := ![8 / 10, 1 / 10, 1 / 10]

/-- `π51` is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem π51_mem : π51 ∈ stdSimplex ℝ (Fin 3) :=
  simplex3 _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Squared-Euclidean dominance on all estimates**: for every random variable `X`,
`∑ w, π w (E_w(X) − X w)^2 ≤ ∑ w, π w (E_π(X) − X w)^2` ("`π` expects all of `P`'s estimates to
be more accurate than its own as measured by squared Euclidean distance").
Source: [[Deference Done Better]] §3 l. 303, fn 51
Kind: D
Fidelity: exact -/
def SqEuclidDominance {W : Type} [Fintype W] (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ X : W → ℝ, ∑ w, π w * (E (F.P w) X - X w) ^ 2 ≤ ∑ w, π w * (E π X - X w) ^ 2

/-- **Fn 51, the sum-of-squares certificate.** On fn 51's frame, for every `X`,
`∑ π (E_π X − X)^2 − ∑ π (E_w X − X)^2 = (21 (X₁ − X₂)^2 + 8 (X₁ − X₀)^2 + 8 (X₂ − X₀)^2) / 500`.
Source: [[Deference Done Better]] fn 51; mandate Target 12(i)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem fn51_sos (X : Fin 3 → ℝ) :
    ∑ w, π51 w * (E π51 X - X w) ^ 2 - ∑ w, π51 w * (E (fn51.P w) X - X w) ^ 2 =
      (21 * (X 1 - X 2) ^ 2 + 8 * (X 1 - X 0) ^ 2 + 8 * (X 2 - X 0) ^ 2) / 500 := by
  obtain ⟨h0, h1, h2⟩ := fn51_P
  simp only [E, Fin.sum_univ_three, vec3_two, h0, h1, h2, π51]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **Fn 51, dominance holds** for every `X` (from the certificate).
Source: [[Deference Done Better]] fn 51
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fn51_sqEuclidDominance : SqEuclidDominance π51 fn51 := by
  intro X
  have h := fn51_sos X
  have : 0 ≤ (21 * (X 1 - X 2) ^ 2 + 8 * (X 1 - X 0) ^ 2 + 8 * (X 2 - X 0) ^ 2) / 500 := by
    positivity
  linarith

/-- **Fn 51, Simple Trust fails** at `(q = {w₂, w₃}, t = 0.4)`: `π(P(q) ≥ 0.4) = 1` while
`π(q) = 0.2 < 0.4`.
Source: [[Deference Done Better]] fn 51
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fn51_not_simpleTrust : ¬ SimpleTrust π51 fn51 := by
  intro h
  obtain ⟨h0, h1, h2⟩ := fn51_P
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  have hev : fn51.probEvent {1, 2} (4 / 10) = univ := by
    ext w
    fin_cases w <;> simp [Frame.probEvent, mass, h0, h1, h2, fin3_mk_two, sum_pair h12]
    all_goals norm_num
  have := h {1, 2} (4 / 10)
  rw [hev] at this
  norm_num [mass, π51, Fin.sum_univ_three, vec3_two, sum_pair h12] at this

/-- **The fn 51 conjecture, proved.** Squared-Euclidean dominance on all estimates implies New
Reflection (strong reading): for every candidate `ρ ∈ C_π`, `0 < ρ(P = ρ)` and
`π(· | P = ρ) = ρ(· | P = ρ)` in product form. DDB: "may entail New Reflection (we've been
unable to find a counterexample)"; the corpus (coverage critique 3) listed it as open. The proof
uses dominance only at the finite family of variables `π u 𝟙_v − π v 𝟙_u` and `𝟙_v` for `u, v`
in a cell — so dominance on that family already forces NR-str; the family cannot be shrunk to
indicators of singletons alone, since DDB's converse failure lives at `𝟙_{w₀}`
(`fig2_not_sqEuclidDominance`).
Source: [[Deference Done Better]] §3 l. 303, fn 51; item 066 (ii); mandate Target 12 (ii)
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem SqEuclidDominance.newReflects {W : Type} [Fintype W] [DecidableEq W] {π : W → ℝ}
    (hπ : π ∈ stdSimplex ℝ W) {F : Frame W} (h : SqEuclidDominance π F) : NewReflects π F := by
  intro ρ hρ
  obtain ⟨v, hv, hρv⟩ := Frame.mem_cands.1 hρ
  set K := F.cell ρ with hK
  have hvK : v ∈ K := by rw [hK, Frame.mem_cell]; exact hρv
  have hρmem : ρ ∈ stdSimplex ℝ W := by rw [← hρv]; exact F.P_mem v
  have hKpos : 0 < mass π K := mass_pos_of_mem hπ.1 hvK hv
  -- the pointwise identity behind every use of dominance
  have key : ∀ X : W → ℝ, ∑ w, π w * (E π X - X w) ^ 2 - ∑ w, π w * (E (F.P w) X - X w) ^ 2 =
      ∑ w, π w * (E (F.P w) X - E π X) * (2 * X w - E (F.P w) X - E π X) := by
    intro X
    rw [← sum_sub_distrib]
    apply sum_congr rfl; intro w _; ring
  -- Step 1: `π u ρ v' = π v' ρ u` for `u, v' ∈ K`
  have cross : ∀ u ∈ K, ∀ v' ∈ K, π u * ρ v' = π v' * ρ u := by
    intro u hu v' hv'
    set X : W → ℝ := fun w => π u * ind {v'} w - π v' * ind {u} w with hX
    have hEπ : E π X = 0 := by
      simp only [E, hX, mul_sub, sum_sub_distrib, ind]
      simp [mul_comm]
    have hEρ : E ρ X = π u * ρ v' - π v' * ρ u := by
      simp only [E, hX, mul_sub, sum_sub_distrib, ind]
      simp [mul_comm]
    have hXoff : ∀ w, w ∉ K → X w = 0 := by
      intro w hw
      have h1 : w ≠ v' := fun e => hw (e ▸ hv')
      have h2 : w ≠ u := fun e => hw (e ▸ hu)
      simp [hX, ind, h1, h2]
    have hd := h X
    have hk := key X
    rw [hEπ] at hk hd
    -- on `K` the estimate is `E_ρ(X)`; off `K`, `X = 0`
    have hterm : ∀ w, π w * (E (F.P w) X - 0) * (2 * X w - E (F.P w) X - 0) ≤
        if w ∈ K then π w * E ρ X * (2 * X w - E ρ X) else 0 := by
      intro w
      by_cases hw : w ∈ K
      · rw [if_pos hw]
        have : F.P w = ρ := by rw [hK, Frame.mem_cell] at hw; exact hw
        rw [this]; simp
      · rw [if_neg hw, hXoff w hw]
        have : π w * (E (F.P w) X - 0) * (2 * 0 - E (F.P w) X - 0) =
            -(π w * (E (F.P w) X) ^ 2) := by ring
        rw [this]
        have := mul_nonneg (hπ.1 w) (sq_nonneg (E (F.P w) X))
        linarith
    have hsum : ∑ w, (if w ∈ K then π w * E ρ X * (2 * X w - E ρ X) else 0) =
        -(E ρ X) ^ 2 * mass π K := by
      rw [sum_ite_mem, univ_inter]
      have hXK : ∑ w ∈ K, π w * X w = 0 := by
        rw [← hEπ]
        simp only [E]
        apply sum_subset (subset_univ K)
        intro w _ hw
        rw [hXoff w hw, mul_zero]
      have : ∑ w ∈ K, π w * E ρ X * (2 * X w - E ρ X) =
          2 * E ρ X * ∑ w ∈ K, π w * X w - (E ρ X) ^ 2 * mass π K := by
        simp only [mass, mul_sum]
        rw [← sum_sub_distrib]
        apply sum_congr rfl; intro w _; ring
      rw [this, hXK]; ring
    have hle : ∑ w, π w * (E (F.P w) X - 0) * (2 * X w - E (F.P w) X - 0) ≤
        -(E ρ X) ^ 2 * mass π K := by
      rw [← hsum]
      exact sum_le_sum fun w _ => hterm w
    have hq0 : (E ρ X) ^ 2 * mass π K ≤ 0 := by linarith
    have hsq : (E ρ X) ^ 2 ≤ 0 := by
      by_contra hcon
      have := mul_pos (lt_of_not_ge hcon) hKpos
      linarith
    have hq' : E ρ X = 0 := by nlinarith [sq_nonneg (E ρ X)]
    rw [hEρ] at hq'
    linarith
  -- Step 2: `ρ(K) > 0`, from `X = 𝟙_{v}`
  have hρK : 0 < mass ρ K := by
    by_contra hcon
    have hρK0 : mass ρ K = 0 := le_antisymm (not_lt.1 hcon) (mass_nonneg hρmem.1 K)
    have hρv0 : ρ v = 0 := eq_zero_of_mass_eq_zero hρmem.1 hρK0 hvK
    have hd := h (ind {v})
    simp only [E_ind] at hd
    have hmv : mass π {v} = π v := by simp [mass]
    have hmw : ∀ w, mass (F.P w) {v} = F.P w v := by intro w; simp [mass]
    simp only [hmv, hmw] at hd
    -- left side ≥ π v (the `w = v` term); right side = π v (1 − π v)
    have hL : π v ≤ ∑ w, π w * (F.P w v - ind {v} w) ^ 2 := by
      have hv' : F.P v v = 0 := by rw [hρv]; exact hρv0
      calc π v = π v * (F.P v v - ind {v} v) ^ 2 := by simp [hv', ind]
        _ ≤ ∑ w, π w * (F.P w v - ind {v} w) ^ 2 :=
          single_le_sum (f := fun w => π w * (F.P w v - ind {v} w) ^ 2)
            (fun w _ => mul_nonneg (hπ.1 w) (sq_nonneg _)) (mem_univ v)
    have hR : ∑ w, π w * (π v - ind {v} w) ^ 2 = π v * (1 - π v) := by
      have e1 : ∀ w, π w * (π v - ind {v} w) ^ 2 =
          π w * π v ^ 2 - (if w = v then π v * (2 * π v - 1) else 0) := by
        intro w
        by_cases hw : w = v
        · subst hw; simp [ind]; ring
        · simp [ind, hw]
      simp only [e1, sum_sub_distrib, ← sum_mul, hπ.2, one_mul, sum_ite_eq', mem_univ, if_true]
      ring
    rw [hR] at hd
    nlinarith
  refine ⟨hρK, ?_⟩
  -- Step 3: the product identity, summing `cross` over `u ∈ K`
  intro w
  simp only [Frame.selfMass, ← hK]
  by_cases hw : w ∈ K
  · simp only [ind, hw, if_true, mul_one]
    simp only [mass, mul_sum, sum_mul]
    apply sum_congr rfl
    intro u hu
    exact cross w hw u hu
  · simp [ind, hw]

/-- **The converse fails**: Figure 2's frame is new-reflected by `π = (½, ½)` (foundation,
`fig2_newReflects`) yet dominance fails at `X = 𝟙_{w₀}`: `16/25 > 1/4`.
Source: [[Deference Done Better]] fn 51 ("Figure 2 shows that `π` can new-reflect `P` while
knowing that `P` is less accurate than `π`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem fig2_not_sqEuclidDominance : NewReflects half fig2 ∧ ¬ SqEuclidDominance half fig2 := by
  refine ⟨fig2_newReflects, ?_⟩
  intro h
  have := h (ind {0})
  norm_num [E, ind, Fin.sum_univ_two, fig2_P0, fig2_P1, half] at this

end

end Cleanroom.Lit.LitDdbAccuracyMm
