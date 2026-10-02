import Cleanroom.Found.LitDdbFrames.TotalTrust
import Cleanroom.Found.LitDdbFrames.Strategies
import Cleanroom.Found.LitDdbFrames.Hull
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# The cycle: Lemmas 7.1, 7.2, 7.3

Package `lit-ddb-frames`, Targets 12–14:
`WeakValue → TotalTrust → HullAndModestlyInformed → WeakValue`. Lemma 7.5 (Weak Value → Value)
and Theorem 7.6 are in `Value.lean`.

Lemma 7.2 uses Hahn–Banach (`geometric_hahn_banach_point_closed` / `_closed_point`) on
`W → ℝ`, with the separating functional extracted as a random variable
(`StrongDual.apply_eq_E`, reusable by `lit-ddb-facts`). Lemma 7.3 is DDB's informed
tie-breaking strategy plus the maximal-set lemma of `Hull.lean` in place of their `A_i^*`
argument.
-/

namespace Cleanroom.Found.LitDdbFrames

open Finset

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Lemma 7.1: Weak Value → Total Trust -/

/-- A threshold strictly between `a` and `t` that also lies strictly above every attained
expert estimate below `t` (finitely many).
Source: [[Deference Done Better]] App. B Lemma 7.1 l. 484 ("let `s` be any number strictly
between `max(a, b)` and `t`")
Kind: L
Fidelity: n/a -/
theorem Frame.exists_sep_threshold (F : Frame W) (X : W → ℝ) {a t : ℝ} (hat : a < t) :
    ∃ s, a < s ∧ s < t ∧ ∀ w, E (F.P w) X < t → E (F.P w) X < s := by
  set B := univ.filter (fun w => E (F.P w) X < t) with hB
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · refine ⟨(a + t) / 2, by linarith, by linarith, ?_⟩
    intro w hw
    exfalso
    have hwB : w ∈ B := mem_filter.2 ⟨mem_univ w, hw⟩
    rw [hBe] at hwB
    exact absurd hwB (Finset.notMem_empty w)
  · obtain ⟨m, hm, hmax⟩ := B.exists_max_image (fun w => E (F.P w) X) hBne
    have hmt : E (F.P m) X < t := (mem_filter.1 hm).2
    have hlt := max_lt hat hmt
    refine ⟨(max a (E (F.P m) X) + t) / 2, ?_, by linarith, ?_⟩
    · have := le_max_left a (E (F.P m) X); linarith
    · intro w hw
      have h1 : E (F.P w) X ≤ E (F.P m) X := hmax w (mem_filter.2 ⟨mem_univ w, hw⟩)
      have := le_max_right a (E (F.P m) X)
      linarith

/-- **Target 12 (Lemma 7.1).** Weak Value implies Total Trust. Contrapositive: a failure of
Total Trust at `(X, t)` has `0 < π(E(X) ≥ t)`; pick `s` strictly between the conditional
expectation `a`, the largest attained estimate below `t`, and `t`; on the menu `{X, const s}`
the recommended strategy is unique and worth less than `const s`. This direction alone is not
Theorem 2.2.
Source: [[Deference Done Better]] App. B Lemma 7.1 l. 480
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem WeakValue.totalTrust {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : WeakValue π F) : TotalTrust π F := by
  by_contra hnot
  unfold TotalTrust at hnot
  push_neg at hnot
  obtain ⟨X, t, hlt⟩ := hnot
  rw [totalTrust_sum_eq] at hlt
  set A := F.estEvent X t with hA
  have hApos : 0 < mass π A := by
    rcases (mass_nonneg hπ.1 A).lt_or_eq with hp | hz
    · exact hp
    · rw [prod_sum_eq_zero_of_mass_eq_zero hπ.1 hz.symm] at hlt
      exact absurd hlt (lt_irrefl _)
  set a := (∑ w ∈ A, π w * X w) / mass π A with ha
  have hat : a < t := by
    by_contra hge
    push_neg at hge
    exact absurd ((prod_ineq_iff_cond hApos).2 hge) (not_le.2 hlt)
  obtain ⟨s, has, hst, hsep⟩ := F.exists_sep_threshold X hat
  obtain ⟨S, hS, hval⟩ := h {X, fun _ => s} (insert_nonempty _ _)
  have hSA : ∀ w, w ∈ A → S w = X := by
    intro w hw
    rw [hA, Frame.mem_estEvent] at hw
    have hmem := hS.mem w
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with h' | h'
    · exact h'
    · exfalso
      have h1 := hS.le w (o := X) (by simp)
      rw [h', E_const (F.P_mem w)] at h1
      linarith
  have hSA' : ∀ w, w ∉ A → S w = fun _ => s := by
    intro w hw
    rw [hA, Frame.mem_estEvent, not_le] at hw
    have hmem := hS.mem w
    simp only [mem_insert, mem_singleton] at hmem
    rcases hmem with h' | h'
    · exfalso
      have h1 := hS.le w (o := fun _ => s) (by simp)
      rw [h', E_const (F.P_mem w)] at h1
      have := hsep w hw
      linarith
    · exact h'
  have hSval : stratValue π S = (∑ w ∈ A, π w * X w) + s * mass π (univ \ A) := by
    unfold stratValue
    rw [← sum_sdiff (subset_univ A), add_comm]
    congr 1
    · apply sum_congr rfl
      intro w hw
      rw [hSA w hw]
    · rw [mass, mul_sum]
      apply sum_congr rfl
      intro w hw
      rw [hSA' w (mem_sdiff.1 hw).2]
      ring
  have hcompl : mass π (univ \ A) = 1 - mass π A := by
    have := mass_inter_add_mass_sdiff π univ A
    rw [univ_inter, mass_univ hπ] at this
    linarith
  have h1 := hval (fun _ => s) (by simp)
  rw [E_const hπ, hSval, hcompl] at h1
  have h2 : ∑ w ∈ A, π w * X w = a * mass π A := by
    rw [ha, div_mul_cancel₀ _ hApos.ne']
  rw [h2] at h1
  have h3 : (a - s) * mass π A < 0 := mul_neg_of_neg_of_pos (by linarith) hApos
  have e : a * mass π A + s * (1 - mass π A) = s + (a - s) * mass π A := by ring
  linarith

/-! ## Lemma 7.2: Total Trust → the hull condition -/

/-- **Target 24 / extraction lemma.** A continuous linear functional on `W → ℝ` is the
expectation of the random variable `w ↦ f(𝟙_{w})`: `f ρ = E_ρ(X)`. This turns a Hahn–Banach
separating functional into a cut `{ρ : E_ρ(X) = u}`; reusable by `lit-ddb-facts` (item 054).
Source: [[Deference Done Better]] §2 l. 213 (cuts are `{ρ : E_ρ(X) = t}`)
Kind: L
Fidelity: n/a -/
theorem StrongDual.apply_eq_E (f : StrongDual ℝ (W → ℝ)) (ρ : W → ℝ) :
    f ρ = E ρ (fun w => f (fun j => if w = j then 1 else 0)) := by
  conv_lhs => rw [pi_eq_sum_univ ρ]
  simp [E, map_sum, map_smul, smul_eq_mul]

/-- **Target 13 (Lemma 7.2, first half).** Total Trust puts `π` in the convex hull of its
candidates: otherwise Hahn–Banach gives `X, u` with `E_π(X) < u < E_{P_w}(X)` for every
candidate, so `π(E(X) ≥ u) = 1` and the product form is `E_π(X) − u < 0`.
Source: [[Deference Done Better]] App. B Lemma 7.2 l. 534
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem TotalTrust.mem_convexHull_cands {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : TotalTrust π F) : π ∈ convexHull ℝ (↑(F.cands π) : Set (W → ℝ)) := by
  by_contra hnot
  obtain ⟨f, u, hfπ, hf⟩ := geometric_hahn_banach_point_closed (convex_convexHull ℝ _)
    ((F.cands π).finite_toSet.isClosed_convexHull ℝ) hnot
  set X : W → ℝ := fun w => f (fun j => if w = j then 1 else 0) with hX
  have hfE : ∀ ρ, f ρ = E ρ X := fun ρ => StrongDual.apply_eq_E f ρ
  have h1 := h.event_sum X u
  have hev : ∀ w, 0 < π w → w ∈ F.estEvent X u := by
    intro w hw
    rw [Frame.mem_estEvent, ← hfE]
    exact (hf _ (subset_convexHull ℝ _ (mem_coe.2 (F.P_mem_cands hw)))).le
  have h2 : ∑ w ∈ F.estEvent X u, π w * (X w - u) = ∑ w, π w * (X w - u) := by
    apply sum_subset (subset_univ _)
    intro w _ hw
    have : π w = 0 := by
      by_contra hne
      exact hw (hev w (lt_of_le_of_ne (hπ.1 w) (Ne.symm hne)))
    simp [this]
  rw [h2] at h1
  have h3 : ∑ w, π w * (X w - u) = E π X - u := by
    simp [E, mul_sub, sum_sub_distrib, ← sum_mul, hπ.2]
  rw [h3, ← hfE] at h1
  linarith

/-- **Target 13 (Lemma 7.2, second half).** Total Trust implies class-convexity: separate a
candidate `ρ` from `convexHull ({P̂_ρ} ∪ (C_π \ {ρ}))` by `(X, u)`; then `[E(X) ≥ u]` meets `W_π`
exactly in `ρ`'s cell, and New Reflection at `ρ` (Target 11(c)) turns the product sum into
`π(P = ρ) · (E_{P̂_ρ}(X) − u) < 0`.
Source: [[Deference Done Better]] App. B Lemma 7.2 l. 536
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem TotalTrust.classConvex {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : TotalTrust π F) : ClassConvex π F := by
  intro ρ hρ
  by_contra hnot
  have hpos := h.selfMass_pos hπ.1 hρ
  have hm : 0 < mass π (F.cell ρ) := (F.mem_cands_iff_mass_cell_pos hπ.1).1 hρ
  have hfin : (insert (F.informed ρ) (↑((F.cands π).erase ρ) : Set (W → ℝ))).Finite :=
    ((F.cands π).erase ρ).finite_toSet.insert _
  obtain ⟨f, u, hf, hfρ⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
    (hfin.isClosed_convexHull ℝ) hnot
  set X : W → ℝ := fun w => f (fun j => if w = j then 1 else 0) with hX
  have hfE : ∀ σ, f σ = E σ X := fun σ => StrongDual.apply_eq_E f σ
  have hK : ∀ σ ∈ insert (F.informed ρ) (↑((F.cands π).erase ρ) : Set (W → ℝ)), E σ X < u :=
    fun σ hσ => by rw [← hfE]; exact hf σ (subset_convexHull ℝ _ hσ)
  have hρu : u < E ρ X := by rw [← hfE]; exact hfρ
  have h1 := h.event_sum X u
  -- the event meets the support of `π` exactly in the cell of `ρ`
  have hsum : ∑ w ∈ F.estEvent X u, π w * (X w - u) = ∑ w ∈ F.cell ρ, π w * (X w - u) := by
    rw [← univ_inter (F.estEvent X u), ← sum_ite_mem, ← univ_inter (F.cell ρ), ← sum_ite_mem]
    apply sum_congr rfl
    intro w _
    rcases (hπ.1 w).lt_or_eq with hw | hw
    · by_cases hc : F.P w = ρ
      · have hin : w ∈ F.estEvent X u := by
          rw [Frame.mem_estEvent, hc]; exact hρu.le
        simp [hin, hc]
      · have hout : w ∉ F.estEvent X u := by
          rw [Frame.mem_estEvent, not_le]
          exact hK _ (Set.mem_insert_of_mem _ (by
            rw [mem_coe, mem_erase]; exact ⟨hc, F.P_mem_cands hw⟩))
        simp [hout, hc]
    · simp [← hw]
  -- New Reflection at `ρ` turns the cell sum into `π(P = ρ) · (E_{P̂_ρ}(X) − u) · ρ(P = ρ)`
  have hkey : (∑ w ∈ F.cell ρ, π w * (X w - u)) * F.selfMass ρ =
      mass π (F.cell ρ) * ((E (F.informed ρ) X - u) * F.selfMass ρ) := by
    rw [sum_mul]
    have hterm : ∀ w ∈ F.cell ρ, π w * (X w - u) * F.selfMass ρ =
        mass π (F.cell ρ) * (ρ w * (X w - u)) := by
      intro w hw
      rw [mul_right_comm, h.cell_identity hπ.1 hρ (Frame.mem_cell.1 hw)]
      ring
    rw [sum_congr rfl hterm, ← mul_sum]
    congr 1
    rw [sub_mul, F.E_informed_mul_selfMass hpos]
    simp only [mul_sub, sum_sub_distrib, Frame.selfMass, mass, mul_sum]
    congr 1
    apply sum_congr rfl
    intro w _
    ring
  have hinf : E (F.informed ρ) X < u := hK _ (Set.mem_insert _ _)
  have hneg : (E (F.informed ρ) X - u) * F.selfMass ρ < 0 :=
    mul_neg_of_neg_of_pos (by linarith) hpos
  have hlt : (∑ w ∈ F.cell ρ, π w * (X w - u)) * F.selfMass ρ < 0 := by
    rw [hkey]; exact mul_neg_of_pos_of_neg hm hneg
  rw [hsum] at h1
  have := mul_nonneg h1 hpos.le
  linarith

/-- **Target 13 (Lemma 7.2).** Total Trust implies the hull condition: `π ∈ convexHull C_π` and
every candidate is modestly informed (via class-convexity and Lemma 7.2.7).
Source: [[Deference Done Better]] App. B Lemma 7.2 l. 498
Kind: C
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem TotalTrust.hullAndModestlyInformed {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : TotalTrust π F) : HullAndModestlyInformed π F :=
  ⟨h.mem_convexHull_cands hπ,
    (classConvex_iff_modestlyInformed hπ (h.mem_convexHull_cands hπ)).1 (h.classConvex hπ)⟩

/-! ## Lemma 7.3: the hull condition → Weak Value -/

/-- The informed expert's expectation of a cellwise strategy's diagonal is its expectation of the
option chosen on the cell (`P̂_ρ` knows the cell).
Source: [[Deference Done Better]] App. B Lemma 7.3 l. 550 (F3: "`P̂_j(S = S_j) = 1`")
Kind: L
Fidelity: n/a -/
theorem Frame.E_informed_diag (F : Frame W) {ρ : W → ℝ} {S : W → (W → ℝ)}
    (hcell : ∀ w v, F.P w = F.P v → S w = S v) {w : W} (hw : F.P w = ρ) :
    E (F.informed ρ) (fun v => S v v) = E (F.informed ρ) (S w) := by
  unfold E
  apply sum_congr rfl
  intro v _
  dsimp only
  by_cases hv : F.P v = ρ
  · rw [hcell v w (hv.trans hw.symm)]
  · rw [F.informed_eq_zero_of_ne hv]; simp

/-- **Target 14 (Lemma 7.3).** The hull condition implies Weak Value, witnessed by the informed
tie-breaking strategy: if some candidate `P_i` preferred an option `O` to it, take the pair
`(O', m)` maximising the divergence `E_j(O' − S)` over options and seen worlds; the maximisers
form a selfless set under class-convexity (each decomposes over its informed self, where the
divergence is `≤ 0`, and other candidates with no larger divergence), contradicting the
maximal-set lemma. Then average over `π = ∑ λ_ρ ρ`.
Source: [[Deference Done Better]] App. B Lemma 7.3 l. 540
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` only -/
theorem HullAndModestlyInformed.weakValue {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W}
    (h : HullAndModestlyInformed π F) : WeakValue π F := by
  intro 𝒪 hne
  refine ⟨F.informedStrategy 𝒪 hne, F.informedStrategy_recommended 𝒪 hne, ?_⟩
  set S := F.informedStrategy 𝒪 hne with hS
  have hrec := F.informedStrategy_recommended 𝒪 hne
  have hcc := h.classConvex hπ
  set Sd : W → ℝ := fun v => S v v with hSd
  -- every candidate weakly values `S`
  have hclaim : ∀ i, 0 < π i → ∀ o ∈ 𝒪, E (F.P i) o ≤ E (F.P i) Sd := by
    by_contra hnot
    push_neg at hnot
    obtain ⟨i, hi, o, ho, hlt⟩ := hnot
    obtain ⟨⟨o', m⟩, hom, hmax⟩ := (𝒪 ×ˢ supp π).exists_max_image
      (fun p => E (F.P p.2) (p.1 - Sd)) ⟨(o, i), mem_product.2 ⟨ho, mem_supp.2 hi⟩⟩
    obtain ⟨ho', hm⟩ := mem_product.1 hom
    simp only at hmax
    have hαpos : 0 < E (F.P m) (o' - Sd) := by
      have := hmax (o, i) (mem_product.2 ⟨ho, mem_supp.2 hi⟩)
      simp only at this
      rw [E_sub_right] at this
      linarith
    set M0 := (supp π).filter (fun j => E (F.P j) (o' - Sd) = E (F.P m) (o' - Sd)) with hM0
    set M := M0.image F.P with hM
    have hMne : M.Nonempty := ⟨F.P m, mem_image.2 ⟨m, mem_filter.2 ⟨hm, rfl⟩, rfl⟩⟩
    refine no_selfless_maximal_set M hMne (o' - Sd) (E (F.P m) (o' - Sd)) ?_ ?_
    · intro σ hσ
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hσ
      exact (mem_filter.1 hj).2
    · intro σ hσ
      obtain ⟨j, hj, rfl⟩ := mem_image.1 hσ
      obtain ⟨hjs, hjα⟩ := mem_filter.1 hj
      have hjπ : 0 < π j := mem_supp.1 hjs
      -- F2: `o'` maximises `E_j` over the menu
      have hF2 : o' ∈ maximizers 𝒪 (F.P j) := by
        rw [mem_maximizers]
        refine ⟨ho', fun o'' ho'' => ?_⟩
        by_contra hgt
        push_neg at hgt
        have h1 := hmax (o'', j) (mem_product.2 ⟨ho'', hjs⟩)
        simp only at h1
        rw [E_sub_right, E_sub_right] at h1 hjα
        linarith
      -- F3: the informed expert's divergence is `≤ 0`
      have hF3 : E (F.informed (F.P j)) (o' - Sd) ≤ 0 := by
        rw [E_sub_right, hSd, F.E_informed_diag hrec.1.2 rfl]
        have := F.informedStrategy_informed_le 𝒪 hne j hF2
        linarith
      obtain hdecj := hcc (F.P j) (F.P_mem_cands hjπ)
      rw [← coe_insert] at hdecj
      obtain ⟨c, hc₀, hc₁, hs⟩ := Finset.mem_convexHull'.1 hdecj
      refine ⟨_, c, hc₀, hc₁, hs, ?_⟩
      intro y hy _
      rcases mem_insert.1 hy with rfl | hyC
      · exact ⟨hF3.trans hαpos.le, fun e => absurd e (by linarith)⟩
      · obtain ⟨hne', hyc⟩ := mem_erase.1 hyC
        obtain ⟨k, hk, rfl⟩ := Frame.mem_cands.1 hyc
        have h1 := hmax (o', k) (mem_product.2 ⟨ho', mem_supp.2 hk⟩)
        simp only at h1
        exact ⟨h1, fun e => ⟨mem_image.2 ⟨k, mem_filter.2 ⟨mem_supp.2 hk, e⟩, rfl⟩, hne'⟩⟩
  -- average over the hull decomposition of `π`
  intro o ho
  obtain ⟨lam, hl₀, hl₁, hπeq, _⟩ := F.exists_weights_of_hull hπ h.1
  rw [stratValue_eq_E, ← hπeq, E_sum_left, E_sum_left]
  apply sum_le_sum
  intro ρ hρ
  obtain ⟨i, hi, rfl⟩ := Frame.mem_cands.1 hρ
  exact mul_le_mul_of_nonneg_left (hclaim i hi o ho) (hl₀ _ hρ)

end

end Cleanroom.Found.LitDdbFrames
