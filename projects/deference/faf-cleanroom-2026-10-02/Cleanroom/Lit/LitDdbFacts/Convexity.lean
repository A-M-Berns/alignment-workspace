import Cleanroom.Lit.LitDdbFacts.Reflection
import Mathlib.Analysis.LocallyConvex.Separation

/-!
# The convexity formulations of Reflection and Total Trust (§2 ll. 219–227)

Package `lit-ddb-facts`, Target 7. Reflection is "`π(· | P ∈ C) ∈ C` for every convex `C`";
Total Trust is "`π(· | P ∈ B) ∈ B` for every biconvex `B`" (both `B` and `Bᶜ` convex). The
content is (⇒) of the second: fn 34's separation of `{P_w ∈ B}` from `{P_w ∉ B}` alone does not
place the conditional `π* = π(· | P ∈ B)` on the right side; `π*` must be separated *together
with* the `Bᶜ` rows, which is where convexity of `Bᶜ` is used
(`geometric_hahn_banach_compact_closed` on two finite hulls). Fn 34's strong separation on finite
frames is `biconvex_strong_sep`. The claim at §2 l. 219 that hyperplanes are the only divisions
into two convex sets is false as stated: `∅`/`univ` are biconvex (degenerately — they are not
divisions into two sets), and the lexicographic half-space `Examples.lexHalf` is biconvex but
neither a closed nor an open half-space, in `ℝ^W` and inside the simplex (its topological
boundary *is* a hyperplane, as fn 34 says, which is what hides the gap); the theorem needs only
the separation.
-/

namespace Cleanroom.Lit.LitDdbFacts

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Definitions of record -/

/-- A set of distributions is **biconvex** when it and its complement are convex. The complement
is taken in `ℝ^W`, as the glossary's definition (l. 410, `B ⊆ ℝ^n`) has it; §2 l. 223 ("divide
probability space") suggests the complement relative to the simplex, and the two readings give
the same headline: the (⇒) proof of `totalTrust_iff_totalTrustBiconvex` uses convexity of the
complement only on rows and on the conditional `π*`, all of which lie in the simplex, and the
relative version implies the `ℝ^W` one trivially.
Source: [[Deference Done Better]] §2 l. 223, glossary l. 410
Kind: D
Fidelity: exact -/
def Biconvex (B : Set (W → ℝ)) : Prop := Convex ℝ B ∧ Convex ℝ Bᶜ

open Classical in
/-- The proposition `[P ∈ B]`: worlds at which the expert's distribution lies in `B`.
Source: [[Deference Done Better]] §2 l. 217 (`π(· | P ∈ C)`)
Kind: D
Fidelity: exact -/
def memEvent (F : Frame W) (B : Set (W → ℝ)) : Finset W := univ.filter (fun w => F.P w ∈ B)

/-- Membership in `[P ∈ B]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_memEvent {F : Frame W} {B : Set (W → ℝ)} {w : W} :
    w ∈ memEvent F B ↔ F.P w ∈ B := by
  simp [memEvent]

/-- "`π(· | P ∈ B) ∈ B`" in product form: some `σ ∈ B` satisfies
`π w · 𝟙[P_w ∈ B] = π(P ∈ B) · σ w` at every world. Under `0 < π(P ∈ B)` the `σ` is the ratio
vector `condOn` (`condIn_iff`).
Source: [[Deference Done Better]] §2 ll. 217, 225
Kind: D
Fidelity: exact -/
def CondIn (π : W → ℝ) (F : Frame W) (B : Set (W → ℝ)) : Prop :=
  ∃ σ ∈ B, ∀ w, π w * ind (memEvent F B) w = mass π (memEvent F B) * σ w

/-- **Reflection (convexity version)**: `π(· | P ∈ C) ∈ C` for every convex `C` with
`π(P ∈ C) > 0`.
Source: [[Deference Done Better]] §2 l. 221
Kind: D
Fidelity: exact -/
def ReflectsConvex (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ C : Set (W → ℝ), Convex ℝ C → 0 < mass π (memEvent F C) → CondIn π F C

/-- **Total Trust (convexity version)**: `π(· | P ∈ B) ∈ B` for every biconvex `B` with
`π(P ∈ B) > 0`.
Source: [[Deference Done Better]] §2 l. 225
Kind: D
Fidelity: exact -/
def TotalTrustBiconvex (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ B : Set (W → ℝ), Biconvex B → 0 < mass π (memEvent F B) → CondIn π F B

open Classical in
/-- The conditional distribution `π(· | P ∈ B)` as a ratio vector (meaningful under
`0 < π(P ∈ B)`; lemma-level, never in a definition of record).
Source: [[Deference Done Better]] §2 l. 217
Kind: D
Fidelity: exact (under `0 < π(P ∈ B)`) -/
def condOn (F : Frame W) (π : W → ℝ) (B : Set (W → ℝ)) : W → ℝ :=
  fun w => if F.P w ∈ B then π w / mass π (memEvent F B) else 0

/-- Under `0 < π(P ∈ B)`, `CondIn` says exactly that the ratio vector lies in `B`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condIn_iff {π : W → ℝ} {F : Frame W} {B : Set (W → ℝ)}
    (hpos : 0 < mass π (memEvent F B)) : CondIn π F B ↔ condOn F π B ∈ B := by
  constructor
  · rintro ⟨σ, hσ, hid⟩
    have : condOn F π B = σ := by
      funext w
      unfold condOn
      have := hid w
      by_cases hw : F.P w ∈ B
      · rw [if_pos hw]
        rw [show ind (memEvent F B) w = 1 by simp [ind, mem_memEvent, hw], mul_one] at this
        rw [this, mul_div_cancel_left₀ _ hpos.ne']
      · rw [if_neg hw]
        rw [show ind (memEvent F B) w = 0 by simp [ind, mem_memEvent, hw], mul_zero] at this
        rcases mul_eq_zero.1 this.symm with h | h
        · exact absurd h hpos.ne'
        · exact h.symm
    rw [this]; exact hσ
  · intro hmem
    refine ⟨condOn F π B, hmem, fun w => ?_⟩
    unfold condOn
    by_cases hw : F.P w ∈ B
    · rw [if_pos hw, show ind (memEvent F B) w = 1 by simp [ind, mem_memEvent, hw], mul_one,
        mul_div_cancel₀ _ hpos.ne']
    · rw [if_neg hw, show ind (memEvent F B) w = 0 by simp [ind, mem_memEvent, hw], mul_zero,
        mul_zero]

/-- The conditional ratio vector is a distribution.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condOn_mem_stdSimplex {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W} {B : Set (W → ℝ)}
    (hpos : 0 < mass π (memEvent F B)) : condOn F π B ∈ stdSimplex ℝ W := by
  classical
  refine ⟨fun w => ?_, ?_⟩
  · unfold condOn
    split_ifs
    · exact div_nonneg (hπ w) hpos.le
    · exact le_rfl
  · unfold condOn
    have e : ∀ w, (if F.P w ∈ B then π w / mass π (memEvent F B) else 0) =
        (mass π (memEvent F B))⁻¹ * (if F.P w ∈ B then π w else 0) := by
      intro w; split_ifs <;> ring
    simp only [e]
    rw [← mul_sum]
    have hM : ∑ w, (if F.P w ∈ B then π w else 0) = mass π (memEvent F B) := by
      unfold mass memEvent
      rw [sum_filter]
    rw [hM, inv_mul_cancel₀ hpos.ne']

/-- `π`-weighted sums over `[P ∈ B]` are `π(P ∈ B)` times the conditional expectation.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_memEvent_eq_condOn {π : W → ℝ} {F : Frame W} {B : Set (W → ℝ)}
    (hpos : 0 < mass π (memEvent F B)) (g : W → ℝ) :
    ∑ w ∈ memEvent F B, π w * g w = mass π (memEvent F B) * E (condOn F π B) g := by
  classical
  have e : ∑ w ∈ memEvent F B, π w * g w = ∑ w, if F.P w ∈ B then π w * g w else 0 := by
    unfold memEvent
    rw [sum_filter]
  rw [e]
  unfold E condOn
  rw [mul_sum]
  apply sum_congr rfl
  intro w _
  split_ifs
  · rw [← mul_assoc, mul_div_cancel₀ _ hpos.ne']
  · ring

/-! ## Target 7(i): Reflection ⟺ its convexity version -/

/-- **Target 7(i).** Reflection is equivalent to its convexity version. (⇒) the conditional
`π(· | P ∈ C)` is the convex combination `∑_{ρ ∈ C_π ∩ C} (π(P = ρ)/π(P ∈ C)) ρ` (Reflection on
each cell, candidates supported on their cells by Target 1), so it lies in `C`. (⇐) take
`C = {ρ}`.
Source: [[Deference Done Better]] §2 l. 221
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem reflects_iff_reflectsConvex {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W} :
    Reflects π F ↔ ReflectsConvex π F := by
  classical
  constructor
  · intro h C hC hpos
    rw [condIn_iff hpos]
    set T := (F.cands π).filter (fun ρ => ρ ∈ C) with hT
    have hsum : ∑ ρ ∈ T, mass π (F.cell ρ) = mass π (memEvent F C) := by
      rw [mass_eq_E_ind π (memEvent F C), E, sum_mul_eq_sum_cands F hπ.1, hT, sum_filter]
      apply sum_congr rfl
      intro ρ _
      by_cases hρC : ρ ∈ C
      · rw [if_pos hρC]
        unfold mass
        apply sum_congr rfl
        intro w hw
        rw [Frame.mem_cell] at hw
        simp [ind, mem_memEvent, hw, hρC]
      · rw [if_neg hρC]
        symm
        apply sum_eq_zero
        intro w hw
        rw [Frame.mem_cell] at hw
        simp [ind, mem_memEvent, hw, hρC]
    have heq : condOn F π C = ∑ ρ ∈ T, (mass π (F.cell ρ) / mass π (memEvent F C)) • ρ := by
      funext w
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul]
      unfold condOn
      by_cases hw : F.P w ∈ C
      · rw [if_pos hw]
        by_cases hwπ : 0 < π w
        · have hmem : F.P w ∈ T := mem_filter.2 ⟨F.P_mem_cands hwπ, hw⟩
          rw [sum_eq_single (F.P w)]
          · have := h (F.P w) (F.P_mem_cands hwπ) w
            rw [show ind (F.cell (F.P w)) w = 1 by simp [ind], mul_one] at this
            rw [this]; ring
          · intro ρ hρ hne
            have hρc := (mem_filter.1 hρ).1
            rw [eq_zero_of_selfMass_eq_one F (F.mem_stdSimplex_of_mem_cands hρc)
              (selfMass_eq_one_of_reflects hπ.1 h hρc) (Ne.symm hne)]
            ring
          · intro habs; exact absurd hmem habs
        · have hz : π w = 0 := le_antisymm (not_lt.1 hwπ) (hπ.1 w)
          rw [hz, zero_div]
          symm
          apply sum_eq_zero
          intro ρ hρ
          have hρc := (mem_filter.1 hρ).1
          have hone := selfMass_eq_one_of_reflects hπ.1 h hρc
          by_cases hρw : F.P w = ρ
          · have := h ρ hρc w
            rw [show ind (F.cell ρ) w = 1 by simp [ind, hρw], mul_one, hz] at this
            have hm : 0 < mass π (F.cell ρ) := (F.mem_cands_iff_mass_cell_pos hπ.1).1 hρc
            rcases mul_eq_zero.1 this.symm with h1 | h1
            · exact absurd h1 hm.ne'
            · rw [h1]; ring
          · rw [eq_zero_of_selfMass_eq_one F (F.mem_stdSimplex_of_mem_cands hρc) hone hρw]
            ring
      · rw [if_neg hw]
        symm
        apply sum_eq_zero
        intro ρ hρ
        have hρC := (mem_filter.1 hρ).2
        have hne : F.P w ≠ ρ := fun e => hw (e ▸ hρC)
        rw [eq_zero_of_selfMass_eq_one F (F.mem_stdSimplex_of_mem_cands (mem_filter.1 hρ).1)
          (selfMass_eq_one_of_reflects hπ.1 h (mem_filter.1 hρ).1) hne]
        ring
    rw [heq]
    apply hC.sum_mem
    · intro ρ _
      exact div_nonneg (mass_nonneg hπ.1 _) (mass_nonneg hπ.1 _)
    · simp_rw [div_eq_mul_inv]
      rw [← sum_mul, hsum, mul_inv_cancel₀ hpos.ne']
    · intro ρ hρ
      exact (mem_filter.1 hρ).2
  · intro h ρ hρ w
    have hev : memEvent F {ρ} = F.cell ρ := by
      ext v; simp [mem_memEvent, Frame.mem_cell]
    have hm : 0 < mass π (F.cell ρ) := (F.mem_cands_iff_mass_cell_pos hπ.1).1 hρ
    obtain ⟨σ, hσ, hid⟩ := h {ρ} (convex_singleton ρ) (by rw [hev]; exact hm)
    rw [Set.mem_singleton_iff] at hσ
    subst hσ
    have := hid w
    rwa [hev] at this

/-! ## Target 7(ii): Total Trust ⟺ its biconvex version -/

/-- Half-spaces `{ρ : t ≤ E_ρ(X)}` are biconvex.
Source: [[Deference Done Better]] §2 l. 213
Kind: L
Fidelity: n/a -/
theorem biconvex_halfSpace (X : W → ℝ) (t : ℝ) : Biconvex {ρ : W → ℝ | t ≤ E ρ X} := by
  have hlin : IsLinearMap ℝ (fun ρ : W → ℝ => E ρ X) :=
    ⟨fun a b => E_add_left a b X, fun c a => E_smul_left c a X⟩
  refine ⟨convex_halfSpace_ge hlin t, ?_⟩
  have : {ρ : W → ℝ | t ≤ E ρ X}ᶜ = {ρ : W → ℝ | E ρ X < t} := by
    ext ρ; simp [not_le]
  rw [this]
  exact convex_halfSpace_lt hlin t

/-- **Target 7(ii), headline.** Total Trust is equivalent to its biconvex version.
(⇐) half-spaces `{ρ : s ≤ E_ρ(X)}` are biconvex and `[P ∈ B] = [E(X) ≥ s]`; membership of the
conditional in the half-space is the product inequality. (⇒) suppose `π* := π(· | P ∈ B) ∉ B`
for a biconvex `B` with `π(P ∈ B) > 0`. The finite sets `C = {P_w : w ∈ W_π, P_w ∈ B}` and
`D = {P_w : w ∈ W_π, P_w ∉ B} ∪ {π*}` have hulls inside `B` and `Bᶜ` respectively, so the hulls
are disjoint compact convex sets; Hahn–Banach gives a functional, i.e. a variable `Y`
(`StrongDual.apply_eq_E`), and `u < v` with `E(Y) < u` on `hull D` and `v < E(Y)` on `hull C`.
Then `[E(Y) ≥ v]` agrees with `[P ∈ B]` on `W_π`, so Total Trust gives `E_{π*}(Y) ≥ v`, while
`π* ∈ hull D` gives `E_{π*}(Y) < u < v`. Fn 34 alone (separating `C` from `D \ {π*}`) does not
suffice: `π*` must sit on the `D` side, which uses convexity of `Bᶜ`.
Source: [[Deference Done Better]] §2 l. 225, fn 34; item 054
Kind: P
Fidelity: exact
Hyps: (a) `hπ : π ∈ stdSimplex ℝ W` -/
theorem totalTrust_iff_totalTrustBiconvex {π : W → ℝ} (hπ : π ∈ stdSimplex ℝ W) {F : Frame W} :
    TotalTrust π F ↔ TotalTrustBiconvex π F := by
  classical
  constructor
  · intro h B hB hpos
    rw [condIn_iff hpos]
    by_contra hnot
    set π' := condOn F π B with hπ'
    set C : Finset (W → ℝ) := ((supp π).filter (fun w => F.P w ∈ B)).image F.P with hC
    set D : Finset (W → ℝ) := insert π' (((supp π).filter (fun w => F.P w ∉ B)).image F.P)
      with hD
    have hCB : (↑C : Set (W → ℝ)) ⊆ B := by
      intro x hx
      rw [mem_coe, hC, mem_image] at hx
      obtain ⟨w, hw, rfl⟩ := hx
      exact (mem_filter.1 hw).2
    have hDB : (↑D : Set (W → ℝ)) ⊆ Bᶜ := by
      intro x hx
      rw [mem_coe, hD, mem_insert] at hx
      rcases hx with rfl | hx
      · exact hnot
      · rw [mem_image] at hx
        obtain ⟨w, hw, rfl⟩ := hx
        exact (mem_filter.1 hw).2
    have hdisj : Disjoint (convexHull ℝ (↑D : Set (W → ℝ))) (convexHull ℝ (↑C : Set (W → ℝ))) := by
      rw [Set.disjoint_left]
      intro x hxD hxC
      exact (convexHull_min hDB hB.2 hxD) (convexHull_min hCB hB.1 hxC)
    obtain ⟨f, u, v, hfD, huv, hfC⟩ := geometric_hahn_banach_compact_closed
      (convex_convexHull ℝ _) (D.finite_toSet.isCompact_convexHull ℝ)
      (convex_convexHull ℝ _) (C.finite_toSet.isClosed_convexHull ℝ) hdisj
    set Y : W → ℝ := fun w => f (fun j => if w = j then 1 else 0) with hY
    have hfE : ∀ ρ, f ρ = E ρ Y := fun ρ => StrongDual.apply_eq_E f ρ
    have hev : ∀ w, 0 < π w → (w ∈ F.estEvent Y v ↔ w ∈ memEvent F B) := by
      intro w hw
      rw [Frame.mem_estEvent, mem_memEvent, ← hfE]
      constructor
      · intro hv
        by_contra hnB
        have hmem : F.P w ∈ (↑D : Set (W → ℝ)) := by
          rw [mem_coe, hD, mem_insert]
          right
          rw [mem_image]
          exact ⟨w, mem_filter.2 ⟨mem_supp.2 hw, hnB⟩, rfl⟩
        have := hfD _ (subset_convexHull ℝ _ hmem)
        linarith
      · intro hB'
        have hmem : F.P w ∈ (↑C : Set (W → ℝ)) := by
          rw [mem_coe, hC, mem_image]
          exact ⟨w, mem_filter.2 ⟨mem_supp.2 hw, hB'⟩, rfl⟩
        exact (hfC _ (subset_convexHull ℝ _ hmem)).le
    have h1 := h.event_sum Y v
    rw [sum_eq_of_supp_iff hπ.1 hev, sum_memEvent_eq_condOn hpos] at h1
    have hπ's := condOn_mem_stdSimplex hπ.1 hpos
    have h2 : E π' (fun w => Y w - v) = E π' Y - v := by
      rw [show (fun w => Y w - v) = Y - (fun _ => v) from rfl, E_sub_right, E_const hπ's]
    rw [h2] at h1
    have h3 : 0 ≤ E π' Y - v := (mul_nonneg_iff_of_pos_left hpos).1 h1
    have hπ'D : π' ∈ convexHull ℝ (↑D : Set (W → ℝ)) :=
      subset_convexHull ℝ _ (by rw [mem_coe, hD]; exact mem_insert_self _ _)
    have h4 := hfD π' hπ'D
    rw [hfE] at h4
    linarith
  · intro h X s
    rw [totalTrust_sum_eq]
    have hev : memEvent F {ρ : W → ℝ | s ≤ E ρ X} = F.estEvent X s := by
      ext w; simp [mem_memEvent, Frame.mem_estEvent]
    rcases (mass_nonneg hπ.1 (F.estEvent X s)).lt_or_eq with hpos | hzero
    · have hpos' : 0 < mass π (memEvent F {ρ : W → ℝ | s ≤ E ρ X}) := by rw [hev]; exact hpos
      obtain ⟨σ, hσ, hid⟩ := h _ (biconvex_halfSpace X s) hpos'
      rw [hev] at hid
      rw [Set.mem_setOf_eq] at hσ
      have hσs : σ ∈ stdSimplex ℝ W := by
        have hc := condOn_mem_stdSimplex hπ.1 hpos'
        have : condOn F π {ρ : W → ℝ | s ≤ E ρ X} = σ := by
          funext w
          unfold condOn
          have := hid w
          by_cases hw : s ≤ E (F.P w) X
          · have hw' : F.P w ∈ {ρ : W → ℝ | s ≤ E ρ X} := hw
            rw [if_pos hw', hev]
            rw [show ind (F.estEvent X s) w = 1 by simp [ind, Frame.mem_estEvent, hw],
              mul_one] at this
            rw [this, mul_div_cancel_left₀ _ hpos.ne']
          · have hw' : F.P w ∉ {ρ : W → ℝ | s ≤ E ρ X} := hw
            rw [if_neg hw']
            rw [show ind (F.estEvent X s) w = 0 by simp [ind, Frame.mem_estEvent, hw],
              mul_zero] at this
            rcases mul_eq_zero.1 this.symm with h1 | h1
            · exact absurd h1 hpos.ne'
            · exact h1.symm
        rw [← this]; exact hc
      have e : ∑ w ∈ F.estEvent X s, π w * (X w - s) =
          mass π (F.estEvent X s) * (E σ X - s) := by
        have : ∑ w ∈ F.estEvent X s, π w * (X w - s) = ∑ w, π w * ind (F.estEvent X s) w * (X w - s) := by
          rw [← univ_inter (F.estEvent X s), ← sum_ite_mem]
          apply sum_congr rfl
          intro w _
          simp [ind]
        rw [this]
        have e2 : ∀ w, π w * ind (F.estEvent X s) w * (X w - s) =
            mass π (F.estEvent X s) * (σ w * (X w - s)) := fun w => by rw [hid w]; ring
        simp only [e2]
        rw [← mul_sum]
        congr 1
        rw [show (∑ w, σ w * (X w - s)) = E σ (X - (fun _ : W => s)) from rfl, E_sub_right,
          E_const hσs]
      rw [e]
      exact mul_nonneg hpos.le (by linarith)
    · rw [prod_sum_eq_zero_of_mass_eq_zero hπ.1 hzero.symm]

/-! ## Target 7(iii): fn 34 on finite frames -/

/-- **Fn 34 on finite frames.** For biconvex `B`, the finite sets `{P_w ∈ B}` and `{P_w ∉ B}` are
strongly separated: some `Y, t, ε > 0` have `t ≤ E_w(Y)` whenever `P_w ∈ B` and
`E_w(Y) ≤ t − ε` whenever `P_w ∉ B`.
Source: [[Deference Done Better]] fn 34
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem biconvex_strong_sep (F : Frame W) {B : Set (W → ℝ)} (hB : Biconvex B) :
    ∃ (Y : W → ℝ) (t ε : ℝ), 0 < ε ∧ (∀ w, F.P w ∈ B → t ≤ E (F.P w) Y) ∧
      ∀ w, F.P w ∉ B → E (F.P w) Y ≤ t - ε := by
  classical
  set C : Finset (W → ℝ) := (univ.filter (fun w => F.P w ∈ B)).image F.P with hC
  set D : Finset (W → ℝ) := (univ.filter (fun w => F.P w ∉ B)).image F.P with hD
  have hCB : (↑C : Set (W → ℝ)) ⊆ B := by
    intro x hx
    rw [mem_coe, hC, mem_image] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact (mem_filter.1 hw).2
  have hDB : (↑D : Set (W → ℝ)) ⊆ Bᶜ := by
    intro x hx
    rw [mem_coe, hD, mem_image] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    exact (mem_filter.1 hw).2
  have hdisj : Disjoint (convexHull ℝ (↑D : Set (W → ℝ))) (convexHull ℝ (↑C : Set (W → ℝ))) := by
    rw [Set.disjoint_left]
    intro x hxD hxC
    exact (convexHull_min hDB hB.2 hxD) (convexHull_min hCB hB.1 hxC)
  obtain ⟨f, u, v, hfD, huv, hfC⟩ := geometric_hahn_banach_compact_closed
    (convex_convexHull ℝ _) (D.finite_toSet.isCompact_convexHull ℝ)
    (convex_convexHull ℝ _) (C.finite_toSet.isClosed_convexHull ℝ) hdisj
  refine ⟨fun w => f (fun j => if w = j then 1 else 0), v, v - u, by linarith, ?_, ?_⟩
  · intro w hw
    rw [← StrongDual.apply_eq_E]
    exact (hfC _ (subset_convexHull ℝ _ (by
      rw [mem_coe, hC, mem_image]; exact ⟨w, mem_filter.2 ⟨mem_univ _, hw⟩, rfl⟩))).le
  · intro w hw
    rw [← StrongDual.apply_eq_E, sub_sub_cancel]
    exact (hfD _ (subset_convexHull ℝ _ (by
      rw [mem_coe, hD, mem_image]; exact ⟨w, mem_filter.2 ⟨mem_univ _, hw⟩, rfl⟩))).le

/-- The empty set is biconvex (a degenerate instance of "hyperplanes are the only divisions into
two convex sets" failing; the real counterexample is `Examples.lexHalf`, biconvex but not a
half-space).
Source: [[Deference Done Better]] §2 l. 219 (refuted as stated)
Kind: L
Fidelity: n/a -/
theorem biconvex_empty : Biconvex (∅ : Set (W → ℝ)) :=
  ⟨convex_empty, by rw [Set.compl_empty]; exact convex_univ⟩

/-- The whole space is biconvex.
Source: [[Deference Done Better]] §2 l. 219 (refuted as stated)
Kind: L
Fidelity: n/a -/
theorem biconvex_univ : Biconvex (Set.univ : Set (W → ℝ)) :=
  ⟨convex_univ, by rw [Set.compl_univ]; exact convex_empty⟩

end

end Cleanroom.Lit.LitDdbFacts
