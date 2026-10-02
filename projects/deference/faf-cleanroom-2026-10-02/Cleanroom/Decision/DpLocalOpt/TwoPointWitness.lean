import Cleanroom.Decision.DpLocalOpt.ChainRule
import Cleanroom.Decision.DpLocalOpt.Trees
import Cleanroom.Decision.DpLocalOpt.AmdWitness

/-!
# `dp-local-opt`: two-point witnesses (T7 off-path vacuity, T8(d) the two-point Stag Hunt,
T11 local maxima on fair trees)

On the two-point trees `twoPoint r₀ r_x r_y` and `twoStag` every procedure is `proc2 p q`
(`p := C(p1)(a)`, `q := C(p2)(a)`), and Theorem 1's functional at each point is read off the tree:
`Φ_{p1}(out) = r₀`, `Φ_{p1}(in) = q r_x + (1−q) r_y`, `Φ_{p2}(x) = (1−p) r_x`, `Φ_{p2}(y) = (1−p) r_y`.
-/

namespace Cleanroom.Decision.DpLocalOpt

open Finset
open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue

/-! ### Two-point procedures -/

section proc2

/-- Every two-point procedure on `Act2` is a `proc2`.
Source: none: infrastructure
Kind: L -/
theorem Proc.pt2_eq_proc2 (C : Proc Pt2 (fun _ => Act2) ℚ) :
    C = proc2 ((C .p1).w .a) ((C .p2).w .a) ((C .p1).nonneg .a) ((C .p1).w_le_one .a)
      ((C .p2).nonneg .a) ((C .p2).w_le_one .a) := by
  funext d; cases d
  · exact FinDistr.eq_act2 (C .p1)
  · exact FinDistr.eq_act2 (C .p2)

variable (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)

/-- Deviating `proc2 p q` at `p1` to `(r, 1 − r)` is `proc2 r q`.
Source: none: infrastructure
Kind: L -/
theorem proc2_deviate_p1 (r : ℚ) (r0 : 0 ≤ r) (r1 : r ≤ 1) :
    (proc2 p q hp0 hp1 hq0 hq1).deviate .p1 (FinDistr.act2 r r0 r1) = proc2 r q r0 r1 hq0 hq1 := by
  funext d; cases d <;> simp [Proc.deviate, proc2]

/-- Deviating `proc2 p q` at `p2` to `(r, 1 − r)` is `proc2 p r`.
Source: none: infrastructure
Kind: L -/
theorem proc2_deviate_p2 (r : ℚ) (r0 : 0 ≤ r) (r1 : r ≤ 1) :
    (proc2 p q hp0 hp1 hq0 hq1).deviate .p2 (FinDistr.act2 r r0 r1) = proc2 p r hp0 hp1 r0 r1 := by
  funext d; cases d <;> simp [Proc.deviate, proc2]

variable {Ω : Type} (B : Tree Ω Pt2 (fun _ => Act2) ℚ)

/-- Mixed coherence of `proc2 p q` at `p1`.
Source: none: infrastructure
Kind: L -/
theorem coherentAt_proc2_p1_iff :
    CoherentAt (proc2 p q hp0 hp1 hq0 hq1) B .p1 ↔
      ∀ r (r0 : 0 ≤ r) (r1 : r ≤ 1),
        value (proc2 r q r0 r1 hq0 hq1) B ≤ value (proc2 p q hp0 hp1 hq0 hq1) B := by
  unfold CoherentAt
  constructor
  · intro h r r0 r1
    have := h (FinDistr.act2 r r0 r1)
    rwa [proc2_deviate_p1] at this
  · intro h m
    rw [FinDistr.eq_act2 m, proc2_deviate_p1]
    exact h _ _ _

/-- Mixed coherence of `proc2 p q` at `p2`.
Source: none: infrastructure
Kind: L -/
theorem coherentAt_proc2_p2_iff :
    CoherentAt (proc2 p q hp0 hp1 hq0 hq1) B .p2 ↔
      ∀ r (r0 : 0 ≤ r) (r1 : r ≤ 1),
        value (proc2 p r hp0 hp1 r0 r1) B ≤ value (proc2 p q hp0 hp1 hq0 hq1) B := by
  unfold CoherentAt
  constructor
  · intro h r r0 r1
    have := h (FinDistr.act2 r r0 r1)
    rwa [proc2_deviate_p2] at this
  · intro h m
    rw [FinDistr.eq_act2 m, proc2_deviate_p2]
    exact h _ _ _

/-- Optimality of `proc2 p q`.
Source: none: infrastructure
Kind: L -/
theorem isOptimal_proc2_iff :
    IsOptimal (proc2 p q hp0 hp1 hq0 hq1) B ↔
      ∀ r s (r0 : 0 ≤ r) (r1 : r ≤ 1) (s0 : 0 ≤ s) (s1 : s ≤ 1),
        value (proc2 r s r0 r1 s0 s1) B ≤ value (proc2 p q hp0 hp1 hq0 hq1) B := by
  unfold IsOptimal
  constructor
  · intro h r s r0 r1 s0 s1; exact h _
  · intro h C'
    rw [Proc.pt2_eq_proc2 C']
    exact h _ _ _ _ _ _

/-- Theorem 1's condition at a point `d` for a procedure with `C(d) = (r, 1 − r)`.
Source: none: infrastructure
Kind: L -/
theorem thm1At_act2_iff (C : Proc Pt2 (fun _ => Act2) ℚ) (d : Pt2) (r : ℚ) (r0 : 0 ≤ r)
    (r1 : r ≤ 1) (hr : C d = FinDistr.act2 r r0 r1) :
    Thm1At C B d ↔
      (0 < r → siaSum C B d .b ≤ siaSum C B d .a) ∧
        (0 < 1 - r → siaSum C B d .a ≤ siaSum C B d .b) := by
  unfold Thm1At
  rw [hr]
  constructor
  · intro h
    exact ⟨fun hq => h .a hq .b, fun hq => h .b hq .a⟩
  · rintro ⟨ha, hb⟩ x hx y
    cases x <;> cases y
    · exact le_rfl
    · exact ha hx
    · exact hb hx
    · exact le_rfl

end proc2

/-! ### `twoPoint`: values and `Φ` -/

section twoPoint

variable (rOut rX rY p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)

/-- `V_{twoPoint}(p, q) = p r_out + (1 − p)(q r_x + (1 − q) r_y)`.
Source: `dp-core-tree` Catalogue (`twoPoint`); mandate T7
Kind: P -/
theorem twoPoint_value :
    value (proc2 p q hp0 hp1 hq0 hq1) (twoPoint rOut rX rY) =
      p * rOut + (1 - p) * (q * rX + (1 - q) * rY) := by
  simp only [twoPoint, value_decision, value_leaf, Act2.sum_univ, proc2_p1, proc2_p2,
    FinDistr.act2_a, FinDistr.act2_b]

/-- Every `twoPoint` tree is almost fair (one node per point).
Source: none: infrastructure (audit r1 adversarial N10: the ledger cited this without a
statement)
Kind: L -/
theorem twoPoint_almostFair : AlmostFair (twoPoint rOut rX rY) := by
  intro d ℓ
  obtain ⟨x, ℓ⟩ := ℓ
  cases x
  · cases d <;> simp [twoPoint, count]
  · obtain ⟨y, ℓ⟩ := ℓ
    cases y <;> cases d <;> simp [twoPoint, count]

/-- `Φ_{p1}(out) = r_out` on `twoPoint`.
Source: mandate T7
Kind: P -/
theorem twoPoint_siaSum_p1_a :
    siaSum (proc2 p q hp0 hp1 hq0 hq1) (twoPoint rOut rX rY) .p1 .a = rOut := by
  simp [twoPoint, siaSum_decision, Act2.sum_univ, value_leaf]

/-- `Φ_{p1}(in) = q r_x + (1 − q) r_y` on `twoPoint`.
Source: mandate T7
Kind: P -/
theorem twoPoint_siaSum_p1_b :
    siaSum (proc2 p q hp0 hp1 hq0 hq1) (twoPoint rOut rX rY) .p1 .b =
      q * rX + (1 - q) * rY := by
  simp [twoPoint, siaSum_decision, Act2.sum_univ, value_decision, value_leaf, proc2]

/-- `Φ_{p2}(x) = (1 − p) r_x` on `twoPoint`.
Source: mandate T7
Kind: P -/
theorem twoPoint_siaSum_p2_a :
    siaSum (proc2 p q hp0 hp1 hq0 hq1) (twoPoint rOut rX rY) .p2 .a = (1 - p) * rX := by
  simp [twoPoint, siaSum_decision, Act2.sum_univ, value_leaf, proc2]

/-- `Φ_{p2}(y) = (1 − p) r_y` on `twoPoint`.
Source: mandate T7
Kind: P -/
theorem twoPoint_siaSum_p2_b :
    siaSum (proc2 p q hp0 hp1 hq0 hq1) (twoPoint rOut rX rY) .p2 .b = (1 - p) * rY := by
  simp [twoPoint, siaSum_decision, Act2.sum_univ, value_leaf, proc2]

end twoPoint

/-! ### T7: off-path vacuity on `(2; 4, 1)` -/

section offPath

/-- The procedure `(out, y)` on a two-point tree: `proc2 1 0`.
Source: A32 ("the procedure (out, `y`)")
Kind: D -/
abbrev outY : Proc Pt2 (fun _ => Act2) ℚ := proc2 1 0 zero_le_one le_rfl le_rfl zero_le_one

/-- **T7 — both local conditions are vacuous off-path (A32)**: on `(2; 4, 1)` the procedure
`(out, y)` is coherent (mixed, hence pure), satisfies Theorem 1's condition at both points —
vacuously at the unreached `p2`, where `Φ_{p2}(x) = Φ_{p2}(y) = 0` — and is not optimal
(`V = 2 < 4 = V(in, x)`).
Source: A32 ("on the two-point tree out `→ 2`; in `→ [x → 4, y → 1]` the procedure (out, `y`) is
coherent in the pure and the mixed form …, satisfies Theorem 1's condition vacuously at the
unreached point, and is not optimal (`2 < 4`)") | dp-cf-2-058
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem outY_coherent_thm1_not_optimal :
    Coherent outY (twoPoint 2 4 1) ∧ CoherentPure outY (twoPoint 2 4 1) ∧
    Thm1 outY (twoPoint 2 4 1) ∧ ¬ IsOptimal outY (twoPoint 2 4 1) ∧
    value outY (twoPoint 2 4 1) = 2 ∧
    siaSum outY (twoPoint 2 4 1) .p2 .a = 0 ∧ siaSum outY (twoPoint 2 4 1) .p2 .b = 0 := by
  have hcoh : Coherent outY (twoPoint 2 4 1) := by
    intro d _
    cases d
    · rw [coherentAt_proc2_p1_iff]
      intro r r0 r1
      rw [twoPoint_value, twoPoint_value]; nlinarith
    · rw [coherentAt_proc2_p2_iff]
      intro r r0 r1
      rw [twoPoint_value, twoPoint_value]; nlinarith
  refine ⟨hcoh, Coherent.pure _ _ hcoh, ?_, ?_, by rw [twoPoint_value]; norm_num,
    by rw [twoPoint_siaSum_p2_a]; norm_num, by rw [twoPoint_siaSum_p2_b]; norm_num⟩
  · intro d _
    cases d
    · rw [thm1At_act2_iff _ _ _ 1 zero_le_one le_rfl rfl, twoPoint_siaSum_p1_a, twoPoint_siaSum_p1_b]
      norm_num
    · rw [thm1At_act2_iff _ _ _ 0 le_rfl zero_le_one rfl, twoPoint_siaSum_p2_a, twoPoint_siaSum_p2_b]
      norm_num
  · intro h
    have := h (proc2 0 1 le_rfl zero_le_one zero_le_one le_rfl)
    rw [twoPoint_value, twoPoint_value] at this
    norm_num at this

/-- The mixed two-point procedure `(½, ½)` at both points.
Source: mandate T6 ("`C(out/in)` mixed")
Kind: D -/
abbrev halfHalf : Proc Pt2 (fun _ => Act2) ℚ :=
  proc2 (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **T6's N+ witness**: on `(2; 4, 1)` with `C = (½, ½)` at both points and `d := p2`:
`μ(occ(d)) = ½ ∈ (0,1)`, `offOcc = 1 = C(p1)(out) · 2`, the EDT+SSA evaluator ranks `x` over `y`
(`4` vs `1`) exactly as `V_B(C[d ↦ ·])` does (`3` vs `3/2`).
Source: mandate T6 ("`twoPoint 2 4 1`, `C(out/in)` mixed, `d :=` the inner point")
Kind: N+
Fidelity: exact -/
theorem twoPoint_ssa_witness :
    mass halfHalf (twoPoint 2 4 1) (occ .p2 (twoPoint 2 4 1)) = 1/2 ∧
    offOcc halfHalf (twoPoint 2 4 1) .p2 = 1 ∧
    ssaValue halfHalf (twoPoint 2 4 1) .p2 (FinDistr.pure .a) = 4 ∧
    ssaValue halfHalf (twoPoint 2 4 1) .p2 (FinDistr.pure .b) = 1 ∧
    value (halfHalf.deviatePure .p2 .a) (twoPoint 2 4 1) = 3 ∧
    value (halfHalf.deviatePure .p2 .b) (twoPoint 2 4 1) = 3/2 := by
  have hmass : mass halfHalf (twoPoint 2 4 1) (occ .p2 (twoPoint 2 4 1)) = 1/2 := by
    rw [occ, mass_filter]
    unfold twoPoint
    rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision,
      Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
    simp [halfHalf, proc2]
    norm_num
  have hnumA : ssaNum halfHalf (twoPoint 2 4 1) .p2 (FinDistr.pure .a) = 2 := by
    unfold ssaNum
    rw [occ, Finset.sum_filter, pure_a_eq_act2, halfHalf, proc2_deviate_p2]
    unfold twoPoint
    rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision,
      Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
    simp [proc2]
    norm_num
  have hnumB : ssaNum halfHalf (twoPoint 2 4 1) .p2 (FinDistr.pure .b) = 1/2 := by
    unfold ssaNum
    rw [occ, Finset.sum_filter, pure_b_eq_act2, halfHalf, proc2_deviate_p2]
    unfold twoPoint
    rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision,
      Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
    simp [proc2]
    norm_num
  refine ⟨hmass, ?_, ?_, ?_, ?_, ?_⟩
  · unfold offOcc
    rw [Finset.sum_filter]
    unfold twoPoint
    rw [sum_leaves_decision, Act2.sum_univ, Tree.sum_leaves_leaf, sum_leaves_decision,
      Act2.sum_univ, Tree.sum_leaves_leaf, Tree.sum_leaves_leaf]
    simp [occ, halfHalf, proc2]
  · rw [ssaValue_eq_div, hnumA, hmass]; norm_num
  · rw [ssaValue_eq_div, hnumB, hmass]; norm_num
  · rw [Proc.deviatePure, pure_a_eq_act2, halfHalf, proc2_deviate_p2, twoPoint_value]; norm_num
  · rw [Proc.deviatePure, pure_b_eq_act2, halfHalf, proc2_deviate_p2, twoPoint_value]; norm_num

end offPath

/-! ### T8(d), T11(b): the two-point Stag Hunt -/

section twoStag

variable (p q : ℚ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)

/-- `Φ_{d₁}(S) = 2q` on `twoStag`.
Source: `repair/P10.md` P10-3′(ii)
Kind: P -/
theorem twoStag_siaSum_p1_S :
    siaSum (proc2 p q hp0 hp1 hq0 hq1) twoStag .p1 .a = 2 * q := by
  simp [twoStag, siaSum_decision, Act2.sum_univ, value_decision, value_leaf, proc2]; ring

/-- `Φ_{d₁}(H) = 1 − q` on `twoStag`.
Source: `repair/P10.md` P10-3′(ii)
Kind: P -/
theorem twoStag_siaSum_p1_H :
    siaSum (proc2 p q hp0 hp1 hq0 hq1) twoStag .p1 .b = 1 - q := by
  simp [twoStag, siaSum_decision, Act2.sum_univ, value_decision, value_leaf, proc2]

/-- `Φ_{d₂}(S) = 2p` on `twoStag`.
Source: `repair/P10.md` P10-3′(ii)
Kind: P -/
theorem twoStag_siaSum_p2_S :
    siaSum (proc2 p q hp0 hp1 hq0 hq1) twoStag .p2 .a = 2 * p := by
  simp [twoStag, siaSum_decision, Act2.sum_univ, value_leaf, proc2]; ring

/-- `Φ_{d₂}(H) = 1 − p` on `twoStag`.
Source: `repair/P10.md` P10-3′(ii)
Kind: P -/
theorem twoStag_siaSum_p2_H :
    siaSum (proc2 p q hp0 hp1 hq0 hq1) twoStag .p2 .b = 1 - p := by
  simp [twoStag, siaSum_decision, Act2.sum_univ, value_leaf, proc2]

/-- The profile `(H, H)`: `proc2 0 0`.
Source: `repair/P10.md` P10-3′(ii)
Kind: D -/
abbrev profHH : Proc Pt2 (fun _ => Act2) ℚ := proc2 0 0 le_rfl zero_le_one le_rfl zero_le_one

/-- **T8(d) — `(H, H)` on the two-point Stag Hunt is coherent (mixed and pure), Theorem-1-ratified
at both points, and not optimal** (`V = 1 < 2`): "EDT+SSA cannot coordinate distinct points".
Source: `repair/P10.md` P10-3′(ii) ("`(H,H)` has `V = 1 < 2`, is Definition-22-coherent pure and
mixed …, and Theorem-1-ratified at both points (`S ↦ 0 < 1 ↦ H`)") | A32 | dp-sl-058 (the
inclusions' strictness witness)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem twoStag_HH_coherent_thm1_not_optimal :
    Coherent profHH twoStag ∧ CoherentPure profHH twoStag ∧ Thm1 profHH twoStag ∧
    ¬ IsOptimal profHH twoStag ∧ value profHH twoStag = 1 ∧
    value (proc2 1 1 zero_le_one le_rfl zero_le_one le_rfl) twoStag = 2 := by
  have hcoh : Coherent profHH twoStag := by
    intro d _
    cases d
    · rw [coherentAt_proc2_p1_iff]
      intro r r0 r1
      rw [twoStag_value, twoStag_value]; nlinarith
    · rw [coherentAt_proc2_p2_iff]
      intro r r0 r1
      rw [twoStag_value, twoStag_value]; nlinarith
  refine ⟨hcoh, Coherent.pure _ _ hcoh, ?_, ?_, by rw [twoStag_value]; norm_num,
    by rw [twoStag_value]; norm_num⟩
  · intro d _
    cases d
    · rw [thm1At_act2_iff _ _ _ 0 le_rfl zero_le_one rfl, twoStag_siaSum_p1_S, twoStag_siaSum_p1_H]
      norm_num
    · rw [thm1At_act2_iff _ _ _ 0 le_rfl zero_le_one rfl, twoStag_siaSum_p2_S, twoStag_siaSum_p2_H]
      norm_num
  · intro h
    have := h (proc2 1 1 zero_le_one le_rfl zero_le_one le_rfl)
    rw [twoStag_value, twoStag_value] at this
    norm_num at this

/-- **T11(b) — a strict non-global local maximum of `V` on an almost-fair tree**: on `twoStag`,
`V(p, q) − 1 = 3pq − p − q < 0` on `[0, 1/3]² ∖ {(0,0)}`, so `(H, H)` (`V = 1`) is a strict local
maximum while `V(S, S) = 2`. `twoStag` is almost fair (`#_d ≤ 1` on every path) and **not
strongly fair**: its two `p2`-nodes (one per `p1`-branch) have non-isomorphic subtrees, so
`dp-fairness-reloc`'s `StronglyFair` fails (`twoStag_not_stronglyFair`, `StrongFair.lean`). Hence
this answers the *almost-fair* form of dp-cf-2-026's extension question positively and leaves
the strongly-fair form answered negatively in general (`stronglyFair_strictLocalMax_isOptimal`,
`GatedInduction.lean`, repair round 2: on a strongly fair tree every strict local maximum is
global; the `twoPoint` family first, `twoPoint_strictLocalMax_isOptimal`). Fairness
*grades* are `dp-fairness-reloc`'s.
Source: mandate T11(b) (mandate writer's derivation, verified here); `repair/dynamic.md` Open 8;
audit r1 fidelity B1
Kind: P
Fidelity: exact (almost-fair class; not the strongly-fair question)
Hyps: (a) all -/
theorem twoStag_HH_strict_local_max :
    AlmostFair twoStag ∧
    (∀ p q (hp0 : 0 ≤ p) (hp1 : p ≤ 1/3) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/3), (p ≠ 0 ∨ q ≠ 0) →
      value (proc2 p q hp0 (by linarith) hq0 (by linarith)) twoStag < 1) ∧
    value profHH twoStag = 1 ∧
    value (proc2 1 1 zero_le_one le_rfl zero_le_one le_rfl) twoStag = 2 := by
  refine ⟨?_, ?_, by rw [twoStag_value]; norm_num, by rw [twoStag_value]; norm_num⟩
  · intro d ℓ
    obtain ⟨x, ℓ⟩ := ℓ
    cases x <;> obtain ⟨y, ℓ⟩ := ℓ <;> cases y <;> cases d <;> simp [twoStag, count]
  · intro p q hp0 hp1 hq0 hq1 hne
    rw [twoStag_value]
    rcases hne with hp | hq
    · have : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hp)
      nlinarith
    · have : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq)
      nlinarith

end twoStag

/-! ### T11(a): the depth-2 fair tree -/

section fairDepth2

/-- **T11(a) — a weak non-global local maximum on `fairDepth2`**: on the face `p_in = 0`
(`p = C(p1)(out) = 1`) the value is `1`, and `V ≤ 1` whenever `p_x = q ≤ 1/7` — a weak local
maximum, not global (`V(in, x) = 4`).
Source: dp-cf-2-026(b); `repair/dynamic.md` Open 8 ("weak non-global local maxima *exist* (the
face `p_in = 0`, `p_x < 1/7` of the depth-2 fair tree, value `1 < 4`)")
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem fairDepth2_weak_local_max :
    (∀ q (hq0 : 0 ≤ q) (hq1 : q ≤ 1),
      value (proc2 1 q zero_le_one le_rfl hq0 hq1) fairDepth2 = 1) ∧
    (∀ p q (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1/7),
      value (proc2 p q hp0 hp1 hq0 (by linarith)) fairDepth2 ≤ 1) ∧
    value (proc2 0 1 le_rfl zero_le_one zero_le_one le_rfl) fairDepth2 = 4 := by
  refine ⟨fun q hq0 hq1 => by rw [fairDepth2_value]; ring, ?_, by rw [fairDepth2_value]; norm_num⟩
  intro p q hp0 hp1 hq0 hq1
  rw [fairDepth2_value]
  nlinarith

end fairDepth2

end Cleanroom.Decision.DpLocalOpt
