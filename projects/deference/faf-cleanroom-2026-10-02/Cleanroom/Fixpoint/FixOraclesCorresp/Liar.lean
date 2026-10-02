import Cleanroom.Fixpoint.FixOraclesCorresp.OracleExists
import Cleanroom.Fixpoint.FixOraclesCorresp.Existence
import Cleanroom.Fixpoint.FixOraclesCorresp.Lifts
import Mathlib.Analysis.Convex.Hull

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.Liar`: the liar, and whole-graph convexification

Target 11 (fixpoint-lit-2-004): the liar machine `M^O() = 1 − O(M, p)` as the evaluation map
`ev x = 1 − x ()` on `I = Unit`. For `p ∈ (0, 1)`, an answer `x` in the cube is reflective iff
`x () = 1 − p` (`reflective_liar_iff`; uniqueness is the survey agent's extension of the paper's `p = ½`
remark); no deterministic answer is reflective (`liar_not_deterministic`), the paper's §1
diagonalization; and the non-strict variant has no solution at all (`liar_no_nonStrict`), so
strictness in `Reflective` is load-bearing. This is also Part A's "negation ↦ mass on 50 %"
desideratum realized by *pointwise* convexification (ATTRIBUTION-UNVETTED that this is Scott's
reading).

Target 17 (fixpoint-lit-2-011): whole-graph convexification destroys reflectivity. With `p = 3/4`,
`(1/2, 1/2)` lies in the convex hull of the graph of the ideal step `σ_p`, and `e = 1 − y` holds there,
so it is a "fixed point" of the graph-convexified liar system — yet `y = 1/2` is not reflective
(reflectivity forces `y = 1/4`). Contrast: fixed points of the pointwise convexification are reflective
(`mem_oracleCorr_self_iff`).

Also here: the genuinely set-valued **N+ witness of target 5** (`liarCollapse`), the liar step
transported to `Δ(Fin 2)` — unique collapse fixed point `![1/2, 1/2]`, value there the whole simplex.
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set Cleanroom.Found.FixKakutani

/-- **The liar as an evaluation map**: one query, output probability `1 − x ()`.
Source: FTC 2015 §2 ("`M^O() = 1 − O(M, 0.5)`"); [[fixpoint-lit-2-inventory]] 004
Kind: D
Fidelity: variant: abstract (the machine's behaviour as a function of the answer)
Hyps: n/a -/
def liarEv : Unit → (Unit → ℝ) → ℝ := fun _ x => 1 - x ()

/-- **Target 11: the liar's unique reflective answer is `1 − p`.** For `p ∈ (0, 1)` and `x` in the cube,
`Reflective liarEv p x ↔ x () = 1 − p`. (⟹: `x () < 1 − p` forces `x () = 1 > 1 − p`; `x () > 1 − p`
forces `x () = 0 < 1 − p`.)
Source: FTC 2015 §2 ("we can set `P(O(M,0.5) = 1) = 0.5`"); [[fixpoint-lit-2-inventory]] 004
(uniqueness for all `p ∈ (0,1)` is the survey agent's extension)
Kind: P
Fidelity: stronger: any `p ∈ (0,1)`, with uniqueness; variant: abstract
Hyps: (a) none; (c) evaluation maps in place of oracle machines -/
theorem reflective_liar_iff {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) {x : Unit → ℝ} (hx : x ∈ cube Unit) :
    Reflective liarEv (fun _ => p) x ↔ x () = 1 - p := by
  have hx0 := hx () (mem_univ _)
  constructor
  · intro h
    have e := h ()
    simp only [liarEv] at e
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := e.1 (by linarith)
      linarith [hp.1]
    · have := e.2 (by linarith)
      linarith [hp.2]
  · intro h i
    simp only [liarEv, h]
    exact ⟨fun h' => absurd h' (by linarith), fun h' => absurd h' (by linarith)⟩

/-- **No deterministic answer is reflective on the liar** at any `p ∈ (0, 1)`, in particular at `1/2`
(the paper's §1 diagonalization): `x () ∈ {0, 1}` contradicts `x () = 1 − p`.
Source: FTC 2015 §1 (the diagonalization argument), §2; [[fixpoint-lit-2-inventory]] 004
Kind: P
Fidelity: variant: abstract
Hyps: (a) none; (c) evaluation maps in place of oracle machines -/
theorem liar_not_deterministic {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) {x : Unit → ℝ}
    (hdet : x () = 0 ∨ x () = 1) : ¬ Reflective liarEv (fun _ => p) x := by
  intro h
  have hx : x ∈ cube Unit := fun i _ => by
    rcases hdet with h0 | h1
    · rw [show i = () from rfl, h0]; exact ⟨le_rfl, zero_le_one⟩
    · rw [show i = () from rfl, h1]; exact ⟨zero_le_one, le_rfl⟩
  have := (reflective_liar_iff hp hx).1 h
  rcases hdet with h0 | h1
  · linarith [hp.2]
  · linarith [hp.1]

/-- **Strictness is load-bearing (N− check of the trap)**: the non-strict variant of reflectivity
has *no* solution on the liar for any `p ∈ (0, 1)`, on or off the cube.
Source: mandate target 9, trap (a); FTC 2015 §2 (ties "randomized")
Kind: N-
Fidelity: n/a
Hyps: (a) none; (c) evaluation maps in place of oracle machines -/
theorem liar_no_nonStrict {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) (x : Unit → ℝ) :
    ¬ ReflectiveNonStrict liarEv (fun _ => p) x := by
  intro h
  have e := h ()
  simp only [liarEv] at e
  by_cases hle : p ≤ 1 - x ()
  · have := e.1 hle; linarith [hp.1]
  · have := e.2 (by linarith); linarith [hp.2]

/-- **Existence for the liar, instantiated** (the N+ witness of target 10 at `n = 1`).
Source: FTC 2015 §2; [[fixpoint-lit-2-inventory]] 004, 010
Kind: N+
Fidelity: variant: abstract
Hyps: (a) none -/
theorem exists_reflective_liar (p : ℝ) : ∃ x ∈ cube Unit, Reflective liarEv (fun _ => p) x :=
  exists_reflective liarEv (fun _ => (continuous_const.sub (continuous_apply ())).continuousOn) _

/-! ### Target 17: whole-graph convexification destroys reflectivity -/

/-- The ideal (deterministic) oracle answer as a function of the output probability: `σ_p e = 1` iff
`p < e`.
Source: [[fixpoint-lit-2-inventory]] 011 (`σ_p`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def idealStep (p e : ℝ) : ℝ := if p < e then 1 else 0

/-- The convex hull of the graph of `σ_p` over `[0, 1]` — the notes' *whole-graph* convexification.
Source: [[fixpoint-lit-2-inventory]] 011 (`conv(Graph σ_p)`); theoretical-insights §2 l. 30 ("require
the entire graph to be convex") / mathematical-formulation §3 Definition 2
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def hullGraph (p : ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 = idealStep p q.1}

/-- **Target 17**: with `p = 3/4`, the point `(1/2, 1/2)` lies in the whole-graph convexification of
the liar's step (it is the midpoint of the graph points `(0, 0)` and `(1, 1)`), it satisfies the liar's
consistency equation `e = 1 − y`, and yet the answer `y = 1/2` is **not** reflective (reflectivity
forces `y = 1/4`). So fixed points of the graph-convexified system need not be reflective, whereas
fixed points of the pointwise convexification are (`mem_oracleCorr_self_iff`).
Source: [[fixpoint-lit-2-inventory]] 011; FTC 2015 App. B against theoretical-insights §2 l. 30
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem hullGraph_fixed_not_reflective :
    ∃ e y : ℝ, (e, y) ∈ hullGraph (3 / 4) ∧ e = 1 - y ∧
      ¬ Reflective liarEv (fun _ => 3 / 4) (fun _ => y) := by
  refine ⟨1 / 2, 1 / 2, ?_, by norm_num, ?_⟩
  · have h0 : ((0 : ℝ), (0 : ℝ)) ∈ {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 = idealStep (3 / 4) q.1} := by
      refine ⟨⟨le_rfl, zero_le_one⟩, ?_⟩
      norm_num [idealStep]
    have h1 : ((1 : ℝ), (1 : ℝ)) ∈ {q : ℝ × ℝ | q.1 ∈ Icc (0 : ℝ) 1 ∧ q.2 = idealStep (3 / 4) q.1} := by
      refine ⟨⟨zero_le_one, le_rfl⟩, ?_⟩
      norm_num [idealStep]
    have key : ((1 / 2 : ℝ), (1 / 2 : ℝ)) =
        (1 / 2 : ℝ) • ((0 : ℝ), (0 : ℝ)) + (1 / 2 : ℝ) • ((1 : ℝ), (1 : ℝ)) := by
      ext <;> simp
    unfold hullGraph
    rw [key]
    exact (convex_convexHull ℝ _) (subset_convexHull ℝ _ h0) (subset_convexHull ℝ _ h1)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num) (by norm_num)
  · intro h
    have hx : (fun _ : Unit => (1 / 2 : ℝ)) ∈ cube Unit := fun _ _ => by norm_num
    have := (reflective_liar_iff (by norm_num) hx).1 h
    norm_num at this

/-! ### The N+ witness of target 5: the liar step transported to `Δ(Fin 2)` -/

/-- The liar step on `Δ(Fin 2)`: `Φ p = {q ∈ Δ | q 1 ∈ signStep (1 − p 1) (1/2)}` (answer `q 1`
must be `1` if the liar's output probability `1 − p 1` exceeds `1/2`, `0` if below, free at the tie).
Source: mandate target 5 (N+ witness: "the pointwise-convexified liar step transported to `Δ(Fin 2)`")
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def liarStep (p : Fin 2 → ℝ) : Set (Fin 2 → ℝ) :=
  {q | q ∈ stdSimplex ℝ (Fin 2) ∧ q 1 ∈ signStep (1 - p 1) (1 / 2)}

/-- **The genuinely set-valued correspondence** `liarCollapse p = {μ ∈ Δ² | bary μ ∈ liarStep p}`.
Source: mandate target 5
Kind: D
Fidelity: variant: Δ² finitely supported
Hyps: n/a -/
def liarCollapse (p : Fin 2 → ℝ) : Set ((Fin 2 → ℝ) →₀ ℝ) :=
  {μ | μ ∈ FinMeasure (Fin 2) ∧ bary μ ∈ liarStep p}

/-- `bary '' liarCollapse p = liarStep p`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem bary_image_liarCollapse (p : Fin 2 → ℝ) : bary '' liarCollapse p = liarStep p := by
  ext q
  constructor
  · rintro ⟨μ, ⟨-, hμ⟩, rfl⟩; exact hμ
  · intro hq
    exact ⟨dirac q, ⟨dirac_mem_finMeasure hq.1, by simpa using hq⟩, by simp⟩

/-- `liarStep p` is nonempty for `p ∈ Δ(Fin 2)` (it contains a vertex).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem liarStep_nonempty (p : Fin 2 → ℝ) : (liarStep p).Nonempty := by
  obtain ⟨y, hy⟩ := signStep_nonempty (1 - p 1) (1 / 2)
  have hy' := (mem_signStep_iff.1 hy).1
  refine ⟨![1 - y, y], ⟨fun i => ?_, ?_⟩, ?_⟩
  · fin_cases i <;> simp <;> linarith [hy'.1, hy'.2]
  · simp [Fin.sum_univ_two]
  · simpa using hy

/-- `liarStep p` is convex.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem liarStep_convex (p : Fin 2 → ℝ) : Convex ℝ (liarStep p) := by
  have : liarStep p = stdSimplex ℝ (Fin 2) ∩ (fun q : Fin 2 → ℝ => q 1) ⁻¹' signStep (1 - p 1) (1 / 2) := by
    ext q; simp [liarStep]
  rw [this]
  exact (convex_stdSimplex ℝ (Fin 2)).inter
    ((signStep_convex _ _).is_linear_preimage (LinearMap.proj (1 : Fin 2)).isLinear)

/-- `p ↦ liarStep p` has a closed graph over `Δ(Fin 2)`.
Source: none: infrastructure (App. B's closed-graph argument, via `isClosed_signStep_graph`)
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem liarStep_hasClosedGraphOn : HasClosedGraphOn liarStep (stdSimplex ℝ (Fin 2)) := by
  unfold HasClosedGraphOn
  have hK : IsClosed (stdSimplex ℝ (Fin 2)) := (isCompact_stdSimplex ℝ (Fin 2)).isClosed
  have hset : {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | q.1 ∈ stdSimplex ℝ (Fin 2) ∧ q.2 ∈ liarStep q.1} =
      {q : (Fin 2 → ℝ) × (Fin 2 → ℝ) | q.2 ∈ stdSimplex ℝ (Fin 2)} ∩
      (fun q : (Fin 2 → ℝ) × (Fin 2 → ℝ) => (q.1, q.2 1)) ⁻¹'
        {q : (Fin 2 → ℝ) × ℝ | q.1 ∈ stdSimplex ℝ (Fin 2) ∧ q.2 ∈ signStep (1 - q.1 1) (1 / 2)} := by
    ext ⟨p, q⟩
    simp only [mem_setOf_eq, liarStep, mem_inter_iff, mem_preimage]
    tauto
  rw [hset]
  refine (hK.preimage continuous_snd).inter ?_
  exact (isClosed_signStep_graph hK ((continuous_const.sub (continuous_apply 1)).continuousOn)
    (1 / 2)).preimage (continuous_fst.prodMk ((continuous_apply 1).comp continuous_snd))

/-- **N+ witness of target 5**: `liarCollapse` inhabits the full hypothesis package of
`exists_collapse_fixed_point` (values in `Δ²`, nonempty, convex, closed collapsed graph), so it has a
collapse fixed point.
Source: mandate target 5
Kind: N+
Fidelity: variant: Δ² finitely supported
Hyps: (a) none: all four hypotheses are theorems -/
theorem liarCollapse_exists_fixed : ∃ p, IsCollapseFixedPoint liarCollapse p :=
  exists_collapse_fixed_point liarCollapse (fun _ _ _ hμ => hμ.1)
    (fun p _ => by
      obtain ⟨q, hq⟩ := liarStep_nonempty p
      exact ⟨dirac q, dirac_mem_finMeasure hq.1, by simpa using hq⟩)
    (fun p _ => by
      have : liarCollapse p = FinMeasure (Fin 2) ∩ bary ⁻¹' liarStep p := by
        ext μ; simp [liarCollapse]
      rw [this]
      exact convex_finMeasure.inter ((liarStep_convex p).linear_preimage bary))
    (by
      have : (fun p => bary '' liarCollapse p) = liarStep := funext bary_image_liarCollapse
      rw [this]
      exact liarStep_hasClosedGraphOn)

/-- **Non-degeneracy certificate**: the collapse fixed points of `liarCollapse` are exactly
`![1/2, 1/2]` (the argument of `reflective_liar_iff` on the simplex), and the value of the collapsed
correspondence there is the *whole* simplex (`liarStep_half`), so the witness is genuinely set-valued
at its fixed point, as `fix-kakutani`'s `mem_mpBR_self_iff` is.
Source: mandate target 5 ("certify as `mem_mpBR_self_iff` does")
Kind: P
Fidelity: n/a
Hyps: (a) none -/
theorem isCollapseFixedPoint_liarCollapse_iff {p : Fin 2 → ℝ} :
    IsCollapseFixedPoint liarCollapse p ↔ p = ![1 / 2, 1 / 2] := by
  constructor
  · rintro ⟨hp, hpF⟩
    rw [bary_image_liarCollapse] at hpF
    obtain ⟨-, hs⟩ := hpF
    rw [mem_signStep_iff] at hs
    have h1 : p 1 = 1 / 2 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := hs.2.1 (by linarith); linarith
      · have := hs.2.2 (by linarith); linarith
    have hsum := hp.2
    simp only [Fin.sum_univ_two] at hsum
    ext i
    fin_cases i <;> simp <;> linarith
  · rintro rfl
    have hΔ : (![1 / 2, 1 / 2] : Fin 2 → ℝ) ∈ stdSimplex ℝ (Fin 2) := by
      refine ⟨fun i => ?_, ?_⟩
      · fin_cases i <;> simp
      · simp [Fin.sum_univ_two]; norm_num
    refine ⟨hΔ, ?_⟩
    rw [bary_image_liarCollapse]
    refine ⟨hΔ, ?_⟩
    rw [mem_signStep_iff]
    simp only [Matrix.cons_val_one]
    norm_num

/-- At the fixed point `![1/2, 1/2]` the value of the collapsed correspondence is the whole simplex.
Source: mandate target 5 ("value there the whole simplex")
Kind: L
Fidelity: n/a
Hyps: none -/
theorem liarStep_half : liarStep ![1 / 2, 1 / 2] = stdSimplex ℝ (Fin 2) := by
  ext q
  simp only [liarStep, mem_setOf_eq, Matrix.cons_val_one]
  constructor
  · exact fun h => h.1
  · intro hq
    refine ⟨hq, ?_⟩
    rw [mem_signStep_iff]
    have h1 := hq.1 1
    have hs := hq.2
    simp only [Fin.sum_univ_two] at hs
    have h0 := hq.1 0
    refine ⟨⟨h1, by linarith⟩, ?_, ?_⟩ <;> intro h <;> norm_num at h

end Cleanroom.Fixpoint.FixOraclesCorresp
