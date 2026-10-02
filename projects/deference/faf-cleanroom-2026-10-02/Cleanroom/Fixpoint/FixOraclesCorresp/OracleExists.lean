import Cleanroom.Fixpoint.FixOraclesCorresp.OracleDefs
import Mathlib.Data.Fin.VecNotation

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.OracleExists`: reflective answer vectors exist

Target 10 (fixpoint-lit-2-010, route (a)): for evaluation maps `ev i` continuous on the cube and any
thresholds `p`, there is `x ∈ [0,1]^I` with `Reflective ev p x`. Proof: `kakutani_pi_Icc`
(`fix-kakutani`, grade (a)) applied to `oracleCorr ev p` — values in the cube, nonempty, convex, and
**closed graph proved** (`oracleCorr_hasClosedGraphOn`, App. B's argument in closed-set form via
`isClosed_signStep_graph`). Nothing about the closed graph or a selection is assumed.

Corollary: polynomial evaluation maps (Theorem 5.1's class), `exists_reflective_polynomial` — the
sign of the coefficients and the range condition `ev i (cube) ⊆ [0,1]` are *not* needed for existence
by this route (they are needed for the paper's game-theoretic route, `GameR.lean`).

Witness (N+): matching pennies `I = Fin 2`, `ev 0 x = x 1`, `ev 1 x = 1 - x 0`, `p = 1/2`, whose unique
reflective vector in the cube is `![1/2, 1/2]` (`reflective_mp_iff`), cross-checked against
`fix-kakutani`'s `mem_mpBR_self_iff` (`reflective_mp_iff_mem_mpBR`). The liar (`Liar.lean`) is the
`n = 1` witness.

Theorem 2.1 (ii)'s finite analogue (`exists_reflectiveOn`, App. B's route on `[0,1]^R`): reflective
on a finite `R` with the answers prescribed off `R`; `I` arbitrary, continuity only at the queries of
`R`. Degenerate ends `reflectiveOn_empty` (`R = ∅`, vacuous) and
`exists_reflective_of_reflectiveOn_univ` (`R = univ` is `exists_reflective`). Witnesses:
`reflectiveOn_twoQuery` (the prescription is honoured and the vector is not globally reflective) and
`exists_reflectiveOn_selfRef` (the liar *inside* `R`, read from outside: the fixed-point step on
`[0,1]^R` forces `x 0 = 1/2`). The `G_R`-based analogue that FTC §5 omits is in `GameR.lean`
(`gameR_nash_reflectiveOn`) and `BrouwerOnly.lean` (`exists_reflectiveOn_via_gameR_brouwer`).
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set Cleanroom.Found.FixKakutani

variable {I : Type*} [Fintype I]

omit [Fintype I] in
/-- **The oracle correspondence has a closed graph over the cube** when every `ev i` is continuous on
the cube (FTC App. B's argument: if `p i < ev i x` then eventually `p i < ev i xₙ`, so `yₙ i = 1`
eventually, so `y i = 1`; symmetric; the tie case is `Icc` closed — here in closed-set form).
Source: FTC 2015 App. B ("to show that `f` has a fixed point, it is sufficient to show that it has
closed graph"); [[fixpoint-lit-2-inventory]] 002, 010
Kind: P
Fidelity: variant: abstract (evaluation maps in place of machines; finite `I`)
Hyps: (a) none -/
theorem oracleCorr_hasClosedGraphOn (ev : I → (I → ℝ) → ℝ)
    (hev : ∀ i, ContinuousOn (ev i) (cube I)) (p : I → ℝ) :
    HasClosedGraphOn (oracleCorr ev p) (cube I) := by
  unfold HasClosedGraphOn
  have hK : IsClosed (cube I) := isClosed_set_pi fun _ _ => isClosed_Icc
  have hset : {q : (I → ℝ) × (I → ℝ) | q.1 ∈ cube I ∧ q.2 ∈ oracleCorr ev p q.1} =
      ⋂ i, (fun q : (I → ℝ) × (I → ℝ) => (q.1, q.2 i)) ⁻¹'
        {q : (I → ℝ) × ℝ | q.1 ∈ cube I ∧ q.2 ∈ signStep (ev i q.1) (p i)} := by
    ext ⟨x, y⟩
    simp only [mem_setOf_eq, oracleCorr, mem_iInter, mem_preimage]
    constructor
    · rintro ⟨hx, hy⟩ i; exact ⟨hx, hy i⟩
    · intro h
      rcases isEmpty_or_nonempty I with hI | hI
      · refine ⟨fun i => (IsEmpty.false i).elim, fun i => (IsEmpty.false i).elim⟩
      · exact ⟨(h (Classical.arbitrary I)).1, fun i => (h i).2⟩
  rw [hset]
  refine isClosed_iInter fun i => ?_
  exact (isClosed_signStep_graph hK (hev i) (p i)).preimage
    (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))

/-- **Target 10: reflective answer vectors exist for continuous evaluation maps.** For every family
`ev` with each `ev i` continuous on the cube and every threshold vector `p`, some `x ∈ [0,1]^I` is
reflective. Proof: `kakutani_pi_Icc` on `oracleCorr ev p`, whose four hypotheses are theorems
(values in the cube by `signStep_subset_Icc`, nonempty by `signStep_nonempty`, convex by
`signStep_convex` and `convex_pi`, closed graph by `oracleCorr_hasClosedGraphOn`), then
`mem_oracleCorr_self_iff`.
Source: FTC 2015 Theorem 2.1 (i) and App. B, finite abstract core; [[fixpoint-lit-2-inventory]] 010
Kind: C
Fidelity: variant: abstract (evaluation maps in place of machines; finite `I`; the paper's thresholds
are rational, here any real)
Hyps: (a) all: Kakutani is `Cleanroom.Found.FixKakutani.kakutani_pi_Icc`; (c) evaluation maps in place of oracle machines -/
theorem exists_reflective (ev : I → (I → ℝ) → ℝ) (hev : ∀ i, ContinuousOn (ev i) (cube I))
    (p : I → ℝ) : ∃ x ∈ cube I, Reflective ev p x := by
  obtain ⟨x, hx, hxF⟩ := kakutani_pi_Icc (oracleCorr ev p)
    (fun x _ y hy i _ => signStep_subset_Icc _ _ (hy i))
    (fun x _ => by
      classical
      refine ⟨fun i => if p i < ev i x then 1 else 0, fun i => ?_⟩
      rw [mem_signStep_iff]
      dsimp only
      split_ifs with h
      · exact ⟨⟨zero_le_one, le_rfl⟩, fun _ => rfl, fun h' => absurd h (lt_asymm h')⟩
      · exact ⟨⟨le_rfl, zero_le_one⟩, fun h' => absurd h' h, fun _ => rfl⟩)
    (fun x _ => by
      rw [oracleCorr_eq_pi]
      exact convex_pi fun i _ => signStep_convex _ _)
    (oracleCorr_hasClosedGraphOn ev hev p)
  exact ⟨x, hx, (mem_oracleCorr_self_iff hx).1 hxF⟩

/-- **Polynomial evaluation maps** (FTC §5's representation `P(Mᵢ() = 1) = ∑ₖ cᵢₖ ∏ᵢ' xᵢ'^{dᵢₖᵢ'}`):
`polyEv c d i x = ∑ k, c i k * ∏ i', x i' ^ d i k i'`.
Source: FTC 2015 §5 (the polynomial display); [[fixpoint-lit-2-inventory]] 007, 010
Kind: D
Fidelity: exact (as a class of maps; the paper asserts, and does not prove, that bounded closed
machines have this form — finding F9)
Hyps: n/a -/
def polyEv {K : Type*} [Fintype K] (c : I → K → ℝ) (d : I → K → I → ℕ) (i : I) (x : I → ℝ) : ℝ :=
  ∑ k, c i k * ∏ i', x i' ^ d i k i'

/-- Polynomial evaluation maps are continuous.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem continuous_polyEv {K : Type*} [Fintype K] (c : I → K → ℝ) (d : I → K → I → ℕ) (i : I) :
    Continuous (polyEv c d i) := by
  unfold polyEv
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  exact continuous_finsetProd _ fun i' _ => (continuous_apply i').pow _

/-- **Target 10, polynomial corollary (Theorem 5.1's class)**: reflective vectors exist for polynomial
evaluation maps and any thresholds. No sign or range condition on the coefficients is needed by this
route.
Source: FTC 2015 Theorem 5.1 (existence part), via Theorem 2.1's route; [[fixpoint-lit-2-inventory]]
010
Kind: C
Fidelity: stronger: no `c ≥ 0`, no `d ≤ B`, no `ev (cube) ⊆ [0,1]`, real thresholds; variant: abstract
Hyps: (a) all; (c) evaluation maps in place of oracle machines -/
theorem exists_reflective_polynomial {K : Type*} [Fintype K] (c : I → K → ℝ) (d : I → K → I → ℕ)
    (p : I → ℝ) : ∃ x ∈ cube I, Reflective (polyEv c d) p x :=
  exists_reflective _ (fun i => (continuous_polyEv c d i).continuousOn) p

/-! ### Theorem 2.1 (ii), finite analogue: reflective on `R`, prescribed off `R` -/

/-- **Reflective on `R`**: the sign conditions for the queries `i ∈ R` only — FTC §2's "reflective on
`R`" with `R ⊆ I`.
Source: FTC 2015 §2 (Definition: "`O` is reflective on `R`"); Theorem 2.1 (ii)
Kind: D
Fidelity: variant: abstract (evaluation maps in place of machines)
Hyps: n/a -/
def ReflectiveOn (R : Finset I) (ev : I → (I → ℝ) → ℝ) (p : I → ℝ) (x : I → ℝ) : Prop :=
  ∀ i ∈ R, (p i < ev i x → x i = 1) ∧ (ev i x < p i → x i = 0)

/-- Reflective on all queries is `Reflective`.
Source: FTC 2015 §2 ("reflective" = reflective on the set of all queries)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem reflectiveOn_univ_iff (ev : I → (I → ℝ) → ℝ) (p x : I → ℝ) :
    ReflectiveOn Finset.univ ev p x ↔ Reflective ev p x := by
  simp [ReflectiveOn, Reflective]

section Extend

variable [DecidableEq I]

/-- **Extension by prescribed answers**: `extendBy R x₀ y` answers `y` on `R` and `x₀` off `R`
(Theorem 2.1 (ii)'s "`P(O'(M,p) = 1) = P(O(M,p) = 1)` for `(M,p) ∉ R`").
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def extendBy (R : Finset I) (x₀ : I → ℝ) (y : R → ℝ) : I → ℝ :=
  fun j => if h : j ∈ R then y ⟨j, h⟩ else x₀ j

omit [Fintype I] in
/-- `extendBy` on `R`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem extendBy_apply_of_mem {R : Finset I} (x₀ : I → ℝ) (y : R → ℝ) {i : I} (hi : i ∈ R) :
    extendBy R x₀ y i = y ⟨i, hi⟩ := dif_pos hi

omit [Fintype I] in
/-- `extendBy` off `R`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem extendBy_apply_of_not_mem {R : Finset I} (x₀ : I → ℝ) (y : R → ℝ) {i : I} (hi : i ∉ R) :
    extendBy R x₀ y i = x₀ i := dif_neg hi

omit [Fintype I] in
/-- `extendBy R x₀` is continuous in `y`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem continuous_extendBy (R : Finset I) (x₀ : I → ℝ) : Continuous (extendBy R x₀) := by
  refine continuous_pi fun j => ?_
  by_cases h : j ∈ R
  · simp only [extendBy, dif_pos h]
    exact continuous_apply _
  · simp only [extendBy, dif_neg h]
    exact continuous_const

omit [Fintype I] in
/-- `extendBy R x₀` maps the cube on `R` into the cube on `I` when `x₀` is in the cube.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem extendBy_mem_cube {R : Finset I} {x₀ : I → ℝ} (hx₀ : x₀ ∈ cube I) {y : R → ℝ}
    (hy : y ∈ cube R) : extendBy R x₀ y ∈ cube I := by
  intro j _
  by_cases h : j ∈ R
  · rw [extendBy_apply_of_mem _ _ h]; exact hy ⟨j, h⟩ (mem_univ _)
  · rw [extendBy_apply_of_not_mem _ _ h]; exact hx₀ j (mem_univ _)

omit [Fintype I] in
/-- **Theorem 2.1 (ii), finite analogue**: for evaluation maps continuous on the cube at the queries
of `R`, every finite query set `R ⊆ I`, every thresholds `p`, and every prescribed answer vector
`x₀ ∈ [0,1]^I` (the paper's "any oracle `O`"), there is `x ∈ [0,1]^I` that agrees with `x₀` off `R`
and is reflective on `R`. Proof: `exists_reflective` on the queries `R` for the evaluation maps
`y ↦ ev i (extendBy R x₀ y)`, which are continuous on the cube of `R` because `extendBy` is
continuous and maps cube to cube — App. B's own route for 2.1 (ii) (the off-`R` clause is the third
condition on the paper's correspondence, "constant in this case"), restricted to finite `R`. With
`R = univ` this is `exists_reflective` (`exists_reflective_of_reflectiveOn_univ`); at `R = ∅` it is
empty (`reflectiveOn_empty`). `I` need not be finite — only `R` is (the Kakutani step runs on
`[0,1]^R`), which is the shape of the paper's countable query set with a finite `R`; and continuity
is needed only at the queries of `R` (Theorem 2.1 (ii) constrains nothing off `R`). What the paper
*omits* (§5: "the proof can be adapted to also show an analog of Theorem 2.1 (ii), but we omit the
details") is the `G_R`-based analogue, not this one: see `gameR_nash_reflectiveOn` and
`exists_reflectiveOn_via_gameR_brouwer` (repair round 2, finding F9).
Source: FTC 2015 Theorem 2.1 (ii) ("for any oracle `O` and every set of queries `R`, there is an
oracle `O'` which is reflective on `R` and satisfies `P(O'(M,p)=1) = P(O(M,p)=1)` for all
`(M,p) ∉ R`") and App. B's proof of it, finite abstract core; mandate target 19, secondary extension
Kind: C
Fidelity: variant: abstract, finite `R`, real thresholds (evaluation maps in place of machines; the
prescribed vector `x₀` stands for the oracle `O`'s answers); stronger: `I` arbitrary, continuity only
at the queries of `R`
Hyps: (a) all: Kakutani via `exists_reflective`; (c) evaluation maps in place of oracle machines -/
theorem exists_reflectiveOn (R : Finset I) (ev : I → (I → ℝ) → ℝ)
    (hev : ∀ i ∈ R, ContinuousOn (ev i) (cube I)) (p : I → ℝ) {x₀ : I → ℝ} (hx₀ : x₀ ∈ cube I) :
    ∃ x ∈ cube I, (∀ i ∉ R, x i = x₀ i) ∧ ReflectiveOn R ev p x := by
  obtain ⟨y, hy, hyR⟩ := exists_reflective (fun (i : R) (y : R → ℝ) => ev i (extendBy R x₀ y))
    (fun i => (hev i i.2).comp (continuous_extendBy R x₀).continuousOn
      (fun y hy => extendBy_mem_cube hx₀ hy)) (fun i => p i)
  refine ⟨extendBy R x₀ y, extendBy_mem_cube hx₀ hy, fun i hi => extendBy_apply_of_not_mem _ _ hi,
    fun i hi => ?_⟩
  rw [extendBy_apply_of_mem _ _ hi]
  exact hyR ⟨i, hi⟩

/-- **The degenerate end `R = univ`**: `exists_reflectiveOn` at the full query set is
`exists_reflective` (the prescription is vacuous), so the theorem generalizes it rather than
standing beside it.
Source: FTC 2015 Theorem 2.1 (ii) at `R` = all queries; audit round 2 (adversarial 3.7)
Kind: L
Fidelity: n/a
Hyps: (a) all -/
theorem exists_reflective_of_reflectiveOn_univ (ev : I → (I → ℝ) → ℝ)
    (hev : ∀ i, ContinuousOn (ev i) (cube I)) (p : I → ℝ) : ∃ x ∈ cube I, Reflective ev p x := by
  obtain ⟨x, hx, -, hR⟩ := exists_reflectiveOn Finset.univ ev (fun i _ => hev i) p
    (x₀ := fun _ => 0) (fun i _ => by simp)
  exact ⟨x, hx, (reflectiveOn_univ_iff ev p x).1 hR⟩

end Extend

omit [Fintype I] in
/-- **The degenerate end `R = ∅`**: reflective on no query is vacuous, so `exists_reflectiveOn` at
`R = ∅` says only that `x₀` lies in the cube. The content of the theorem sits at nonempty proper
`R` (witness: `exists_reflectiveOn_selfRef`).
Source: FTC 2015 Theorem 2.1 (ii) at `R = ∅`; audit round 2 (adversarial 3.7)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem reflectiveOn_empty (ev : I → (I → ℝ) → ℝ) (p x : I → ℝ) :
    ReflectiveOn (∅ : Finset I) ev p x := by
  simp [ReflectiveOn]

/-- Two queries: `ev 0 x = x 1` ("is query `1` answered `1`?") and `ev 1 x = 1 − x 1` (the liar on
query `1`).
Source: none: infrastructure (witness of `exists_reflectiveOn`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def twoQueryEv : Fin 2 → (Fin 2 → ℝ) → ℝ := ![fun x => x 1, fun x => 1 - x 1]

/-- **N+ witness of `exists_reflectiveOn`**: with `R = {0}`, the prescription `x 1 = 1` and thresholds
`1/2`, being reflective on `R` forces `x 0 = 1`, while the vector is *not* reflective on all queries
(the liar at query `1` would need `x 1 = 1/2`). So "reflective on `R` with prescribed answers off `R`"
is genuinely weaker than `Reflective`, and the prescription is honoured.
Source: FTC 2015 Theorem 2.1 (ii) (the content of "reflective on `R`" for a proper `R`)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem reflectiveOn_twoQuery (x : Fin 2 → ℝ) (hx1 : x 1 = 1)
    (h : ReflectiveOn {0} twoQueryEv (fun _ => 1 / 2) x) :
    x 0 = 1 ∧ ¬ Reflective twoQueryEv (fun _ => 1 / 2) x := by
  have h0 := h 0 (Finset.mem_singleton_self 0)
  simp only [twoQueryEv, Matrix.cons_val_zero, hx1] at h0
  refine ⟨h0.1 (by norm_num), fun hr => ?_⟩
  have h1 := (hr 1).2
  norm_num [twoQueryEv, hx1] at h1

/-- **`exists_reflectiveOn` instantiated** on `twoQueryEv` with `R = {0}` and `x₀ = ![0, 1]`: a vector
in the cube with `x 1 = 1` that is reflective on `{0}` (hence, by `reflectiveOn_twoQuery`, `x 0 = 1`).
Source: FTC 2015 Theorem 2.1 (ii)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem exists_reflectiveOn_twoQuery :
    ∃ x ∈ cube (Fin 2), x 1 = 1 ∧ ReflectiveOn {0} twoQueryEv (fun _ => 1 / 2) x := by
  obtain ⟨x, hx, hoff, hR⟩ := exists_reflectiveOn {0} twoQueryEv
    (fun i _ => by
      fin_cases i
      · exact (continuous_apply 1).continuousOn
      · exact (continuous_const.sub (continuous_apply 1)).continuousOn)
    (fun _ => 1 / 2) (x₀ := ![0, 1]) (fun i _ => by fin_cases i <;> simp)
  refine ⟨x, hx, ?_, hR⟩
  have := hoff 1 (by simp)
  simpa using this

/-- **The liar inside `R`, read from outside**: `ev 0 x = 1 − x 0` (query `0` is the liar about
itself) and `ev 1 x = x 0` (query `1` reads query `0`'s answer).
Source: none: infrastructure (witness of `exists_reflectiveOn`; audit round 2, adversarial 3.1)
Kind: D
Fidelity: exact
Hyps: n/a -/
def selfRefEv : Fin 2 → (Fin 2 → ℝ) → ℝ := ![fun x => 1 - x 0, fun x => x 0]

/-- **Reflectivity on `{0}` alone pins the self-referential answer**: for `selfRefEv` at thresholds
`![1/2, 1/4]`, any `x` in the cube that is reflective on `{0}` has `x 0 = 1/2` — the fixed-point step
of `exists_reflectiveOn` on `[0,1]^R` does the work here (`ev 0` reads its own answer), unlike
`reflectiveOn_twoQuery`, where the query in `R` reads only the prescribed coordinate.
Source: FTC 2015 Theorem 2.1 (ii) (the self-referential content of "reflective on `R`"); audit
round 2 (adversarial 3.1)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem selfRef_forces_half {x : Fin 2 → ℝ} (hx : x ∈ cube (Fin 2))
    (h : ReflectiveOn {0} selfRefEv ![1 / 2, 1 / 4] x) : x 0 = 1 / 2 := by
  have h0 := h 0 (Finset.mem_singleton_self 0)
  simp only [selfRefEv, Matrix.cons_val_zero] at h0
  have hx0 := hx 0 (mem_univ _)
  rcases lt_trichotomy (1 / 2 : ℝ) (1 - x 0) with hlt | heq | hgt
  · have := h0.1 hlt
    linarith
  · linarith
  · have := h0.2 hgt
    linarith [hx0.1]

/-- **`exists_reflectiveOn` instantiated on the self-referential instance**: with `R = {0}`,
prescription `x₀ = ![0, 0]` and thresholds `![1/2, 1/4]`, the vector produced has `x 1 = 0`
(prescribed), `x 0 = 1/2` (forced by the liar inside `R`), and is not `Reflective` (query `1` sees
`x 0 = 1/2 > 1/4` and would need `x 1 = 1`). This inhabits the full hypothesis package with the
fixed-point step exercised inside `R`.
Source: FTC 2015 Theorem 2.1 (ii); audit round 2 (adversarial 3.1)
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem exists_reflectiveOn_selfRef :
    ∃ x ∈ cube (Fin 2), x 1 = 0 ∧ x 0 = 1 / 2 ∧ ReflectiveOn {0} selfRefEv ![1 / 2, 1 / 4] x ∧
      ¬ Reflective selfRefEv ![1 / 2, 1 / 4] x := by
  obtain ⟨x, hx, hoff, hR⟩ := exists_reflectiveOn {0} selfRefEv
    (fun i _ => by
      fin_cases i
      · exact (continuous_const.sub (continuous_apply 0)).continuousOn
      · exact (continuous_apply 0).continuousOn)
    ![1 / 2, 1 / 4] (x₀ := ![0, 0]) (fun i _ => by fin_cases i <;> simp)
  have h1 : x 1 = 0 := by simpa using hoff 1 (by simp)
  have h0 : x 0 = 1 / 2 := selfRef_forces_half hx hR
  refine ⟨x, hx, h1, h0, hR, fun hr => ?_⟩
  have := (hr 1).1
  simp only [selfRefEv, Matrix.cons_val_one, Matrix.cons_val_zero, h0, h1] at this
  norm_num at this

/-! ### Witness: matching pennies -/

/-- **Matching pennies as evaluation maps**: query `0` ("does the row player match?") has output
probability `x 1`, query `1` ("does the column player mismatch?") has `1 - x 0`; thresholds `1/2`.
Source: [[fixpoint-lit-2-inventory]] 010 ("matching pennies: `n = 2`, `ev₁ = x₂`, `ev₂ = 1 − x₁`,
`p = ½`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def mpEv : Fin 2 → (Fin 2 → ℝ) → ℝ := ![fun x => x 1, fun x => 1 - x 0]

/-- **N+ witness of target 10**: in the cube, the reflective vectors of matching pennies at threshold
`1/2` are exactly `![1/2, 1/2]` (both coordinates are forced to the tie).
Source: [[fixpoint-lit-2-inventory]] 010 ("unique solution `(½, ½)`")
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem reflective_mp_iff {x : Fin 2 → ℝ} (hx : x ∈ cube (Fin 2)) :
    Reflective mpEv (fun _ => 1 / 2) x ↔ x = ![1 / 2, 1 / 2] := by
  have h0 := hx 0 (mem_univ _)
  have h1 := hx 1 (mem_univ _)
  constructor
  · intro h
    have e0 := h 0
    have e1 := h 1
    simp only [mpEv, Matrix.cons_val_zero, Matrix.cons_val_one] at e0 e1
    have hx1 : x 1 = 1 / 2 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := e0.2 hlt
        have := e1.1 (by linarith)
        linarith
      · have := e0.1 hgt
        have := e1.2 (by linarith)
        linarith
    have hx0 : x 0 = 1 / 2 := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have := e1.1 (by linarith)
        linarith
      · have := e1.2 (by linarith)
        linarith
    ext i
    fin_cases i <;> simp [hx0, hx1]
  · rintro rfl i
    fin_cases i <;> simp [mpEv]
    all_goals norm_num

/-- **Cross-check against `fix-kakutani`**: on the square, reflectivity of matching pennies at `1/2`
coincides with being a fixed point of `fix-kakutani`'s best-response correspondence `mpBR` (both are
`x = (1/2, 1/2)`, by `reflective_mp_iff` and `mem_mpBR_self_iff`).
Source: mandate target 10 ("cross-check against `fix-kakutani`'s `mem_mpBR_self_iff`")
Kind: L
Fidelity: n/a
Hyps: none -/
theorem reflective_mp_iff_mem_mpBR {x : Fin 2 → ℝ} (hx : x ∈ cube (Fin 2)) :
    Reflective mpEv (fun _ => 1 / 2) x ↔ x ∈ mpBR x := by
  rw [reflective_mp_iff hx, mem_mpBR_self_iff]
  constructor
  · rintro rfl; ext i; fin_cases i <;> simp
  · intro h; rw [h]; ext i; fin_cases i <;> simp

/-- **Existence for matching pennies, instantiated** (the N+ witness inhabits the full hypothesis
package of `exists_reflective`: `mpEv` is continuous).
Source: [[fixpoint-lit-2-inventory]] 010
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exists_reflective_mp : ∃ x ∈ cube (Fin 2), Reflective mpEv (fun _ => 1 / 2) x :=
  exists_reflective mpEv (fun i => by
    fin_cases i
    · exact (continuous_apply 1).continuousOn
    · exact (continuous_const.sub (continuous_apply 0)).continuousOn) _

end Cleanroom.Fixpoint.FixOraclesCorresp
