import Cleanroom.Fixpoint.FixOraclesCorresp.GameR
import LogicalInduction.Construction.Brouwer
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.BrouwerOnly`: Kakutani-free existence of reflective oracles

Target 19 (extension; the mandate's "run's own theorem"), route (c) of fixpoint-lit-2-010. The
Kakutani step in `exists_reflective` — a fixed point of the correspondence `oracleCorr ev p` with
interval-valued coordinates — is replaced by a **Brouwer** step on a single continuous self-map of
the cube: the clamp step

  `clampStep ev p x i = max 0 (min 1 (x i + (ev i x − p i)))`,

which moves each answer in the direction of its excess over the threshold and clamps to `[0, 1]`.
It is continuous when `ev` is, maps the cube to itself, and **every fixed point of it is reflective**
(`reflective_of_clampStep_eq`): if `ev i x > p i` the clamp can only fix `x i` at `1`, and if
`ev i x < p i` only at `0`. Brouwer (FAF's `LogicalInduction.brouwer_fixed_point`, transported to
finite-dimensional normed spaces by `brouwer_findim` along the same continuous linear equivalence
`fix-kakutani` uses) then gives `exists_reflective_brouwer`, and the chain

  `exists_reflective_polynomial_brouwer` → `exists_isMixedNashEq_brouwer` →
  `exists_reflective_via_gameR_brouwer`

is Theorem 5.1's existence route with no Kakutani anywhere: the only fixed-point theorem in the
proof terms is Brouwer, through `brouwer_findim`; everything else is the algebra of
`isMixedNashEq_iff_reflective` and `gameR_nash_reflective`. **Kakutani-freeness is machine-checked**
at the proof-term level, not by reading: the round-2 audit probes
`run/wp/fix-oracles-corresp/audit-r2-probes/{KakutaniFree,AdvKakutaniFree}.lean` walk the transitive
constant closure of every headline here (≈ 1760–2010 constants, `ConstantInfo.value?` with
`allowOpaque := true`, the necessary flag under Lean v4.31 to see theorem bodies) and find no
constant of `Cleanroom.Found.FixKakutani` and none of `exists_reflective` /
`exists_isMixedNashEq` / `exists_reflective_via_gameR`, while the control cases do
(`AdvKakutaniFree.out.txt`). What "Brouwer only" *removes* is the correspondence, the selection and
the closed-graph machinery; the controls also reach FAF's Brouwer (fix-kakutani proves Kakutani from
it). The route through `G_R` via `exists_isMixedNashEq_brouwer` is a second *route*, not an
independent proof: that Nash-existence input is itself obtained from `exists_reflective_brouwer` via
Theorem 4.1. The independent second proof is `exists_reflective_via_gameR_nashMap`, whose Nash input
`exists_isMixedNashEq_nashMap` is Brouwer on Nash's own normalized map (`nashStep`, the mandate's
first option for target 19); it is probe-checked to share nothing with the clamp-step route beyond
Brouwer and Theorem 4.1's algebra (`run/wp/fix-oracles-corresp/repair-r2-probes/NashMapIndependent.lean`).

The clamp step is an exact reformulation, not an artifact with some reflective fixed points:
`clampStep_eq_iff_reflective` — on the cube, `clampStep ev p x = x ↔ Reflective ev p x`.
`exists_reflectiveOn_brouwer` is Theorem 2.1 (ii)'s finite analogue (App. B's route) with Brouwer,
and `exists_reflectiveOn_via_gameR_brouwer` the `G_R`-based analogue that FTC §5 omits, Brouwer only.
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set StrategicGame

/-- **Brouwer on a finite-dimensional real normed space**: a continuous self-map of a nonempty
compact convex `K ⊆ E` has a fixed point in `K`. Transport of FAF's `brouwer_fixed_point`
(`EuclideanSpace ℝ (Fin d)`) along `ContinuousLinearEquiv.ofFinrankEq`, the path `kakutani_findim`
takes for correspondences.
Source: FAF `LogicalInduction.brouwer_fixed_point` (`Construction/Brouwer.lean`); none: infrastructure
Kind: C (thin: a transport along one continuous linear equivalence — image of compact/convex/nonempty,
conjugation of `f`, FAF's theorem, injectivity)
Fidelity: stronger: any finite-dimensional real normed space
Hyps: (a) all -/
theorem brouwer_findim {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {K : Set E} (hK_compact : IsCompact K) (hK_convex : Convex ℝ K) (hK_nonempty : K.Nonempty)
    (f : E → E) (hf_cont : ContinuousOn f K) (hf_maps : MapsTo f K K) : ∃ x ∈ K, f x = x := by
  let e : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let g : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun y => e (f (e.symm y))
  have hK'c : IsCompact (e '' K) := hK_compact.image e.continuous
  have hK'v : Convex ℝ (e '' K) := hK_convex.is_linear_image ⟨e.map_add, e.map_smul⟩
  have hK'n : (e '' K).Nonempty := hK_nonempty.image e
  have hsymm : MapsTo e.symm (e '' K) K := by
    rintro y ⟨x, hx, rfl⟩
    simpa using hx
  have hg_cont : ContinuousOn g (e '' K) :=
    e.continuous.comp_continuousOn (hf_cont.comp e.symm.continuous.continuousOn hsymm)
  have hg_maps : MapsTo g (e '' K) (e '' K) := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨f x, hf_maps hx, by simp [g]⟩
  obtain ⟨y, hyK, hy⟩ := LogicalInduction.brouwer_fixed_point hK'c hK'v hK'n g hg_cont hg_maps
  obtain ⟨x, hx, rfl⟩ := hyK
  refine ⟨x, hx, ?_⟩
  simp only [g, e.symm_apply_apply] at hy
  exact e.injective hy

variable {I : Type*} [Fintype I]

/-- **The clamp step**: `clampStep ev p x i = max 0 (min 1 (x i + (ev i x − p i)))` — each answer
moves by its excess over the threshold and is clamped to `[0, 1]`.
Source: [[fixpoint-lit-2-inventory]] 010, route (c) ("interval-valued coordinates make the selection
step elementary"); mandate target 19
Kind: D
Fidelity: variant: abstract (evaluation maps in place of machines)
Hyps: n/a -/
noncomputable def clampStep (ev : I → (I → ℝ) → ℝ) (p : I → ℝ) (x : I → ℝ) : I → ℝ :=
  fun i => max 0 (min 1 (x i + (ev i x - p i)))

omit [Fintype I] in
/-- The clamp step maps the cube to itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem clampStep_mapsTo (ev : I → (I → ℝ) → ℝ) (p : I → ℝ) :
    MapsTo (clampStep ev p) (cube I) (cube I) := by
  intro x _ i _
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

omit [Fintype I] in
/-- The clamp step is continuous on the cube when the evaluation maps are.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem continuousOn_clampStep (ev : I → (I → ℝ) → ℝ) (hev : ∀ i, ContinuousOn (ev i) (cube I))
    (p : I → ℝ) : ContinuousOn (clampStep ev p) (cube I) := by
  have hin : ContinuousOn (fun x : I → ℝ => fun i => x i + (ev i x - p i)) (cube I) :=
    continuousOn_pi.2 fun i =>
      (continuous_apply i).continuousOn.add ((hev i).sub continuousOn_const)
  have hout : Continuous (fun v : I → ℝ => fun i => max 0 (min 1 (v i))) :=
    continuous_pi fun i => continuous_const.max (continuous_const.min (continuous_apply i))
  exact hout.comp_continuousOn hin

omit [Fintype I] in
/-- **A fixed point of the clamp step in the cube is reflective.** If `p i < ev i x` then
`x i + (ev i x − p i) > x i`, so the clamp can return `x i` only by saturating at `1`; symmetrically
`ev i x < p i` forces `x i = 0`.
Source: [[fixpoint-lit-2-inventory]] 010, route (c); mandate target 19
Kind: P
Fidelity: variant: abstract
Hyps: (a) none; (c) evaluation maps in place of oracle machines -/
theorem reflective_of_clampStep_eq {ev : I → (I → ℝ) → ℝ} {p x : I → ℝ} (hx : x ∈ cube I)
    (h : clampStep ev p x = x) : Reflective ev p x := by
  intro i
  have hi := congrFun h i
  simp only [clampStep] at hi
  have hx0 := (hx i (mem_univ _)).1
  have hx1 := (hx i (mem_univ _)).2
  constructor
  · intro hlt
    by_contra hne
    have hlt1 : x i < 1 := lt_of_le_of_ne hx1 hne
    rcases le_or_gt (x i + (ev i x - p i)) 1 with h1 | h1
    · rw [min_eq_right h1, max_eq_right (by linarith)] at hi
      linarith
    · rw [min_eq_left h1.le, max_eq_right zero_le_one] at hi
      linarith
  · intro hlt
    by_contra hne
    have hpos : 0 < x i := lt_of_le_of_ne hx0 (Ne.symm hne)
    rcases le_or_gt 0 (x i + (ev i x - p i)) with h0 | h0
    · rw [min_eq_right (by linarith), max_eq_right h0] at hi
      linarith
    · rw [min_eq_right (by linarith), max_eq_left h0.le] at hi
      linarith

omit [Fintype I] in
/-- **A reflective vector in the cube is a fixed point of the clamp step** (the converse of
`reflective_of_clampStep_eq`): above the threshold `x i = 1` and the clamp saturates at `1`; below it
`x i = 0` and the clamp saturates at `0`; at a tie the step is the identity on `[0, 1]`.
Source: audit round 2 (adversarial 3.3); [[fixpoint-lit-2-inventory]] 010, route (c)
Kind: P
Fidelity: variant: abstract
Hyps: (a) none; (c) evaluation maps in place of oracle machines -/
theorem clampStep_eq_of_reflective {ev : I → (I → ℝ) → ℝ} {p x : I → ℝ} (hx : x ∈ cube I)
    (h : Reflective ev p x) : clampStep ev p x = x := by
  funext i
  simp only [clampStep]
  have hx0 := (hx i (mem_univ _)).1
  have hx1 := (hx i (mem_univ _)).2
  rcases lt_trichotomy (p i) (ev i x) with hlt | heq | hgt
  · have h1 := (h i).1 hlt
    rw [h1, min_eq_left (by linarith), max_eq_right zero_le_one]
  · rw [heq, sub_self, add_zero, min_eq_right hx1, max_eq_right hx0]
  · have h0 := (h i).2 hgt
    rw [h0, min_eq_right (by linarith), max_eq_left (by linarith)]

omit [Fintype I] in
/-- **The clamp step is an exact reformulation**: on the cube, its fixed points are *exactly* the
reflective vectors, so `{x ∈ cube | clampStep ev p x = x}` is the reflective set and the Brouwer
route loses nothing. This is the honest answer to "is the clamp step an artifact that happens to
have some reflective fixed points?" — no: the finite core of FTC needs Brouwer on one self-map whose
fixed points are the objects sought.
Source: audit round 2 (adversarial 3.3); FTC 2015 App. B (the correspondence's fixed points are the
reflective oracles, `mem_oracleCorr_self_iff`) — the clamp step plays that role for a single map
Kind: P
Fidelity: variant: abstract
Hyps: (a) none; (c) evaluation maps in place of oracle machines -/
theorem clampStep_eq_iff_reflective {ev : I → (I → ℝ) → ℝ} {p x : I → ℝ} (hx : x ∈ cube I) :
    clampStep ev p x = x ↔ Reflective ev p x :=
  ⟨reflective_of_clampStep_eq hx, clampStep_eq_of_reflective hx⟩

/-- **Target 19: Kakutani-free existence of reflective oracles (Brouwer only).** For continuous
evaluation maps on the cube and any thresholds, some `x ∈ [0,1]^I` is reflective — Brouwer
(`brouwer_findim`) on the clamp step, then `reflective_of_clampStep_eq`. Same statement as
`exists_reflective`; the proof uses no correspondence and no selection.
Source: FTC 2015 Theorem 2.1 (i), finite abstract core; [[fixpoint-lit-2-inventory]] 010 route (c);
mandate target 19 ("the run's new theorem")
Kind: C
Fidelity: variant: abstract, finite `I`, real thresholds
Hyps: (a) all: Brouwer is FAF's `brouwer_fixed_point` through `brouwer_findim`; (c) evaluation maps in
place of oracle machines -/
theorem exists_reflective_brouwer (ev : I → (I → ℝ) → ℝ) (hev : ∀ i, ContinuousOn (ev i) (cube I))
    (p : I → ℝ) : ∃ x ∈ cube I, Reflective ev p x := by
  obtain ⟨x, hx, hfix⟩ := brouwer_findim (isCompact_univ_pi fun _ => isCompact_Icc)
    (convex_pi fun _ _ => convex_Icc 0 1)
    (Set.univ_pi_nonempty_iff.2 fun _ => Set.nonempty_Icc.2 zero_le_one)
    (clampStep ev p) (continuousOn_clampStep ev hev p) (clampStep_mapsTo ev p)
  exact ⟨x, hx, reflective_of_clampStep_eq hx hfix⟩

/-- **Matching pennies through the Brouwer route** (inhabits the full package of
`exists_reflective_brouwer`; by `reflective_mp_iff` the vector produced is `![1/2, 1/2]`).
Source: [[fixpoint-lit-2-inventory]] 010
Kind: N+
Fidelity: exact
Hyps: (a) all -/
theorem exists_reflective_mp_brouwer : ∃ x ∈ cube (Fin 2), Reflective mpEv (fun _ => 1 / 2) x :=
  exists_reflective_brouwer mpEv (fun i => by
    fin_cases i
    · exact (continuous_apply 1).continuousOn
    · exact (continuous_const.sub (continuous_apply 0)).continuousOn) _

/-- **Kakutani-free existence of polynomial reflective oracles** (Theorem 5.1's class).
Source: FTC 2015 Theorem 5.1 (existence part); mandate target 19
Kind: C
Fidelity: stronger: no `d ≤ B`, no range condition, and no `c ≥ 0` (a condition of the mandate's
phrasing, not the paper's — FTC §5 writes the polynomial with no sign condition on `c`; the liar's own
polynomial has `c = ![1, −1]`); variant: abstract
Hyps: (a) all (Brouwer only); (c) evaluation maps in place of oracle machines -/
theorem exists_reflective_polynomial_brouwer {K : Type*} [Fintype K] (c : I → K → ℝ)
    (d : I → K → I → ℕ) (p : I → ℝ) : ∃ x ∈ cube I, Reflective (polyEv c d) p x :=
  exists_reflective_brouwer _ (fun i => (continuous_polyEv c d i).continuousOn) p

/-- **Two-action Nash existence from Brouwer only**: every finite two-action game has a mixed Nash
equilibrium, via `exists_reflective_brouwer` on `evOf u` and Theorem 4.1
(`isMixedNashEq_iff_reflective`). The Kakutani-based twin is `exists_isMixedNashEq`.
Source: FTC 2015 §4 (corollary of 4.1 + 2.1); Nash 1951 (Brouwer route); mandate target 19
Kind: C
Fidelity: variant: abstract, two actions
Hyps: (a) all (Brouwer only); (c) evaluation maps in place of oracle machines -/
theorem exists_isMixedNashEq_brouwer {N : Type*} [Fintype N] [DecidableEq N]
    (u : (N → Fin 2) → N → ℝ) :
    ∃ σ : MixedProfile (twoActionGame u), IsMixedNashEq (twoActionGame u) σ := by
  obtain ⟨x, hx, hrefl⟩ := exists_reflective_brouwer (evOf u) (continuousOn_evOf u) (fun _ => 1 / 2)
  refine ⟨ofCube u x hx, ?_⟩
  rw [isMixedNashEq_iff_reflective, toCube_ofCube]
  exact hrefl

/-- **Theorem 5.1's existence route, Kakutani-free**: a mixed Nash equilibrium of `G_R` exists by
`exists_isMixedNashEq_brouwer`, and its main answer vector is reflective for `polyEv c d` at `p` by
`gameR_nash_reflective`. Compare `exists_reflective_via_gameR`, whose Nash existence rests on
`exists_reflective` (Kakutani); here the only fixed-point theorem in the proof term is Brouwer
(probe-checked, see the module header). A second *route*, not an independent proof: its Nash input
`exists_isMixedNashEq_brouwer` is obtained from `exists_reflective_brouwer` via Theorem 4.1, so the
paper's "more elementary" (which rests on Nash existence as an independently known theorem) does not
transfer; the independent second proof derives two-action Nash existence from Brouwer via Nash's
own normalized map (the mandate's first option: `exists_isMixedNashEq_nashMap`,
`exists_reflective_via_gameR_nashMap` below).
Source: FTC 2015 Theorem 5.1 ("the existence of oracles reflective on `R` follows from the existence
of Nash equilibria in `G_R`"); mandate target 19
Kind: C
Fidelity: variant: abstract (polynomial representation as hypothesis class, F9)
Hyps: (a) all (Brouwer only); `hd` is the paper's "bounded"; (c) evaluation maps in place of oracle
machines -/
theorem exists_reflective_via_gameR_brouwer [DecidableEq I] {K : Type*} [Fintype K] {B : ℕ}
    (c : I → K → ℝ) (d : I → K → I → ℕ) (hd : ∀ i k i', d i k i' ≤ B) (p : I → ℝ) :
    ∃ σ : MixedProfile (gameR (B := B) c d p), IsMixedNashEq (gameR c d p) σ ∧
      Reflective (polyEv c d) p (fun i => (σ (mainP i)).val 1) := by
  obtain ⟨σ, hσ⟩ := exists_isMixedNashEq_brouwer (gameRPayoff (B := B) c d p)
  exact ⟨σ, hσ, gameR_nash_reflective c d hd p hσ⟩

omit [Fintype I] in
/-- **Theorem 2.1 (ii)'s finite analogue, Kakutani-free**: as `exists_reflectiveOn` (App. B's route
for 2.1 (ii), restricted to finite `R`), with `exists_reflective_brouwer` on `[0,1]^R` in place of
`exists_reflective`. Continuity is needed only at the queries of `R`.
Source: FTC 2015 Theorem 2.1 (ii) and App. B's proof of it; mandate target 19
Kind: C
Fidelity: variant: abstract, finite `R`; stronger: `I` arbitrary, continuity only at the queries of `R`
Hyps: (a) all (Brouwer only); (c) evaluation maps in place of oracle machines -/
theorem exists_reflectiveOn_brouwer [DecidableEq I] (R : Finset I) (ev : I → (I → ℝ) → ℝ)
    (hev : ∀ i ∈ R, ContinuousOn (ev i) (cube I)) (p : I → ℝ) {x₀ : I → ℝ} (hx₀ : x₀ ∈ cube I) :
    ∃ x ∈ cube I, (∀ i ∉ R, x i = x₀ i) ∧ ReflectiveOn R ev p x := by
  obtain ⟨y, hy, hyR⟩ := exists_reflective_brouwer
    (fun (i : R) (y : R → ℝ) => ev i (extendBy R x₀ y))
    (fun i => (hev i i.2).comp (continuous_extendBy R x₀).continuousOn
      (fun y hy => extendBy_mem_cube hx₀ hy)) (fun i => p i)
  refine ⟨extendBy R x₀ y, extendBy_mem_cube hx₀ hy, fun i hi => extendBy_apply_of_not_mem _ _ hi,
    fun i hi => ?_⟩
  rw [extendBy_apply_of_mem _ _ hi]
  exact hyR ⟨i, hi⟩

/-! ### Nash's own map: two-action Nash existence from Brouwer, independent of the clamp step

The mandate's first option for target 19. `exists_isMixedNashEq_brouwer` obtains Nash existence
*from* reflective-oracle existence (Theorem 4.1 read backwards), so the `G_R` route through it is a
second route but not an independent proof (audit round 2, both lenses). Here two-action Nash
existence is proved the way Nash 1951 proves it — Brouwer on Nash's normalized map — with no
reference to the clamp step or to `exists_reflective_brouwer`; the resulting `G_R` route
`exists_reflective_via_gameR_nashMap` is then a second proof of polynomial reflective-oracle
existence whose only shared input with the direct proof is Brouwer itself (and Theorem 4.1's algebra,
which the paper's route also uses). Independence is a claim about proof terms; it is probe-checked
(`run/wp/fix-oracles-corresp/repair-r2-probes/NashMapIndependent.lean`). -/

/-- **Nash's normalized map** for a two-action game, on the cube of the players' probabilities of
action `1`: with `g = gain u i x` (player `i`'s payoff difference between the pure actions `1` and
`0` against the others' mixtures — independent of `x i`, `gain_update`), the gains from deviating to
the pure actions are `(1 − x i) · g` (to `1`) and `−x i · g` (to `0`), and Nash's map sends `x i` to
`(x i + max 0 ((1 − x i) · g)) / (1 + max 0 ((1 − x i) · g) + max 0 (−x i · g))`.
Source: Nash 1951 (*Non-cooperative games*, the map `T` of the Brouwer proof), specialized to two
actions with the simplex parametrized by `x i`; mandate target 19, first option
Kind: D
Fidelity: exact (Nash's `T` in the two-action parametrization)
Hyps: n/a -/
noncomputable def nashStep {N : Type*} [Fintype N] [DecidableEq N] (u : (N → Fin 2) → N → ℝ)
    (x : N → ℝ) : N → ℝ := fun i =>
  (x i + max 0 ((1 - x i) * gain u i x)) /
    (1 + max 0 ((1 - x i) * gain u i x) + max 0 (-(x i) * gain u i x))

/-- Nash's map sends the cube to itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem nashStep_mapsTo {N : Type*} [Fintype N] [DecidableEq N] (u : (N → Fin 2) → N → ℝ) :
    MapsTo (nashStep u) (cube N) (cube N) := by
  intro x hx i _
  have hx0 := (hx i (mem_univ _)).1
  have hx1 := (hx i (mem_univ _)).2
  have hA : 0 ≤ max 0 ((1 - x i) * gain u i x) := le_max_left _ _
  have hB : 0 ≤ max 0 (-(x i) * gain u i x) := le_max_left _ _
  have hD : 0 < 1 + max 0 ((1 - x i) * gain u i x) + max 0 (-(x i) * gain u i x) := by linarith
  exact ⟨div_nonneg (by linarith) hD.le, (div_le_one hD).2 (by linarith)⟩

/-- Nash's map is continuous (the gains are polynomials; the denominator is `≥ 1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem continuous_nashStep {N : Type*} [Fintype N] [DecidableEq N] (u : (N → Fin 2) → N → ℝ) :
    Continuous (nashStep u) := by
  refine continuous_pi fun i => ?_
  have hg := continuous_gain u i
  have hA : Continuous fun x : N → ℝ => max 0 ((1 - x i) * gain u i x) :=
    continuous_const.max ((continuous_const.sub (continuous_apply i)).mul hg)
  have hB : Continuous fun x : N → ℝ => max 0 (-(x i) * gain u i x) :=
    continuous_const.max ((continuous_apply i).neg.mul hg)
  refine ((continuous_apply i).add hA).div ((continuous_const.add hA).add hB) fun x => ?_
  have h1 := le_max_left (0 : ℝ) ((1 - x i) * gain u i x)
  have h2 := le_max_left (0 : ℝ) (-(x i) * gain u i x)
  exact (by linarith : (0 : ℝ) < 1 + max 0 ((1 - x i) * gain u i x) + max 0 (-(x i) * gain u i x)).ne'

/-- **A fixed point of Nash's map in the cube is a reflective vector for `evOf u` at `1/2`** — Nash's
argument: at a fixed point `x i + A = x i (1 + A + B)` with `A = max 0 ((1 − x i) g)`,
`B = max 0 (−x i g)`; if `g > 0` then `B = 0` and `(1 − x i)² g = 0`, so `x i = 1`; if `g < 0` then
`A = 0` and `x i² g = 0`, so `x i = 0`. (Through Theorem 4.1 this is "a fixed point of Nash's map is
a Nash equilibrium"; the sign conditions are stated directly.)
Source: Nash 1951, the fixed-point step of the Brouwer proof; mandate target 19, first option
Kind: P
Fidelity: variant: abstract (two actions, cube coordinates)
Hyps: (a) none; (c) evaluation maps in place of oracle machines -/
theorem reflective_of_nashStep_eq {N : Type*} [Fintype N] [DecidableEq N]
    {u : (N → Fin 2) → N → ℝ} {x : N → ℝ} (hx : x ∈ cube N) (h : nashStep u x = x) :
    Reflective (evOf u) (fun _ => 1 / 2) x := by
  intro i
  have hi := congrFun h i
  simp only [nashStep] at hi
  have hx0 := (hx i (mem_univ _)).1
  have hx1 := (hx i (mem_univ _)).2
  have hA : 0 ≤ max 0 ((1 - x i) * gain u i x) := le_max_left _ _
  have hB : 0 ≤ max 0 (-(x i) * gain u i x) := le_max_left _ _
  have hD : 0 < 1 + max 0 ((1 - x i) * gain u i x) + max 0 (-(x i) * gain u i x) := by linarith
  rw [div_eq_iff hD.ne'] at hi
  simp only [evOf]
  constructor
  · intro hlt
    have hgpos : 0 < gain u i x := by linarith
    have hA' : max 0 ((1 - x i) * gain u i x) = (1 - x i) * gain u i x :=
      max_eq_right (mul_nonneg (by linarith) hgpos.le)
    have hB' : max 0 (-(x i) * gain u i x) = 0 :=
      max_eq_left (by linarith [mul_nonneg hx0 hgpos.le])
    rw [hA', hB'] at hi
    have h2 : (1 - x i) * (1 - x i) * gain u i x = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · rcases mul_eq_zero.1 h3 with h4 | h4 <;> linarith
    · linarith
  · intro hlt
    have hgneg : gain u i x < 0 := by linarith
    have hA' : max 0 ((1 - x i) * gain u i x) = 0 :=
      max_eq_left (by linarith [mul_nonneg (sub_nonneg.2 hx1) (neg_nonneg.2 hgneg.le)])
    have hB' : max 0 (-(x i) * gain u i x) = -(x i) * gain u i x :=
      max_eq_right (by linarith [mul_nonneg hx0 (neg_nonneg.2 hgneg.le)])
    rw [hA', hB'] at hi
    have h2 : x i * x i * gain u i x = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h3 | h3
    · rcases mul_eq_zero.1 h3 with h4 | h4 <;> linarith
    · linarith

/-- **Two-action Nash existence from Brouwer via Nash's own map** (Nash 1951's proof, in the
two-action parametrization): Brouwer (`brouwer_findim`) on `nashStep u` over the cube, then
`reflective_of_nashStep_eq` and Theorem 4.1. Independent of `exists_reflective_brouwer` and of the
clamp step (probe-checked); the Kakutani twin is `exists_isMixedNashEq`, the clamp-step twin
`exists_isMixedNashEq_brouwer`.
Source: Nash 1951; FTC 2015 §5 ("more elementary proof … from the existence of Nash equilibria");
mandate target 19, first option
Kind: C
Fidelity: variant: abstract, two actions
Hyps: (a) all (Brouwer only); (c) evaluation maps in place of oracle machines -/
theorem exists_isMixedNashEq_nashMap {N : Type*} [Fintype N] [DecidableEq N]
    (u : (N → Fin 2) → N → ℝ) :
    ∃ σ : MixedProfile (twoActionGame u), IsMixedNashEq (twoActionGame u) σ := by
  obtain ⟨x, hx, hfix⟩ := brouwer_findim (isCompact_univ_pi fun _ => isCompact_Icc)
    (convex_pi fun _ _ => convex_Icc 0 1)
    (Set.univ_pi_nonempty_iff.2 fun _ => Set.nonempty_Icc.2 zero_le_one)
    (nashStep u) (continuous_nashStep u).continuousOn (nashStep_mapsTo u)
  refine ⟨ofCube u x hx, ?_⟩
  rw [isMixedNashEq_iff_reflective, toCube_ofCube]
  exact reflective_of_nashStep_eq hx hfix

/-- **Theorem 5.1's existence route as an independent second proof**: Nash existence by Nash's own
map (`exists_isMixedNashEq_nashMap`), reflectivity by `gameR_nash_reflective`. Its proof term
contains neither the clamp step nor `exists_reflective_brouwer` nor any Kakutani constant
(probe-checked), so — unlike `exists_reflective_via_gameR_brouwer` — this is the paper's "more
elementary" second proof of polynomial reflective-oracle existence, resting on Nash existence proved
on its own.
Source: FTC 2015 Theorem 5.1 and §5's "more elementary proof"; mandate target 19, first option
Kind: C
Fidelity: variant: abstract (polynomial representation as hypothesis class, F9)
Hyps: (a) all (Brouwer only); `hd` is the paper's "bounded"; (c) evaluation maps in place of oracle
machines -/
theorem exists_reflective_via_gameR_nashMap [DecidableEq I] {K : Type*} [Fintype K] {B : ℕ}
    (c : I → K → ℝ) (d : I → K → I → ℕ) (hd : ∀ i k i', d i k i' ≤ B) (p : I → ℝ) :
    ∃ σ : MixedProfile (gameR (B := B) c d p), IsMixedNashEq (gameR c d p) σ ∧
      Reflective (polyEv c d) p (fun i => (σ (mainP i)).val 1) := by
  obtain ⟨σ, hσ⟩ := exists_isMixedNashEq_nashMap (gameRPayoff (B := B) c d p)
  exact ⟨σ, hσ, gameR_nash_reflective c d hd p hσ⟩

/-- **The `G_R`-based analogue of Theorem 2.1 (ii) that FTC §5 omits, Brouwer only**: for polynomial
evaluation maps, a finite query set `R ⊆ I` and prescribed answers `x₀ ∈ [0,1]^I`, the game `G_R`
built for the polynomials with `x₀` substituted off `R` (`substOff`, `restrictDeg`) has a mixed Nash
equilibrium (`exists_isMixedNashEq_brouwer`), and the vector its main players induce, extended by
`x₀` off `R`, lies in the cube, agrees with `x₀` off `R` and is reflective on `R`
(`gameR_nash_reflectiveOn`). This is §5's "the proof can be adapted to also show an analog of
Theorem 2.1 (ii)" carried out in the abstract polynomial setting, with no Kakutani anywhere; the
Kakutani-based twin is `exists_reflectiveOn_via_gameR`.
Source: FTC 2015 §5 ("The proof can be adapted to also show an analog of Theorem 2.1 (ii), but we
omit the details here"); mandate target 19; repair round 2 (audit round 2, fidelity B1)
Kind: C
Fidelity: variant: abstract (polynomial representation as hypothesis class, F9; finite `I`)
Hyps: (a) all (Brouwer only); `hd` is the paper's "bounded"; (c) evaluation maps in place of oracle
machines -/
theorem exists_reflectiveOn_via_gameR_brouwer [DecidableEq I] {K : Type*} [Fintype K] {B : ℕ}
    (R : Finset I) (c : I → K → ℝ) (d : I → K → I → ℕ) (hd : ∀ i k i', d i k i' ≤ B) (p : I → ℝ)
    {x₀ : I → ℝ} (hx₀ : x₀ ∈ cube I) :
    ∃ σ : MixedProfile (gameR (B := B) (substOff R x₀ c d) (restrictDeg R d) (fun i : R => p i)),
      IsMixedNashEq (gameR (substOff R x₀ c d) (restrictDeg R d) (fun i : R => p i)) σ ∧
      extendBy R x₀ (fun i : R => (σ (mainP i)).val 1) ∈ cube I ∧
      (∀ i ∉ R, extendBy R x₀ (fun i : R => (σ (mainP i)).val 1) i = x₀ i) ∧
      ReflectiveOn R (polyEv c d) p (extendBy R x₀ (fun i : R => (σ (mainP i)).val 1)) := by
  obtain ⟨σ, hσ⟩ := exists_isMixedNashEq_brouwer
    (gameRPayoff (B := B) (substOff R x₀ c d) (restrictDeg R d) (fun i : R => p i))
  exact ⟨σ, hσ, extendBy_mem_cube hx₀ (fun i _ => toCube_mem_cube σ (mainP i) (mem_univ _)),
    fun i hi => extendBy_apply_of_not_mem _ _ hi, gameR_nash_reflectiveOn R x₀ c d hd p hσ⟩

end Cleanroom.Fixpoint.FixOraclesCorresp
