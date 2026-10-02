import Cleanroom.Udt.UdtEndorsePolicy.Defs
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# T2: what "control endorsement generalizes the others" amounts to

Source: [[meaning-and-agency-reference]] §Control Endorsement, the line "Control endorsement
generalizes selection endorsement (since U can ignore its first argument), expectation
endorsement (since U can be some loss function), and belief endorsement (when that loss function
is a proper scoring rule)"; udt-rep-2-013.

* (a) selection ⟷ control with a world-blind utility: `control_of_selection` (kind T).
* (b) expectation ⟶ control with the Brier loss on a grid: `brier_control_of_expectation` (P);
  the converse **under the hypothesis that every realized conditional mean is a grid point**:
  `expectation_of_brier_control_of_grid` (P). Over the real line (`A = ℝ`, `g = id`, the post's
  natural reading) the grid hypothesis is discharged by the conditional mean itself and the two
  directions give an **exact equivalence** with no hypothesis: `brier_real_iff` (P, `exact`).
  On a *finite* grid the hypothesis is needed: `brier_grid_refuted` (N+) is a grid report that is
  Brier-control-endorsed by a tie yet not expectation-endorsed, and `grid_refutation_is_artifact`
  shows the same report, with the argmax taken over `ℝ`, is not control-endorsed at all — the
  tie is an artifact of the finite grid, not a gap in the post (repair round 1, audit r1 B1).
* (c) belief ⟷ expectation of the indicator: `beliefEndorses_iff_expectation_ind` (T).
* (d)(i) the translations are proper: control for `U` vs selection for the averaged `Ū`
  separate in both directions (`knowsMore_*`, `goodOnAverage_*`, N+). (d)(ii) is in
  `Reflection.lean`, (d)(iii) in `Defs.lean` (`beliefEndorses_of_condBeliefEndorses`,
  `controlEndorses_of_condControlEndorses`), its converse failure in `Transitive.lean`.
-/

namespace Cleanroom.Udt.UdtEndorsePolicy

open Cleanroom.Udt.UdtPolicyCalc Finset

noncomputable section

variable {Ω : Type} [Fintype Ω]

/-! ### (a) Selection endorsement is control endorsement with a world-blind utility -/

/-- **Selection endorsement is control endorsement for a utility that ignores the world**
(M&A: "since U can ignore its first argument"). On a positive class the conditional expectation of
`U a'` is `U a'` itself, so the two argmax conditions coincide.
Source: [[meaning-and-agency-reference]] §Control Endorsement | udt-rep-2-013
Kind: T
Fidelity: exact
Hyps: (a) none -/
theorem control_of_selection {A : Type} [DecidableEq A] (w : Ω → ℝ) (U : A → ℝ) (C : Ω → A) :
    SelectionEndorses w U C ↔ ControlEndorses w (fun _ a => U a) C := by
  unfold SelectionEndorses ControlEndorses
  refine forall_congr' fun a => forall_congr' fun ha => ?_
  have e : ∀ a', wsum w (fun _ => U a') (cls C a) = U a' * mass w (cls C a) := fun a' =>
    wsum_const_on fun _ _ => rfl
  simp only [e]
  unfold IsArgmax
  exact (forall_congr' fun a' => (mul_le_mul_iff_left₀ ha).symm)

/-! ### (b) Expectation endorsement and the Brier loss on a grid -/

/-- The **Brier (squared-error) utility** for a grid embedding `g : A → ℝ`: `U ω a = −(V ω − g a)²`.
Source: [[meaning-and-agency-reference]] §Control Endorsement ("U can be some loss function") | udt-rep-2-013
Kind: D
Fidelity: exact (Brier; other proper scoring rules are the stretch target)
Hyps: n/a -/
def brierU (V : Ω → ℝ) {A : Type} (g : A → ℝ) (ω : Ω) (a : A) : ℝ := -(V ω - g a) ^ 2

omit [Fintype Ω] in
/-- Supporting lemma: the weighted Brier sum on an event, expanded.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wsum_brier (w V : Ω → ℝ) (c : ℝ) (E : Finset Ω) :
    wsum w (fun ω => -(V ω - c) ^ 2) E =
      -(wsum w (fun ω => V ω ^ 2) E) + 2 * c * wsum w V E - c ^ 2 * mass w E := by
  simp only [wsum, mass, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun ω _ => by ring

/-- Supporting lemma: for an injective grid embedding, the class of the grid report at `g a` is the
class of the choice at `a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cls_comp_of_injective {A : Type} [DecidableEq A] {g : A → ℝ} (hg : Function.Injective g)
    (C : Ω → A) (a : A) : cls (fun ω => g (C ω)) (g a) = cls C a := by
  ext ω; simp [hg.eq_iff]

/-- **Expectation endorsement implies Brier control endorsement on the grid** (M&A: "expectation
endorsement (since U can be some loss function)"): if the grid report `g ∘ C` is
expectation-endorsed for `V`, then `C` is control-endorsed for `U ω a = −(V ω − g a)²`. On the
class of `a`, `E[−(V − g a')²] − E[−(V − g a)²] = −P(C = a)·(g a − g a')² ≤ 0`.
Source: [[meaning-and-agency-reference]] §Control Endorsement | udt-rep-2-013
Kind: P
Fidelity: exact (stated for any injective `g : A → ℝ`; `g = id : ℝ → ℝ` is the post's `A = ℝ` reading, `brier_real_iff`)
Hyps: (a) all -/
theorem brier_control_of_expectation {A : Type} [DecidableEq A] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) {V : Ω → ℝ} {g : A → ℝ} (hg : Function.Injective g) {C : Ω → A}
    (h : ExpectationEndorses w V (fun ω => g (C ω))) : ControlEndorses w (brierU V g) C := by
  intro a ha a'
  have hE := h (g a) (by rwa [cls_comp_of_injective hg])
  rw [cls_comp_of_injective hg] at hE
  unfold brierU
  dsimp only
  rw [wsum_brier, wsum_brier, hE]
  have hm : 0 ≤ mass w (cls C a) := mass_nonneg hw _
  nlinarith [mul_nonneg hm (sq_nonneg (g a - g a'))]

/-- **Brier control endorsement implies expectation endorsement when every realized conditional
mean is a grid point**: if `C` is control-endorsed for the Brier utility and on each realized
class the conditional mean `E[V | C = a]` equals some grid value `g a'`, then `g ∘ C` is
expectation-endorsed for `V`. (The Brier argmax over the grid is the grid point nearest the
conditional mean; when the mean is itself a grid point that argmax is unique, so it must be the
realized `g a`.)
Source: [[meaning-and-agency-reference]] §Control Endorsement | udt-rep-2-013
Kind: P
Fidelity: exact over `ℝ` (`hmean` is automatic for `g = id`, `brier_real_iff`); on a finite grid `hmean` is needed (`brier_grid_refuted`)
Hyps: (a) all; the grid hypothesis `hmean` is the theorem's content, not a squeeze (it names a grid point, not the conclusion) -/
theorem expectation_of_brier_control_of_grid {A : Type} [DecidableEq A] {w : Ω → ℝ}
    (hw : ∀ ω, 0 ≤ w ω) {V : Ω → ℝ} {g : A → ℝ} (hg : Function.Injective g) {C : Ω → A}
    (h : ControlEndorses w (brierU V g) C)
    (hmean : ∀ a, 0 < mass w (cls C a) → ∃ a', wsum w V (cls C a) = g a' * mass w (cls C a)) :
    ExpectationEndorses w V (fun ω => g (C ω)) := by
  intro x hx
  obtain ⟨ω, hωE, hω⟩ := exists_pos_of_mass_pos hw hx
  have hxω : g (C ω) = x := by simpa using hωE
  rw [← hxω, cls_comp_of_injective hg] at hx ⊢
  obtain ⟨a', ha'⟩ := hmean (C ω) hx
  have hle := h (C ω) hx a'
  unfold brierU at hle
  dsimp only at hle
  rw [wsum_brier, wsum_brier, ha'] at hle
  have : mass w (cls C (C ω)) * (g (C ω) - g a') ^ 2 ≤ 0 := by nlinarith
  have hsq : (g (C ω) - g a') ^ 2 = 0 := by
    rcases (sq_nonneg (g (C ω) - g a')).lt_or_eq with hpos | hz
    · exact absurd (mul_pos hx hpos) (not_lt.2 this)
    · exact hz.symm
  have : g (C ω) = g a' := by nlinarith [sq_nonneg (g (C ω) - g a')]
  rw [ha', this]

/-- **Over the real line, expectation endorsement is exactly Brier control endorsement** (M&A:
"expectation endorsement (since U can be some loss function)", read with `A = ℝ` and
`U ω x = −(V ω − x)²`, udt-rep-2-013's first reading): `Q` is expectation-endorsed for `V` iff `Q`
is control-endorsed for the Brier utility, with no hypothesis. Both directions are the grid
theorems at `g = id`; the grid hypothesis of the converse is discharged by the conditional mean
`E[V | Q = x]` itself, which is a point of `ℝ`. The argmax is over all of `ℝ` (set-valued; here it
is in fact unique, the class's conditional mean).
Source: [[meaning-and-agency-reference]] §Control Endorsement | udt-rep-2-013 (T2(b)); audit r1 B1
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem brier_real_iff {w : Ω → ℝ} (hw : ∀ ω, 0 ≤ w ω) (V Q : Ω → ℝ) :
    ExpectationEndorses w V Q ↔ ControlEndorses w (brierU V (id : ℝ → ℝ)) Q := by
  constructor
  · intro h
    exact brier_control_of_expectation hw (g := (id : ℝ → ℝ)) Function.injective_id (C := Q) h
  · intro h
    exact expectation_of_brier_control_of_grid hw (g := (id : ℝ → ℝ)) Function.injective_id h
      (fun a ha => ⟨wsum w V (cls Q a) / mass w (cls Q a), by
        show _ = wsum w V (cls Q a) / mass w (cls Q a) * mass w (cls Q a)
        rw [div_mul_cancel₀ _ ha.ne']⟩)

/-! #### On a finite grid the converse needs the grid hypothesis (and the failure is the grid's) -/

/-- The grid `{0, 1}` as an injective embedding `Fin 2 → ℝ`.
Source: mandate T2(b) (refutation witness)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def grid01 : Fin 2 → ℝ := ![0, 1]

/-- The uniform weight on `Fin 4`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def unif4w : Fin 4 → ℝ := fun _ => 1 / 4

/-- The event `X = {0, 2}` on `Fin 4`.
Source: mandate T2(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def X02 : Finset (Fin 4) := {0, 2}

/-- The non-constant report `C = (1, 1, 0, 0)` on `Fin 4`: each class holds one point of `X` and
one point outside it, so `P(X | C = a) = 1/2` on both classes.
Source: mandate T2(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def C1100 : Fin 4 → Fin 2 := ![1, 1, 0, 0]

/-- Supporting lemma `grid01_injective`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem grid01_injective : Function.Injective grid01 := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp [grid01] at h ⊢

/-- **On a finite grid, Brier control endorsement does not imply expectation endorsement without
the grid hypothesis** (N+, the witness that `expectation_of_brier_control_of_grid`'s `hmean` is
needed for finite `A`): on the uniform `Fin 4` with `V = 1_{\{0,2\}}`, grid `{0, 1}` and the
non-constant report `C = (1, 1, 0, 0)`, both classes have `P(X | C = a) = 1/2`, so the two grid
points tie under the Brier loss (each realized value is an argmax: control-endorsed on the grid),
while `E[V | g ∘ C = 1] = 1/2 ≠ 1` (not expectation-endorsed). This does **not** refute M&A's
sentence: over `ℝ` the equivalence is exact (`brier_real_iff`), and the same report with the
argmax over `ℝ` is not control-endorsed at all (`grid_refutation_is_artifact`) — the tie exists
only because `1/2` is not an available action. What it shows is that a *finite-action* encoding
of "control endorsement with a loss function" must put the conditional means on the grid.
Source: udt-rep-2-013 (T2(b), the finite-grid variant) | audit r1 B1
Kind: N+
Fidelity: n/a (non-constant report, both classes exercised; a fact about the finite-grid variant, not about the post's `A = ℝ` claim)
Hyps: none -/
theorem brier_grid_refuted :
    ControlEndorses unif4w (brierU (ind X02) grid01) C1100 ∧
      ¬ ExpectationEndorses unif4w (ind X02) (fun ω => grid01 (C1100 ω)) := by
  constructor
  · rw [controlEndorses_iff_forall_pt (fun _ => by norm_num [unif4w])]
    intro ω _ a'
    fin_cases ω <;> fin_cases a' <;>
    · simp +decide only [wsum_event_eq, Fin.sum_univ_four, brierU, C1100, grid01, unif4w, ind, X02,
        Fin.isValue, Finset.mem_insert, Finset.mem_singleton]
      norm_num
  · intro h
    have := h 1 (by
      rw [mass_event_eq, Fin.sum_univ_four]
      simp +decide only [C1100, grid01, unif4w, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three, Fin.isValue]
      norm_num)
    rw [wsum_event_eq, mass_event_eq, Fin.sum_univ_four, Fin.sum_univ_four] at this
    simp +decide only [C1100, grid01, unif4w, ind, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Fin.isValue] at this
    norm_num at this

/-- **The grid refutation is an artifact of the finite grid** (the STANDARDS §3 encoding check):
the report of `brier_grid_refuted`, read as a real-valued report `grid01 ∘ C1100` with the Brier
argmax taken over all of `ℝ`, is *not* control-endorsed — the tie between `0` and `1` disappears
once the action `1/2` (the conditional mean) is available. So the finite-grid failure is the
grid's, not the post's.
Source: udt-rep-2-013 (T2(b)) | audit r1 B1
Kind: N+ (component: the encoding check for `brier_grid_refuted`)
Fidelity: n/a
Hyps: none -/
theorem grid_refutation_is_artifact :
    ¬ ControlEndorses unif4w (brierU (ind X02) (id : ℝ → ℝ)) (fun ω => grid01 (C1100 ω)) :=
  fun h => brier_grid_refuted.2 ((brier_real_iff (fun _ => by norm_num [unif4w]) _ _).2 h)

/-! ### (c) Belief endorsement is expectation endorsement of the indicator -/

/-- **Belief endorsement is expectation endorsement of the indicator** (M&A: "we can take V to be
the indicator variable for X"): `P(X ∩ {Q = p}) = ∑_{Q = p} w · 1_X`.
Source: [[meaning-and-agency-reference]] §Expectation Endorsement | udt-rep-2-013
Kind: T
Fidelity: exact
Hyps: (a) none -/
theorem beliefEndorses_iff_expectation_ind [DecidableEq Ω] (w : Ω → ℝ) (X : Finset Ω)
    (Q : Ω → ℝ) : BeliefEndorses w X Q ↔ ExpectationEndorses w (ind X) Q := by
  unfold BeliefEndorses ExpectationEndorses
  simp only [mass_inter_eq_wsum_ind]

/-! ### (d)(i) The control/selection translation is proper: two separations -/

/-- The **averaged utility** `Ū a := E[U(·, a)]` (the pure utility a selection reading of a control
problem would use).
Source: mandate T2(d)(i)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def avgU (w : Ω → ℝ) {A : Type} (U : Ω → A → ℝ) (a : A) : ℝ := wsum w (fun ω => U ω a) univ

/-- Uniform weight on `Fin 2`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def unif2w : Fin 2 → ℝ := fun _ => 1 / 2

/-- **"The agent knows more than the average"**: `U ω a = 1` if `ω = a = 0`, `3` if
`ω = a = 1`, else `0`. The identity choice `C = id` is control-endorsed (it matches the world) but
not selection-endorsed for `Ū = (1/2, 3/2)`: the realized action `0` is not an argmax of `Ū`.
Source: mandate T2(d)(i)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def knowsMoreU : Fin 2 → Fin 2 → ℝ := ![![1, 0], ![0, 3]]

/-- **Control endorsement for `U` does not imply selection endorsement for the averaged `Ū`**
(N+): `id` is control-endorsed for `knowsMoreU`, but `Ū = (1/2, 3/2)` has the unique argmax `1`,
while `0` is realized.
Source: [[meaning-and-agency-reference]] §Control Endorsement (the "generalizes" line) | udt-rep-2-013 (T2(d)(i))
Kind: N+
Fidelity: n/a (non-constant choice; `U` non-constant in both arguments)
Hyps: none -/
theorem knowsMore_control_not_selection :
    ControlEndorses unif2w knowsMoreU id ∧ ¬ SelectionEndorses unif2w (avgU unif2w knowsMoreU) id := by
  constructor
  · rw [controlEndorses_iff_forall_pt (fun _ => by norm_num [unif2w])]
    intro ω _ a'
    fin_cases ω <;> fin_cases a' <;>
    · simp only [wsum_event_eq, Fin.sum_univ_two, knowsMoreU, unif2w, id, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.isValue]
      norm_num
  · intro h
    have := h 0 (by
      rw [mass_event_eq, Fin.sum_univ_two]
      simp only [unif2w, id, Fin.isValue]
      norm_num) 1
    simp only [avgU, wsum, Fin.sum_univ_two, knowsMoreU, unif2w, Matrix.cons_val_zero,
      Matrix.cons_val_one, Fin.isValue] at this
    norm_num at this

/-- **"Good on average, bad where taken"**: three actions, `U 0 = (0, 4, 1)`, `U 1 = (4, 0, 1)`;
`Ū = (2, 2, 1)`. The choice `C ω = ω` (as an element of `Fin 3`) is selection-endorsed for `Ū`
(both realized actions are argmaxes of `Ū`, strictly beating action `2`) but not
control-endorsed for `U` (in world `0`, action `0` scores `0` while action `1` scores `4`).
Source: mandate T2(d)(i)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def goodOnAvgU : Fin 2 → Fin 3 → ℝ := ![![0, 4, 1], ![4, 0, 1]]

/-- The choice `0 ↦ 0`, `1 ↦ 1` into `Fin 3`.
Source: mandate T2(d)(i)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def castChoice : Fin 2 → Fin 3 := ![0, 1]

/-- **Selection endorsement for the averaged `Ū` does not imply control endorsement for `U`**
(N+): both realized actions of `castChoice` are argmaxes of `Ū = (2, 2, 1)`, but in world `0` the
realized action `0` is beaten by action `1` under `U`.
Source: [[meaning-and-agency-reference]] §Control Endorsement (the "generalizes" line) | udt-rep-2-013 (T2(d)(i))
Kind: N+
Fidelity: n/a (non-constant choice; `Ū` has a strictly dominated action, so the selection clause has content)
Hyps: none -/
theorem goodOnAverage_selection_not_control :
    SelectionEndorses unif2w (avgU unif2w goodOnAvgU) castChoice ∧
      ¬ ControlEndorses unif2w goodOnAvgU castChoice := by
  constructor
  · intro a ha a'
    fin_cases a
    · fin_cases a' <;>
      · simp only [avgU, wsum, Fin.sum_univ_two, goodOnAvgU, unif2w, Matrix.cons_val_zero,
          Matrix.cons_val_one, Fin.isValue]
        norm_num
    · fin_cases a' <;>
      · simp only [avgU, wsum, Fin.sum_univ_two, goodOnAvgU, unif2w, Matrix.cons_val_zero,
          Matrix.cons_val_one, Fin.isValue]
        norm_num
    · exfalso
      rw [mass_event_eq, Fin.sum_univ_two] at ha
      simp +decide at ha
  · intro h
    have := h 0 (by
      rw [mass_event_eq, Fin.sum_univ_two]
      simp only [castChoice, unif2w, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
      norm_num) 1
    simp only [wsum_event_eq, Fin.sum_univ_two, goodOnAvgU, castChoice, unif2w,
      Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue] at this
    norm_num at this

/-! ### T12 (stretch, finite reconnaissance): "capable agents have beliefs", constant-action reading -/

/-- Two worlds, three actions: the matching action pays `1`, the mismatch `0`, and the safe action
`2` pays `9/10` in both worlds.
Source: mandate T12 (finite reconnaissance of M&A Q4; udt-rep-2-017)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def safeU : Fin 2 → Fin 3 → ℝ := ![![1, 0, 9 / 10], ![0, 1, 9 / 10]]

/-- **The constant-action reading of "capable agents have beliefs" is false** (N+): the choice
`castChoice` (`0 ↦ 0`, `1 ↦ 1`: match the world) is control-endorsed under the uniform prior, yet no single belief
`P₂ = (q, 1 − q)` makes both realized actions argmaxes of `a' ↦ E_{P₂}[U(·, a')] = (q, 1 − q, 9/10)`:
the safe action strictly beats whichever of `0`, `1` has expected value `≤ 1/2`. (i) The refuted
sentence: udt-rep-2-017's candidate form "endorsed choices are rationalizable by *some* belief"
(constant-action reading, ATTRIBUTION-UNVETTED: M&A Q4 only asks the question); (ii) reading: one
`P₂` for all realized actions, set-valued argmax; (iii) survivor: the per-value policy reading
`P₂ := P₁(· | C = a)` (definitional) — and with only two actions the constant-action reading holds
by an intermediate-value argument, so a third, unrealized action is what breaks it.
Source: [[meaning-and-agency-reference]] Q4 | udt-rep-2-017 (mandate T12)
Kind: N+
Fidelity: n/a (finite reconnaissance; the representation-theorem question proper stays open)
Hyps: none -/
theorem capable_beliefs_constant_refuted :
    ControlEndorses unif2w safeU castChoice ∧
      ¬ ∃ q : ℝ, 0 ≤ q ∧ q ≤ 1 ∧
        IsArgmax (fun a' => q * safeU 0 a' + (1 - q) * safeU 1 a') 0 ∧
        IsArgmax (fun a' => q * safeU 0 a' + (1 - q) * safeU 1 a') 1 := by
  constructor
  · rw [controlEndorses_iff_forall_pt (fun _ => by norm_num [unif2w])]
    intro ω _ a'
    fin_cases ω <;> fin_cases a' <;>
    · simp only [wsum_event_eq, Fin.sum_univ_two, safeU, unif2w, castChoice, Matrix.cons_val_zero,
        Matrix.cons_val_one, Fin.isValue]
      norm_num
  · rintro ⟨q, _, _, h0, h1⟩
    have e0 := h0 2
    have e1 := h1 2
    simp only [safeU, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.isValue] at e0 e1
    linarith

end

end Cleanroom.Udt.UdtEndorsePolicy
