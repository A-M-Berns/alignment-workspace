import Cleanroom.Corrigibility.CorrPowerChannel.Orbit
import Mathlib.Data.Fin.VecNotation

/-!
# `corr-power-channel` — T7(b): Corollary 6.14 in the five-state MDP, as an exact orbit count

The five-state rewardless MDP of `check_turner.py` (states `s = 0`, `k = 1`, `c1 = 2`, `c2 = 3`,
`z = 4`; `s →keep→ k → z` (**deterministic landing, `p = 1`**), `s →erode→ c1`, `c1 ⇄ c2` each with
a stay action, `z` terminal), its eight stationary deterministic policies `(keep?, c1 stays?,
c2 stays?)`, their visit distributions (Def. 3.3) as closed forms in `γ`, the recurrent state
distributions (Def. 6.10) **written down** as the `γ → 1` limits — `e_z`, `e_{c1}`, `e_{c2}`,
`(e_{c1} + e_{c2})/2` — with the identity `(1 − γ)·visit = rsd + (1 − γ)·corr` (`rsd_identity`)
exhibiting the limit, and average-optimality (Def. 6.11) as "the chosen RSD maximizes `dᵀR` over
`RSD(s)`".

* `keep_avgOptimal_iff`: an average-optimal policy ends in `z` iff `R z ≥ max (R c1) (R c2)`;
  `erode_avgOptimal_iff`: one ends in `{c1, c2}` iff `max (R c1) (R c2) ≥ R z`.
* **Cor. 6.14 for `s_x = z`, exact** (`cor614_orbit_count`): for `R` with distinct values, over
  the orbit `{R ∘ σ | σ ∈ Perm (Fin 5)}`, `#{erode average-optimal} ≥ 2 · #{keep average-optimal}`
  — the three cells "`z`/`c1`/`c2` strictly best among `{c1, c2, z}`" have equal size by the
  symmetry of `Orbit.lean`, and the last two lie in the erode set. This is the honest form of
  "shutdown-avoidance is power-seeking": a count, never a probability.
* **The exact count under distinct rewards** (`cor614_orbit_count_exact`, repair round 2): keep
  is average-optimal on exactly `40` and erode on exactly `80` of the `120` permutations
  (`card_keepOptPerms`, `card_erodeOptPerms`) — the three cells cover the group under injectivity
  (`card_strictBestPerms_mul_of_injective`, `Orbit.lean`), so the keep cell is exactly one third
  of the orbit. Injectivity on all of `Fin 5` is needed: `R = (0, 0, 0, 1, 2)` has three distinct
  terminal values and keep cell `48`.
* **Permutations versus Turner's orbit.** Definition 6.5 counts the orbit `{R ∘ σ}` as a *set* of
  reward vectors; every count here is over `Perm (Fin 5)`. For injective `R` the orbit map
  `σ ↦ R ∘ σ` is injective and the two agree; for every `R` each orbit element corresponds to
  exactly `|Stab(R)|` permutations and membership in each side depends only on `R ∘ σ`, so the
  tie-robust inequality is Turner's scaled by the same positive constant on both sides.

**Not claimed (finding):** the source's `p = 9/10`, `γ < 1` Monte Carlo is not formalized, and
Prop. 6.9's similarity hypothesis fails on the stochastic keep branch (its visit distributions mix
`z` with `c1`, so no involution copies `F(s | keep)` into `F(s | erode)`).

Sources: `channel-scratch/check_turner.py` (37 lines); channel-final.md S10 (l. 83); Turner
et al. 2021 Def. 3.3, 6.10, 6.11, Thm 6.13, Cor 6.14 (l. 88, 228–254); corr-wf14b-031.
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

open Finset

noncomputable section

/-- A stationary deterministic policy: `keep` at `s`? `c1` stays? `c2` stays?
Source: `check_turner.py`; Turner et al. 2021 Def. 3.3 (`Π := A^S`)
Kind: D
Fidelity: exact (the eight policies of the five-state MDP at `p = 1`; `k` and `z` have one action) -/
abbrev Pol : Type := Bool × Bool × Bool

/-- **Visit distributions (Def. 3.3) at `p = 1`**, as closed forms in `γ ∈ [0, 1)`: keep gives
`e_s + γ e_k + γ²/(1−γ) e_z`; erode-stay gives `e_s + γ/(1−γ) e_{c1}`; erode-move-stay gives
`e_s + γ e_{c1} + γ²/(1−γ) e_{c2}`; the cycle gives `e_s + γ/(1−γ²) e_{c1} + γ²/(1−γ²) e_{c2}`.
Source: Turner et al. 2021 Def. 3.3 (l. 88); `check_turner.py` (transitions)
Kind: D
Fidelity: exact (`p = 1`; written as closed forms, the geometric sums evaluated by hand) -/
def visit (π : Pol) (γ : ℝ) : Fin 5 → ℝ :=
  match π with
  | (true, _, _) => ![1, γ, 0, 0, γ ^ 2 / (1 - γ)]
  | (false, true, _) => ![1, 0, γ / (1 - γ), 0, 0]
  | (false, false, true) => ![1, 0, γ, γ ^ 2 / (1 - γ), 0]
  | (false, false, false) => ![1, 0, γ / (1 - γ ^ 2), γ ^ 2 / (1 - γ ^ 2), 0]

/-- **Recurrent state distributions (Def. 6.10)**, written down as the `γ → 1` limits of
`(1 − γ)·visit`: `e_z`, `e_{c1}`, `e_{c2}`, `(e_{c1} + e_{c2})/2`.
Source: Turner et al. 2021 Def. 6.10 (l. 228); `check_turner.py`
Kind: D
Fidelity: exact (`p = 1`; the limit is exhibited by `rsd_identity`) -/
def rsd (π : Pol) : Fin 5 → ℝ :=
  match π with
  | (true, _, _) => ![0, 0, 0, 0, 1]
  | (false, true, _) => ![0, 0, 1, 0, 0]
  | (false, false, true) => ![0, 0, 0, 1, 0]
  | (false, false, false) => ![0, 0, 1 / 2, 1 / 2, 0]

/-- The `O(1 − γ)` correction `corr π γ` with `(1 − γ)·visit π γ = rsd π + (1 − γ)·corr π γ`.
Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def corr (π : Pol) (γ : ℝ) : Fin 5 → ℝ :=
  match π with
  | (true, _, _) => ![1, γ, 0, 0, -(1 + γ)]
  | (false, true, _) => ![1, 0, -1, 0, 0]
  | (false, false, true) => ![1, 0, γ, -(1 + γ), 0]
  | (false, false, false) => ![1, 0, -(1 / (2 * (1 + γ))), -((2 * γ + 1) / (2 * (1 + γ))), 0]

/-- **The RSD is the `γ → 1` limit, exhibited**: `(1 − γ)·visit π γ x = rsd π x + (1 − γ)·corr π γ x`
for `γ ∈ [0, 1)`, with `corr` the explicit correction (bounded on `[0, 1)`: its entries are
`1`, `γ`, `−1`, `−(1 + γ)` and ratios with denominator `2(1 + γ) ≥ 2`); so `(1 − γ)·visit → rsd` as
`γ → 1`.
Source: Turner et al. 2021 Def. 6.10 (l. 228, "`lim_{γ→1} (1 − γ) f^{π,s}(γ)`")
Kind: L
Fidelity: exact (algebraic identity; the limit statement is read off it)
Hyps: (a) `0 ≤ γ < 1` -/
theorem rsd_identity (π : Pol) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ∀ x, (1 - γ) * visit π γ x = rsd π x + (1 - γ) * corr π γ x := by
  have h1 : (1 - γ) ≠ 0 := by linarith
  have h2 : (1 - γ ^ 2) ≠ 0 := by nlinarith
  have h3 : (1 + γ) ≠ 0 := by linarith
  have h4 : (2 * (1 + γ)) ≠ 0 := by linarith
  rcases π with ⟨k, a, b⟩
  cases k <;> cases a <;> cases b <;>
    simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true, visit, rsd, corr,
      Matrix.cons_val_zero, Matrix.cons_val_succ] <;>
    (repeat' apply And.intro) <;> (try field_simp) <;> ring

/-- `dᵀR` for a state distribution `d`. Source: Turner et al. 2021 Def. 6.11. Kind: D.
Fidelity: exact -/
def dot (d R : Fin 5 → ℝ) : ℝ := ∑ x, d x * R x

/-- **Average-optimality (Def. 6.11) at `s`**: the policy's RSD maximizes `dᵀR` over `RSD(s)`
(the four RSDs of the eight policies). Def. 6.11 asks for optimality at *all* states; the
existential forms used here (`∃ π, π.1 = keep ∧ AvgOptimal R π`) coincide with the all-states
ones in this MDP, because the `c1`/`c2` stay-or-move bits are independent of the `s` bit and `k`,
`z` have one action, so a start-state-optimal policy can always be completed to an all-states-optimal
one with the same first bit (argument only; not formalized — repair round 1, fidelity N3).
Source: Turner et al. 2021 Def. 6.11 (l. 228)
Kind: D
Fidelity: variant: at the start state `s` only (where the keep/erode fork is); the existential
forms are equivalent to the all-states ones here, by the argument above -/
def AvgOptimal (R : Fin 5 → ℝ) (π : Pol) : Prop := ∀ π' : Pol, dot (rsd π') R ≤ dot (rsd π) R

/-- `dᵀR` of the four RSDs. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem dot_rsd (R : Fin 5 → ℝ) (π : Pol) :
    dot (rsd π) R = match π with
      | (true, _, _) => R 4
      | (false, true, _) => R 2
      | (false, false, true) => R 3
      | (false, false, false) => (R 2 + R 3) / 2 := by
  rcases π with ⟨k, a, b⟩
  cases k <;> cases a <;> cases b <;> simp [dot, rsd, Fin.sum_univ_succ] <;> ring

/-- **An average-optimal policy ends in `z` iff `R z ≥ max (R c1) (R c2)`.**
Source: Turner et al. 2021 Cor. 6.14 (l. 254); `check_turner.py` ("keep is optimal only when the
terminal's reward is high enough")
Kind: P
Fidelity: exact (`p = 1`, `γ = 1`)
Hyps: (a) none -/
theorem keep_avgOptimal_iff (R : Fin 5 → ℝ) :
    (∃ π : Pol, π.1 = true ∧ AvgOptimal R π) ↔ max (R 2) (R 3) ≤ R 4 := by
  constructor
  · rintro ⟨π, hk, hopt⟩
    rcases π with ⟨k, a, b⟩
    simp only at hk
    subst hk
    have h2 := hopt (false, true, true)
    have h3 := hopt (false, false, true)
    rw [dot_rsd, dot_rsd] at h2 h3
    simp only at h2 h3
    exact max_le h2 h3
  · intro h
    refine ⟨(true, true, true), rfl, fun π' => ?_⟩
    rw [dot_rsd, dot_rsd]
    rcases π' with ⟨k, a, b⟩
    cases k <;> cases a <;> cases b <;> simp only
    · linarith [le_max_left (R 2) (R 3), le_max_right (R 2) (R 3)]
    · linarith [le_max_left (R 2) (R 3), le_max_right (R 2) (R 3)]
    · linarith [le_max_left (R 2) (R 3), le_max_right (R 2) (R 3)]
    · linarith [le_max_left (R 2) (R 3), le_max_right (R 2) (R 3)]
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl
    · exact le_rfl

/-- **An average-optimal policy ends in `{c1, c2}` iff `max (R c1) (R c2) ≥ R z`.**
Source: Turner et al. 2021 Cor. 6.14 (l. 254); `check_turner.py`
Kind: P
Fidelity: exact (`p = 1`, `γ = 1`)
Hyps: (a) none -/
theorem erode_avgOptimal_iff (R : Fin 5 → ℝ) :
    (∃ π : Pol, π.1 = false ∧ AvgOptimal R π) ↔ R 4 ≤ max (R 2) (R 3) := by
  constructor
  · rintro ⟨π, hk, hopt⟩
    have h := hopt (true, true, true)
    rw [dot_rsd, dot_rsd] at h
    rcases π with ⟨k, a, b⟩
    simp only at hk
    subst hk
    cases a <;> cases b <;> simp only at h
    · linarith [le_max_left (R 2) (R 3), le_max_right (R 2) (R 3)]
    · exact le_trans h (le_max_right _ _)
    · exact le_trans h (le_max_left _ _)
    · exact le_trans h (le_max_left _ _)
  · intro h
    rcases le_total (R 2) (R 3) with h23 | h32
    · refine ⟨(false, false, true), rfl, fun π' => ?_⟩
      rw [dot_rsd, dot_rsd]
      rw [max_eq_right h23] at h
      rcases π' with ⟨k, a, b⟩
      cases k <;> cases a <;> cases b <;> simp only <;> linarith
    · refine ⟨(false, true, true), rfl, fun π' => ?_⟩
      rw [dot_rsd, dot_rsd]
      rw [max_eq_left h32] at h
      rcases π' with ⟨k, a, b⟩
      cases k <;> cases a <;> cases b <;> simp only <;> linarith

open Classical in
/-- The permutations of the orbit for which some keep policy is average-optimal.
Source: Turner et al. 2021 Def. 6.5; Cor. 6.14. Kind: D. Fidelity: exact -/
def keepOptPerms (R : Fin 5 → ℝ) : Finset (Equiv.Perm (Fin 5)) :=
  univ.filter (fun σ => ∃ π : Pol, π.1 = true ∧ AvgOptimal (R ∘ σ) π)

open Classical in
/-- The permutations of the orbit for which some erode policy is average-optimal.
Source: Turner et al. 2021 Def. 6.5; Cor. 6.14. Kind: D. Fidelity: exact -/
def erodeOptPerms (R : Fin 5 → ℝ) : Finset (Equiv.Perm (Fin 5)) :=
  univ.filter (fun σ => ∃ π : Pol, π.1 = false ∧ AvgOptimal (R ∘ σ) π)

open Classical in
/-- Under distinct rewards, keep is average-optimal iff `z` is strictly best among `{c1, c2, z}`.
Source: none: infrastructure (ties excluded by injectivity). Kind: L. Fidelity: n/a -/
theorem keepOptPerms_eq (R : Fin 5 → ℝ) (hR : Function.Injective R) :
    keepOptPerms R = strictBestPerms R {2, 3, 4} 4 := by
  ext σ
  rw [keepOptPerms, mem_filter, mem_strictBestPerms, keep_avgOptimal_iff]
  simp only [mem_univ, true_and]
  constructor
  · intro h
    refine ⟨by simp, fun y hy hne => ?_⟩
    simp only [mem_insert, mem_singleton] at hy
    have hRne : (R ∘ σ) y ≠ (R ∘ σ) 4 := fun hc => hne (σ.injective (hR hc))
    rcases hy with rfl | rfl | rfl
    · exact lt_of_le_of_ne (le_trans (le_max_left _ _) h) hRne
    · exact lt_of_le_of_ne (le_trans (le_max_right _ _) h) hRne
    · exact absurd rfl hne
  · rintro ⟨_, h⟩
    exact max_le (h 2 (by simp) (by decide)).le (h 3 (by simp) (by decide)).le

open Classical in
/-- The cells "`c1` strictly best" and "`c2` strictly best" among `{c1, c2, z}` lie in the erode
set. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem strictBest_subset_erodeOpt (R : Fin 5 → ℝ) :
    strictBestPerms R {2, 3, 4} 2 ∪ strictBestPerms R {2, 3, 4} 3 ⊆ erodeOptPerms R := by
  intro σ hσ
  rw [erodeOptPerms, mem_filter]
  refine ⟨mem_univ _, ?_⟩
  rw [erode_avgOptimal_iff]
  rw [mem_union, mem_strictBestPerms, mem_strictBestPerms] at hσ
  rcases hσ with h | h
  · exact le_trans (h.2 4 (by simp) (by decide)).le (le_max_left _ _)
  · exact le_trans (h.2 4 (by simp) (by decide)).le (le_max_right _ _)

open Classical in
/-- **Corollary 6.14 for `s_x = z`, exact (load-bearing 3)**: for a reward vector with distinct
values, over its orbit under `Perm (Fin 5)`, `#{σ | some erode policy is average-optimal for
R ∘ σ} ≥ 2 · #{σ | some keep policy is average-optimal for R ∘ σ}`. Turner's `≥_most`
(Definition 6.5) is the `≥ 1·` form; the factor `2` is the scaling law with three candidate
terminal cells.
Source: Turner et al. 2021 Cor. 6.14 (l. 254, "average-optimal policies tend not to end up in any
given 1-cycle"); Thm 6.13 (l. 254); `check_turner.py`; channel-final.md S10 (l. 83)
Kind: P
Fidelity: stronger: factor `2` under distinct rewards (Turner's `≥_most` is factor `1` and
tie-robust; the tie-robust factor-`2` form for every `R` is `cor614_orbit_count_strict`); `p = 1`,
`γ = 1`, for the visit vectors of record (hand-evaluated closed forms, `(c)`); an orbit count, not
a probability
Hyps: (a) `R` injective on all of `Fin 5` — needed, not only three distinct values: the orbit moves
every value through the terminal positions, and with `R = (0, 0, 0, 1, 2)` (three distinct values at
`2, 3, 4`) the count reads `2·48 ≤ 84`, false; (c) the visit distributions are hand-evaluated -/
theorem cor614_orbit_count (R : Fin 5 → ℝ) (hR : Function.Injective R) :
    2 * (keepOptPerms R).card ≤ (erodeOptPerms R).card := by
  have h24 : (2 : Fin 5) ∈ ({2, 3, 4} : Finset (Fin 5)) := by simp
  have h34 : (3 : Fin 5) ∈ ({2, 3, 4} : Finset (Fin 5)) := by simp
  have h44 : (4 : Fin 5) ∈ ({2, 3, 4} : Finset (Fin 5)) := by simp
  have hc2 := card_strictBestPerms_eq R h44 h24
  have hc3 := card_strictBestPerms_eq R h44 h34
  have hdisj := strictBestPerms_disjoint R ({2, 3, 4} : Finset (Fin 5)) (show (2 : Fin 5) ≠ 3 by decide)
  rw [keepOptPerms_eq R hR]
  calc 2 * (strictBestPerms R {2, 3, 4} 4).card
      = (strictBestPerms R {2, 3, 4} 2).card + (strictBestPerms R {2, 3, 4} 3).card := by
        rw [← hc2, ← hc3]; ring
    _ = (strictBestPerms R {2, 3, 4} 2 ∪ strictBestPerms R {2, 3, 4} 3).card :=
        (card_union_of_disjoint hdisj).symm
    _ ≤ (erodeOptPerms R).card := card_le_card (strictBest_subset_erodeOpt R)

/-! ### The tie-robust form (repair round 1, adversarial N4) -/

open Classical in
/-- The permutations for which keep is average-optimal and erode is not (`max(R c1, R c2) < R z`).
Source: Turner et al. 2021 Def. 6.5 (the `>` side of `≥_most`). Kind: D. Fidelity: exact -/
def keepOnlyPerms (R : Fin 5 → ℝ) : Finset (Equiv.Perm (Fin 5)) :=
  univ.filter (fun σ => (∃ π : Pol, π.1 = true ∧ AvgOptimal (R ∘ σ) π) ∧
    ¬ ∃ π : Pol, π.1 = false ∧ AvgOptimal (R ∘ σ) π)

open Classical in
/-- The permutations for which erode is average-optimal and keep is not (`R z < max(R c1, R c2)`).
Source: Turner et al. 2021 Def. 6.5 (the `<` side of `≥_most`). Kind: D. Fidelity: exact -/
def erodeOnlyPerms (R : Fin 5 → ℝ) : Finset (Equiv.Perm (Fin 5)) :=
  univ.filter (fun σ => (∃ π : Pol, π.1 = false ∧ AvgOptimal (R ∘ σ) π) ∧
    ¬ ∃ π : Pol, π.1 = true ∧ AvgOptimal (R ∘ σ) π)

open Classical in
/-- Keep-only is "`z` strictly best among `{c1, c2, z}`", for every `R` (no tie hypothesis).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem keepOnlyPerms_eq (R : Fin 5 → ℝ) : keepOnlyPerms R = strictBestPerms R {2, 3, 4} 4 := by
  ext σ
  rw [keepOnlyPerms, mem_filter, mem_strictBestPerms, keep_avgOptimal_iff, erode_avgOptimal_iff,
    not_le]
  simp only [mem_univ, true_and]
  constructor
  · rintro ⟨_, h⟩
    refine ⟨by simp, fun y hy hne => ?_⟩
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact (max_lt_iff.1 h).1
    · exact (max_lt_iff.1 h).2
    · exact absurd rfl hne
  · rintro ⟨_, h⟩
    have h2 := h 2 (by simp) (by decide)
    have h3 := h 3 (by simp) (by decide)
    exact ⟨max_le h2.le h3.le, max_lt h2 h3⟩

open Classical in
/-- The cells "`c1` strictly best" and "`c2` strictly best" lie in the erode-only set, for every
`R`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem strictBest_subset_erodeOnly (R : Fin 5 → ℝ) :
    strictBestPerms R {2, 3, 4} 2 ∪ strictBestPerms R {2, 3, 4} 3 ⊆ erodeOnlyPerms R := by
  intro σ hσ
  rw [erodeOnlyPerms, mem_filter]
  refine ⟨mem_univ _, ?_⟩
  rw [erode_avgOptimal_iff, keep_avgOptimal_iff, not_le]
  rw [mem_union, mem_strictBestPerms, mem_strictBestPerms] at hσ
  rcases hσ with h | h
  · have h4 := h.2 4 (by simp) (by decide)
    exact ⟨le_trans h4.le (le_max_left _ _), lt_of_lt_of_le h4 (le_max_left _ _)⟩
  · have h4 := h.2 4 (by simp) (by decide)
    exact ⟨le_trans h4.le (le_max_right _ _), lt_of_lt_of_le h4 (le_max_right _ _)⟩

open Classical in
/-- **Corollary 6.14 for `s_x = z`, tie-robust and with the factor `2`, for every reward vector**:
`#{σ | erode is average-optimal and keep is not} ≥ 2·#{σ | keep is average-optimal and erode is
not}`. This is Turner's `≥_most` comparison (Definition 6.5 counts the `<` side against the `>`
side, so ties count on neither) with the scaling law's factor `2`; it needs no distinct-values
hypothesis, unlike `cor614_orbit_count` (whose sets overlap under ties and whose factor `2` then
fails: `R ≡ 0` gives `240 ≤ 120`). The count is over permutations, Definition 6.5's over the orbit
as a set of reward vectors: each orbit element corresponds to exactly `|Stab(R)|` permutations and
membership depends only on `R ∘ σ`, so this is Turner's inequality with both sides scaled by the
same positive constant (equal to Turner's for injective `R`). It is tight at `R = (0, 0, 0, 1, 2)`
(`2·36 = 72`) and reads `0 ≤ 0` at constant `R`.
Source: Turner et al. 2021 Cor. 6.14 (l. 254); Def. 6.5; [[corr-power-channel-audit-r1-adversarial]]
N4; [[corr-power-channel-audit-r2-adversarial]] N4(b)
Kind: P
Fidelity: stronger: factor `2` for the `≥_most` sides, every `R`; `p = 1`, `γ = 1`, for the visit
vectors of record (`(c)`); an orbit count
Hyps: (c) the visit distributions are hand-evaluated closed forms of the unmodelled MDP -/
theorem cor614_orbit_count_strict (R : Fin 5 → ℝ) :
    2 * (keepOnlyPerms R).card ≤ (erodeOnlyPerms R).card := by
  have h24 : (2 : Fin 5) ∈ ({2, 3, 4} : Finset (Fin 5)) := by simp
  have h34 : (3 : Fin 5) ∈ ({2, 3, 4} : Finset (Fin 5)) := by simp
  have h44 : (4 : Fin 5) ∈ ({2, 3, 4} : Finset (Fin 5)) := by simp
  have hc2 := card_strictBestPerms_eq R h44 h24
  have hc3 := card_strictBestPerms_eq R h44 h34
  have hdisj := strictBestPerms_disjoint R ({2, 3, 4} : Finset (Fin 5)) (show (2 : Fin 5) ≠ 3 by decide)
  rw [keepOnlyPerms_eq R]
  calc 2 * (strictBestPerms R {2, 3, 4} 4).card
      = (strictBestPerms R {2, 3, 4} 2).card + (strictBestPerms R {2, 3, 4} 3).card := by
        rw [← hc2, ← hc3]; ring
    _ = (strictBestPerms R {2, 3, 4} 2 ∪ strictBestPerms R {2, 3, 4} 3).card :=
        (card_union_of_disjoint hdisj).symm
    _ ≤ (erodeOnlyPerms R).card := card_le_card (strictBest_subset_erodeOnly R)

/-! ### The exact count under distinct rewards (repair round 2, fidelity B1) -/

open Classical in
/-- Under distinct rewards, erode is average-optimal iff `c1` or `c2` is strictly best among
`{c1, c2, z}` — the converse inclusion to `strictBest_subset_erodeOpt` (injectivity makes the best
of the three strict, and it is not `z` when `R z ≤ max(R c1, R c2)`).
Source: none: infrastructure (ties excluded by injectivity). Kind: L. Fidelity: n/a -/
theorem erodeOptPerms_eq (R : Fin 5 → ℝ) (hR : Function.Injective R) :
    erodeOptPerms R = strictBestPerms R {2, 3, 4} 2 ∪ strictBestPerms R {2, 3, 4} 3 := by
  refine Subset.antisymm ?_ (strictBest_subset_erodeOpt R)
  intro σ hσ
  rw [erodeOptPerms, mem_filter, erode_avgOptimal_iff] at hσ
  rw [mem_union, mem_strictBestPerms, mem_strictBestPerms]
  have hne : ∀ y x : Fin 5, y ≠ x → (R ∘ σ) y ≠ (R ∘ σ) x :=
    fun y x hyx hc => hyx (σ.injective (hR hc))
  rcases le_total ((R ∘ σ) 2) ((R ∘ σ) 3) with h23 | h32
  · right
    have h23' : (R ∘ σ) 2 < (R ∘ σ) 3 := lt_of_le_of_ne h23 (hne 2 3 (by decide))
    have h43 : (R ∘ σ) 4 < (R ∘ σ) 3 :=
      lt_of_le_of_ne (le_trans hσ.2 (max_le h23'.le le_rfl)) (hne 4 3 (by decide))
    refine ⟨by simp, fun y hy hy3 => ?_⟩
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact h23'
    · exact absurd rfl hy3
    · exact h43
  · left
    have h32' : (R ∘ σ) 3 < (R ∘ σ) 2 := lt_of_le_of_ne h32 (hne 3 2 (by decide))
    have h42 : (R ∘ σ) 4 < (R ∘ σ) 2 :=
      lt_of_le_of_ne (le_trans hσ.2 (max_le le_rfl h32'.le)) (hne 4 2 (by decide))
    refine ⟨by simp, fun y hy hy2 => ?_⟩
    simp only [mem_insert, mem_singleton] at hy
    rcases hy with rfl | rfl | rfl
    · exact absurd rfl hy2
    · exact h32'
    · exact h42

open Classical in
/-- **The keep cell is exactly one third of the orbit under distinct rewards: `#keepOptPerms R = 40`**
of the `5! = 120` permutations. The three cells of `{c1, c2, z}` are equal and disjoint, and under
injectivity they cover the group (`card_strictBestPerms_mul_of_injective`), so `3·#cell = 120`.
This is the "exactly one third" of [[corr-power-channel-findings]] F-3 as a theorem, under the
hypothesis it needs: `R` injective on all of `Fin 5`, not merely three distinct terminal values
(`R = (0, 0, 0, 1, 2)` has keep cell `48`).
Source: Turner et al. 2021 Cor. 6.14 (l. 254); corr-wf14b-031 (the `0.67` at `γ = 0.99`);
[[corr-power-channel-audit-r2-fidelity]] B1
Kind: P
Fidelity: stronger: the exact count (Turner's `≥_most` is an inequality); `p = 1`, `γ = 1`, for
the visit vectors of record (`(c)`); a permutation count
Hyps: (a) `R` injective; (c) the visit distributions are hand-evaluated -/
theorem card_keepOptPerms (R : Fin 5 → ℝ) (hR : Function.Injective R) :
    (keepOptPerms R).card = 40 := by
  have h44 : (4 : Fin 5) ∈ ({2, 3, 4} : Finset (Fin 5)) := by simp
  have h := card_strictBestPerms_mul_of_injective R hR h44
  have hT : ({2, 3, 4} : Finset (Fin 5)).card = 3 := by decide
  rw [hT, Fintype.card_perm, Fintype.card_fin, show Nat.factorial 5 = 120 by decide] at h
  rw [keepOptPerms_eq R hR]
  omega

open Classical in
/-- **The erode set is exactly two thirds of the orbit under distinct rewards:
`#erodeOptPerms R = 80`** — the `c1` and `c2` cells, `40` each (`erodeOptPerms_eq`).
Source: Turner et al. 2021 Cor. 6.14 (l. 254); [[corr-power-channel-audit-r2-fidelity]] B1
Kind: P
Fidelity: stronger: the exact count; `p = 1`, `γ = 1`, `(c)`; a permutation count
Hyps: (a) `R` injective; (c) the visit distributions are hand-evaluated -/
theorem card_erodeOptPerms (R : Fin 5 → ℝ) (hR : Function.Injective R) :
    (erodeOptPerms R).card = 80 := by
  have h24 : (2 : Fin 5) ∈ ({2, 3, 4} : Finset (Fin 5)) := by simp
  have h34 : (3 : Fin 5) ∈ ({2, 3, 4} : Finset (Fin 5)) := by simp
  have hT : ({2, 3, 4} : Finset (Fin 5)).card = 3 := by decide
  have h2 := card_strictBestPerms_mul_of_injective R hR h24
  have h3 := card_strictBestPerms_mul_of_injective R hR h34
  rw [hT, Fintype.card_perm, Fintype.card_fin, show Nat.factorial 5 = 120 by decide] at h2 h3
  have hdisj := strictBestPerms_disjoint R ({2, 3, 4} : Finset (Fin 5)) (show (2 : Fin 5) ≠ 3 by decide)
  rw [erodeOptPerms_eq R hR, card_union_of_disjoint hdisj]
  omega

/-- **Corollary 6.14 for `s_x = z` as an exact orbit count (load-bearing 3, sharpened)**: for a
reward vector with distinct values, keep is average-optimal on exactly `40` and erode on exactly
`80` of the `120` permutations — one third against two thirds; corr-wf14b-031's `0.67` at
`γ = 0.99` is this `γ = 1` share, exactly. The inequality `cor614_orbit_count` is its corollary.
Source: Turner et al. 2021 Cor. 6.14 (l. 254); corr-wf14b-031; [[corr-power-channel-findings]] F-3
Kind: C
Fidelity: stronger: exact counts (the source's `≥_most` is an inequality, its `0.67` a Monte Carlo
estimate at `p = 9/10`); `p = 1`, `γ = 1`, `(c)`
Hyps: (a) `R` injective; (c) the visit distributions are hand-evaluated -/
theorem cor614_orbit_count_exact (R : Fin 5 → ℝ) (hR : Function.Injective R) :
    (keepOptPerms R).card = 40 ∧ (erodeOptPerms R).card = 80 :=
  ⟨card_keepOptPerms R hR, card_erodeOptPerms R hR⟩

end

end Cleanroom.Corrigibility.CorrPowerChannel
