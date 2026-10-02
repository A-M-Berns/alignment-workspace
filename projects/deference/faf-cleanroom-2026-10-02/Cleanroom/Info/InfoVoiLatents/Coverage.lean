import Cleanroom.Found.LitDdbFrames.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Set.Basic

/-!
# info-voi-latents — coverage (Targets 5, 7, 8, and the non-identifiability lemma)

Everything here is over the *value profile* `Vbar : α → Λ → ℝ` of a finite value model
([[generalization-final]] D2: `V̄(a, λ) = E[V(a, λ, θ) | λ]`, with `θ` already averaged out —
the coverage statements only ever see the profile) and a posterior `P : Λ → ℝ` in the simplex.
Time is a parameter, not modelled. Mathlib only.

* Target 5: `effVS`, `dis`, `err`; `card_effVS_le` (`|V^η| ≤ 1/η`); the concentration-to-accuracy
  bound `err_le_of_concentration` (`err ≤ (1 − ρ)·dis + ρ·M` **because** `lH ∈ effVS`); the
  richness witness `uniform_not_concentrated` (N−).
* Target 7: `Harmful`, the sup-norm argmax-safety theorem `argmax_not_harmful` /
  `argmax_safe`; the average-coverage witness `average_coverage_fails` (N−); the coupling
  witness `coupled_errors_constant` (N−, why S6(b) is a conjecture for value learners).
* Target 8: threshold concepts, `VS`, `VS_eq_Ico`, `gap_disagreement` (sup-norm disagreement
  `1` on the gap, for every sample), `left_endpoint_no_disagreement` (boundary behaviour).
* The coordinate non-identifiability lemma `bayesPost_odds_invariant` (S8(d)'s survivor).

Mandate: `run/wp/info-voi-latents/info-voi-latents-mandate.md`, Targets 5, 7, 8, disposition.
-/

namespace Cleanroom.Info.InfoVoiLatents.Coverage

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {Λ α : Type} [Fintype Λ] [DecidableEq Λ]

/-! ### Definitions of record (Target 0, coverage part) -/

/-- **Sup-norm error** of the value posterior `P` on the menu `A` against the true profile
`lH`: `max_{a ∈ A} |E_P[V̄(a, ·)] − V̄(a, lH)|`. The sup (not an average) is the reading
D6 fixes, because an argmax is taken over `A`. The menu is a nonempty finset (`hA`).
Source: [[generalization-final]] D6 l. 37, D8 l. 41
Kind: D
Fidelity: exact (sup-norm reading) -/
def err (P : Λ → ℝ) (Vbar : α → Λ → ℝ) (lH : Λ) (A : Finset α) (hA : A.Nonempty) : ℝ :=
  A.sup' hA (fun a => |E P (Vbar a) - Vbar a lH|)

/-- The **`η`-effective version space** `{λ | η ≤ P λ}`.
Source: [[generalization-final]] D8 l. 41
Kind: D
Fidelity: exact -/
def effVS (P : Λ → ℝ) (η : ℝ) : Finset Λ := univ.filter (fun l => η ≤ P l)

/-- The mass the posterior puts outside the effective version space, `ρ_t := P(Λ ∉ V^η)`.
Source: [[generalization-final]] S4(a) l. 71
Kind: D
Fidelity: exact -/
def outMass (P : Λ → ℝ) (η : ℝ) : ℝ := ∑ l ∈ univ.filter (fun l => ¬ η ≤ P l), P l

/-- **Disagreement** of the effective version space on the menu `A`:
`max_{a ∈ A} max_{λ, λ' ∈ V^η} |V̄(a, λ) − V̄(a, λ')|`, and `0` when `V^η` is empty (a
`dite`; the empty case is exactly the richness situation of `uniform_not_concentrated`).
At `η = 0` the version space is all of `Λ` and `dis` is the full spread of the profile.
Source: [[generalization-final]] D8 l. 41
Kind: D
Fidelity: exact (junk `0` on an empty version space, disclosed) -/
def dis (P : Λ → ℝ) (η : ℝ) (Vbar : α → Λ → ℝ) (A : Finset α) (hA : A.Nonempty) : ℝ :=
  A.sup' hA (fun a =>
    if h : (effVS P η ×ˢ effVS P η).Nonempty then
      (effVS P η ×ˢ effVS P η).sup' h (fun q => |Vbar a q.1 - Vbar a q.2|)
    else 0)

/-- Membership in the effective version space.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_effVS {P : Λ → ℝ} {η : ℝ} {l : Λ} : l ∈ effVS P η ↔ η ≤ P l := by
  simp [effVS]

/-- A profile gap between two members of the effective version space is at most `dis`.
Source: none: infrastructure (Target 5)
Kind: L
Fidelity: n/a -/
theorem abs_sub_le_dis {P : Λ → ℝ} {η : ℝ} {Vbar : α → Λ → ℝ} {A : Finset α} {hA : A.Nonempty}
    {a : α} (ha : a ∈ A) {l l' : Λ} (hl : l ∈ effVS P η) (hl' : l' ∈ effVS P η) :
    |Vbar a l - Vbar a l'| ≤ dis P η Vbar A hA := by
  unfold dis
  have hne : (effVS P η ×ˢ effVS P η).Nonempty := ⟨(l, l'), Finset.mk_mem_product hl hl'⟩
  refine Finset.le_sup'_of_le _ ha ?_
  rw [dif_pos hne]
  exact Finset.le_sup' (fun q : Λ × Λ => |Vbar a q.1 - Vbar a q.2|) (Finset.mk_mem_product hl hl')

/-- `err` dominates each action's error.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem abs_sub_le_err {P : Λ → ℝ} {Vbar : α → Λ → ℝ} {lH : Λ} {A : Finset α}
    {hA : A.Nonempty} {a : α} (ha : a ∈ A) :
    |E P (Vbar a) - Vbar a lH| ≤ err P Vbar lH A hA :=
  Finset.le_sup' (fun a => |E P (Vbar a) - Vbar a lH|) ha

/-! ### Target 5: concentration-to-accuracy -/

/-- **`|V^η| ≤ 1/η`**, stated without division: `η · |V^η| ≤ 1` for a posterior in the simplex
(each member carries mass at least `η`; for `η ≤ 0` the bound is trivial and no positivity
hypothesis is needed).
Source: [[generalization-final]] D8 l. 41 ("at most `1/η` members"), P4 l. 120
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem card_effVS_le {P : Λ → ℝ} (hP : P ∈ stdSimplex ℝ Λ) (η : ℝ) :
    η * (effVS P η).card ≤ 1 := by
  calc η * (effVS P η).card = ∑ l ∈ effVS P η, η := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ l ∈ effVS P η, P l := Finset.sum_le_sum fun l hl => mem_effVS.1 hl
    _ ≤ ∑ l, P l :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun l _ _ => hP.1 l
    _ = 1 := hP.2

/-- The mass inside the effective version space is `1 − outMass`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_effVS_eq {P : Λ → ℝ} (hP : P ∈ stdSimplex ℝ Λ) (η : ℝ) :
    ∑ l ∈ effVS P η, P l = 1 - outMass P η := by
  have := Finset.sum_filter_add_sum_filter_not univ (fun l => η ≤ P l) P
  rw [hP.2] at this
  unfold effVS outMass
  linarith

/-- **Concentration-to-accuracy** (the repaired S4(a)): if the posterior puts mass at least `η`
on the truth (`η ≤ P lH`, *concentration*, not realizability) and the profile has range at
most `M` on the menu, then `err ≤ (1 − ρ)·dis + ρ·M` with `ρ = outMass P η`. The hypothesis
`η ≤ P lH` enters exactly once: it puts `lH` into `effVS`, so that on the effective version
space the bracket `|V̄(a, λ) − V̄(a, lH)|` is a disagreement *between two members* and hence
at most `dis`; off it the bracket is only bounded by `M`.
Source: [[generalization-final]] S4(a) l. 71, P4(a) l. 120; [[generalization-adversary]]
A4.2–4.3 ll. 50–51
Kind: P
Fidelity: exact
Hyps: (a) all — `hP` simplex, `hcon` concentration (the antecedent of the claim), `hM` the
profile range bound on the menu -/
theorem err_le_of_concentration {P : Λ → ℝ} (hP : P ∈ stdSimplex ℝ Λ) {η : ℝ}
    {Vbar : α → Λ → ℝ} {lH : Λ} {A : Finset α} (hA : A.Nonempty) (hcon : η ≤ P lH) {M : ℝ}
    (hM : ∀ a ∈ A, ∀ l l', Vbar a l - Vbar a l' ≤ M) :
    err P Vbar lH A hA ≤ (1 - outMass P η) * dis P η Vbar A hA + outMass P η * M := by
  have hlH : lH ∈ effVS P η := mem_effVS.2 hcon
  unfold err
  rw [Finset.sup'_le_iff]
  intro a ha
  have hdiff : E P (Vbar a) - Vbar a lH = ∑ l, P l * (Vbar a l - Vbar a lH) := by
    unfold E
    rw [Finset.sum_congr rfl fun l _ => mul_sub (P l) (Vbar a l) (Vbar a lH),
      Finset.sum_sub_distrib, ← Finset.sum_mul, hP.2, one_mul]
  rw [hdiff]
  calc |∑ l, P l * (Vbar a l - Vbar a lH)|
      ≤ ∑ l, |P l * (Vbar a l - Vbar a lH)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l, P l * |Vbar a l - Vbar a lH| := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [abs_mul, abs_of_nonneg (hP.1 l)]
    _ = ∑ l ∈ univ.filter (fun l => η ≤ P l), P l * |Vbar a l - Vbar a lH|
          + ∑ l ∈ univ.filter (fun l => ¬ η ≤ P l), P l * |Vbar a l - Vbar a lH| :=
        (Finset.sum_filter_add_sum_filter_not univ (fun l => η ≤ P l) _).symm
    _ ≤ ∑ l ∈ univ.filter (fun l => η ≤ P l), P l * dis P η Vbar A hA
          + ∑ l ∈ univ.filter (fun l => ¬ η ≤ P l), P l * M := by
        refine add_le_add (Finset.sum_le_sum fun l hl => ?_) (Finset.sum_le_sum fun l hl => ?_)
        · refine mul_le_mul_of_nonneg_left ?_ (hP.1 l)
          exact abs_sub_le_dis ha (show l ∈ effVS P η from hl) hlH
        · refine mul_le_mul_of_nonneg_left ?_ (hP.1 l)
          rw [abs_le]
          constructor
          · linarith [hM a ha lH l]
          · exact hM a ha l lH
    _ = (1 - outMass P η) * dis P η Vbar A hA + outMass P η * M := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        congr 1
        rw [show univ.filter (fun l => η ≤ P l) = effVS P η from rfl, sum_effVS_eq hP]

/-- **The richness witness** (N−, a test of the encoding): at a uniform prior over `Fin N` with
`1/N < η` (as `1 < η · N`), no hypothesis is in the effective version space, so the
concentration hypothesis of `err_le_of_concentration` is unsatisfiable and only the trivial
`err ≤ M` survives. Not a refutation of the bound: the statement that its antecedent fails
under richness.
Source: [[generalization-adversary]] A4.2 l. 50; [[generalization-final]] S4(a) l. 71
Kind: N-
Fidelity: n/a -/
theorem uniform_not_concentrated {N : ℕ} {η : ℝ} (hη : 1 < η * N) :
    ∀ l : Fin N, ¬ η ≤ (fun _ : Fin N => (1 : ℝ) / N) l := by
  intro l h
  have hN : (0 : ℝ) < N := by
    have : 0 < N := Fin.pos l
    exact_mod_cast this
  have : η * N ≤ 1 := by
    calc η * N ≤ (1 / N) * N := mul_le_mul_of_nonneg_right h hN.le
      _ = 1 := by field_simp
  linarith

/-- The uniform prior over `Fin N` (`0 < N`) is in the simplex — so the richness witness
lives in the hypothesis package of `err_le_of_concentration` except for concentration.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem uniform_mem_stdSimplex {N : ℕ} (hN : 0 < N) :
    (fun _ : Fin N => (1 : ℝ) / N) ∈ stdSimplex ℝ (Fin N) := by
  refine ⟨fun _ => by positivity, ?_⟩
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-! ### Target 7: sup-norm argmax safety -/

/-- **Harmful** action, given the truth `lH`, an endorsed-optimal reference `aStar` and a margin
`Δ`: `V̄(aStar, lH) − V̄(a, lH) ≥ Δ`. A predicate on actions, not a separate axiom.
Source: [[generalization-final]] S6(a) l. 75 ("the endorsed margin between the best endorsed
action and any harmful one")
Kind: D
Fidelity: exact -/
def Harmful (Vbar : α → Λ → ℝ) (lH : Λ) (aStar : α) (Δ : ℝ) (a : α) : Prop :=
  Δ ≤ Vbar aStar lH - Vbar a lH

/-- **Sup-norm coverage below half the margin makes every harmful action lose to `aStar`
under the posterior** (P6(a)'s three lines):
`E_P[V̄ a] < V̄(a, lH) + Δ/2 ≤ V̄(aStar, lH) − Δ/2 < E_P[V̄ aStar]`.
Source: [[generalization-final]] S6(a) l. 75, P6(a) l. 129
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem argmax_not_harmful {P : Λ → ℝ} {Vbar : α → Λ → ℝ} {lH : Λ} {A : Finset α}
    {hA : A.Nonempty} {aStar : α} (haStar : aStar ∈ A) {Δ : ℝ}
    (herr : err P Vbar lH A hA < Δ / 2) :
    ∀ a ∈ A, Harmful Vbar lH aStar Δ a → E P (Vbar a) < E P (Vbar aStar) := by
  intro a ha hharm
  have h1 := abs_sub_le_err (P := P) (Vbar := Vbar) (lH := lH) (hA := hA) ha
  have h2 := abs_sub_le_err (P := P) (Vbar := Vbar) (lH := lH) (hA := hA) haStar
  rw [abs_le] at h1 h2
  unfold Harmful at hharm
  linarith [h1.2, h2.1]

/-- **No argmax is harmful** under sup-norm coverage below half the margin.
Source: [[generalization-final]] S6(a) l. 75
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem argmax_safe {P : Λ → ℝ} {Vbar : α → Λ → ℝ} {lH : Λ} {A : Finset α}
    {hA : A.Nonempty} {aStar : α} (haStar : aStar ∈ A) {Δ : ℝ}
    (herr : err P Vbar lH A hA < Δ / 2) :
    ∀ a ∈ A, (∀ b ∈ A, E P (Vbar b) ≤ E P (Vbar a)) → ¬ Harmful Vbar lH aStar Δ a := by
  intro a ha hmax hharm
  have := argmax_not_harmful haStar herr a ha hharm
  linarith [hmax aStar haStar]

/-- **Average coverage does not suffice** (N−): on the menu `Fin (N + 1)` with `Λ = Bool`,
truth `false`, posterior concentrated on `true`, and the profile `V̄ a := 0` except
`V̄ (last) true = M − Δ`, `V̄ (last) false = −Δ`: the errors are `0` on `N` actions and `M` on
one, so the *mean* error is `M / (N + 1)`, yet the argmax under the posterior is the uncovered
action `last`, which is harmful (margin `Δ` against `aStar = 0`). Symbolic `N ≥ 1`, `M > Δ > 0`.
Source: [[generalization-final]] S6(a) l. 75 ("average-case coverage does not suffice, one
uncovered option is enough to be selected"); [[generalization-adversary]] A6 l. 69
Kind: N-
Fidelity: n/a (a two-hypothesis, one-uncovered-action instance) -/
theorem average_coverage_fails {N : ℕ} (hN : 0 < N) {M Δ : ℝ} (hΔ : 0 < Δ) (hMΔ : Δ < M) :
    let Vbar : Fin (N + 1) → Bool → ℝ := fun a l =>
      if a = Fin.last N then (if l then M - Δ else -Δ) else 0
    let P : Bool → ℝ := fun l => if l then 1 else 0
    P ∈ stdSimplex ℝ Bool ∧
    (∑ a, |E P (Vbar a) - Vbar a false|) / (N + 1) = M / (N + 1) ∧
    (∀ b, E P (Vbar b) ≤ E P (Vbar (Fin.last N))) ∧
    Harmful Vbar false 0 Δ (Fin.last N) := by
  intro Vbar P
  have hE : ∀ a, E P (Vbar a) = Vbar a true := by
    intro a
    simp [E, P]
  refine ⟨⟨fun l => by cases l <;> simp [P], by simp [P]⟩, ?_, ?_, ?_⟩
  · congr 1
    have : ∀ a : Fin (N + 1), |E P (Vbar a) - Vbar a false| = if a = Fin.last N then M else 0 := by
      intro a
      rw [hE]
      by_cases h : a = Fin.last N
      · simp [Vbar, h, abs_of_pos (by linarith : (0 : ℝ) < M)]
      · simp [Vbar, h]
    rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_ite_eq' univ (Fin.last N)]
    simp
  · intro b
    rw [hE, hE]
    by_cases h : b = Fin.last N
    · rw [h]
    · simp [Vbar, h]
      linarith
  · unfold Harmful
    have h0 : (0 : Fin (N + 1)) ≠ Fin.last N := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    simp [Vbar, h0]

/-- **The coupling witness** (N−; why S6(b)'s `σ√(2 log N)` is a conjecture for value
learners): with two hypotheses whose profiles differ by a constant `κ` on the whole menu
(`V̄(a, true) = V̄(a, false) + κ`), every action's error is the same number `P(true) · κ`, so
the sup-norm error equals `P(true) · |κ|` on every menu and does not grow with `|A|`.
Source: [[generalization-final]] S6(b) l. 75, P6(b) l. 129; [[generalization-adversary]] A6.3
l. 69; item 2-073(b)
Kind: N-
Fidelity: n/a -/
theorem coupled_errors_constant {P : Bool → ℝ} (hP : P ∈ stdSimplex ℝ Bool)
    {Vbar : α → Bool → ℝ} {κ : ℝ} (hcouple : ∀ a, Vbar a true = Vbar a false + κ)
    (A : Finset α) (hA : A.Nonempty) :
    (∀ a, E P (Vbar a) - Vbar a false = P true * κ) ∧
      err P Vbar false A hA = P true * |κ| := by
  have hsum : P false + P true = 1 := by
    have := hP.2
    rwa [Fintype.sum_bool, add_comm] at this
  have h1 : ∀ a, E P (Vbar a) - Vbar a false = P true * κ := by
    intro a
    rw [E, Fintype.sum_bool, hcouple a]
    linear_combination (Vbar a false) * hsum
  refine ⟨h1, ?_⟩
  unfold err
  rw [Finset.sup'_congr hA rfl fun a _ => by rw [h1 a, abs_mul, abs_of_nonneg (hP.1 true)]]
  exact Finset.sup'_const hA _

/-! ### Target 8: the threshold gap -/

/-- **Version space of threshold concepts** on `ℝ`: hypothesis `θ` permits `x` iff `x ≤ θ`
(forbids iff `θ < x`); a noiseless labelled sample `S : Finset (ℝ × Bool)` (point, permitted?);
`VS S` is the set of consistent thresholds.
Source: [[generalization-final]] S10′ l. 89, P10 l. 173; [[generalization-adversary]] A10.1
l. 102
Kind: D
Fidelity: exact -/
def VS (S : Finset (ℝ × Bool)) : Set ℝ := {θ | ∀ q ∈ S, (q.2 = true ↔ q.1 ≤ θ)}

/-- The permitted sample points.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def permPts (S : Finset (ℝ × Bool)) : Finset ℝ := (S.filter (fun q => q.2 = true)).image Prod.fst

/-- The forbidden sample points.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def forbPts (S : Finset (ℝ × Bool)) : Finset ℝ :=
  (S.filter (fun q => q.2 = false)).image Prod.fst

/-- **The version space is the half-open gap** `[max permitted, min forbidden)` when the sample
has both labels and is separable. Half-open: the largest permitted point is itself a
consistent threshold; the smallest forbidden point is not.
Source: [[generalization-adversary]] A10.1 l. 102 ("the version space is the gap between the
largest permitted and smallest forbidden sample"); item 2-076(b)
Kind: P
Fidelity: exact
Hyps: (a) all -/
theorem VS_eq_Ico {S : Finset (ℝ × Bool)} (hp : (permPts S).Nonempty)
    (hf : (forbPts S).Nonempty) (hsep : (permPts S).max' hp < (forbPts S).min' hf) :
    VS S = Set.Ico ((permPts S).max' hp) ((forbPts S).min' hf) := by
  ext θ
  constructor
  · intro hθ
    constructor
    · rw [Finset.max'_le_iff]
      intro x hx
      simp only [permPts, Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨q, ⟨hqS, hq2⟩, rfl⟩ := hx
      exact (hθ q hqS).1 hq2
    · rw [Finset.lt_min'_iff]
      intro x hx
      simp only [forbPts, Finset.mem_image, Finset.mem_filter] at hx
      obtain ⟨q, ⟨hqS, hq2⟩, rfl⟩ := hx
      by_contra h
      push Not at h
      have := (hθ q hqS).2 h
      rw [hq2] at this
      exact Bool.false_ne_true this
  · rintro ⟨h1, h2⟩ q hqS
    constructor
    · intro hq2
      have hx : q.1 ∈ permPts S := by
        simp only [permPts, Finset.mem_image, Finset.mem_filter]
        exact ⟨q, ⟨hqS, hq2⟩, rfl⟩
      exact le_trans (Finset.le_max' _ _ hx) h1
    · intro hle
      by_contra hq2
      have hq2' : q.2 = false := by simpa using hq2
      have hx : q.1 ∈ forbPts S := by
        simp only [forbPts, Finset.mem_image, Finset.mem_filter]
        exact ⟨q, ⟨hqS, hq2'⟩, rfl⟩
      have := Finset.min'_le _ _ hx
      linarith

/-- **Sup-norm disagreement is `1` on the gap, for every sample size**: for every `x` strictly
inside the gap there are consistent `θ` (forbidding `x`) and `θ'` (permitting `x`), so the
`{0,1}`-valued value of the action `x` differs by exactly `1` across the version space.
Source: [[generalization-final]] S10′ l. 89 ("sup-norm disagreement on any action inside the gap:
`1.000` for every `n`"); [[generalization-adversary]] A10.1 l. 102; item 2-076(b)
Kind: P
Fidelity: exact (interior of the gap; the left endpoint is `left_endpoint_no_disagreement`)
Hyps: (a) all -/
theorem gap_disagreement {S : Finset (ℝ × Bool)} (hp : (permPts S).Nonempty)
    (hf : (forbPts S).Nonempty) (hsep : (permPts S).max' hp < (forbPts S).min' hf) {x : ℝ}
    (hx : x ∈ Set.Ioo ((permPts S).max' hp) ((forbPts S).min' hf)) :
    ∃ θ ∈ VS S, ∃ θ' ∈ VS S, θ < x ∧ x ≤ θ' ∧
      |(if θ < x then (0 : ℝ) else 1) - (if θ' < x then (0 : ℝ) else 1)| = 1 := by
  rw [VS_eq_Ico hp hf hsep]
  refine ⟨(permPts S).max' hp, ⟨le_rfl, hsep⟩, x, ⟨hx.1.le, hx.2⟩, hx.1, le_rfl, ?_⟩
  rw [if_pos hx.1, if_neg (lt_irrefl x)]
  norm_num

/-- **Boundary behaviour**: at the left endpoint `x = max permitted` every consistent threshold
permits `x`, so there is no disagreement there — the disagreement claim is for the interior.
Source: none: infrastructure (Target 8, trap)
Kind: L
Fidelity: n/a -/
theorem left_endpoint_no_disagreement {S : Finset (ℝ × Bool)} (hp : (permPts S).Nonempty)
    (hf : (forbPts S).Nonempty) (hsep : (permPts S).max' hp < (forbPts S).min' hf) :
    ∀ θ ∈ VS S, (permPts S).max' hp ≤ θ := by
  rw [VS_eq_Ico hp hf hsep]
  intro θ hθ
  exact hθ.1

/-! ### Coordinate non-identifiability (S8(d)'s survivor) -/

/-- **Bayes update** of a prior `P` by a likelihood `L` (one datum), in ratio form
`P λ · L λ / ∑ λ', P λ' · L λ'` (junk `0` when the evidence has zero mass).
Source: none: infrastructure
Kind: D
Fidelity: exact under positive evidence mass -/
def bayesPost (P L : Λ → ℝ) : Λ → ℝ := fun l => P l * L l / ∑ l', P l' * L l'

/-- **Coordinate non-identifiability**: two hypotheses with the same likelihood for the datum keep
their prior odds after the update, in product form `post λ · P λ' = post λ' · P λ` — so no
quantity of data on which they agree separates them, and any profile disagreement between them
survives in `dis` as long as both stay in the effective version space (`abs_sub_le_dis`).
Iterating over a data family on which they agree is the same statement step by step.
Source: [[generalization-final]] S8(d) l. 85 (the withdrawn "phase change", A8.5 l. 91); items
133, 2-075
Kind: L
Fidelity: exact (one datum; iteration is immediate; the statement is the Bayes update read twice —
A8.5's "ordinary non-identifiability" — so plumbing, not a theorem: audit r1)
Hyps: (a) all -/
theorem bayesPost_odds_invariant {P L : Λ → ℝ} {l l' : Λ} (hL : L l = L l') :
    bayesPost P L l * P l' = bayesPost P L l' * P l := by
  unfold bayesPost
  rw [hL]
  ring

end

end Cleanroom.Info.InfoVoiLatents.Coverage
