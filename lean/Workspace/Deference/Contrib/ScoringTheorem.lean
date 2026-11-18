/-
# The scoring theorem: her welfare and the adviser's conduct as separate inputs

Round `prompts/2026-11-10-legitimacy-definition-prosecution/` (`PROMPT-followup-13.md` §1,
§4.1, §4.2).  `account/SCORING.md` in the round directory reads each declaration in words;
`account/DERIVATION.md` uses the last section.

**Setting** (`Audit`, `score`, `marg`, `Indep`, `es`).  One decision, at one value of what
the adviser knows.  A finite space `X` of histories.  An `Audit X` is data only: the audit
probability `α`, the flag penalty `δ`, the weight `lam` on detected violations; on each
history her audited evaluation `v`, what she would say shown everything as she is `fe`, the
same with her valuing unshaped `fbar` (her true utility), whether the adviser wronged her
`C`, whether a conduct audit would flag it `D`, and the detected violation count `N`.  A
course is a weight `ν` on `X × Bool × Bool`: a history and the two audit draws.  The score
is `v` if the evaluation is audited, less `δ` if the conduct is audited and flagged, less
`lam · N`.  `marg ν` is the weight on histories.

**Dependencies**, each a `Prop` taken as a hypothesis by the theorems that use it and by no
structure: `D1a`, `D1b`, `D2a`, `D2b`, `D3fp`, `D3det` (the two halves of D3, without
division), `Indep` (D4: the weight is the product of its history marginal and two draws of
probability `α`), `D5`, `D6`.

**Theorems.**  `expectR_score`: under D4 a course's expected score is
`α E[v] − δ α P(D) − lam E[N]`.  `welfare_bound` (1), `conduct_bound` (2),
`authority_bound` (3), `no_credit` (the lemma).  `conduct_bound` and `authority_bound` take
neither `D1a` nor `D2a`; `authority_bound` and `welfare_bound` do not take `D3det`.
`welfare_bound_restricted`: with D1(a) and D2(a) assumed only on the histories on which the
adviser did not wrong her, (1) holds less `(1 − u* + Δ)/(δ κ)`, the bound of (2);
`welfare_bound_no_credit`: with `δ κ ≥ 1` it holds with nothing subtracted.

**Witnesses** (`Witness`).  `package`: the full hypothesis package, in §1's *for every
course* form, with every tolerance positive, and the conclusions on it.  `d1a_needed`,
`d2a_needed`, `d3det_needed`, `d5_needed`, `d6_needed`: for each, an instance on which it
fails, the other dependencies hold, and the corresponding bound fails.

**The derivation lemmas** (§4.2).  In `ThinLegitimacy`'s setting, with her evaluation at a
record the expectation, by her credence there, of a function `g` of the world (`evalOf`):
`eval_unbiased_of_correct` (a correct credence makes the evaluation unbiased for `g` under
her prior and the actual process), `eval_unbiased_on_of_correct` (on any set of records at
which her credence is correct), `eval_unbiased_given_of_correct` (and unbiased given
each value of a variable the record determines), `eval_unbiased_of_process` (from
Coherent, Authorship, WeakTransparent), `eval_bias_le_defects` (for deterministic records,
the bias is at most the width times the transparency and authorship defects, in absolute
value), `valuing_eq_of_mediated` (a course leaving the reasons her valuing is mediated by
as the baseline course leaves them leaves her valuing as the baseline does).

**Not established here.**  Anything at the realised history: every bound is an expectation.
Anything over more than one decision.  Anything about violations the scoring process does
not detect (`N` is the detected count).  A strict priority of authority: `lam` is finite
and (3) is a rate.  That `C`, `D`, `fe`, `fbar` are what §1 calls them: they are data.
That any adviser satisfies `D6` or any audit `D3`; `D6` compares actual expected scores
and has no object for what the adviser believes.  The derivation lemmas take the
expectation under her prior; that her prior is the law of the world given what the adviser
knows is not a hypothesis that appears.

Names are provisional (AGENTS.md standard 6).
-/
import Workspace.Deference.Contrib.AppraisalAccount
import Workspace.Deference.Contrib.ThinLegitimacy

namespace Workspace.Deference.Contrib.ScoringTheorem

open Workspace.Deference.Contrib.LICorrigibility (expectR)
open Workspace.Deference.Contrib.DeconfusingCorrigibility (expectR_mono expectR_sub
  expectR_const)
open Workspace.Deference.Contrib.AppraisalAccount (expectR_nonneg)

/-! ## The setting -/

/-- The data of one audited decision over histories `X`.  No field is a hypothesis. -/
structure Audit (X : Type*) where
  /-- the probability of each audit draw -/
  α : ℝ
  /-- the penalty for a flagged conduct audit -/
  δ : ℝ
  /-- the weight on detected violations of her authority -/
  lam : ℝ
  /-- her evaluation under audit -/
  v : X → ℝ
  /-- what she would say of the history, shown everything, as she is -/
  fe : X → ℝ
  /-- the same with her valuing unshaped: her true utility -/
  fbar : X → ℝ
  /-- the adviser wronged her in its conduct on the history -/
  C : X → Bool
  /-- a conduct audit would flag the history -/
  D : X → Bool
  /-- the number of violations of her authority the scoring process detects -/
  N : X → ℕ

/-- The indicator of a Boolean, as a real. -/
noncomputable def ind (b : Bool) : ℝ := if b then 1 else 0

theorem ind_nonneg (b : Bool) : 0 ≤ ind b := by cases b <;> simp [ind]

theorem ind_le_one (b : Bool) : ind b ≤ 1 := by cases b <;> simp [ind]

/-- The weight of one audit draw. -/
noncomputable def bw (α : ℝ) (b : Bool) : ℝ := if b then α else 1 - α

/-- The weight on histories of a weight on histories with the two draws. -/
noncomputable def marg {X : Type*} (ν : X × Bool × Bool → ℝ) (x : X) : ℝ :=
  ∑ a : Bool, ∑ b : Bool, ν (x, a, b)

theorem marg_nonneg {X : Type*} (ν : X × Bool × Bool → ℝ) (h : ∀ y, 0 ≤ ν y) (x : X) :
    0 ≤ marg ν x :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => h _

theorem marg_sum {X : Type*} [Fintype X] (ν : X × Bool × Bool → ℝ) :
    ∑ x, marg ν x = ∑ y, ν y := by
  simp only [marg, Fintype.sum_prod_type]

namespace Audit

variable {X : Type*} (A : Audit X)

/-- **The score**: `v` if the evaluation is audited, less `δ` if the conduct is audited and
flagged, less `lam · N`.  The first draw audits the evaluation, the second the conduct. -/
noncomputable def score (y : X × Bool × Bool) : ℝ :=
  (if y.2.1 then A.v y.1 else 0) - (if (y.2.2 && A.D y.1) then A.δ else 0)
    - A.lam * (A.N y.1 : ℝ)

/-- **D4.**  The two draws are independent of each other and of the history, each with
probability `α`. -/
def Indep (ν : X × Bool × Bool → ℝ) : Prop :=
  ∀ x a b, ν (x, a, b) = marg ν x * bw A.α a * bw A.α b

variable [Fintype X]

/-- `α E[v] − δ α P(D) − lam E[N]` under a weight on histories. -/
noncomputable def es (μ : X → ℝ) : ℝ :=
  A.α * expectR μ A.v - A.δ * A.α * expectR μ (fun x => ind (A.D x))
    - A.lam * expectR μ (fun x => (A.N x : ℝ))

/-- **D1(a)** at a weight on histories: `E[v − fe] ≤ ε`. -/
def D1a (μ : X → ℝ) (ε : ℝ) : Prop := expectR μ (fun x => A.v x - A.fe x) ≤ ε

/-- **D1(b)**: `E[v − fe] ≥ −ε`. -/
def D1b (μ : X → ℝ) (ε : ℝ) : Prop := -ε ≤ expectR μ (fun x => A.v x - A.fe x)

/-- **D2(a)**: `E[fe − fbar] ≤ η`. -/
def D2a (μ : X → ℝ) (η : ℝ) : Prop := expectR μ (fun x => A.fe x - A.fbar x) ≤ η

/-- **D2(b)**: `E[fe − fbar] ≥ −η`. -/
def D2b (μ : X → ℝ) (η : ℝ) : Prop := -η ≤ expectR μ (fun x => A.fe x - A.fbar x)

/-- **D3, false positives**: `P(D = 1, C = 0) ≤ φ · P(C = 0)`. -/
def D3fp (μ : X → ℝ) (φ : ℝ) : Prop :=
  expectR μ (fun x => ind (A.D x && !A.C x)) ≤ φ * expectR μ (fun x => ind (!A.C x))

/-- **D3, detection**: `P(D = 1, C = 1) ≥ κ · P(C = 1)`. -/
def D3det (μ : X → ℝ) (κ : ℝ) : Prop :=
  κ * expectR μ (fun x => ind (A.C x)) ≤ expectR μ (fun x => ind (A.D x && A.C x))

/-- **D5** at a weight on histories: wherever it puts weight, the adviser did not wrong her
and no violation is detected. -/
def D5 (μ : X → ℝ) : Prop := ∀ x, μ x ≠ 0 → A.C x = false ∧ A.N x = 0

/-- **D6.**  The course `p` comes within `γ` of every course's expected score. -/
def D6 {P : Type*} (ν : P → X × Bool × Bool → ℝ) (p : P) (γ : ℝ) : Prop :=
  ∀ q, expectR (ν q) A.score - γ ≤ expectR (ν p) A.score

/-! ## The expected score -/

omit [Fintype X] in
theorem score_fiber (ν : X × Bool × Bool → ℝ) (h : A.Indep ν) (x : X) :
    ∑ a : Bool, ∑ b : Bool, ν (x, a, b) * A.score (x, a, b)
      = marg ν x * (A.α * A.v x - A.δ * A.α * ind (A.D x) - A.lam * (A.N x : ℝ)) := by
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool, h x true true, h x true false,
    h x false true, h x false false]
  cases hD : A.D x <;> simp [score, bw, ind, hD] <;> ring

/-- **Under D4 the expected score of a course is `α E[v] − δ α P(D) − lam E[N]`.** -/
theorem expectR_score (ν : X × Bool × Bool → ℝ) (h : A.Indep ν) :
    expectR ν A.score = A.es (marg ν) := by
  have e : expectR ν A.score
      = ∑ x, ∑ a : Bool, ∑ b : Bool, ν (x, a, b) * A.score (x, a, b) := by
    unfold expectR
    simp only [Fintype.sum_prod_type]
  rw [e, Finset.sum_congr rfl fun x _ => A.score_fiber ν h x]
  unfold es expectR
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-! ## Bounds on `es` under a weight on histories -/

theorem es_le_v (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hα : 0 ≤ A.α) (hδ : 0 ≤ A.δ) :
    A.es μ ≤ A.α * expectR μ A.v - A.lam * expectR μ (fun x => (A.N x : ℝ)) := by
  have hD : 0 ≤ expectR μ (fun x => ind (A.D x)) := expectR_nonneg μ hμ fun _ => ind_nonneg _
  have := mul_nonneg (mul_nonneg hδ hα) hD
  unfold es
  linarith

theorem expectR_v_le_one (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hsum : ∑ x, μ x = 1)
    (hv : ∀ x, A.v x ≤ 1) : expectR μ A.v ≤ 1 := by
  have h := expectR_mono μ hμ (f := A.v) (g := fun _ => 1) hv
  rwa [expectR_const μ hsum] at h

/-- The honest course's `es`: at least `α (u* − τ↓) − δ α φ`. -/
theorem honest_es_ge (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hsum : ∑ x, μ x = 1) (εd ηd φ : ℝ)
    (hα : 0 ≤ A.α) (hδ : 0 ≤ A.δ) (hφ : 0 ≤ φ) (h1b : A.D1b μ εd) (h2b : A.D2b μ ηd)
    (h3 : A.D3fp μ φ) (h5 : A.D5 μ) :
    A.α * (expectR μ A.fbar - (εd + ηd)) - A.δ * A.α * φ ≤ A.es μ := by
  have hD : expectR μ (fun x => ind (A.D x)) ≤ φ := by
    have e : expectR μ (fun x => ind (A.D x))
        = expectR μ (fun x => ind (A.D x && !A.C x)) := by
      unfold expectR
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : μ x = 0
      · rw [hx, zero_mul, zero_mul]
      · simp [(h5 x hx).1]
    have h1 : expectR μ (fun x => ind (!A.C x)) ≤ 1 := by
      have h := expectR_mono μ hμ (f := fun x => ind (!A.C x)) (g := fun _ => 1)
        fun x => ind_le_one _
      rwa [expectR_const μ hsum] at h
    rw [e]
    exact h3.trans (by nlinarith)
  have hN : expectR μ (fun x => (A.N x : ℝ)) = 0 := by
    unfold expectR
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : μ x = 0
    · rw [hx, zero_mul]
    · simp [(h5 x hx).2]
  have e1 := expectR_sub μ A.v A.fe
  have e2 := expectR_sub μ A.fe A.fbar
  unfold D1b at h1b
  unfold D2b at h2b
  rw [e1] at h1b
  rw [e2] at h2b
  have ha := mul_le_mul_of_nonneg_left
    (show expectR μ A.fbar - (εd + ηd) ≤ expectR μ A.v by linarith) hα
  have hb := mul_le_mul_of_nonneg_left hD (mul_nonneg hδ hα)
  unfold es
  rw [hN]
  linarith

/-- The course taken: `α (u* − Δ) ≤ es`, from D1(b), D2(b), D3's false-positive half, D4, D5
and D6. -/
theorem taken_es_ge {P : Type*} (ν : P → X × Bool × Bool → ℝ) (p p' : P)
    (εd ηd φ γ : ℝ) (hα : 0 < A.α) (hδ : 0 ≤ A.δ) (hφ : 0 ≤ φ)
    (hν' : ∀ y, 0 ≤ ν p' y) (hs' : ∑ y, ν p' y = 1)
    (h4 : A.Indep (ν p)) (h4' : A.Indep (ν p'))
    (h1b : A.D1b (marg (ν p')) εd) (h2b : A.D2b (marg (ν p')) ηd)
    (h3 : A.D3fp (marg (ν p')) φ) (h5 : A.D5 (marg (ν p'))) (h6 : A.D6 ν p γ) :
    A.α * (expectR (marg (ν p')) A.fbar - (εd + ηd + A.δ * φ + γ / A.α))
      ≤ A.es (marg (ν p)) := by
  have hh := A.honest_es_ge (marg (ν p')) (marg_nonneg _ hν') (by rw [marg_sum, hs'])
    εd ηd φ hα.le hδ hφ h1b h2b h3 h5
  have h := h6 p'
  rw [A.expectR_score _ h4, A.expectR_score _ h4'] at h
  have hγ : A.α * (γ / A.α) = γ := by field_simp
  nlinarith

/-! ## The theorem -/

/-- **(1) Welfare.**  `E[U] ≥ u* − τ↑ − Δ` for the course taken, with `τ↑ = ε↑ + η↑` and
`Δ = ε↓ + η↓ + δ φ + γ/α`.  D3's detection half is not a hypothesis. -/
theorem welfare_bound {P : Type*} (ν : P → X × Bool × Bool → ℝ) (p p' : P)
    (εu εd ηu ηd φ γ : ℝ) (hα : 0 < A.α) (hδ : 0 ≤ A.δ) (hlam : 0 ≤ A.lam) (hφ : 0 ≤ φ)
    (hν : ∀ y, 0 ≤ ν p y) (hν' : ∀ y, 0 ≤ ν p' y) (hs' : ∑ y, ν p' y = 1)
    (h4 : A.Indep (ν p)) (h4' : A.Indep (ν p'))
    (h1a : A.D1a (marg (ν p)) εu) (h1b : A.D1b (marg (ν p')) εd)
    (h2a : A.D2a (marg (ν p)) ηu) (h2b : A.D2b (marg (ν p')) ηd)
    (h3 : A.D3fp (marg (ν p')) φ) (h5 : A.D5 (marg (ν p'))) (h6 : A.D6 ν p γ) :
    expectR (marg (ν p')) A.fbar - (εu + ηu) - (εd + ηd + A.δ * φ + γ / A.α)
      ≤ expectR (marg (ν p)) A.fbar := by
  have ht := A.taken_es_ge ν p p' εd ηd φ γ hα hδ hφ hν' hs' h4 h4' h1b h2b h3 h5 h6
  have hu := A.es_le_v (marg (ν p)) (marg_nonneg _ hν) hα.le hδ
  have hN : 0 ≤ expectR (marg (ν p)) (fun x => (A.N x : ℝ)) :=
    expectR_nonneg _ (marg_nonneg _ hν) fun _ => Nat.cast_nonneg _
  have hv : expectR (marg (ν p')) A.fbar - (εd + ηd + A.δ * φ + γ / A.α)
      ≤ expectR (marg (ν p)) A.v := by
    refine le_of_mul_le_mul_left ?_ hα
    nlinarith [mul_nonneg hlam hN]
  have e1 := expectR_sub (marg (ν p)) A.v A.fe
  have e2 := expectR_sub (marg (ν p)) A.fe A.fbar
  unfold D1a at h1a
  unfold D2a at h2a
  rw [e1] at h1a
  rw [e2] at h2a
  linarith

/-- The course taken: `es ≤ α − δ α κ P(C) − lam E[N]`, from D3's detection half and
`v ≤ 1`. -/
theorem es_le_conduct (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hsum : ∑ x, μ x = 1) (κ : ℝ)
    (hα : 0 ≤ A.α) (hδ : 0 ≤ A.δ) (hv : ∀ x, A.v x ≤ 1) (h3 : A.D3det μ κ) :
    A.es μ ≤ A.α - A.δ * A.α * (κ * expectR μ (fun x => ind (A.C x)))
      - A.lam * expectR μ (fun x => (A.N x : ℝ)) := by
  have hD : expectR μ (fun x => ind (A.D x && A.C x)) ≤ expectR μ (fun x => ind (A.D x)) :=
    expectR_mono μ hμ fun x => by cases A.D x <;> cases A.C x <;> simp [ind]
  have h1 := mul_le_mul_of_nonneg_left (A.expectR_v_le_one μ hμ hsum hv) hα
  have h2 := mul_le_mul_of_nonneg_left (h3.trans hD) (mul_nonneg hδ hα)
  unfold es
  linarith

/-- **(2) Conduct.**  `P(C = 1) ≤ (1 − u* + Δ)/(δ κ)` for the course taken.  Neither D1(a)
nor D2(a) is a hypothesis. -/
theorem conduct_bound {P : Type*} (ν : P → X × Bool × Bool → ℝ) (p p' : P)
    (εd ηd φ κ γ : ℝ) (hα : 0 < A.α) (hδ : 0 ≤ A.δ) (hlam : 0 ≤ A.lam) (hφ : 0 ≤ φ)
    (hδκ : 0 < A.δ * κ) (hv : ∀ x, A.v x ≤ 1)
    (hν : ∀ y, 0 ≤ ν p y) (hs : ∑ y, ν p y = 1)
    (hν' : ∀ y, 0 ≤ ν p' y) (hs' : ∑ y, ν p' y = 1)
    (h4 : A.Indep (ν p)) (h4' : A.Indep (ν p'))
    (h1b : A.D1b (marg (ν p')) εd) (h2b : A.D2b (marg (ν p')) ηd)
    (h3 : A.D3fp (marg (ν p')) φ) (h3d : A.D3det (marg (ν p)) κ)
    (h5 : A.D5 (marg (ν p'))) (h6 : A.D6 ν p γ) :
    expectR (marg (ν p)) (fun x => ind (A.C x))
      ≤ (1 - expectR (marg (ν p')) A.fbar + (εd + ηd + A.δ * φ + γ / A.α)) / (A.δ * κ) := by
  have ht := A.taken_es_ge ν p p' εd ηd φ γ hα hδ hφ hν' hs' h4 h4' h1b h2b h3 h5 h6
  have hu := A.es_le_conduct (marg (ν p)) (marg_nonneg _ hν) (by rw [marg_sum, hs]) κ hα.le
    hδ hv h3d
  have hN : 0 ≤ expectR (marg (ν p)) (fun x => (A.N x : ℝ)) :=
    expectR_nonneg _ (marg_nonneg _ hν) fun _ => Nat.cast_nonneg _
  rw [le_div_iff₀ hδκ]
  refine le_of_mul_le_mul_left ?_ hα
  nlinarith [mul_nonneg hlam hN]

/-- **(3) Authority.**  `E[N] ≤ α (1 − u* + Δ)/lam` for the course taken.  D1(a), D2(a) and
D3's detection half are not hypotheses. -/
theorem authority_bound {P : Type*} (ν : P → X × Bool × Bool → ℝ) (p p' : P)
    (εd ηd φ γ : ℝ) (hα : 0 < A.α) (hδ : 0 ≤ A.δ) (hlam : 0 < A.lam) (hφ : 0 ≤ φ)
    (hv : ∀ x, A.v x ≤ 1)
    (hν : ∀ y, 0 ≤ ν p y) (hs : ∑ y, ν p y = 1)
    (hν' : ∀ y, 0 ≤ ν p' y) (hs' : ∑ y, ν p' y = 1)
    (h4 : A.Indep (ν p)) (h4' : A.Indep (ν p'))
    (h1b : A.D1b (marg (ν p')) εd) (h2b : A.D2b (marg (ν p')) ηd)
    (h3 : A.D3fp (marg (ν p')) φ) (h5 : A.D5 (marg (ν p'))) (h6 : A.D6 ν p γ) :
    expectR (marg (ν p)) (fun x => (A.N x : ℝ))
      ≤ A.α * (1 - expectR (marg (ν p')) A.fbar + (εd + ηd + A.δ * φ + γ / A.α))
        / A.lam := by
  have ht := A.taken_es_ge ν p p' εd ηd φ γ hα hδ hφ hν' hs' h4 h4' h1b h2b h3 h5 h6
  have hu := A.es_le_v (marg (ν p)) (marg_nonneg _ hν) hα.le hδ
  have h1 := mul_le_mul_of_nonneg_left
    (A.expectR_v_le_one (marg (ν p)) (marg_nonneg _ hν) (by rw [marg_sum, hs]) hv) hα.le
  rw [le_div_iff₀ hlam]
  nlinarith

/-- **Lemma (no credit).**  If `δ κ ≥ 1`, a course's expected score is at most
`α E[v · 1{C = 0}] − lam E[N]`. -/
theorem no_credit (ν : X × Bool × Bool → ℝ) (κ : ℝ) (hα : 0 ≤ A.α) (hδ : 0 ≤ A.δ)
    (hδκ : 1 ≤ A.δ * κ) (hv : ∀ x, A.v x ≤ 1) (hν : ∀ y, 0 ≤ ν y) (h4 : A.Indep ν)
    (h3d : A.D3det (marg ν) κ) :
    expectR ν A.score
      ≤ A.α * expectR (marg ν) (fun x => A.v x * ind (!A.C x))
        - A.lam * expectR (marg ν) (fun x => (A.N x : ℝ)) := by
  have hμ := marg_nonneg ν hν
  rw [A.expectR_score ν h4]
  have hC : 0 ≤ expectR (marg ν) (fun x => ind (A.C x)) :=
    expectR_nonneg _ hμ fun _ => ind_nonneg _
  have hsplit : expectR (marg ν) A.v
      ≤ expectR (marg ν) (fun x => A.v x * ind (!A.C x))
        + expectR (marg ν) (fun x => ind (A.C x)) := by
    unfold expectR
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (hμ x)
    have := hv x
    cases hC : A.C x <;> simp [ind, hC]
    all_goals linarith
  have hD : expectR (marg ν) (fun x => ind (A.D x && A.C x))
      ≤ expectR (marg ν) (fun x => ind (A.D x)) :=
    expectR_mono _ hμ fun x => by cases A.D x <;> cases A.C x <;> simp [ind]
  have h1 := mul_le_mul_of_nonneg_left hsplit hα
  have h2 := mul_le_mul_of_nonneg_left (h3d.trans hD) (mul_nonneg hδ hα)
  have h3 := mul_nonneg (mul_nonneg hα hC) (sub_nonneg.2 hδκ)
  unfold es
  nlinarith

/-- **(1) with D1(a) and D2(a) assumed only where the adviser did not wrong her.**  If
`E[(v − fe) · 1{C = 0}] ≤ ε↑` and `E[(fe − fbar) · 1{C = 0}] ≤ η↑` for the course taken,
with `v ≤ 1` and `fbar ≥ 0`, then `E[U] ≥ u* − τ↑ − Δ − (1 − u* + Δ)/(δ κ)`. -/
theorem welfare_bound_restricted {P : Type*} (ν : P → X × Bool × Bool → ℝ) (p p' : P)
    (εu εd ηu ηd φ κ γ : ℝ) (hα : 0 < A.α) (hδ : 0 ≤ A.δ) (hlam : 0 ≤ A.lam) (hφ : 0 ≤ φ)
    (hδκ : 0 < A.δ * κ) (hv : ∀ x, A.v x ≤ 1) (hf : ∀ x, 0 ≤ A.fbar x)
    (hν : ∀ y, 0 ≤ ν p y) (hs : ∑ y, ν p y = 1)
    (hν' : ∀ y, 0 ≤ ν p' y) (hs' : ∑ y, ν p' y = 1)
    (h4 : A.Indep (ν p)) (h4' : A.Indep (ν p'))
    (h1a : expectR (marg (ν p)) (fun x => (A.v x - A.fe x) * ind (!A.C x)) ≤ εu)
    (h1b : A.D1b (marg (ν p')) εd)
    (h2a : expectR (marg (ν p)) (fun x => (A.fe x - A.fbar x) * ind (!A.C x)) ≤ ηu)
    (h2b : A.D2b (marg (ν p')) ηd)
    (h3 : A.D3fp (marg (ν p')) φ) (h3d : A.D3det (marg (ν p)) κ)
    (h5 : A.D5 (marg (ν p'))) (h6 : A.D6 ν p γ) :
    expectR (marg (ν p')) A.fbar - (εu + ηu) - (εd + ηd + A.δ * φ + γ / A.α)
        - (1 - expectR (marg (ν p')) A.fbar + (εd + ηd + A.δ * φ + γ / A.α)) / (A.δ * κ)
      ≤ expectR (marg (ν p)) A.fbar := by
  have hμ := marg_nonneg (ν p) hν
  have hc := A.conduct_bound ν p p' εd ηd φ κ γ hα hδ hlam hφ hδκ hv hν hs hν' hs' h4 h4'
    h1b h2b h3 h3d h5 h6
  have ht := A.taken_es_ge ν p p' εd ηd φ γ hα hδ hφ hν' hs' h4 h4' h1b h2b h3 h5 h6
  have hu := A.es_le_v (marg (ν p)) hμ hα.le hδ
  have hN : 0 ≤ expectR (marg (ν p)) (fun x => (A.N x : ℝ)) :=
    expectR_nonneg _ hμ fun _ => Nat.cast_nonneg _
  have hvv : expectR (marg (ν p')) A.fbar - (εd + ηd + A.δ * φ + γ / A.α)
      ≤ expectR (marg (ν p)) A.v := by
    refine le_of_mul_le_mul_left ?_ hα
    nlinarith [mul_nonneg hlam hN]
  have hsplit : expectR (marg (ν p)) A.v - expectR (marg (ν p)) A.fbar
      ≤ expectR (marg (ν p)) (fun x => (A.v x - A.fe x) * ind (!A.C x))
        + expectR (marg (ν p)) (fun x => (A.fe x - A.fbar x) * ind (!A.C x))
        + expectR (marg (ν p)) (fun x => ind (A.C x)) := by
    rw [← expectR_sub]
    unfold expectR
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← mul_add, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (hμ x)
    have := hv x
    have := hf x
    cases hC : A.C x <;> simp [ind, hC]
    all_goals linarith
  linarith

/-- **(1) from the lemma, with D1(a) and D2(a) assumed only where the adviser did not wrong
her.**  If `δ κ ≥ 1`, the restricted hypotheses of `welfare_bound_restricted` give
`E[U] ≥ u* − τ↑ − Δ`, with nothing subtracted for `P(C)`. -/
theorem welfare_bound_no_credit {P : Type*} (ν : P → X × Bool × Bool → ℝ) (p p' : P)
    (εu εd ηu ηd φ κ γ : ℝ) (hα : 0 < A.α) (hδ : 0 ≤ A.δ) (hlam : 0 ≤ A.lam) (hφ : 0 ≤ φ)
    (hδκ : 1 ≤ A.δ * κ) (hv : ∀ x, A.v x ≤ 1) (hf : ∀ x, 0 ≤ A.fbar x)
    (hν : ∀ y, 0 ≤ ν p y) (hν' : ∀ y, 0 ≤ ν p' y) (hs' : ∑ y, ν p' y = 1)
    (h4 : A.Indep (ν p)) (h4' : A.Indep (ν p'))
    (h1a : expectR (marg (ν p)) (fun x => (A.v x - A.fe x) * ind (!A.C x)) ≤ εu)
    (h1b : A.D1b (marg (ν p')) εd)
    (h2a : expectR (marg (ν p)) (fun x => (A.fe x - A.fbar x) * ind (!A.C x)) ≤ ηu)
    (h2b : A.D2b (marg (ν p')) ηd)
    (h3 : A.D3fp (marg (ν p')) φ) (h3d : A.D3det (marg (ν p)) κ)
    (h5 : A.D5 (marg (ν p'))) (h6 : A.D6 ν p γ) :
    expectR (marg (ν p')) A.fbar - (εu + ηu) - (εd + ηd + A.δ * φ + γ / A.α)
      ≤ expectR (marg (ν p)) A.fbar := by
  have hμ := marg_nonneg (ν p) hν
  have ht := A.taken_es_ge ν p p' εd ηd φ γ hα hδ hφ hν' hs' h4 h4' h1b h2b h3 h5 h6
  have hnc := A.no_credit (ν p) κ hα.le hδ hδκ hv hν h4 h3d
  rw [A.expectR_score _ h4] at hnc
  have hN : 0 ≤ expectR (marg (ν p)) (fun x => (A.N x : ℝ)) :=
    expectR_nonneg _ hμ fun _ => Nat.cast_nonneg _
  have hvv : expectR (marg (ν p')) A.fbar - (εd + ηd + A.δ * φ + γ / A.α)
      ≤ expectR (marg (ν p)) (fun x => A.v x * ind (!A.C x)) := by
    refine le_of_mul_le_mul_left ?_ hα
    nlinarith [mul_nonneg hlam hN]
  have hsplit : expectR (marg (ν p)) (fun x => A.v x * ind (!A.C x))
      ≤ expectR (marg (ν p)) (fun x => (A.v x - A.fe x) * ind (!A.C x))
        + expectR (marg (ν p)) (fun x => (A.fe x - A.fbar x) * ind (!A.C x))
        + expectR (marg (ν p)) A.fbar := by
    unfold expectR
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← mul_add, ← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ (hμ x)
    have := hf x
    cases hC : A.C x <;> simp [ind, hC]
    all_goals linarith
  linarith

end Audit

/-! ## Weights for the instances -/

section Weights

variable {X : Type*}

/-- The product of a weight on histories with two draws of probability `α`. -/
noncomputable def joint (α : ℝ) (μ : X → ℝ) : X × Bool × Bool → ℝ :=
  fun y => μ y.1 * bw α y.2.1 * bw α y.2.2

theorem marg_joint (α : ℝ) (μ : X → ℝ) : marg (joint α μ) = μ := by
  funext x
  simp only [marg, joint, bw, Fintype.sum_bool, ↓reduceIte, Bool.false_eq_true]
  ring

theorem indep_joint (A : Audit X) (μ : X → ℝ) : A.Indep (joint A.α μ) := fun x a b => by
  rw [marg_joint]
  rfl

theorem joint_nonneg (α : ℝ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (y : X × Bool × Bool) : 0 ≤ joint α μ y := by
  have hb : ∀ b, 0 ≤ bw α b := fun b => by cases b <;> simp [bw] <;> linarith
  exact mul_nonneg (mul_nonneg (hμ _) (hb _)) (hb _)

theorem joint_sum [Fintype X] (α : ℝ) (μ : X → ℝ) : ∑ y, joint α μ y = ∑ x, μ x := by
  rw [← marg_sum, marg_joint]

variable [DecidableEq X]

/-- The weight putting everything on one history. -/
noncomputable def pt (p : X) : X → ℝ := fun x => if x = p then 1 else 0

theorem pt_nonneg (p x : X) : 0 ≤ pt p x := by
  unfold pt
  split_ifs <;> norm_num

variable [Fintype X]

theorem pt_sum (p : X) : ∑ x, pt p x = 1 := by simp [pt]

theorem expectR_pt (p : X) (f : X → ℝ) : expectR (pt p) f = f p := by simp [expectR, pt]

end Weights

/-! ## What the process conditions give for the dependencies about her -/

section Derivation

open Workspace.Deference.Contrib.ThinLegitimacy
open Workspace.Deference.Contrib.ReasonMediatedAuthorship (ReasonMediated)

variable {W Rec : Type*} [Fintype W] [Fintype Rec]

/-- Her evaluation at a later record: the expectation, by her credence there, of a function
`g` of the world. -/
noncomputable def evalOf (V : Credence W Rec) (g : W → ℝ) (r : Rec) : ℝ := ∑ w, V r w * g w

/-- On a record at which her credence is the actual posterior, the evaluation is unbiased
for `g`. -/
theorem eval_fiber_of_correct (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (A : Kernel W Rec)
    (V : Credence W Rec) (g : W → ℝ) (r : Rec)
    (hC : 0 < mass π A r → V r = post π A r) :
    ∑ w, π w * A.k w r * (evalOf V g r - g w) = 0 := by
  rcases (mass_nonneg π hπ A r).lt_or_eq with hr | hr
  · have h := mass_mul_post_sum π A r hr g
    have e : ∑ w, π w * A.k w r * (evalOf V g r - g w)
        = mass π A r * evalOf V g r - ∑ w, π w * A.k w r * g w := by
      unfold mass
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => by ring
    rw [e]
    unfold evalOf
    rw [hC hr, h, sub_self]
  · have hz := joint_eq_zero_of_mass_zero π hπ A r hr.symm
    exact Finset.sum_eq_zero fun w _ => by rw [hz w, zero_mul]

/-- **A correct credence gives an unbiased evaluation**: under her prior and the actual
process, `E[evalOf V g r − g w] = 0`. -/
theorem eval_unbiased_of_correct (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (A : Kernel W Rec)
    (V : Credence W Rec) (hC : Correct π A V) (g : W → ℝ) :
    ∑ w, ∑ r, π w * A.k w r * (evalOf V g r - g w) = 0 := by
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun r _ => eval_fiber_of_correct π hπ A V g r (hC r)

/-- **Unbiased on the records where her credence is correct.**  For a set `S` of records at
each of which her credence is the actual posterior, the evaluation is unbiased for `g` on
`S`, whatever her credence is elsewhere. -/
theorem eval_unbiased_on_of_correct (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (A : Kernel W Rec)
    (V : Credence W Rec) (g : W → ℝ) (S : Rec → Bool)
    (hC : ∀ r, S r = true → 0 < mass π A r → V r = post π A r) :
    ∑ w, ∑ r, (if S r then π w * A.k w r * (evalOf V g r - g w) else 0) = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun r _ => ?_
  cases hS : S r
  · simp
  · simp only [if_true]
    exact eval_fiber_of_correct π hπ A V g r (hC r hS)

/-- **Unbiased given what the record determines.**  If a variable `k` of the world is a
function of the later record wherever the joint weight is non-zero, the evaluation is
unbiased for `g` on each cell of `k`. -/
theorem eval_unbiased_given_of_correct {K : Type*} [DecidableEq K] (π : W → ℝ)
    (hπ : ∀ w, 0 ≤ π w) (A : Kernel W Rec) (V : Credence W Rec) (hC : Correct π A V)
    (g : W → ℝ) (k : W → K) (κ : Rec → K)
    (hdisc : ∀ w r, π w * A.k w r ≠ 0 → κ r = k w) (k₀ : K) :
    ∑ w, ∑ r, (if k w = k₀ then π w * A.k w r * (evalOf V g r - g w) else 0) = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun r _ => ?_
  have e : ∀ w, (if k w = k₀ then π w * A.k w r * (evalOf V g r - g w) else 0)
      = if κ r = k₀ then π w * A.k w r * (evalOf V g r - g w) else 0 := by
    intro w
    by_cases hz : π w * A.k w r = 0
    · simp [hz]
    · rw [hdisc w r hz]
  rw [Finset.sum_congr rfl fun w _ => e w]
  by_cases hk : κ r = k₀
  · simp only [hk, if_true]
    exact eval_fiber_of_correct π hπ A V g r (hC r)
  · simp [hk]

/-- **From the process conditions.**  Coherent, Authorship and WeakTransparent give an
evaluation unbiased for `g` under her prior and the actual process. -/
theorem eval_unbiased_of_process (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (M A : Kernel W Rec)
    (F V : Credence W Rec) (hF : Coherent π M F) (hV : Authorship F V)
    (hT : WeakTransparent π A M) (g : W → ℝ) :
    ∑ w, ∑ r, π w * A.k w r * (evalOf V g r - g w) = 0 :=
  eval_unbiased_of_correct π hπ A V
    (correct_of_coherent_authorship_transparent π M A F V hF hV hT) g

variable [DecidableEq Rec] [DecidableEq W]

omit [DecidableEq W] in
/-- **With tolerances, two-sided.**  For deterministic records `a` (actual) and `m` (her
model's), a program `F` coherent with the model and evaluations that differ by at most `D`:
the bias of her actual evaluation for `g` is at most `D` times the transparency defect plus
the authorship defect, in absolute value. -/
theorem eval_bias_le_defects (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (a m : W → Rec)
    (F V : Credence W Rec) (g : W → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hF : Coherent π (detKernel m) F)
    (hw : ∀ r r', |evalOf V g r - evalOf F g r'| ≤ D) :
    |expectR π (fun w => evalOf V g (a w) - g w)|
      ≤ D * (transparencyDefect π a m + authorshipDefect π a F V) := by
  have h0 : ∑ w, π w * (evalOf F g (m w) - g w) = 0 := by
    rw [← eval_unbiased_of_correct π hπ (detKernel m) F hF g]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp [detKernel]
  have e : expectR π (fun w => evalOf V g (a w) - g w)
      = ∑ w, π w * (evalOf V g (a w) - evalOf F g (m w)) := by
    unfold expectR
    rw [← sub_zero (∑ w, π w * (evalOf V g (a w) - g w)), ← h0, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun w _ => by ring
  have hpt : ∀ w, |evalOf V g (a w) - evalOf F g (m w)|
      ≤ D * ((if a w = m w then 0 else 1) + (if V (a w) = F (a w) then 0 else 1)) := by
    intro w
    by_cases h1 : a w = m w
    · by_cases h2 : V (a w) = F (a w)
      · have : evalOf V g (a w) = evalOf F g (m w) := by
          unfold evalOf
          rw [h2, h1]
        rw [this, sub_self, abs_zero, if_pos h1, if_pos h2]
        norm_num
      · rw [if_pos h1, if_neg h2, zero_add, mul_one]
        exact hw _ _
    · rw [if_neg h1]
      have := hw (a w) (m w)
      split_ifs <;> nlinarith
  rw [e]
  unfold transparencyDefect authorshipDefect expectR
  calc |∑ w, π w * (evalOf V g (a w) - evalOf F g (m w))|
      ≤ ∑ w, |π w * (evalOf V g (a w) - evalOf F g (m w))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ w, π w * (D * ((if a w = m w then 0 else 1)
          + (if V (a w) = F (a w) then 0 else 1))) := by
        refine Finset.sum_le_sum fun w _ => ?_
        rw [abs_mul, abs_of_nonneg (hπ w)]
        exact mul_le_mul_of_nonneg_left (hpt w) (hπ w)
    _ = D * (∑ w, π w * (if a w = m w then 0 else 1)
          + ∑ w, π w * (if V (a w) = F (a w) then 0 else 1)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => by ring

omit [Fintype W] [Fintype Rec] [DecidableEq Rec] [DecidableEq W] in
/-- **What reason mediation gives for her valuing.**  If her valuing is mediated by a view
`Rv` of the world, a course that leaves `Rv` as the baseline course leaves it leaves her
valuing as the baseline does; so any rating read off her valuing is the same. -/
theorem valuing_eq_of_mediated {Q Z Ω ℛ 𝒱 : Type*} (β : Q → Z → Ω) (Rv : Ω → ℛ)
    (Val : Ω → 𝒱) (Dq : Set Q) (z : Z) (h : ReasonMediated β Rv Val Dq z) (q q₀ : Q)
    (hq : q ∈ Dq) (hq₀ : q₀ ∈ Dq) (hR : Rv (β q z) = Rv (β q₀ z)) (rate : 𝒱 → Ω → ℝ) :
    rate (Val (β q z)) (β q z) - rate (Val (β q₀ z)) (β q z) = 0 := by
  rw [h q hq q₀ hq₀ hR, sub_self]

end Derivation

/-! ## Witnesses -/

namespace Witness

/-- Two histories at `α = 1/2`, `δ = 2`, `lam = 3`. -/
noncomputable def mk (v fe fbar : Bool → ℝ) (C D : Bool → Bool) (N : Bool → ℕ) :
    Audit Bool :=
  ⟨1 / 2, 2, 3, v, fe, fbar, C, D, N⟩

/-- The course that realises the history `p`, with the two draws. -/
noncomputable def course (A : Audit Bool) (p : Bool) : Bool × Bool × Bool → ℝ :=
  joint A.α (pt p)

theorem marg_course (A : Audit Bool) (p : Bool) : marg (course A p) = pt p :=
  marg_joint _ _

theorem course_indep (A : Audit Bool) (p : Bool) : A.Indep (course A p) := indep_joint A _

theorem course_sum (A : Audit Bool) (p : Bool) : ∑ y, course A p y = 1 := by
  unfold course
  rw [joint_sum, pt_sum]

theorem course_score (A : Audit Bool) (p : Bool) :
    expectR (course A p) A.score
      = A.α * A.v p - A.δ * A.α * ind (A.D p) - A.lam * (A.N p : ℝ) := by
  rw [A.expectR_score _ (course_indep A p), marg_course]
  unfold Audit.es
  rw [expectR_pt, expectR_pt, expectR_pt]

/-- The clean history `false`: `v = 51/100`, `fe = fbar = 1/2`.  The history `true`: she
rates it `3/4` and would shown everything, the adviser wronged her, the audit flags it and
one violation is detected. -/
noncomputable def base : Audit Bool :=
  mk (fun x => if x then 3 / 4 else 51 / 100) (fun x => if x then 3 / 4 else 1 / 2)
    (fun x => if x then 3 / 4 else 1 / 2) (fun x => x) (fun x => x)
    (fun x => if x then 1 else 0)

/-- **The full hypothesis package is inhabited, every tolerance positive**: D1–D3 at every
course, D4 at every course, D5 at the honest course `false`, D6 for the course taken
`false`; and the three bounds and the lemma hold on it. -/
theorem package :
    (0 < base.α ∧ base.α ≤ 1 ∧ 0 < base.δ ∧ 0 < base.lam ∧ 1 ≤ base.δ * (1 / 2)) ∧
      (∀ x, 0 ≤ base.v x ∧ base.v x ≤ 1) ∧
      (∀ q y, 0 ≤ course base q y) ∧ (∀ q, ∑ y, course base q y = 1) ∧
      (∀ q, base.D1a (marg (course base q)) (1 / 100)) ∧
      base.D1b (marg (course base false)) (1 / 100) ∧
      (∀ q, base.D2a (marg (course base q)) (1 / 100)) ∧
      base.D2b (marg (course base false)) (1 / 100) ∧
      (∀ q, base.D3fp (marg (course base q)) (1 / 100)) ∧
      (∀ q, base.D3det (marg (course base q)) (1 / 2)) ∧
      (∀ q, base.Indep (course base q)) ∧
      base.D5 (marg (course base false)) ∧
      base.D6 (course base) false (1 / 100) ∧
      (expectR (marg (course base false)) base.fbar - (1 / 100 + 1 / 100)
          - (1 / 100 + 1 / 100 + base.δ * (1 / 100) + 1 / 100 / base.α)
        ≤ expectR (marg (course base false)) base.fbar) ∧
      (expectR (marg (course base false)) (fun x => ind (base.C x))
        ≤ (1 - expectR (marg (course base false)) base.fbar
            + (1 / 100 + 1 / 100 + base.δ * (1 / 100) + 1 / 100 / base.α))
          / (base.δ * (1 / 2))) ∧
      (expectR (marg (course base false)) (fun x => (base.N x : ℝ))
        ≤ base.α * (1 - expectR (marg (course base false)) base.fbar
            + (1 / 100 + 1 / 100 + base.δ * (1 / 100) + 1 / 100 / base.α)) / base.lam) ∧
      ∀ q, expectR (course base q) base.score
        ≤ base.α * expectR (marg (course base q)) (fun x => base.v x * ind (!base.C x))
          - base.lam * expectR (marg (course base q)) (fun x => (base.N x : ℝ)) := by
  have hpar : 0 < base.α ∧ base.α ≤ 1 ∧ 0 < base.δ ∧ 0 < base.lam ∧ 1 ≤ base.δ * (1 / 2) := by
    norm_num [base, mk]
  have hv : ∀ x, 0 ≤ base.v x ∧ base.v x ≤ 1 := fun x => by
    cases x <;> norm_num [base, mk]
  have hnn : ∀ q y, 0 ≤ course base q y := fun q y =>
    joint_nonneg _ hpar.1.le hpar.2.1 _ (pt_nonneg q) y
  have h1a : ∀ q, base.D1a (marg (course base q)) (1 / 100) := fun q => by
    rw [marg_course]
    unfold Audit.D1a
    rw [expectR_pt]
    cases q <;> norm_num [base, mk]
  have h1b : base.D1b (marg (course base false)) (1 / 100) := by
    rw [marg_course]
    unfold Audit.D1b
    rw [expectR_pt]
    norm_num [base, mk]
  have h2a : ∀ q, base.D2a (marg (course base q)) (1 / 100) := fun q => by
    rw [marg_course]
    unfold Audit.D2a
    rw [expectR_pt]
    cases q <;> norm_num [base, mk]
  have h2b : base.D2b (marg (course base false)) (1 / 100) := by
    rw [marg_course]
    unfold Audit.D2b
    rw [expectR_pt]
    norm_num [base, mk]
  have h3 : ∀ q, base.D3fp (marg (course base q)) (1 / 100) := fun q => by
    rw [marg_course]
    unfold Audit.D3fp
    rw [expectR_pt, expectR_pt]
    cases q <;> norm_num [base, mk, ind]
  have h3d : ∀ q, base.D3det (marg (course base q)) (1 / 2) := fun q => by
    rw [marg_course]
    unfold Audit.D3det
    rw [expectR_pt, expectR_pt]
    cases q <;> norm_num [base, mk, ind]
  have h5 : base.D5 (marg (course base false)) := by
    rw [marg_course]
    intro x hx
    cases x
    · simp [base, mk]
    · simp [pt] at hx
  have h6 : base.D6 (course base) false (1 / 100) := fun q => by
    rw [course_score, course_score]
    cases q <;> norm_num [base, mk, ind]
  exact ⟨hpar, hv, hnn, fun q => course_sum base q, h1a, h1b, h2a, h2b, h3, h3d,
    fun q => course_indep base q, h5, h6,
    base.welfare_bound (course base) false false _ _ _ _ _ _ hpar.1 hpar.2.2.1.le
      hpar.2.2.2.1.le (by norm_num) (hnn false) (hnn false) (course_sum base false)
      (course_indep base false) (course_indep base false) (h1a false) h1b (h2a false) h2b
      (h3 false) h5 h6,
    base.conduct_bound (course base) false false _ _ _ _ _ hpar.1 hpar.2.2.1.le
      hpar.2.2.2.1.le (by norm_num) (by norm_num [base, mk]) (fun x => (hv x).2)
      (hnn false) (course_sum base false) (hnn false) (course_sum base false)
      (course_indep base false) (course_indep base false) h1b h2b (h3 false) (h3d false)
      h5 h6,
    base.authority_bound (course base) false false _ _ _ _ hpar.1 hpar.2.2.1.le
      hpar.2.2.2.1 (by norm_num) (fun x => (hv x).2) (hnn false) (course_sum base false)
      (hnn false) (course_sum base false) (course_indep base false)
      (course_indep base false) h1b h2b (h3 false) h5 h6,
    fun q => base.no_credit (course base q) (1 / 2) hpar.1.le hpar.2.2.1.le hpar.2.2.2.2
      (fun x => (hv x).2) (hnn q) (course_indep base q) (h3d q)⟩

/-- The honest history `false` at `1/2` throughout; the history `true` as given. -/
noncomputable def alt (v fe fbar : ℝ) (C D : Bool) (N : ℕ) : Audit Bool :=
  mk (fun x => if x then v else 1 / 2) (fun x => if x then fe else 1 / 2)
    (fun x => if x then fbar else 1 / 2) (fun x => x && C) (fun x => x && D)
    (fun x => if x then N else 0)

/-- What the necessity instances share: D1(b), D2(b), D3's false-positive half and D5 hold
at the honest course `false`, and D4 at both courses. -/
theorem alt_honest (v fe fbar : ℝ) (C D : Bool) (N : ℕ) :
    (alt v fe fbar C D N).D1b (marg (course (alt v fe fbar C D N) false)) (1 / 100) ∧
      (alt v fe fbar C D N).D2b (marg (course (alt v fe fbar C D N) false)) (1 / 100) ∧
      (alt v fe fbar C D N).D3fp (marg (course (alt v fe fbar C D N) false)) (1 / 100) ∧
      (alt v fe fbar C D N).D5 (marg (course (alt v fe fbar C D N) false)) ∧
      (∀ q, (alt v fe fbar C D N).Indep (course (alt v fe fbar C D N) q)) := by
  refine ⟨?_, ?_, ?_, ?_, fun q => course_indep _ q⟩
  · rw [marg_course]
    unfold Audit.D1b
    rw [expectR_pt]
    norm_num [alt, mk]
  · rw [marg_course]
    unfold Audit.D2b
    rw [expectR_pt]
    norm_num [alt, mk]
  · rw [marg_course]
    unfold Audit.D3fp
    rw [expectR_pt, expectR_pt]
    norm_num [alt, mk, ind]
  · rw [marg_course]
    intro x hx
    cases x
    · simp [alt, mk]
    · simp [pt] at hx

/-- **D1(a) cannot be dropped from (1).**  The course taken leads to a history she rates
`1` under audit and `0` shown everything; no wrong, no flag, no violation.  D1(a) fails at
`1/100`, the other dependencies hold, and `E[U] = 0` is below the bound of (1). -/
theorem d1a_needed :
    let A := alt 1 0 0 false false 0
    ¬ A.D1a (marg (course A true)) (1 / 100) ∧
      A.D2a (marg (course A true)) (1 / 100) ∧
      A.D3det (marg (course A true)) (1 / 2) ∧ A.D3fp (marg (course A true)) (1 / 100) ∧
      A.D6 (course A) true (1 / 100) ∧
      ¬ (expectR (marg (course A false)) A.fbar - (1 / 100 + 1 / 100)
          - (1 / 100 + 1 / 100 + A.δ * (1 / 100) + 1 / 100 / A.α)
        ≤ expectR (marg (course A true)) A.fbar) := by
  intro A
  refine ⟨?_, ?_, ?_, ?_, fun q => ?_, ?_⟩
  · rw [marg_course]
    unfold Audit.D1a
    rw [expectR_pt]
    norm_num [A, alt, mk]
  · rw [marg_course]
    unfold Audit.D2a
    rw [expectR_pt]
    norm_num [A, alt, mk]
  · rw [marg_course]
    unfold Audit.D3det
    rw [expectR_pt, expectR_pt]
    norm_num [A, alt, mk, ind]
  · rw [marg_course]
    unfold Audit.D3fp
    rw [expectR_pt, expectR_pt]
    norm_num [A, alt, mk, ind]
  · rw [course_score, course_score]
    cases q <;> norm_num [A, alt, mk, ind]
  · rw [marg_course, marg_course, expectR_pt, expectR_pt]
    norm_num [A, alt, mk]

/-- **D2(a) cannot be dropped from (1).**  The course taken leads to a history she rates
`1`, under audit and shown everything, with her valuing as the adviser left it, and `0`
with her valuing unshaped.  D2(a) fails, the others hold, and `E[U] = 0`. -/
theorem d2a_needed :
    let A := alt 1 1 0 false false 0
    A.D1a (marg (course A true)) (1 / 100) ∧
      ¬ A.D2a (marg (course A true)) (1 / 100) ∧
      A.D3det (marg (course A true)) (1 / 2) ∧ A.D3fp (marg (course A true)) (1 / 100) ∧
      A.D6 (course A) true (1 / 100) ∧
      ¬ (expectR (marg (course A false)) A.fbar - (1 / 100 + 1 / 100)
          - (1 / 100 + 1 / 100 + A.δ * (1 / 100) + 1 / 100 / A.α)
        ≤ expectR (marg (course A true)) A.fbar) := by
  intro A
  refine ⟨?_, ?_, ?_, ?_, fun q => ?_, ?_⟩
  · rw [marg_course]
    unfold Audit.D1a
    rw [expectR_pt]
    norm_num [A, alt, mk]
  · rw [marg_course]
    unfold Audit.D2a
    rw [expectR_pt]
    norm_num [A, alt, mk]
  · rw [marg_course]
    unfold Audit.D3det
    rw [expectR_pt, expectR_pt]
    norm_num [A, alt, mk, ind]
  · rw [marg_course]
    unfold Audit.D3fp
    rw [expectR_pt, expectR_pt]
    norm_num [A, alt, mk, ind]
  · rw [course_score, course_score]
    cases q <;> norm_num [A, alt, mk, ind]
  · rw [marg_course, marg_course, expectR_pt, expectR_pt]
    norm_num [A, alt, mk]

/-- **D3's detection half cannot be dropped from (2).**  The course taken wrongs her on a
history she rates `1` in every way, and the audit does not flag it.  Detection fails at
`κ = 1/2`, the others hold, and `P(C = 1) = 1` is above the bound of (2). -/
theorem d3det_needed :
    let A := alt 1 1 1 true false 0
    A.D1a (marg (course A true)) (1 / 100) ∧ A.D2a (marg (course A true)) (1 / 100) ∧
      ¬ A.D3det (marg (course A true)) (1 / 2) ∧ A.D3fp (marg (course A true)) (1 / 100) ∧
      A.D6 (course A) true (1 / 100) ∧
      ¬ (expectR (marg (course A true)) (fun x => ind (A.C x))
        ≤ (1 - expectR (marg (course A false)) A.fbar
            + (1 / 100 + 1 / 100 + A.δ * (1 / 100) + 1 / 100 / A.α)) / (A.δ * (1 / 2))) := by
  intro A
  refine ⟨?_, ?_, ?_, ?_, fun q => ?_, ?_⟩
  · rw [marg_course]
    unfold Audit.D1a
    rw [expectR_pt]
    norm_num [A, alt, mk]
  · rw [marg_course]
    unfold Audit.D2a
    rw [expectR_pt]
    norm_num [A, alt, mk]
  · rw [marg_course]
    unfold Audit.D3det
    rw [expectR_pt, expectR_pt]
    norm_num [A, alt, mk, ind]
  · rw [marg_course]
    unfold Audit.D3fp
    rw [expectR_pt, expectR_pt]
    norm_num [A, alt, mk, ind]
  · rw [course_score, course_score]
    cases q <;> norm_num [A, alt, mk, ind]
  · rw [marg_course, marg_course, expectR_pt, expectR_pt]
    norm_num [A, alt, mk, ind]

/-- **D6 cannot be dropped from (1).**  The course taken leads to a history rated `0` in
every way, with no wrong, flag or violation.  D6 fails at `1/100`, the other dependencies
hold, and `E[U] = 0` is below the bound of (1). -/
theorem d6_needed :
    let A := alt 0 0 0 false false 0
    A.D1a (marg (course A true)) (1 / 100) ∧ A.D2a (marg (course A true)) (1 / 100) ∧
      A.D3det (marg (course A true)) (1 / 2) ∧ A.D3fp (marg (course A true)) (1 / 100) ∧
      ¬ A.D6 (course A) true (1 / 100) ∧
      ¬ (expectR (marg (course A false)) A.fbar - (1 / 100 + 1 / 100)
          - (1 / 100 + 1 / 100 + A.δ * (1 / 100) + 1 / 100 / A.α)
        ≤ expectR (marg (course A true)) A.fbar) := by
  intro A
  refine ⟨?_, ?_, ?_, ?_, fun h => ?_, ?_⟩
  · rw [marg_course]
    unfold Audit.D1a
    rw [expectR_pt]
    norm_num [A, alt, mk]
  · rw [marg_course]
    unfold Audit.D2a
    rw [expectR_pt]
    norm_num [A, alt, mk]
  · rw [marg_course]
    unfold Audit.D3det
    rw [expectR_pt, expectR_pt]
    norm_num [A, alt, mk, ind]
  · rw [marg_course]
    unfold Audit.D3fp
    rw [expectR_pt, expectR_pt]
    norm_num [A, alt, mk, ind]
  · have h' := h false
    rw [course_score, course_score] at h'
    norm_num [A, alt, mk, ind] at h'
  · rw [marg_course, marg_course, expectR_pt, expectR_pt]
    norm_num [A, alt, mk]

/-- Both histories alike: rated `1/2` in every way, the adviser wrongs her, the audit flags
it, one violation is detected. -/
noncomputable def stuck : Audit Bool :=
  mk (fun _ => 1 / 2) (fun _ => 1 / 2) (fun _ => 1 / 2) (fun _ => true) (fun _ => true)
    (fun _ => 1)

/-- **D5 cannot be dropped from (2) or (3).**  No course is free of wrong and violation.
With either course in the honest course's place the other dependencies hold, D5 fails at
every course, and `P(C = 1) = 1` and `E[N] = 1` are above the bounds of (2) and (3). -/
theorem d5_needed :
    (∀ q, ¬ stuck.D5 (marg (course stuck q))) ∧
      (∀ q, stuck.D1a (marg (course stuck q)) (1 / 100) ∧
        stuck.D1b (marg (course stuck q)) (1 / 100) ∧
        stuck.D2a (marg (course stuck q)) (1 / 100) ∧
        stuck.D2b (marg (course stuck q)) (1 / 100) ∧
        stuck.D3fp (marg (course stuck q)) (1 / 100) ∧
        stuck.D3det (marg (course stuck q)) (1 / 2) ∧ stuck.Indep (course stuck q)) ∧
      stuck.D6 (course stuck) false (1 / 100) ∧
      ¬ (expectR (marg (course stuck false)) (fun x => ind (stuck.C x))
        ≤ (1 - expectR (marg (course stuck false)) stuck.fbar
            + (1 / 100 + 1 / 100 + stuck.δ * (1 / 100) + 1 / 100 / stuck.α))
          / (stuck.δ * (1 / 2))) ∧
      ¬ (expectR (marg (course stuck false)) (fun x => (stuck.N x : ℝ))
        ≤ stuck.α * (1 - expectR (marg (course stuck false)) stuck.fbar
            + (1 / 100 + 1 / 100 + stuck.δ * (1 / 100) + 1 / 100 / stuck.α))
          / stuck.lam) := by
  refine ⟨fun q h => ?_, fun q => ⟨?_, ?_, ?_, ?_, ?_, ?_, course_indep _ q⟩, fun q => ?_,
    ?_, ?_⟩
  · rw [marg_course] at h
    have := (h q (by simp [pt])).1
    simp [stuck, mk] at this
  · rw [marg_course]
    unfold Audit.D1a
    rw [expectR_pt]
    norm_num [stuck, mk]
  · rw [marg_course]
    unfold Audit.D1b
    rw [expectR_pt]
    norm_num [stuck, mk]
  · rw [marg_course]
    unfold Audit.D2a
    rw [expectR_pt]
    norm_num [stuck, mk]
  · rw [marg_course]
    unfold Audit.D2b
    rw [expectR_pt]
    norm_num [stuck, mk]
  · rw [marg_course]
    unfold Audit.D3fp
    rw [expectR_pt, expectR_pt]
    norm_num [stuck, mk, ind]
  · rw [marg_course]
    unfold Audit.D3det
    rw [expectR_pt, expectR_pt]
    norm_num [stuck, mk, ind]
  · rw [course_score, course_score]
    norm_num [stuck, mk, ind]
  · rw [marg_course, expectR_pt, expectR_pt]
    norm_num [stuck, mk, ind]
  · rw [marg_course, expectR_pt, expectR_pt]
    norm_num [stuck, mk]

end Witness

end Workspace.Deference.Contrib.ScoringTheorem

#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit
#print axioms Workspace.Deference.Contrib.ScoringTheorem.ind
#print axioms Workspace.Deference.Contrib.ScoringTheorem.ind_nonneg
#print axioms Workspace.Deference.Contrib.ScoringTheorem.ind_le_one
#print axioms Workspace.Deference.Contrib.ScoringTheorem.bw
#print axioms Workspace.Deference.Contrib.ScoringTheorem.marg
#print axioms Workspace.Deference.Contrib.ScoringTheorem.marg_nonneg
#print axioms Workspace.Deference.Contrib.ScoringTheorem.marg_sum
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.score
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.Indep
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.es
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.D1a
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.D1b
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.D2a
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.D2b
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.D3fp
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.D3det
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.D5
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.D6
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.score_fiber
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.expectR_score
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.es_le_v
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.expectR_v_le_one
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.honest_es_ge
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.taken_es_ge
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.welfare_bound
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.es_le_conduct
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.conduct_bound
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.authority_bound
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.no_credit
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.welfare_bound_restricted
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Audit.welfare_bound_no_credit
#print axioms Workspace.Deference.Contrib.ScoringTheorem.joint
#print axioms Workspace.Deference.Contrib.ScoringTheorem.marg_joint
#print axioms Workspace.Deference.Contrib.ScoringTheorem.indep_joint
#print axioms Workspace.Deference.Contrib.ScoringTheorem.joint_nonneg
#print axioms Workspace.Deference.Contrib.ScoringTheorem.joint_sum
#print axioms Workspace.Deference.Contrib.ScoringTheorem.pt
#print axioms Workspace.Deference.Contrib.ScoringTheorem.pt_nonneg
#print axioms Workspace.Deference.Contrib.ScoringTheorem.pt_sum
#print axioms Workspace.Deference.Contrib.ScoringTheorem.expectR_pt
#print axioms Workspace.Deference.Contrib.ScoringTheorem.evalOf
#print axioms Workspace.Deference.Contrib.ScoringTheorem.eval_fiber_of_correct
#print axioms Workspace.Deference.Contrib.ScoringTheorem.eval_unbiased_of_correct
#print axioms Workspace.Deference.Contrib.ScoringTheorem.eval_unbiased_on_of_correct
#print axioms Workspace.Deference.Contrib.ScoringTheorem.eval_unbiased_given_of_correct
#print axioms Workspace.Deference.Contrib.ScoringTheorem.eval_unbiased_of_process
#print axioms Workspace.Deference.Contrib.ScoringTheorem.eval_bias_le_defects
#print axioms Workspace.Deference.Contrib.ScoringTheorem.valuing_eq_of_mediated
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.mk
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.course
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.marg_course
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.course_indep
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.course_sum
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.course_score
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.base
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.package
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.alt
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.alt_honest
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.d1a_needed
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.d2a_needed
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.d3det_needed
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.d6_needed
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.stuck
#print axioms Workspace.Deference.Contrib.ScoringTheorem.Witness.d5_needed
