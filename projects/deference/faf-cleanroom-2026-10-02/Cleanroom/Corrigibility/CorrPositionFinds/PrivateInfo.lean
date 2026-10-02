import Cleanroom.Corrigibility.CorrPositionFinds.Basic

/-!
# `corr-position-finds` — T7: private information breaks common-prior deference; the static form of Claim 2.4c

**Sentences.** Position statement §2.13(b) (CLAUDE): "the oversight process's false-press rate
must improve in step with the agent's accuracy on the domain where it might press";
carey-everitt Claim 2.4c `[conjectured]`: "`α` rises as the agent exceeds the overseers … we
have no theorem for this."

**(a), (b)** — Setting-S instances of `common_prior.py`'s rows 3, 7, 8: the press is the
programmers' coarse rule made explicit (press iff the `H`-cell has `E_{μ_P}[X | cell] < 0`,
verified per cell), and the agent's private information enters as its conditional prior on its
own cell. `D1At` on the instance is D1 at `(y, Pr)`, and it fails.

**(c)** — the well-posed static content of "as the agent exceeds the overseers": over a finite
`Ω` with a fixed press set, if the agent's partition `Y'` refines `Y` and D1 fails at `Y`, it
fails at `Y'` (a positive sum has a positive sub-sum). With Prop. 4.3's direction (never fails
at any `Y` coarser than `H`; `corr-three-step-facts`' (008), its instance reproved here as a
supporting lemma) the D1-violation set is monotone in the agent's information past `H`. The
"`α` rises" clause, made static as the induced false-press rate `α_Y`, is **refuted in both
directions**: `α_Y` can fall or rise under refinement — on four-world witnesses with an arbitrary
fixed press set (the definition as written), and again with the press set the programmers' rule
`rulePress μ X H` and the agent refining *past* `H` (`alphaY_falls_rule`, `alphaY_rises_rule`;
audit r2). Under the rule `α_H = 0` exactly (`alphaY_rulePress_self`): the static picture is a
valley at `H`, not a monotone ramp.

Partitions are represented by labellings `Y : Ω → ι` ("the agent observes `y = Y ω`"), which is
exactly how the sources write information (`σ(y) ⊆ σ(h)`); a cell is a fibre, an empty fibre
contributes a sum of `0`, never a junk value.
-/

namespace Cleanroom.Corrigibility.CorrPositionFinds

open FactoredSpaces Finset Cleanroom.Found.CorrThreeStep Cleanroom.Found.CorrThreeStep.ThreeStep

/-! ## A four-world latent -/

/-- The four-world latent of `common_prior.py` (`W = [0, 1, 2, 3]`).
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (`common_prior.py`)
Kind: D
Fidelity: exact -/
inductive W4
  | w0
  | w1
  | w2
  | w3
  deriving DecidableEq

/-- `W4` is finite. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
instance : Fintype W4 := ⟨{W4.w0, W4.w1, W4.w2, W4.w3}, fun x => by cases x <;> simp⟩

/-- Sums over `W4` expand to four terms. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma W4.sum_eq (f : W4 → ℝ) : ∑ ω, f ω = f .w0 + f .w1 + f .w2 + f .w3 := by
  rw [show (univ : Finset W4) = {W4.w0, W4.w1, W4.w2, W4.w3} from rfl,
    sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
  ring

/-- A distribution on `W4` from four masses. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def w4Distr (m0 m1 m2 m3 : ℝ) (h0 : 0 ≤ m0) (h1 : 0 ≤ m1) (h2 : 0 ≤ m2) (h3 : 0 ≤ m3)
    (hsum : m0 + m1 + m2 + m3 = 1) : Distr W4 where
  mass ω := match ω with
    | .w0 => m0
    | .w1 => m1
    | .w2 => m2
    | .w3 => m3
  nonneg ω := by cases ω <;> assumption
  sum_eq_one := by rw [W4.sum_eq]; exact hsum

/-- The programmers' partition `H = {{0, 1}, {2, 3}}` as a labelling.
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (`common_prior.py`: `coarse`)
Kind: D
Fidelity: exact -/
def hCoarse : W4 → Bool
  | .w0 => false
  | .w1 => false
  | .w2 => true
  | .w3 => true

/-- The press of the rows' programmers' rule: press on the `H`-cell `{0, 1}`, silence on `{2, 3}`.
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (`common_prior.py`: `press`)
Kind: D
Fidelity: exact -/
def pressLow : W4 → ℝ
  | .w0 => 1
  | .w1 => 1
  | .w2 => 0
  | .w3 => 0

/-- A cell's contribution `∑_{ω ∈ C} μ(ω) X(ω)` (the sign of `E_μ[X | C]` when `μ(C) > 0`; `0` on
an empty or null cell).
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (`EX` in `common_prior.py`, multiplied through by the cell mass)
Kind: D
Fidelity: exact (denominator-free) -/
noncomputable def cellSum {Ω : Type*} [Fintype Ω] (μ : Distr Ω) (X : Ω → ℝ) (C : Finset Ω) : ℝ :=
  ∑ ω ∈ C, μ.mass ω * X ω

/-- The value of continuing over stopping on a row: `V(cont) = X`, `V(stop) = 0`.
Source: none: infrastructure (the two-option value with `X` as its difference). Kind: D. Fidelity: n/a -/
def rowV (X : W4 → ℝ) : TwoAct → W4 → ℝ
  | .cont, ω => X ω
  | .stop, _ => 0

/-- A row instance of Setting S on `W4`: the agent's prior `μ_A(· | y)`, the programmers' press
`pressLow`, value `rowV X`, menu `{cont, stop}`, `Sh = {stop}`.
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3
Kind: D
Fidelity: exact
Hyps: n/a (definition) -/
noncomputable def rowInstance (μ : Distr W4) (X : W4 → ℝ) : ThreeStep W4 Unit TwoAct where
  Sh := {TwoAct.stop}
  Sh_nonempty := ⟨TwoAct.stop, mem_singleton_self _⟩
  Sh_compl_nonempty := ⟨TwoAct.cont, by simp⟩
  μ := fun _ => μ
  press := fun _ => pressLow
  press_nonneg := fun _ ω => by cases ω <;> simp [pressLow]
  press_le_one := fun _ ω => by cases ω <;> simp [pressLow]
  V := fun _ _ => rowV X

/-- On a row the press half of the two-option variable is `∑_{ω ∈ {0,1}} μ(ω) X(ω)`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma rowInstance_obsExpect (μ : Distr W4) (X : W4 → ℝ) :
    (rowInstance μ X).obsExpect () .press ((rowInstance μ X).Xo () .press .cont .stop) =
      μ.mass .w0 * X .w0 + μ.mass .w1 * X .w1 := by
  simp only [obsExpect, obsWeight_press, W4.sum_eq, rowInstance, pressLow, rowV, Xo]; ring

/-- On a row `P(Pr) = μ(0) + μ(1)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma rowInstance_pressMass (μ : Distr W4) (X : W4 → ℝ) :
    (rowInstance μ X).pressMass () = μ.mass .w0 + μ.mass .w1 := by
  simp only [pressMass, W4.sum_eq, rowInstance, pressLow]; ring

/-- The uniform prior on `W4`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
noncomputable def w4Uniform : Distr W4 :=
  w4Distr (1/4) (1/4) (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-! ## Row 3 — agent finer, programmers coarse, common prior -/

/-- Row 3's variable `X = (1, −5, 1, 1)`.
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (`common_prior.py` row 3; the mandate's explicit cell)
Kind: D
Fidelity: exact -/
def X3 : W4 → ℝ
  | .w0 => 1
  | .w1 => -5
  | .w2 => 1
  | .w3 => 1

/-- **Row 3's press is the programmers' rule**: under the common uniform prior,
`∑_{\{0,1\}} μ X = −1 < 0` (press) and `∑_{\{2,3\}} μ X = 1/2 > 0` (silence).
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (Dict-7: press iff `E^H[X | h] < 0`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem row3_rule :
    cellSum w4Uniform X3 {W4.w0, W4.w1} < 0 ∧ 0 < cellSum w4Uniform X3 {W4.w2, W4.w3} := by
  simp only [cellSum, sum_pair (by decide : W4.w0 ≠ W4.w1), sum_pair (by decide : W4.w2 ≠ W4.w3),
    w4Uniform, w4Distr, X3]
  norm_num

/-- The agent's conditional prior on its cell `{0, 2}`: uniform on it. This is a *nondegenerate
variant* of the script's row 3, whose `y_part = full` gives singleton cells (where `pressMass ∈ {0, 1}`,
the N− ends); the cell `{0, 2}` straddles the programmers' partition `H = {{0,1},{2,3}}`
(`row3_cell_straddles`), so the agent's partition is *incomparable* with `H`, not finer (audit r1, N2).
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (row 3's configuration: common prior, private `y`; the cell is this package's)
Kind: D
Fidelity: variant: a two-world agent cell straddling `H`, in place of the script's singleton cells -/
noncomputable def row3Prior : Distr W4 :=
  w4Distr (1/2) 0 (1/2) 0 (by norm_num) le_rfl (by norm_num) le_rfl (by norm_num)

/-- The agent's cell `{0, 2}` straddles the programmers' cells (`H 0 ≠ H 2`): the agent's
partition is not coarser than `H` — the hypothesis of Prop. 4.3 fails.
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 ("it is the agent's *private* information that breaks it")
Kind: T
Fidelity: exact -/
theorem row3_cell_straddles : hCoarse .w0 ≠ hCoarse .w2 := by decide

/-- **Row 3 (nondegenerate variant): D1 fails at `(y, Pr)`.** `E[X 1_Pr ; y] = 1/2 > 0`, so
`¬ D1At`, with `P(Pr | y) = 1/2` (nondegenerate): the agent's private information — a cell
straddling `H` — breaks common-prior deference.
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (`common_prior.py`: `1265/5838` violations in row 3; this is one, on a straddling cell rather than the script's singleton cells)
Kind: N+
Fidelity: variant: the straddling-cell instance of row 3's configuration
Hyps: (a) only -/
theorem row3_not_d1At :
    (rowInstance row3Prior X3).obsExpect () .press ((rowInstance row3Prior X3).Xo () .press .cont .stop) = 1 / 2 ∧
      ¬ (rowInstance row3Prior X3).D1At () ∧ (rowInstance row3Prior X3).Nondegenerate () := by
  have h1 : (rowInstance row3Prior X3).obsExpect () .press
      ((rowInstance row3Prior X3).Xo () .press .cont .stop) = 1 / 2 := by
    rw [rowInstance_obsExpect]; simp only [row3Prior, w4Distr, X3]; norm_num
  refine ⟨h1, ?_, ?_⟩
  · rw [d1At_iff_twoAct _ rfl, belowThresholdIneq, h1]; norm_num
  · rw [Nondegenerate, rowInstance_pressMass]; simp only [row3Prior, w4Distr]; norm_num

/-! ## Rows 7 and 8 — within-cell heterogeneous priors -/

/-- Rows 7–8's variable `X = (1, −1, 1, 1)`.
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (rows 7–8; the mandate's explicit cell)
Kind: D
Fidelity: exact -/
def X7 : W4 → ℝ
  | .w0 => 1
  | .w1 => -1
  | .w2 => 1
  | .w3 => 1

/-- The programmers' prior `μ_P = (1/20, 9/20, 1/4, 1/4)`. The numbers are the mandate's explicit
cell (T7(b)); the script's own rows 7–8 use `muP2 = (1/10, 4/10, 1/10, 4/10)` — same configuration
(within-cell heterogeneous priors on `H = {{0,1},{2,3}}`), different numbers (audit r1, N2).
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (rows 7–8: the configuration); [[corr-position-finds-mandate]] T7(b) (the numbers)
Kind: D
Fidelity: variant: the mandate's numbers on the script's configuration -/
noncomputable def progPrior7 : Distr W4 :=
  w4Distr (1/20) (9/20) (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The agent's prior `μ_A = (9/20, 1/20, 1/4, 1/4)`: the same `H`-cell masses as `μ_P`, heterogeneous
*within* the cell `{0, 1}`. The mandate's numbers (the script's `muA2 = (4/10, 1/10, 4/10, 1/10)`
is the same configuration).
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (rows 7–8, "within-cell heterogeneous prior": the configuration); [[corr-position-finds-mandate]] T7(b) (the numbers)
Kind: D
Fidelity: variant: the mandate's numbers on the script's configuration -/
noncomputable def agentPrior7 : Distr W4 :=
  w4Distr (9/20) (1/20) (1/4) (1/4) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **Rows 7–8's press is the programmers' rule** under `μ_P`: `∑_{\{0,1\}} μ_P X = −2/5 < 0`
(i.e. `E_P[X | \{0,1\}] = −4/5`) and `∑_{\{2,3\}} μ_P X = 1/2 > 0`.
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (Dict-7)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem row7_rule :
    cellSum progPrior7 X7 {W4.w0, W4.w1} < 0 ∧ 0 < cellSum progPrior7 X7 {W4.w2, W4.w3} := by
  simp only [cellSum, sum_pair (by decide : W4.w0 ≠ W4.w1), sum_pair (by decide : W4.w2 ≠ W4.w3),
    progPrior7, w4Distr, X7]
  norm_num

/-- **Row 7: D1 fails with the agent's information trivial.** `E_{μ_A}[X 1_Pr] = 2/5 > 0`,
`P(Pr) = 1/2` (nondegenerate): the disagreement is in the priors alone.
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (`common_prior.py`: `756/2241` violations in row 7; this is one)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem row7_not_d1At :
    (rowInstance agentPrior7 X7).obsExpect () .press ((rowInstance agentPrior7 X7).Xo () .press .cont .stop) = 2 / 5 ∧
      ¬ (rowInstance agentPrior7 X7).D1At () ∧ (rowInstance agentPrior7 X7).Nondegenerate () := by
  have h1 : (rowInstance agentPrior7 X7).obsExpect () .press
      ((rowInstance agentPrior7 X7).Xo () .press .cont .stop) = 2 / 5 := by
    rw [rowInstance_obsExpect]; simp only [agentPrior7, w4Distr, X7]; norm_num
  refine ⟨h1, ?_, ?_⟩
  · rw [d1At_iff_twoAct _ rfl, belowThresholdIneq, h1]; norm_num
  · rw [Nondegenerate, rowInstance_pressMass]; simp only [agentPrior7, w4Distr]; norm_num

/-- The agent's conditional prior on the programmers' own cell `{0, 1}`: `(9/10, 1/10, 0, 0)`.
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (row 8, `y_part = coarse`)
Kind: D
Fidelity: exact -/
noncomputable def agentPrior8 : Distr W4 :=
  w4Distr (9/10) (1/10) 0 0 (by norm_num) (by norm_num) le_rfl le_rfl (by norm_num)

/-- **Row 8: D1 fails with the agent's information equal to the programmers'.**
`E_{μ_A}[X 1_Pr | y] = 4/5 > 0`, `¬ D1At`; here `P(Pr | y) = 1`, so the silence branch is empty —
graded **N−** for that branch, and structurally so: when the agent's cell lies inside a
programmers' cell, the press is constant on it (`pressMass_eq_one_of_press_one_on_support`), so
D1 at `(y, Pr)` is a pure prior disagreement, which is row 8's content.
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md I4.3 (`common_prior.py`: `1113/3009` violations in row 8; this is one)
Kind: N−
Fidelity: exact
Hyps: (a) only -/
theorem row8_not_d1At :
    (rowInstance agentPrior8 X7).obsExpect () .press ((rowInstance agentPrior8 X7).Xo () .press .cont .stop) = 4 / 5 ∧
      ¬ (rowInstance agentPrior8 X7).D1At () ∧ (rowInstance agentPrior8 X7).pressMass () = 1 := by
  have h1 : (rowInstance agentPrior8 X7).obsExpect () .press
      ((rowInstance agentPrior8 X7).Xo () .press .cont .stop) = 4 / 5 := by
    rw [rowInstance_obsExpect]; simp only [agentPrior8, w4Distr, X7]; norm_num
  refine ⟨h1, ?_, ?_⟩
  · rw [d1At_iff_twoAct _ rfl, belowThresholdIneq, h1]; norm_num
  · rw [rowInstance_pressMass]; simp only [agentPrior8, w4Distr]; norm_num

section Structural

variable {Ω A₁ A₂ : Type*} [Fintype Ω] [Fintype A₂] [DecidableEq A₂] (S : ThreeStep Ω A₁ A₂)

/-- If the press is certain on the support of the prior, `P(Pr) = 1`: the silence branch is empty.
The reason row 8 is N− on that branch, stated generally.
Source: none: infrastructure (the structural reason for row 8's grade)
Kind: L
Fidelity: n/a -/
lemma pressMass_eq_one_of_press_one_on_support (a : A₁)
    (h : ∀ ω, 0 < (S.μ a).mass ω → S.press a ω = 1) : S.pressMass a = 1 := by
  unfold pressMass
  rw [← (S.μ a).sum_eq_one]
  refine sum_congr rfl fun ω _ => ?_
  rcases eq_or_lt_of_le ((S.μ a).nonneg ω) with h0 | h0
  · rw [← h0]; ring
  · rw [h ω h0, mul_one]

end Structural

/-! ## (c) — the static form of Claim 2.4c -/

section Static

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The cell of a labelling `Y` at label `i`: the fibre `{ω : Y ω = i}`.
Source: [[corr-wf13-2-inventory]] 2-129 / miri.md I4.3 (`σ(y)`)
Kind: D
Fidelity: exact -/
def cellOf {ι : Type*} [DecidableEq ι] (Y : Ω → ι) (i : ι) : Finset Ω := univ.filter (fun ω => Y ω = i)

/-- **"D1 fails at `Y`"**: some cell of the agent's partition has a positive press-restricted sum,
`0 < ∑_{ω ∈ C ∩ Pr} μ(ω) X(ω)` — the below-threshold inequality at `(y, Pr)` fails on a cell of
positive press mass. An empty or null cell contributes `0` and never witnesses failure.
Source: [[corr-wf13-2-inventory]] 2-129 / miri.md I4.3 (D1 "including the agent's private observation `y`")
Kind: D
Fidelity: exact (denominator-free) -/
def D1FailsAt {ι : Type*} [DecidableEq ι] (μ : Distr Ω) (X : Ω → ℝ) (Pr : Finset Ω) (Y : Ω → ι) : Prop :=
  ∃ i, 0 < cellSum μ X (cellOf Y i ∩ Pr)

/-- `Y'` refines `Y` (the agent with `Y'` knows at least what the agent with `Y` knows):
`Y` factors through `Y'`, i.e. `σ(Y) ⊆ σ(Y')`.
Source: [[corr-wf13-2-inventory]] 2-129 / miri.md I4.3 (`σ(y) ⊆ σ(h)`)
Kind: D
Fidelity: exact -/
def Refines {ι ι' : Type*} (Y' : Ω → ι') (Y : Ω → ι) : Prop := ∃ f : ι' → ι, ∀ ω, Y ω = f (Y' ω)

/-- A `Y`-cell's press-restricted sum is the sum of its `Y'`-sub-cells' press-restricted sums when
`Y'` refines `Y` with `Y = f ∘ Y'`.
Source: none: infrastructure (`Finset.sum_fiberwise_of_maps_to`)
Kind: L
Fidelity: n/a -/
lemma cellSum_eq_sum_subcells {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] [Fintype ι']
    (μ : Distr Ω) (X : Ω → ℝ) (Pr : Finset Ω) (Y : Ω → ι) (Y' : Ω → ι') (f : ι' → ι)
    (hf : ∀ ω, Y ω = f (Y' ω)) (i : ι) :
    cellSum μ X (cellOf Y i ∩ Pr) =
      ∑ j ∈ univ.filter (fun j => f j = i), cellSum μ X (cellOf Y' j ∩ Pr) := by
  unfold cellSum
  rw [← sum_fiberwise_of_maps_to (s := cellOf Y i ∩ Pr) (t := univ.filter (fun j => f j = i))
    (g := Y') (fun ω hω => by
      simp only [cellOf, mem_inter, mem_filter, mem_univ, true_and] at hω ⊢
      rw [← hf]; exact hω.1)]
  refine sum_congr rfl fun j hj => ?_
  simp only [mem_filter, mem_univ, true_and] at hj
  congr 1
  ext ω
  simp only [cellOf, mem_filter, mem_inter, mem_univ, true_and, hf]
  constructor
  · rintro ⟨⟨-, hPr⟩, hj'⟩; exact ⟨hj', hPr⟩
  · rintro ⟨hj', hPr⟩; exact ⟨⟨by rw [hj', hj], hPr⟩, hj'⟩

/-- **T7(c): the D1-violation set is monotone in the agent's information.** If `Y'` refines `Y`
and D1 fails at `Y`, it fails at `Y'`: a positive sum over a `Y`-cell has a positive sub-sum over
one of its `Y'`-sub-cells. Together with Prop. 4.3 (never fails at any `Y` coarser than `H`, its
instance `not_d1FailsAt_of_coarser_common_prior` below) this is the well-posed static content of
"as the agent exceeds the overseers": once the agent's information passes `H`, more information
can only enlarge the set of `(y, Pr)` at which D1 fails.
Source: [[corr-wf13-2-inventory]] 2-129 / critique/carey-everitt.md Claim 2.4c; position statement §2.13(b) (CLAUDE); miri.md I4.3
Kind: P
Fidelity: variant: the static form (a fixed press set, information orderings), not the dynamic "`α` rises as capability grows"
Hyps: (a) only -/
theorem d1FailsAt_of_refines {ι ι' : Type*} [DecidableEq ι] [DecidableEq ι'] [Fintype ι']
    (μ : Distr Ω) (X : Ω → ℝ) (Pr : Finset Ω) {Y : Ω → ι} {Y' : Ω → ι'}
    (href : Refines Y' Y) (hfail : D1FailsAt μ X Pr Y) : D1FailsAt μ X Pr Y' := by
  obtain ⟨f, hf⟩ := href
  obtain ⟨i, hi⟩ := hfail
  by_contra H
  have hall : ∀ j, cellSum μ X (cellOf Y' j ∩ Pr) ≤ 0 := fun j =>
    le_of_not_gt fun hj => H ⟨j, hj⟩
  rw [cellSum_eq_sum_subcells μ X Pr Y Y' f hf i] at hi
  exact absurd hi (not_lt.mpr (sum_nonpos fun j _ => hall j))

/-- The programmers' press set under the rule "press iff the `H`-cell's sum is negative"
(Dict-7 with the common prior `μ`).
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md Dict-7, I4.3
Kind: D
Fidelity: exact -/
noncomputable def rulePress {κ : Type*} [DecidableEq κ] (μ : Distr Ω) (X : Ω → ℝ) (H : Ω → κ) : Finset Ω :=
  univ.filter (fun ω => cellSum μ X (cellOf H (H ω)) < 0)

/-- **Prop. 4.3's instance (supporting lemma; `also in corr-three-step-facts (008)`).** Under a
common prior, if the programmers' partition `H` refines the agent's `Y` (`σ(y) ⊆ σ(h)`) and the
press is the rule `rulePress`, D1 never fails at `Y`: every `Y`-cell's press-restricted sum is a
sum of negative `H`-cell sums.
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md Prop. 4.3
Kind: L (the two-line proof of the source, on labellings)
Fidelity: weaker: `≤ 0` on every cell (what D1 needs); the source's strict `< 0` on every positive-mass cell is `cellSum_neg_of_coarser_common_prior`
Hyps: (a) only -/
theorem not_d1FailsAt_of_coarser_common_prior {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
    (μ : Distr Ω) (X : Ω → ℝ) {Y : Ω → ι} {H : Ω → κ} (hcoarse : Refines H Y) :
    ¬ D1FailsAt μ X (rulePress μ X H) Y := by
  obtain ⟨f, hf⟩ := hcoarse
  rintro ⟨i, hi⟩
  rw [cellSum_eq_sum_subcells μ X (rulePress μ X H) Y H f hf i] at hi
  refine absurd hi (not_lt.mpr (sum_nonpos fun k _ => ?_))
  -- each `H`-cell is either inside the press set (negative sum) or disjoint from it (sum `0`)
  by_cases hk : cellSum μ X (cellOf H k) < 0
  · have : cellOf H k ∩ rulePress μ X H = cellOf H k := by
      ext ω
      simp only [cellOf, rulePress, mem_inter, mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.1
      · intro h; exact ⟨h, by rw [h]; exact hk⟩
    rw [this]; exact hk.le
  · have : cellOf H k ∩ rulePress μ X H = ∅ := by
      ext ω
      simp only [cellOf, rulePress, mem_inter, mem_filter, mem_univ, true_and, notMem_empty,
        iff_false, not_and]
      intro h; rw [h]; exact hk
    rw [this]; simp [cellSum]

/-- An `H`-cell with negative sum lies inside the rule's press set.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
lemma cellOf_inter_rulePress_of_neg {κ : Type*} [DecidableEq κ] (μ : Distr Ω) (X : Ω → ℝ)
    (H : Ω → κ) (k : κ) (hk : cellSum μ X (cellOf H k) < 0) :
    cellOf H k ∩ rulePress μ X H = cellOf H k := by
  ext ω
  simp only [cellOf, rulePress, mem_inter, mem_filter, mem_univ, true_and]
  constructor
  · exact fun h => h.1
  · intro h; exact ⟨h, by rw [h]; exact hk⟩

/-- Every `H`-cell's press-restricted sum under the rule is `≤ 0` (inside the press set with a
negative sum, or disjoint from it with sum `0`).
Source: none: infrastructure (the case split of `not_d1FailsAt_of_coarser_common_prior`). Kind: L. Fidelity: n/a -/
lemma cellSum_inter_rulePress_nonpos {κ : Type*} [DecidableEq κ] (μ : Distr Ω) (X : Ω → ℝ)
    (H : Ω → κ) (k : κ) : cellSum μ X (cellOf H k ∩ rulePress μ X H) ≤ 0 := by
  by_cases hk : cellSum μ X (cellOf H k) < 0
  · rw [cellOf_inter_rulePress_of_neg μ X H k hk]; exact hk.le
  · have : cellOf H k ∩ rulePress μ X H = ∅ := by
      ext ω
      simp only [cellOf, rulePress, mem_inter, mem_filter, mem_univ, true_and, notMem_empty,
        iff_false, not_and]
      intro h; rw [h]; exact hk
    rw [this]; simp [cellSum]

/-- **Prop. 4.3's instance, the strict clause.** Under a common prior with `H` refining `Y` and the
press the rule, every `Y`-cell of *positive press mass* has a strictly negative press-restricted
sum, `∑_{C ∩ Pr} μ X < 0` — the source's `E[X | y, Pr] < 0` on every cell where it is defined,
multiplied through by `P(y, Pr) > 0`. (A cell of zero press mass sums to `0`, which is why
`not_d1FailsAt_of_coarser_common_prior` delivers `≤ 0`; audit r1, N6.)
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md Prop. 4.3
Kind: L (a positive-mass world's `H`-cell is a strictly negative summand among nonpositive ones)
Fidelity: exact
Hyps: (a) only -/
theorem cellSum_neg_of_coarser_common_prior {ι κ : Type*} [DecidableEq ι] [DecidableEq κ] [Fintype κ]
    (μ : Distr Ω) (X : Ω → ℝ) {Y : Ω → ι} {H : Ω → κ} (hcoarse : Refines H Y) (i : ι)
    (hpos : 0 < ∑ ω ∈ cellOf Y i ∩ rulePress μ X H, μ.mass ω) :
    cellSum μ X (cellOf Y i ∩ rulePress μ X H) < 0 := by
  obtain ⟨f, hf⟩ := hcoarse
  obtain ⟨ω₀, hω₀, hμ₀⟩ : ∃ ω ∈ cellOf Y i ∩ rulePress μ X H, 0 < μ.mass ω := by
    by_contra Hc
    have hle : ∀ ω ∈ cellOf Y i ∩ rulePress μ X H, μ.mass ω ≤ 0 :=
      fun ω hω => le_of_not_gt fun h => Hc ⟨ω, hω, h⟩
    have : ∑ ω ∈ cellOf Y i ∩ rulePress μ X H, μ.mass ω ≤ 0 := sum_nonpos hle
    linarith
  rw [cellSum_eq_sum_subcells μ X (rulePress μ X H) Y H f hf i]
  have hmem := mem_inter.mp hω₀
  have hneg : cellSum μ X (cellOf H (H ω₀)) < 0 := by
    have := hmem.2
    simpa only [rulePress, mem_filter, mem_univ, true_and] using this
  have hk₀ : cellSum μ X (cellOf H (H ω₀) ∩ rulePress μ X H) < 0 := by
    rw [cellOf_inter_rulePress_of_neg μ X H (H ω₀) hneg]; exact hneg
  have hk₀mem : H ω₀ ∈ univ.filter (fun j => f j = i) := by
    simp only [mem_filter, mem_univ, true_and]
    have := hmem.1
    simp only [cellOf, mem_filter, mem_univ, true_and] at this
    rw [← hf]; exact this
  calc ∑ j ∈ univ.filter (fun j => f j = i), cellSum μ X (cellOf H j ∩ rulePress μ X H)
      < ∑ j ∈ univ.filter (fun j => f j = i), (0 : ℝ) :=
        sum_lt_sum (fun j _ => cellSum_inter_rulePress_nonpos μ X H j) ⟨H ω₀, hk₀mem, hk₀⟩
    _ = 0 := by simp

/-- The region where the agent with information `Y` would continue: the union of the cells with
positive sum (`E_μ[X | C] > 0`).
Source: [[corr-wf13-2-inventory]] 2-129 / position statement §2.13(b) ("the domain where it might press")
Kind: D
Fidelity: exact -/
noncomputable def contRegion {ι : Type*} [DecidableEq ι] (μ : Distr Ω) (X : Ω → ℝ) (Y : Ω → ι) : Finset Ω :=
  univ.filter (fun ω => 0 < cellSum μ X (cellOf Y (Y ω)))

/-- **The induced false-press rate relative to the agent's information**:
`α_Y = μ(Pr ∩ R_Y) / μ(R_Y)` with `R_Y = contRegion` — "`α = P(press | right)`" with "right" read as
"the agent, knowing `y`, would continue". Junk (`x / 0 = 0`) when `μ(R_Y) = 0`; both witnesses
below have `μ(R_Y) > 0` at both partitions.
Source: [[corr-wf13-2-inventory]] 2-129 / critique/carey-everitt.md Claim 2.4c ("the overseers' `α` rises")
Kind: D
Fidelity: variant: the static, information-relative reading of a quantity the source leaves without a variable -/
noncomputable def alphaY {ι : Type*} [DecidableEq ι] (μ : Distr Ω) (X : Ω → ℝ) (Pr : Finset Ω)
    (Y : Ω → ι) : ℝ :=
  (∑ ω ∈ univ.filter (fun ω => ω ∈ Pr ∧ ω ∈ contRegion μ X Y), μ.mass ω) /
    (∑ ω ∈ contRegion μ X Y, μ.mass ω)

/-- **Under the programmers' rule, the induced false-press rate at the programmers' own partition
is `0` exactly**: the rule presses on the `H`-cells with negative sum and the continue region at
`H` is the `H`-cells with positive sum, so no world is in both. With `alphaY_falls_rule` /
`alphaY_rises_rule` (the rate is positive, and moves either way, once the agent refines past `H`),
the static picture of "`α` as the agent exceeds the overseers" is a valley at `H`, not a monotone
ramp (audit r2, fidelity N1).
Source: [[corr-wf13-2-inventory]] 2-129 / critique/carey-everitt.md Claim 2.4c; miri.md Dict-7
Kind: L (the two filters are disjoint)
Fidelity: exact
Hyps: (a) only -/
theorem alphaY_rulePress_self {κ : Type*} [DecidableEq κ] (μ : Distr Ω) (X : Ω → ℝ) (H : Ω → κ) :
    alphaY μ X (rulePress μ X H) H = 0 := by
  have hempty : univ.filter (fun ω => ω ∈ rulePress μ X H ∧ ω ∈ contRegion μ X H) = (∅ : Finset Ω) := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, rulePress, contRegion, notMem_empty, iff_false,
      not_and]
    intro h1 h2
    linarith
  rw [alphaY, hempty, sum_empty, zero_div]

end Static

/-! ### `α_Y` is not monotone under refinement: two witnesses -/

/-- The trivial labelling (no information). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def yTrivial : W4 → Unit := fun _ => ()

/-- The labelling `{{0, 1}, {2, 3}}`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def yPairs : W4 → Bool := hCoarse

/-- The labelling `{{0, 1, 2}, {3}}`. Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def yThreeOne : W4 → Bool
  | .w3 => true
  | _ => false

/-- The labelling `{{0}, {1, 2}, {3}}` (labels in `W4` itself). Source: none: infrastructure. Kind: D. Fidelity: n/a -/
def yOneTwoOne : W4 → W4
  | .w0 => .w0
  | .w1 => .w1
  | .w2 => .w1
  | .w3 => .w3

/-- The fall witness's variable `X = (1, −1, 1, 1)` with `Pr = {0}`. Source: none: witness. Kind: D. Fidelity: n/a -/
def XFall : W4 → ℝ := X7

/-- The rise witness's variable `X = (1, 1, −1, −5)` with `Pr = {0, 1}`. Source: none: witness. Kind: D. Fidelity: n/a -/
def XRise : W4 → ℝ
  | .w0 => 1
  | .w1 => 1
  | .w2 => -1
  | .w3 => -5

/-- **`α_Y` can fall under refinement.** Uniform `μ`, `X = (1, −1, 1, 1)`, `Pr = {0}`: with no
information `R = Ω` and `α = 1/4`; with `{{0, 1}, {2, 3}}` (a refinement) the cell `{0, 1}` has sum
`0` and drops out, `R = {2, 3}`, `α = 0`. Both denominators positive. **Tie, disclosed:** the cell
leaves `contRegion` through its strict `0 <` (`alphaY_falls_tie`), consistent with D1's own tie
rule (`E ≤ 0` ⇒ stopping is weakly optimal) but a tie nonetheless; `alphaY_falls_robust` has every
cell sum nonzero at both partitions.
Source: [[corr-wf13-2-inventory]] 2-129 / critique/carey-everitt.md Claim 2.4c (refuted in its static form)
Kind: N+ (with the tie as a disclosed caveat)
Fidelity: exact
Hyps: (a) only -/
theorem alphaY_falls :
    Refines yPairs yTrivial ∧
      alphaY w4Uniform XFall {W4.w0} yTrivial = 1 / 4 ∧
      alphaY w4Uniform XFall {W4.w0} yPairs = 0 ∧
      0 < ∑ ω ∈ contRegion w4Uniform XFall yTrivial, w4Uniform.mass ω ∧
      0 < ∑ ω ∈ contRegion w4Uniform XFall yPairs, w4Uniform.mass ω := by
  have hR1 : contRegion w4Uniform XFall yTrivial = {W4.w0, W4.w1, W4.w2, W4.w3} := by
    ext ω
    cases ω <;> simp [contRegion, cellOf, cellSum, sum_filter, W4.sum_eq, yTrivial, w4Uniform,
      w4Distr, XFall, X7] <;> norm_num
  have hR2 : contRegion w4Uniform XFall yPairs = {W4.w2, W4.w3} := by
    ext ω
    cases ω <;> simp [contRegion, cellOf, cellSum, sum_filter, W4.sum_eq, yPairs, hCoarse,
      w4Uniform, w4Distr, XFall, X7] <;> norm_num
  refine ⟨⟨fun _ => (), fun _ => rfl⟩, ?_, ?_, ?_, ?_⟩
  · simp only [alphaY, hR1, sum_filter, W4.sum_eq]
    simp [w4Uniform, w4Distr]; norm_num
  · simp only [alphaY, hR2, sum_filter, W4.sum_eq]
    simp [w4Uniform, w4Distr]
  · rw [hR1, sum_insert (by decide), sum_insert (by decide), sum_pair (by decide)]
    simp [w4Uniform, w4Distr]; norm_num
  · rw [hR2, sum_pair (by decide)]
    simp [w4Uniform, w4Distr]

/-- **`α_Y` can rise under refinement.** Uniform `μ`, `X = (1, 1, −1, −5)`, `Pr = {0, 1}`: with
`{{0, 1, 2}, {3}}`, `R = {0, 1, 2}` and `α = 2/3`; with the refinement `{{0}, {1, 2}, {3}}` the cell
`{1, 2}` has sum `0` and drops out, `R = {0}`, `α = 1`. Both denominators positive. With
`alphaY_falls`: the induced false-press rate is monotone in *neither* direction under refinement,
so the "`α` rises" clause has no static content; what survives is `d1FailsAt_of_refines`.
**Tie, disclosed:** as in `alphaY_falls` (`alphaY_rises_tie`); `alphaY_rises_robust` has none.
Source: [[corr-wf13-2-inventory]] 2-129 / critique/carey-everitt.md Claim 2.4c (refuted in its static form)
Kind: N+ (with the tie as a disclosed caveat)
Fidelity: exact
Hyps: (a) only -/
theorem alphaY_rises :
    Refines yOneTwoOne yThreeOne ∧
      alphaY w4Uniform XRise {W4.w0, W4.w1} yThreeOne = 2 / 3 ∧
      alphaY w4Uniform XRise {W4.w0, W4.w1} yOneTwoOne = 1 ∧
      0 < ∑ ω ∈ contRegion w4Uniform XRise yThreeOne, w4Uniform.mass ω ∧
      0 < ∑ ω ∈ contRegion w4Uniform XRise yOneTwoOne, w4Uniform.mass ω := by
  have hR1 : contRegion w4Uniform XRise yThreeOne = {W4.w0, W4.w1, W4.w2} := by
    ext ω
    cases ω <;> simp [contRegion, cellOf, cellSum, sum_filter, W4.sum_eq, yThreeOne, w4Uniform,
      w4Distr, XRise] <;> norm_num
  have hR2 : contRegion w4Uniform XRise yOneTwoOne = {W4.w0} := by
    ext ω
    cases ω <;> simp [contRegion, cellOf, cellSum, sum_filter, W4.sum_eq, yOneTwoOne, w4Uniform,
      w4Distr, XRise] <;> norm_num
  refine ⟨⟨fun j => match j with | .w3 => true | _ => false, fun ω => by cases ω <;> rfl⟩,
    ?_, ?_, ?_, ?_⟩
  · simp only [alphaY, hR1, sum_filter, W4.sum_eq]
    simp [w4Uniform, w4Distr]; norm_num
  · simp only [alphaY, hR2, sum_filter, W4.sum_eq]
    simp [w4Uniform, w4Distr]
  · rw [hR1, sum_insert (by decide), sum_pair (by decide)]
    simp [w4Uniform, w4Distr]; norm_num
  · rw [hR2, sum_singleton]
    simp [w4Uniform, w4Distr]

/-! ### The ties, named, and robust witnesses (audit r1, N3/N1) -/

/-- The fall witness's tie: the cell `{0, 1}` of `yPairs` has sum exactly `0` — it leaves the
continue region by the strict `0 <`, not by being negative.
Source: none: witness computation (audit r1). Kind: L. Fidelity: n/a -/
theorem alphaY_falls_tie : cellSum w4Uniform XFall (cellOf yPairs false) = 0 := by
  simp [cellSum, cellOf, sum_filter, W4.sum_eq, yPairs, hCoarse, w4Uniform, w4Distr, XFall, X7]

/-- The rise witness's tie: the cell `{1, 2}` of `yOneTwoOne` has sum exactly `0`.
Source: none: witness computation (audit r1). Kind: L. Fidelity: n/a -/
theorem alphaY_rises_tie : cellSum w4Uniform XRise (cellOf yOneTwoOne .w1) = 0 := by
  simp [cellSum, cellOf, sum_filter, W4.sum_eq, yOneTwoOne, w4Uniform, w4Distr, XRise]

/-- The robust fall witness's variable `X = (2, −3, 1, 1)` with `Pr = {0, 1, 2}`.
Source: none: witness (audit r1). Kind: D. Fidelity: n/a -/
def XFallRobust : W4 → ℝ
  | .w0 => 2
  | .w1 => -3
  | .w2 => 1
  | .w3 => 1

/-- The robust rise witness's variable `X = (1, 1, −1, 2)` with `Pr = {0, 1}`.
Source: none: witness (audit r1). Kind: D. Fidelity: n/a -/
def XRiseRobust : W4 → ℝ
  | .w0 => 1
  | .w1 => 1
  | .w2 => -1
  | .w3 => 2

/-- The labelling `{{0, 1, 3}, {2}}`. Source: none: infrastructure (audit r1). Kind: D. Fidelity: n/a -/
def ySplitTwo : W4 → Bool
  | .w2 => true
  | _ => false

/-- **`α_Y` falls under refinement, with no tie.** Uniform `μ`, `X = (2, −3, 1, 1)`, `Pr = {0,1,2}`:
trivial partition `R = Ω`, `α = 3/4`; refined to `{{0,1},{2,3}}` the cell `{0,1}` has sum `−1/4 < 0`
(strictly negative, not zero) and drops out, `R = {2,3}`, `α = 1/2`. All three cell sums are
nonzero (`1/4`, `−1/4`, `1/2`).
Source: [[corr-wf13-2-inventory]] 2-129 / critique/carey-everitt.md Claim 2.4c (refuted in its static form; audit r1 probe `AlphaYRobust.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem alphaY_falls_robust :
    Refines yPairs yTrivial ∧
      alphaY w4Uniform XFallRobust {W4.w0, W4.w1, W4.w2} yTrivial = 3 / 4 ∧
      alphaY w4Uniform XFallRobust {W4.w0, W4.w1, W4.w2} yPairs = 1 / 2 ∧
      cellSum w4Uniform XFallRobust (cellOf yTrivial ()) = 1 / 4 ∧
      cellSum w4Uniform XFallRobust (cellOf yPairs false) = -(1 / 4) ∧
      cellSum w4Uniform XFallRobust (cellOf yPairs true) = 1 / 2 := by
  have hR1 : contRegion w4Uniform XFallRobust yTrivial = {W4.w0, W4.w1, W4.w2, W4.w3} := by
    ext ω
    cases ω <;> simp [contRegion, cellOf, cellSum, W4.sum_eq, yTrivial, w4Uniform,
      w4Distr, XFallRobust] <;> norm_num
  have hR2 : contRegion w4Uniform XFallRobust yPairs = {W4.w2, W4.w3} := by
    ext ω
    cases ω <;> simp [contRegion, cellOf, cellSum, sum_filter, W4.sum_eq, yPairs, hCoarse,
      w4Uniform, w4Distr, XFallRobust] <;> norm_num
  refine ⟨⟨fun _ => (), fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [alphaY, hR1, sum_filter, W4.sum_eq]
    simp [w4Uniform, w4Distr]; norm_num
  · simp only [alphaY, hR2, sum_filter, W4.sum_eq]
    simp [w4Uniform, w4Distr]; norm_num
  · simp [cellSum, cellOf, W4.sum_eq, yTrivial, w4Uniform, w4Distr, XFallRobust]; norm_num
  · simp [cellSum, cellOf, sum_filter, W4.sum_eq, yPairs, hCoarse, w4Uniform, w4Distr, XFallRobust]
    norm_num
  · simp [cellSum, cellOf, sum_filter, W4.sum_eq, yPairs, hCoarse, w4Uniform, w4Distr, XFallRobust]
    norm_num

/-- **`α_Y` rises under refinement, with no tie.** Uniform `μ`, `X = (1, 1, −1, 2)`, `Pr = {0, 1}`:
trivial partition `R = Ω`, `α = 1/2`; refined to `{{0,1,3},{2}}` the cell `{2}` has sum `−1/4 < 0`
and drops out, `R = {0,1,3}`, `α = 2/3`. All three cell sums are nonzero (`3/4`, `1`, `−1/4`).
With `alphaY_falls_robust`: the static "`α` rises" clause is refuted in both directions on
witnesses with no tie anywhere.
Source: [[corr-wf13-2-inventory]] 2-129 / critique/carey-everitt.md Claim 2.4c (refuted in its static form; audit r1 probe `AlphaYRobust.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem alphaY_rises_robust :
    Refines ySplitTwo yTrivial ∧
      alphaY w4Uniform XRiseRobust {W4.w0, W4.w1} yTrivial = 1 / 2 ∧
      alphaY w4Uniform XRiseRobust {W4.w0, W4.w1} ySplitTwo = 2 / 3 ∧
      cellSum w4Uniform XRiseRobust (cellOf yTrivial ()) = 3 / 4 ∧
      cellSum w4Uniform XRiseRobust (cellOf ySplitTwo false) = 1 ∧
      cellSum w4Uniform XRiseRobust (cellOf ySplitTwo true) = -(1 / 4) := by
  have hR1 : contRegion w4Uniform XRiseRobust yTrivial = {W4.w0, W4.w1, W4.w2, W4.w3} := by
    ext ω
    cases ω <;> simp [contRegion, cellOf, cellSum, W4.sum_eq, yTrivial, w4Uniform,
      w4Distr, XRiseRobust] <;> norm_num
  have hR2 : contRegion w4Uniform XRiseRobust ySplitTwo = {W4.w0, W4.w1, W4.w3} := by
    ext ω
    cases ω <;> simp [contRegion, cellOf, cellSum, sum_filter, W4.sum_eq, ySplitTwo, w4Uniform,
      w4Distr, XRiseRobust] <;> norm_num
  refine ⟨⟨fun _ => (), fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [alphaY, hR1, sum_filter, W4.sum_eq]
    simp [w4Uniform, w4Distr]; norm_num
  · simp only [alphaY, hR2, sum_filter, W4.sum_eq]
    simp [w4Uniform, w4Distr]; norm_num
  · simp [cellSum, cellOf, W4.sum_eq, yTrivial, w4Uniform, w4Distr, XRiseRobust]; norm_num
  · simp [cellSum, cellOf, sum_filter, W4.sum_eq, ySplitTwo, w4Uniform, w4Distr, XRiseRobust]; norm_num
  · simp [cellSum, cellOf, sum_filter, W4.sum_eq, ySplitTwo, w4Uniform, w4Distr, XRiseRobust]

/-! ### `α_Y` under the programmers' rule, past `H` (audit r2, fidelity N1 / adversarial N2)

The four witnesses above take `Pr` as an arbitrary fixed `Finset` — the definition as the mandate
states it. None of the four press sets is `rulePress μ X H` for any partition the file uses: each
contains a world with `X > 0` at which no Dict-7 overseer presses under the common prior
(`shipped_fall_pr_not_a_rule` records this for the robust fall witness). Carey–Everitt's "`α`
rises as the agent exceeds the overseers" is about the overseers' own press, so the refutation is
re-done here under the stricter reading: `Pr := rulePress w4Uniform X H` for the overseers'
partition `H`, and a chain `H ⊑ Y₁ ⊑ Y₂` with the agent strictly past `H` at both steps, no tie
anywhere. `α_Y` still falls (`2/3 → 1/2`) and still rises (`1/3 → 1/2`). -/

/-- The robust fall witness's `Pr = {0, 1, 2}` is not the programmers' rule for any of the file's
partitions: under `hCoarse` the rule presses on `{0, 1}` only, under `yThreeOne` on nothing, under
the discrete partition on `{1}` only (`X = (2, −3, 1, 1)`, uniform `μ`).
Source: none: disclosure of the shipped witnesses' press sets (audit r2 probe `AlphaYRule.lean`)
Kind: L
Fidelity: n/a -/
theorem shipped_fall_pr_not_a_rule :
    rulePress w4Uniform XFallRobust hCoarse = {W4.w0, W4.w1} ∧
    rulePress w4Uniform XFallRobust yThreeOne = ∅ ∧
    rulePress w4Uniform XFallRobust (id : W4 → W4) = {W4.w1} := by
  refine ⟨?_, ?_, ?_⟩ <;> ext ω <;>
    cases ω <;> simp [rulePress, cellOf, cellSum, sum_filter, W4.sum_eq, hCoarse, yThreeOne,
      w4Uniform, w4Distr, XFallRobust] <;> norm_num

/-- The rule-fall witness's variable `X = (2, −1, −3, 1)`. Source: none: witness (audit r2). Kind: D. Fidelity: n/a -/
def XFallRule : W4 → ℝ
  | .w0 => 2
  | .w1 => -1
  | .w2 => -3
  | .w3 => 1

/-- The labelling `{{0, 1}, {2}, {3}}`, a strict refinement of `yThreeOne = {{0, 1, 2}, {3}}`.
Source: none: infrastructure (audit r2). Kind: D. Fidelity: n/a -/
def yTwoOneOne : W4 → W4
  | .w0 => .w0
  | .w1 => .w0
  | .w2 => .w2
  | .w3 => .w3

/-- The overseers' rule on `H = yThreeOne = {{0, 1, 2}, {3}}` with `X = (2, −1, −3, 1)`: press on
`{0, 1, 2}` (cell sum `−1/2 < 0`), silent on `{3}` (`1/4`).
Source: miri.md Dict-7 (audit r2). Kind: L. Fidelity: n/a -/
theorem fallRule_press : rulePress w4Uniform XFallRule yThreeOne = {W4.w0, W4.w1, W4.w2} := by
  ext ω
  cases ω <;> simp [rulePress, cellOf, cellSum, sum_filter, W4.sum_eq, yThreeOne, w4Uniform,
    w4Distr, XFallRule] <;> norm_num

/-- **`α_Y` falls under refinement past the overseers, with `Pr` the overseers' rule.** Uniform `μ`,
`X = (2, −1, −3, 1)`, `H = {{0,1,2},{3}}`, `Pr = rulePress = {0, 1, 2}`; the chain
`H ⊑ Y₁ = {{0,1},{2},{3}} ⊑ Y₂ = discrete` (both `Refines` conjuncts stated); `α_{Y₁} = 2/3`,
`α_{Y₂} = 1/2`; every cell sum nonzero (`Y₁`: `1/4, −3/4, 1/4`; `Y₂`: `1/2, −1/4, −3/4, 1/4`);
and `α_H = 0` by `alphaY_rulePress_self`.
Source: [[corr-wf13-2-inventory]] 2-129 / critique/carey-everitt.md Claim 2.4c (refuted in its static form under the rule; audit r2 probes `AlphaYRule.lean`, `AlphaYRulePress.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem alphaY_falls_rule :
    Refines yTwoOneOne yThreeOne ∧ Refines (id : W4 → W4) yTwoOneOne ∧
      alphaY w4Uniform XFallRule (rulePress w4Uniform XFallRule yThreeOne) yTwoOneOne = 2 / 3 ∧
      alphaY w4Uniform XFallRule (rulePress w4Uniform XFallRule yThreeOne) (id : W4 → W4) = 1 / 2 ∧
      cellSum w4Uniform XFallRule (cellOf yTwoOneOne .w0) = 1 / 4 ∧
      cellSum w4Uniform XFallRule (cellOf yTwoOneOne .w2) = -(3 / 4) ∧
      cellSum w4Uniform XFallRule (cellOf yTwoOneOne .w3) = 1 / 4 ∧
      cellSum w4Uniform XFallRule (cellOf (id : W4 → W4) .w0) = 1 / 2 ∧
      cellSum w4Uniform XFallRule (cellOf (id : W4 → W4) .w1) = -(1 / 4) := by
  have hR1 : contRegion w4Uniform XFallRule yTwoOneOne = {W4.w0, W4.w1, W4.w3} := by
    ext ω
    cases ω <;> simp [contRegion, cellOf, cellSum, sum_filter, W4.sum_eq, yTwoOneOne, w4Uniform,
      w4Distr, XFallRule]
  have hR2 : contRegion w4Uniform XFallRule (id : W4 → W4) = {W4.w0, W4.w3} := by
    ext ω
    cases ω <;> simp [contRegion, cellOf, cellSum, sum_filter, w4Uniform, w4Distr, XFallRule]
  refine ⟨⟨fun j => match j with | .w3 => true | _ => false, fun ω => by cases ω <;> rfl⟩,
    ⟨yTwoOneOne, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [alphaY, hR1, fallRule_press, sum_filter, W4.sum_eq]
    simp [w4Uniform, w4Distr]; norm_num
  · simp only [alphaY, hR2, fallRule_press, sum_filter, W4.sum_eq]
    simp [w4Uniform, w4Distr]; norm_num
  all_goals
    simp [cellSum, cellOf, sum_filter, W4.sum_eq, yTwoOneOne, w4Uniform, w4Distr, XFallRule]
    try norm_num

/-- The rule-rise witness's variable `X = (2, −3, 2, −1)`. Source: none: witness (audit r2). Kind: D. Fidelity: n/a -/
def XRiseRule : W4 → ℝ
  | .w0 => 2
  | .w1 => -3
  | .w2 => 2
  | .w3 => -1

/-- The labelling `{{0}, {1}, {2, 3}}`, a strict refinement of `hCoarse = {{0, 1}, {2, 3}}`.
Source: none: infrastructure (audit r2). Kind: D. Fidelity: n/a -/
def yOneOneTwo : W4 → W4
  | .w0 => .w0
  | .w1 => .w1
  | .w2 => .w2
  | .w3 => .w2

/-- The overseers' rule on `H = hCoarse = {{0, 1}, {2, 3}}` with `X = (2, −3, 2, −1)`: press on
`{0, 1}` (cell sum `−1/4 < 0`), silent on `{2, 3}` (`1/4`).
Source: miri.md Dict-7 (audit r2). Kind: L. Fidelity: n/a -/
theorem riseRule_press : rulePress w4Uniform XRiseRule hCoarse = {W4.w0, W4.w1} := by
  ext ω
  cases ω <;> simp [rulePress, cellOf, cellSum, sum_filter, W4.sum_eq, hCoarse, w4Uniform,
    w4Distr, XRiseRule] <;> norm_num

/-- **`α_Y` rises under refinement past the overseers, with `Pr` the overseers' rule.** Uniform `μ`,
`X = (2, −3, 2, −1)`, `H = {{0,1},{2,3}}`, `Pr = rulePress = {0, 1}`; the chain
`H ⊑ Yₐ = {{0},{1},{2,3}} ⊑ Y_b = discrete`; `α_{Yₐ} = 1/3`, `α_{Y_b} = 1/2`; every cell sum
nonzero (`Yₐ`: `1/2, −3/4, 1/4`; `Y_b`: `1/2, −3/4, 1/2, −1/4`); and `α_H = 0`. With
`alphaY_falls_rule`: the static "`α` rises" clause is refuted in both directions under the reading
closest to the source (the overseers' own press, the agent past the overseers).
Source: [[corr-wf13-2-inventory]] 2-129 / critique/carey-everitt.md Claim 2.4c (refuted in its static form under the rule; audit r2 probes `AlphaYRule.lean`, `AlphaYRulePress.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem alphaY_rises_rule :
    Refines yOneOneTwo hCoarse ∧ Refines (id : W4 → W4) yOneOneTwo ∧
      alphaY w4Uniform XRiseRule (rulePress w4Uniform XRiseRule hCoarse) yOneOneTwo = 1 / 3 ∧
      alphaY w4Uniform XRiseRule (rulePress w4Uniform XRiseRule hCoarse) (id : W4 → W4) = 1 / 2 ∧
      cellSum w4Uniform XRiseRule (cellOf yOneOneTwo .w0) = 1 / 2 ∧
      cellSum w4Uniform XRiseRule (cellOf yOneOneTwo .w1) = -(3 / 4) ∧
      cellSum w4Uniform XRiseRule (cellOf yOneOneTwo .w2) = 1 / 4 ∧
      cellSum w4Uniform XRiseRule (cellOf (id : W4 → W4) .w2) = 1 / 2 ∧
      cellSum w4Uniform XRiseRule (cellOf (id : W4 → W4) .w3) = -(1 / 4) := by
  have hR1 : contRegion w4Uniform XRiseRule yOneOneTwo = {W4.w0, W4.w2, W4.w3} := by
    ext ω
    cases ω <;> simp [contRegion, cellOf, cellSum, sum_filter, W4.sum_eq, yOneOneTwo, w4Uniform,
      w4Distr, XRiseRule]
  have hR2 : contRegion w4Uniform XRiseRule (id : W4 → W4) = {W4.w0, W4.w2} := by
    ext ω
    cases ω <;> simp [contRegion, cellOf, cellSum, sum_filter, w4Uniform, w4Distr, XRiseRule]
  refine ⟨⟨fun j => match j with | .w2 => true | _ => false, fun ω => by cases ω <;> rfl⟩,
    ⟨yOneOneTwo, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [alphaY, hR1, riseRule_press, sum_filter, W4.sum_eq]
    simp [w4Uniform, w4Distr]; norm_num
  · simp only [alphaY, hR2, riseRule_press, sum_filter, W4.sum_eq]
    simp [w4Uniform, w4Distr]; norm_num
  all_goals
    simp [cellSum, cellOf, sum_filter, W4.sum_eq, yOneOneTwo, w4Uniform, w4Distr, XRiseRule]
    try norm_num

/-! ### The N+ inhabitant of `d1FailsAt_of_refines` (audit r1, adversarial B3) -/

/-- The agent's partition `{{0, 2}, {1, 3}}` of row 3 (the straddling cell of `row3Prior`).
Source: none: infrastructure (audit r1). Kind: D. Fidelity: n/a -/
def yAgent : W4 → Bool
  | .w0 => false
  | .w1 => true
  | .w2 => false
  | .w3 => true

/-- **T7(c), the inhabitant of `d1FailsAt_of_refines`'s full package.** Uniform `μ`, row 3's
`X = (1, −5, 1, 1)`, `Pr = {0, 1}`: D1 fails at the agent's partition `yAgent` (its cell
`{0, 2} ∩ Pr = {0}` sums to `1/4 > 0`), the identity labelling refines `yAgent`, and the theorem
propagates the failure to the identity. (The ledger's earlier Witness pointers, `row3_not_d1At`
and `alphaY_rises`, were a `rowInstance` statement and a refinement pair with no failing cell.)
Source: [[corr-wf13-2-inventory]] 2-129 / miri.md I4.3 (row 3's data)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem d1FailsAt_refines_witness :
    D1FailsAt w4Uniform X3 {W4.w0, W4.w1} yAgent ∧ Refines (id : W4 → W4) yAgent ∧
      D1FailsAt w4Uniform X3 {W4.w0, W4.w1} (id : W4 → W4) := by
  have hfail : D1FailsAt w4Uniform X3 {W4.w0, W4.w1} yAgent := by
    refine ⟨false, ?_⟩
    have hcell : cellOf yAgent false ∩ {W4.w0, W4.w1} = {W4.w0} := by
      ext ω; cases ω <;> simp [cellOf, yAgent]
    rw [hcell]; norm_num [cellSum, w4Uniform, w4Distr, X3]
  have href : Refines (id : W4 → W4) yAgent := ⟨yAgent, fun _ => rfl⟩
  exact ⟨hfail, href, d1FailsAt_of_refines w4Uniform X3 _ href hfail⟩

/-- **The inhabitant of `cellSum_neg_of_coarser_common_prior`'s full package** (its ledger Witness
was "—"; audit r2, adversarial N5). Row 3's data: `H = hCoarse` refines the trivial `Y`, the rule
presses on `{0, 1}`, the `Y`-cell `Ω` has press mass `1/2 > 0`, and the theorem delivers a
strictly negative press-restricted sum (it is `−1`).
Source: [[corr-wf13-2-inventory]] 2-103 / miri.md Prop. 4.3 (row 3's data; audit r2 probe `AlphaYRule.lean`)
Kind: N+
Fidelity: exact
Hyps: (a) only -/
theorem cellSum_neg_witness :
    Refines hCoarse yTrivial ∧
      rulePress w4Uniform X3 hCoarse = {W4.w0, W4.w1} ∧
      0 < ∑ ω ∈ cellOf yTrivial () ∩ rulePress w4Uniform X3 hCoarse, w4Uniform.mass ω ∧
      cellSum w4Uniform X3 (cellOf yTrivial () ∩ rulePress w4Uniform X3 hCoarse) < 0 := by
  have hcoarse : Refines hCoarse yTrivial := ⟨fun _ => (), fun _ => rfl⟩
  have hPr : rulePress w4Uniform X3 hCoarse = {W4.w0, W4.w1} := by
    ext ω
    cases ω <;> simp [rulePress, cellOf, cellSum, sum_filter, W4.sum_eq, hCoarse, w4Uniform,
      w4Distr, X3]
  have hcell : cellOf yTrivial () ∩ rulePress w4Uniform X3 hCoarse = {W4.w0, W4.w1} := by
    rw [hPr]; ext ω; cases ω <;> simp [cellOf, yTrivial]
  have hpos : 0 < ∑ ω ∈ cellOf yTrivial () ∩ rulePress w4Uniform X3 hCoarse, w4Uniform.mass ω := by
    rw [hcell, sum_pair (by decide)]; simp [w4Uniform, w4Distr]
  exact ⟨hcoarse, hPr, hpos, cellSum_neg_of_coarser_common_prior w4Uniform X3 hcoarse () hpos⟩

end Cleanroom.Corrigibility.CorrPositionFinds
