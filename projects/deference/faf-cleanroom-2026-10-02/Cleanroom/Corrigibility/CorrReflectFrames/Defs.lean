import Cleanroom.Found.LitDdbFrames

/-!
# corr-reflect-frames — definitions of record

Package `corr-reflect-frames` (faf-cleanroom run, 2026-09-30). Reflection forms, restricted
deferrers, legitimizing events, refinements and selections, over `lit-ddb-frames`' finite
frames. A frame `F : Frame W` is the two-time credence `P_{t₂}` as a function of the world; the
deferrer `π` is `P_{t₁}`. Radical's introspection (INT) at candidates is DDB's immodesty at
candidates, `CandsIntrospective`.

Conventions (binding, from the mandate): every predicate is product-form with no division;
"conditional on `L`" is the predicate applied to the *restricted* deferrer `restrict π L`
(`π w · 𝟙_L w`, unnormalized), which every `lit-ddb-frames` theorem with hypothesis
`∀ w, 0 ≤ π w` accepts verbatim; the homogeneity lemmas (`*_smul_iff`) and
`restrict_normalize_mem` transfer the `stdSimplex`-hypothesis theorems.

Nothing here is named `TotalTrust`, `Calibrated`, `Coherent`, `Fair`, `Rule` or
`EpistemicValue`; `Legitimizing*` names carry their sense (`Val`, `TT`).
-/

namespace Cleanroom.Corrigibility.CorrReflectFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## Cells of announced values and estimates -/

/-- The cell `{P_{t₂}(φ) = c}`: worlds whose expert row gives `φ` probability exactly `c`
(`mass (F.P w) φ = E (F.P w) (ind φ)`, `E_ind`).
Source: [[radical]] S3 (R-val), Def I5.1 notation `C_c`
Kind: D
Fidelity: exact -/
def valCell (F : Frame W) (φ : Finset W) (c : ℝ) : Finset W :=
  univ.filter (fun w => mass (F.P w) φ = c)

/-- Membership in a value cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem mem_valCell {F : Frame W} {φ : Finset W} {c : ℝ} {w : W} :
    w ∈ valCell F φ c ↔ mass (F.P w) φ = c := by simp [valCell]

/-- The cell `{E_{P_{t₂}}(X) = s}`: worlds whose expert row estimates `X` at exactly `s`.
Source: [[radical]] Theorem I4.1 (R-var)
Kind: D
Fidelity: exact -/
def estCell (F : Frame W) (X : W → ℝ) (s : ℝ) : Finset W :=
  univ.filter (fun w => E (F.P w) X = s)

/-- Membership in an estimate cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem mem_estCell {F : Frame W} {X : W → ℝ} {s : ℝ} {w : W} :
    w ∈ estCell F X s ↔ E (F.P w) X = s := by simp [estCell]

/-- The estimate cell is the intersection of DDB's `[E(X) ≥ s]` and `[E(X) ≤ s]`.
Source: none: infrastructure (mandate, Representation)
Kind: L
Fidelity: n/a -/
theorem estCell_eq_inter (F : Frame W) (X : W → ℝ) (s : ℝ) :
    estCell F X s = F.estEvent X s ∩ F.estEventLE X s := by
  ext w
  simp only [mem_estCell, mem_inter, Frame.mem_estEvent, Frame.mem_estEventLE]
  exact ⟨fun h => ⟨h.ge, h.le⟩, fun h => le_antisymm h.2 h.1⟩

/-- The estimate cell of an indicator is the value cell.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem estCell_ind (F : Frame W) (φ : Finset W) (c : ℝ) :
    estCell F (ind φ) c = valCell F φ c := by
  ext w; simp [E_ind]

/-! ## The reflection forms -/

/-- **Value-form reflection** (van Fraassen; radical (R-val)): for every event `φ` and every
value `c`, `P_{t₁}(φ ∩ {P_{t₂}(φ) = c}) = c · P_{t₁}(P_{t₂}(φ) = c)` — the product form of
`P_{t₁}(φ | P_{t₂}(φ) = c) = c`, quantified over **all** `c : ℝ` and vacuous at null cells
(`valueReflects_iff_ratio`).
Source: [[radical]] S3 (R-val) l. 24; [[armstrong]] S16 "general reflection" (event form)
Kind: D
Fidelity: exact (product form; ratio form is `valueReflects_iff_ratio`) -/
def ValueReflects (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ (φ : Finset W) (c : ℝ), mass π (φ ∩ valCell F φ c) = c * mass π (valCell F φ c)

/-- **Variable-form reflection** (radical (R-var)): for every random variable `X` and value `s`,
`∑_{E_{P_{t₂}}X = s} π w · X w = s · π(E_{P_{t₂}}X = s)` — the product form of
`E_{P_{t₁}}[X | E_{P_{t₂}}X = s] = s`, vacuous at null cells.
Source: [[radical]] Theorem I4.1 (R-var) l. 127
Kind: D
Fidelity: exact (product form) -/
def VarReflects (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ (X : W → ℝ) (s : ℝ), ∑ w ∈ estCell F X s, π w * X w = s * mass π (estCell F X s)

/-- **Estimate matching** (radical (Mart); Armstrong's sequential unbiasedness in one step;
stationarity `π = πP`): `∑ w, π w · E_{P_w}(X) = E_π(X)` for every `X`.
Source: [[radical]] S3 (Mart) l. 25; [[armstrong]] S7/I2.2 (SU)
Kind: D
Fidelity: exact (bounded is automatic on a finite `W`) -/
def EstimateMatching (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ X : W → ℝ, ∑ w, π w * E (F.P w) X = E π X

/-- **Introspection at candidates** (radical's INT restricted to the range on `π`'s support;
DDB's immodesty at the candidates of `π`): every candidate row gives its own cell probability
one. Weaker than `Frame.Immodest` (all rows); the hypothesis every collapse theorem carries.
Source: [[radical]] S1 (INT) l. 17; [[armstrong]] S16 (introspection of `ρ_j`)
Kind: D
Fidelity: exact (restricted to candidates; the all-rows form implies it) -/
def CandsIntrospective (π : W → ℝ) (F : Frame W) : Prop :=
  ∀ ρ ∈ F.cands π, F.selfMass ρ = 1

/-- An immodest frame is introspective at the candidates of every deferrer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem candsIntrospective_of_immodest {F : Frame W} (h : F.Immodest) (π : W → ℝ) :
    CandsIntrospective π F := by
  intro ρ hρ
  obtain ⟨w, _, rfl⟩ := Frame.mem_cands.1 hρ
  exact h w

/-! ## Restriction: conditioning without division -/

/-- The **restricted deferrer** `π · 𝟙_L`: conditioning `π` on `L` without normalizing. Every
product-form predicate is homogeneous of degree one in `π`, so "`Φ` conditional on `L`" is
`Φ (restrict π L) F`; `restrict_normalize_mem` supplies the simplex point when `π(L) > 0`.
Source: none: infrastructure (mandate, Representation: the package's mechanism)
Kind: D
Fidelity: exact (unnormalized conditional) -/
def restrict (π : W → ℝ) (L : Finset W) : W → ℝ := fun w => π w * ind L w

/-- The restricted deferrer pointwise.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_apply (π : W → ℝ) (L : Finset W) (w : W) :
    restrict π L w = if w ∈ L then π w else 0 := by
  unfold restrict ind; split_ifs <;> simp

/-- Restriction preserves nonnegativity.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_nonneg {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) (L : Finset W) (w : W) :
    0 ≤ restrict π L w := by
  rw [restrict_apply]; split_ifs <;> simp [hπ w]

/-- Mass under the restricted deferrer is mass of the intersection.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_restrict (π : W → ℝ) (L q : Finset W) :
    mass (restrict π L) q = mass π (q ∩ L) := by
  simp only [mass, restrict_apply]
  rw [← sum_filter, filter_mem_eq_inter]

/-- Expectation under the restricted deferrer is the sum over `L`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem E_restrict (π : W → ℝ) (L : Finset W) (X : W → ℝ) :
    E (restrict π L) X = ∑ w ∈ L, π w * X w := by
  simp only [E, restrict_apply, ite_mul, zero_mul]
  rw [← sum_filter, filter_mem_eq_inter, univ_inter]

/-- Restricting to everything changes nothing.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_univ (π : W → ℝ) : restrict π univ = π := by
  funext w; simp [restrict_apply]

/-- Restriction is transitive: `restrict (restrict π L) M = restrict π (L ∩ M)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_restrict (π : W → ℝ) (L M : Finset W) :
    restrict (restrict π L) M = restrict π (L ∩ M) := by
  funext w; simp only [restrict_apply, mem_inter]; split_ifs <;> simp_all

/-- The normalized restricted deferrer is a distribution when `π(L) > 0`.
Source: none: infrastructure (mandate, Representation)
Kind: L
Fidelity: n/a -/
theorem restrict_normalize_mem {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {L : Finset W}
    (h : 0 < mass π L) : (mass π L)⁻¹ • restrict π L ∈ stdSimplex ℝ W := by
  rw [mem_stdSimplex_iff]
  refine ⟨fun w => mul_nonneg (inv_nonneg.2 h.le) (restrict_nonneg hπ L w), ?_⟩
  have : ∑ w, ((mass π L)⁻¹ • restrict π L) w = (mass π L)⁻¹ * mass (restrict π L) univ := by
    simp [mass, mul_sum]
  rw [this, mass_restrict, univ_inter, inv_mul_cancel₀ h.ne']

/-! ## Homogeneity of the product-form predicates -/

/-- Mass is homogeneous in the deferrer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_smul (c : ℝ) (π : W → ℝ) (q : Finset W) : mass (c • π) q = c * mass π q := by
  simp [mass, mul_sum]

/-- A weighted sum is homogeneous in the deferrer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_smul_mul (c : ℝ) (π g : W → ℝ) (q : Finset W) :
    ∑ w ∈ q, (c • π) w * g w = c * ∑ w ∈ q, π w * g w := by
  rw [mul_sum]; apply sum_congr rfl; intro w _; simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- Positive scaling preserves the support.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem supp_smul {c : ℝ} (hc : 0 < c) (π : W → ℝ) : supp (c • π) = supp π := by
  ext w
  rw [mem_supp, mem_supp, Pi.smul_apply, smul_eq_mul]
  exact mul_pos_iff_of_pos_left hc

/-- Positive scaling preserves the candidates.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem cands_smul (F : Frame W) {c : ℝ} (hc : 0 < c) (π : W → ℝ) :
    F.cands (c • π) = F.cands π := by
  unfold Frame.cands; rw [supp_smul hc]

/-- Introspection at candidates is invariant under positive scaling.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem candsIntrospective_smul_iff {c : ℝ} (hc : 0 < c) (π : W → ℝ) (F : Frame W) :
    CandsIntrospective (c • π) F ↔ CandsIntrospective π F := by
  unfold CandsIntrospective; rw [cands_smul F hc]

/-- Reflection is homogeneous of degree one in the deferrer.
Source: none: infrastructure (mandate, Representation)
Kind: L
Fidelity: n/a -/
theorem reflects_smul_iff {c : ℝ} (hc : 0 < c) (π : W → ℝ) (F : Frame W) :
    Reflects (c • π) F ↔ Reflects π F := by
  unfold Reflects
  rw [cands_smul F hc]
  simp only [mass_smul, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_right_inj' hc.ne']

/-- Total Trust is homogeneous of degree one in the deferrer.
Source: none: infrastructure (mandate, Representation)
Kind: L
Fidelity: n/a -/
theorem totalTrust_smul_iff {c : ℝ} (hc : 0 < c) (π : W → ℝ) (F : Frame W) :
    TotalTrust (c • π) F ↔ TotalTrust π F := by
  unfold TotalTrust
  have key : ∀ (X : W → ℝ) (s : ℝ),
      ∑ w, (c • π) w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) =
        c * ∑ w, π w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) := by
    intro X s; rw [mul_sum]; apply sum_congr rfl; intro w _
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp only [key, mul_nonneg_iff_of_pos_left hc]

/-- Value-form reflection is homogeneous of degree one in the deferrer.
Source: none: infrastructure (mandate, Representation)
Kind: L
Fidelity: n/a -/
theorem valueReflects_smul_iff {c : ℝ} (hc : 0 < c) (π : W → ℝ) (F : Frame W) :
    ValueReflects (c • π) F ↔ ValueReflects π F := by
  unfold ValueReflects
  simp only [mass_smul, mul_left_comm _ c, mul_right_inj' hc.ne']

/-- Variable-form reflection is homogeneous of degree one in the deferrer.
Source: none: infrastructure (mandate, Representation)
Kind: L
Fidelity: n/a -/
theorem varReflects_smul_iff {c : ℝ} (hc : 0 < c) (π : W → ℝ) (F : Frame W) :
    VarReflects (c • π) F ↔ VarReflects π F := by
  unfold VarReflects
  simp only [mass_smul, sum_smul_mul, mul_left_comm _ c, mul_right_inj' hc.ne']

/-- Estimate matching is homogeneous of degree one in the deferrer.
Source: none: infrastructure (mandate, Representation)
Kind: L
Fidelity: n/a -/
theorem estimateMatching_smul_iff {c : ℝ} (hc : 0 < c) (π : W → ℝ) (F : Frame W) :
    EstimateMatching (c • π) F ↔ EstimateMatching π F := by
  unfold EstimateMatching
  simp only [sum_smul_mul, E_smul_left, mul_right_inj' hc.ne']

/-- The strategy value is homogeneous in the deferrer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem stratValue_smul (c : ℝ) (π : W → ℝ) (S : W → (W → ℝ)) :
    stratValue (c • π) S = c * stratValue π S := by
  unfold stratValue; exact sum_smul_mul c π (fun w => S w w) univ

/-- Value is homogeneous of degree one in the deferrer.
Source: none: infrastructure (mandate, Representation)
Kind: L
Fidelity: n/a -/
theorem value_smul_iff {c : ℝ} (hc : 0 < c) (π : W → ℝ) (F : Frame W) :
    Value (c • π) F ↔ Value π F := by
  unfold Value
  simp only [E_smul_left, stratValue_smul, mul_le_mul_iff_right₀ hc]

/-! ## Legitimizing events -/

/-- **Legitimizing event, value form** (radical Def I5.1 via Lemma I5.2's linear
characterization, taken as the definition): `L` is legitimizing for `φ` when in every cell
`C_c = {P_{t₂}(φ) = c}`, `π(φ ∩ L ∩ C_c) = c · π(L ∩ C_c)` — the hits and misses inside `L` stand
in the ratio `c : (1 − c)`. The ratio form (Def I5.1 as printed, "for every `c` with
`π(C_c ∩ L) > 0`, `π(φ | C_c, L) = c`") is `legitimizingVal_iff_ratio`. `L = ∅` is vacuously
legitimizing (findings).
Source: [[radical]] Def I5.1 l. 147, Lemma I5.2 l. 149
Kind: D
Fidelity: exact (Lemma I5.2's form as the definition; Def I5.1's ratio form is the iff) -/
def LegitimizingVal (π : W → ℝ) (F : Frame W) (φ L : Finset W) : Prop :=
  ∀ c : ℝ, mass π (φ ∩ L ∩ valCell F φ c) = c * mass π (L ∩ valCell F φ c)

/-- **Legitimizing event, Total-Trust sense** (ddb's strong sense): Total Trust of the deferrer
restricted to `L`. Coincides with "`LegitimizingVal` for every `φ`" under introspection
(`Clarity`/`Legit` modules), differs without it.
Source: [[ddb]] L-C l. 49 (conditional Total Trust)
Kind: D
Fidelity: exact (unnormalized restriction; homogeneity makes this DDB's conditional form) -/
def LegitimizingTT (π : W → ℝ) (F : Frame W) (L : Finset W) : Prop :=
  TotalTrust (restrict π L) F

/-! ## Refinements and selections -/

variable {S K : Type} [DecidableEq S]

/-- The fibre `{v : f v = f w}` of a partition map through `w`.
Source: none: infrastructure
Kind: D
Fidelity: exact -/
def fibre (f : W → S) (w : W) : Finset W := univ.filter (fun v => f v = f w)

/-- Membership in a fibre.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem mem_fibre {f : W → S} {v w : W} : v ∈ fibre f w ↔ f v = f w := by simp [fibre]

/-- Every world is in its own fibre.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mem_fibre_self (f : W → S) (w : W) : w ∈ fibre f w := by simp

/-- The **conditional row** `π(· | f = f w)` in product form, `v ↦ 𝟙[f v = f w] · π v / π(f = f w)`
on a `π`-positive fibre; on a `π`-null fibre the ratio would be `0/0`, and the row is defined as
the point mass `δ_w` so that the frame stays row-stochastic. Candidates (positive-mass rows) are
never on a null fibre (`refineFrame_P_of_pos`).
Source: [[armstrong]] S16 (Bayesian refinement); mandate, Representation (junk trap)
Kind: D
Fidelity: exact on positive fibres; `δ_w` on null fibres (disclosed) -/
def condRow (π : W → ℝ) (f : W → S) (w : W) : W → ℝ :=
  if 0 < mass π (fibre f w) then fun v => ind (fibre f w) v * π v / mass π (fibre f w)
  else fun v => if v = w then 1 else 0

/-- The conditional row on a positive fibre.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condRow_of_pos {π : W → ℝ} {f : W → S} {w : W} (h : 0 < mass π (fibre f w)) :
    condRow π f w = fun v => ind (fibre f w) v * π v / mass π (fibre f w) := if_pos h

/-- The conditional row on a null fibre.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condRow_of_not_pos {π : W → ℝ} {f : W → S} {w : W} (h : ¬ 0 < mass π (fibre f w)) :
    condRow π f w = fun v => if v = w then 1 else 0 := if_neg h

/-- `∑ v, 𝟙_q v · π v = π(q)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem sum_ind_mul (π : W → ℝ) (q : Finset W) : ∑ v, ind q v * π v = mass π q := by
  rw [← E_ind]; unfold E; exact sum_congr rfl (fun v _ => mul_comm _ _)

/-- Conditional rows are distributions.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem condRow_mem {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) (f : W → S) (w : W) :
    condRow π f w ∈ stdSimplex ℝ W := by
  rw [mem_stdSimplex_iff]
  by_cases h : 0 < mass π (fibre f w)
  · rw [condRow_of_pos h]
    refine ⟨fun v => ?_, ?_⟩
    · refine div_nonneg (mul_nonneg ?_ (hπ v)) h.le
      unfold ind; split_ifs <;> norm_num
    · simp only [div_eq_mul_inv]
      rw [← sum_mul, sum_ind_mul, mul_inv_cancel₀ h.ne']
  · rw [condRow_of_not_pos h]
    exact ⟨fun v => by dsimp only; split_ifs <;> norm_num, by simp⟩

/-- The **Bayesian refinement** of `π` along a partition map `f`: the frame whose row at `w` is
`π(· | f = f w)` (`condRow`).
Source: [[armstrong]] S16 (Bayesian refinement), [[selection]] R1.1 (candidates `P(· | ℱ_k)`)
Kind: D
Fidelity: exact (null-fibre rows are `δ_w`, see `condRow`) -/
def refineFrame (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (f : W → S) : Frame W where
  P := condRow π f
  P_mem := condRow_mem hπ f

/-- The **selected frame**: candidates `refineFrame π (f k)` indexed by `k : K`, a selection rule
`s : W → K`; the row at `w` is the row of the selected candidate, `π(· | f (s w) = f (s w) w)`.
Source: [[selection]] R1.1 (`ρ^s(ω) := ρ^{s(ω)}(ω)`), [[armstrong]] A1
Kind: D
Fidelity: exact -/
def selectFrame (π : W → ℝ) (hπ : ∀ w, 0 ≤ π w) (f : K → W → S) (s : W → K) : Frame W where
  P := fun w => condRow π (f (s w)) w
  P_mem := fun w => condRow_mem hπ (f (s w)) w

/-- **Retention of grounds** (per-`k` form): the event `{s = k}` is measurable with respect to
the selected candidate's partition `f k` — if `w` selects `k` and `w'` is `f k`-indistinguishable
from `w`, then `w'` selects `k` too. The common generalization of R1.1's "`G` coarser than every
`ℱ_k`" and of adapted stopping (`{τ = m}` is `ℱ_m`-measurable).
Source: [[selection]] R1.1, R1.3, R2.1 (retention); [[armstrong]] A1 (proof)
Kind: D
Fidelity: variant: per-`k` measurability, strictly weaker than R1.1's common-`G` hypothesis
(`Selection.lean`) -/
def RetainsGrounds (f : K → W → S) (s : W → K) : Prop :=
  ∀ k w w', s w = k → f k w = f k w' → s w' = k

end

end Cleanroom.Corrigibility.CorrReflectFrames
