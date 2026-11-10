/-
# Incompatibility semantics on the rational row language

Round `projects/normativity/rounds/2026-11-08-content-recollection/`, matter 2, first half.

**Incompatibility** of a finite list of rows (§1) is a valid conflict from compilation: a
Farkas certificate over the list's rows and the cube rows (`Incompatible`,
`incompatible_iff_conflict`).  It holds exactly when the rows have no common point in the cube
(`incompatible_iff_not_feasible`): soundness is `farkas_sound`; completeness is the rational
alternative, so a compiler over this row schema never needs its `unknown` output for want of
a certificate.

**Incompatibility entailment** (§2): `Γ` entails `g` when every list incompatible with `g` is
incompatible with `Γ` (`IncEntails`).  **Certificate entailment**: `g` is a nonnegative
combination of rows allowed against `Γ`, with slack in the constant (`EntailCert`,
`CertEntails`); a `BoundCert` is the case of a row `s · x φ ≤ v` (`ofBoundCert`,
`toBoundCert`).  The two coincide, and coincide with validity on the cube points of `Γ`
(`incEntails_iff_certEntails`, `incEntails_iff_sem`, `certEntails_iff_sem`).  No nonemptiness
hypothesis is needed: against an infeasible `Γ` a conflict certificate scaled up and added to
a cube certificate derives every row (`certEntails_of_incompatible`).

**Item 118** (§3).  Every valid lower or upper bound on a forced region has a bound
certificate over the forced bundle's allowed rows (`lowerBound_certified`,
`upperBound_certified`); and the interval `SeedStatics.forcedInterval` computes inhabits the
rational predicate `IsForcedInterval`, its endpoints attained at rational points
(`forcedInterval_isForcedInterval`).  Both hypothesis packages are inhabited on
`SeedStatics.widenSeed` (`lowerBound_witness`, `forcedInterval_witness`).

**The Form language alone is degenerate** (§4).  The all-ones point satisfies every form of
strength at most one, so no list of such forms is incompatible (`humble_forms_feasible`) and
incompatibility entailment restricted to form contexts holds between any two of them
(`formIncEntails_total`), while on rows `P(X) ≥ 1/2` does not entail `P(X) ≥ 3/4`
(`form_role_needs_rows`).  The role of a form is its role among rows.

Names are provisional (`AGENTS.md` standard 6).
-/
import Workspace.Normativity.Contrib.RowAlternative

namespace Workspace.Normativity.Contrib.IncompatibilitySemantics

open Workspace.Normativity.Contrib.NormativeInductorComposition
open Workspace.Normativity.Contrib.SeedStatics
open Workspace.Normativity.Contrib.RowAlternative
open Finset

variable {d : ℕ}

/-! ## 1. Incompatibility -/

/-- The rows a certificate may weight against a list of rows: the list's and the cube's. -/
def Allowed (L : List (Row d)) (r : Row d) : Prop :=
  r ∈ L ∨ (∃ i, r = cubeUpper i) ∨ (∃ i, r = cubeLower i)

theorem allowed_iff_mem (L : List (Row d)) (r : Row d) : Allowed L r ↔ r ∈ L ++ cubeRows d := by
  rw [List.mem_append, mem_cubeRows]; rfl

theorem allowed_bundle {Q : Type*} (B : Bundle Q d) (r : Row d) :
    Allowed (B.map CitedRow.row) r ↔ B.Allowed r := by
  unfold Allowed Bundle.Allowed
  simp only [List.mem_map]

theorem Allowed.mono {L L' : List (Row d)} (h : ∀ r ∈ L, r ∈ L') {r : Row d}
    (hr : Allowed L r) : Allowed L' r :=
  hr.imp (h r) id

/-- **Incompatibility** of a finite list of rows: a valid conflict from compilation. -/
def Incompatible (L : List (Row d)) : Prop :=
  ∃ m, ∃ c : FarkasCert d m, ∀ i, Allowed L (c.row i)

/-- Incompatibility of a bundle's rows is a valid `conflict` result of the compiler. -/
theorem incompatible_iff_conflict {Q : Type*} (B : Bundle Q d) :
    Incompatible (B.map CitedRow.row) ↔
      ∃ m, ∃ cert : FarkasCert d m, (CompileResult.conflict m cert : CompileResult Q d).Valid B := by
  unfold Incompatible CompileResult.Valid
  simp only [allowed_bundle]

/-- The rows have a common point in the cube. -/
def Feasible (L : List (Row d)) : Prop := ∃ x, InCube x ∧ SatAll L x

theorem feasible_iff (L : List (Row d)) : Feasible L ↔ ∃ x, SatAll (L ++ cubeRows d) x := by
  simp only [Feasible, satAll_append, cubeRows_sat_iff, and_comm]

/-- **Incompatible iff infeasible in the cube.**  Soundness is `farkas_sound`; completeness is
the rational alternative. -/
theorem incompatible_iff_not_feasible (L : List (Row d)) : Incompatible L ↔ ¬ Feasible L := by
  constructor
  · rintro ⟨m, c, hall⟩ ⟨x, hcube, hx⟩
    refine farkas_sound c x fun i => ?_
    rcases hall i with h | ⟨j, hj⟩ | ⟨j, hj⟩
    · exact hx _ h
    · rw [hj]; exact cubeUpper_sat hcube j
    · rw [hj]; exact cubeLower_sat hcube j
  · intro h
    rw [feasible_iff] at h
    obtain ⟨w, hc, hb⟩ := (alternative _).1 h
    exact ⟨_, ⟨w.u, (L ++ cubeRows d).get, w.nonneg, hc, hb⟩,
      fun i => (allowed_iff_mem L _).2 (List.get_mem _ i)⟩

/-! ## 2. Incompatibility entailment and certificate entailment -/

/-- **Incompatibility entailment**: every list incompatible with `g` is incompatible with `Γ`. -/
def IncEntails (Γ : List (Row d)) (g : Row d) : Prop :=
  ∀ X : List (Row d), Incompatible (g :: X) → Incompatible (Γ ++ X)

/-- **An entailment certificate** for a row `g`: nonnegative multipliers on rows whose weighted
coefficient sum is `g`'s coefficient vector and whose weighted constant sum is at most `g`'s
constant. -/
structure EntailCert (d m : ℕ) (g : Row d) where
  mult : Fin m → ℚ
  row : Fin m → Row d
  mult_nonneg : ∀ i, 0 ≤ mult i
  coeff_sum : ∀ j, ∑ i, mult i * (row i).a j = g.a j
  const_le : ∑ i, mult i * (row i).b ≤ g.b

/-- **Soundness**: at any point satisfying every weighted row, `g` holds. -/
theorem EntailCert.sound {m : ℕ} {g : Row d} (c : EntailCert d m g) (x : Fin d → ℚ)
    (hx : ∀ i, (c.row i).Sat x) : g.Sat x := by
  have h1 : ∑ i, c.mult i * ∑ j, (c.row i).a j * x j ≤ ∑ i, c.mult i * (c.row i).b :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hx i) (c.mult_nonneg i)
  have h2 : ∑ i, c.mult i * ∑ j, (c.row i).a j * x j = ∑ j, g.a j * x j := by
    simp only [← c.coeff_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  have := c.const_le
  unfold Row.Sat
  linarith

/-- **Certificate entailment**: an entailment certificate over rows allowed against `Γ`. -/
def CertEntails (Γ : List (Row d)) (g : Row d) : Prop :=
  ∃ m, ∃ c : EntailCert d m g, ∀ i, Allowed Γ (c.row i)

/-- Validity of `g` at every cube point of `Γ`. -/
def SemEntails (Γ : List (Row d)) (g : Row d) : Prop := ∀ x, InCube x → SatAll Γ x → g.Sat x

theorem certEntails_sem {Γ : List (Row d)} {g : Row d} (h : CertEntails Γ g) : SemEntails Γ g := by
  obtain ⟨m, c, hall⟩ := h
  intro x hcube hx
  refine c.sound x fun i => ?_
  rcases hall i with h | ⟨j, hj⟩ | ⟨j, hj⟩
  · exact hx _ h
  · rw [hj]; exact cubeUpper_sat hcube j
  · rw [hj]; exact cubeLower_sat hcube j

/-- Completeness where `Γ` has a cube point. -/
theorem semEntails_cert_of_feasible {Γ : List (Row d)} {g : Row d} (hfeas : Feasible Γ)
    (h : SemEntails Γ g) : CertEntails Γ g := by
  rw [feasible_iff] at hfeas
  have hall : ∀ x, SatAll (Γ ++ cubeRows d) x → g.Sat x := by
    intro x hx
    rw [satAll_append, cubeRows_sat_iff] at hx
    exact h x hx.2 hx.1
  obtain ⟨w, hc, hb⟩ := (entails_iff _ g hfeas).1 hall
  exact ⟨_, ⟨w.u, (Γ ++ cubeRows d).get, w.nonneg, hc, hb⟩,
    fun i => (allowed_iff_mem Γ _).2 (List.get_mem _ i)⟩

/-- In the cube, `a · x ≤ Σ max (a j) 0`. -/
lemma cube_bound (g : Row d) : SemEntails [] ⟨g.a, ∑ j, max (g.a j) 0⟩ := by
  intro x hcube _
  unfold Row.Sat
  refine Finset.sum_le_sum fun j _ => ?_
  obtain ⟨h0, h1⟩ := hcube j
  rcases le_total 0 (g.a j) with ha | ha
  · rw [max_eq_left ha]; nlinarith
  · rw [max_eq_right ha]; nlinarith

/-- **Against an infeasible list every row is certified**: a conflict certificate, scaled, added
to a cube certificate of the row's coefficient vector. -/
theorem certEntails_of_incompatible {Γ : List (Row d)} (h : Incompatible Γ) (g : Row d) :
    CertEntails Γ g := by
  obtain ⟨m₀, c₀, h₀⟩ := h
  obtain ⟨m₁, c₁, h₁⟩ := semEntails_cert_of_feasible (Γ := [])
    ⟨fun _ => 0, fun _ => by norm_num, fun _ hr => by simp at hr⟩ (cube_bound g)
  obtain ⟨M, hM⟩ : ∃ M : ℚ, M = ∑ j, max (g.a j) 0 := ⟨_, rfl⟩
  have h1' : ∑ i, c₁.mult i * (c₁.row i).b ≤ M := by rw [hM]; exact c₁.const_le
  set s : ℚ := -∑ i, c₀.mult i * (c₀.row i).b with hs
  have hspos : 0 < s := by have := c₀.const_sum; rw [hs]; linarith
  set t : ℚ := max 0 ((M - g.b) / s) with ht
  have ht0 : 0 ≤ t := le_max_left _ _
  have hts : M - g.b ≤ t * s := by
    have := le_max_right 0 ((M - g.b) / s)
    rw [← ht] at this
    exact (div_le_iff₀ hspos).1 this
  refine ⟨m₀ + m₁,
    ⟨Fin.append (fun i => t * c₀.mult i) c₁.mult, Fin.append c₀.row c₁.row, ?_, ?_, ?_⟩, ?_⟩
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact mul_nonneg ht0 (c₀.mult_nonneg i)
    · rw [Fin.append_right]; exact c₁.mult_nonneg i
  · intro j
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have h0 : ∑ i, t * c₀.mult i * (c₀.row i).a j = 0 := by
      rw [show ∑ i, t * c₀.mult i * (c₀.row i).a j = t * ∑ i, c₀.mult i * (c₀.row i).a j by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
      rw [c₀.coeff_sum j, mul_zero]
    rw [h0, zero_add]
    exact c₁.coeff_sum j
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    have h0 : ∑ i, t * c₀.mult i * (c₀.row i).b = -(t * s) := by
      rw [show ∑ i, t * c₀.mult i * (c₀.row i).b = t * ∑ i, c₀.mult i * (c₀.row i).b by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring]
      rw [hs]; ring
    rw [h0]
    linarith
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · show Allowed Γ (Fin.append c₀.row c₁.row (Fin.castAdd m₁ i))
      rw [Fin.append_left]; exact h₀ i
    · show Allowed Γ (Fin.append c₀.row c₁.row (Fin.natAdd m₀ i))
      rw [Fin.append_right]
      exact Allowed.mono (L := []) (fun r hr => absurd hr List.not_mem_nil) (h₁ i)

/-- **Certificate entailment is validity on the cube points of `Γ`.** -/
theorem certEntails_iff_sem (Γ : List (Row d)) (g : Row d) : CertEntails Γ g ↔ SemEntails Γ g := by
  refine ⟨certEntails_sem, fun h => ?_⟩
  by_cases hfeas : Feasible Γ
  · exact semEntails_cert_of_feasible hfeas h
  · exact certEntails_of_incompatible ((incompatible_iff_not_feasible Γ).2 hfeas) g

/-- **Incompatibility entailment is validity on the cube points of `Γ`.** -/
theorem incEntails_iff_sem (Γ : List (Row d)) (g : Row d) : IncEntails Γ g ↔ SemEntails Γ g := by
  constructor
  · intro h x hcube hΓ
    by_contra hg
    have hinc : Incompatible (g :: [⟨fun j => -g.a j, -∑ j, g.a j * x j⟩]) := by
      rw [incompatible_iff_not_feasible]
      rintro ⟨y, -, hy⟩
      have h1 := hy g (by simp)
      have h2 := hy ⟨fun j => -g.a j, -∑ j, g.a j * x j⟩ (by simp)
      unfold Row.Sat at h1 h2 hg
      simp only [neg_mul, Finset.sum_neg_distrib] at h2
      linarith
    have := (incompatible_iff_not_feasible _).1 (h _ hinc)
    refine this ⟨x, hcube, (satAll_append _ _ _).2 ⟨hΓ, fun r hr => ?_⟩⟩
    simp only [List.mem_singleton] at hr
    subst hr
    unfold Row.Sat
    simp only [neg_mul, Finset.sum_neg_distrib]
    exact le_rfl
  · intro h X hinc
    rw [incompatible_iff_not_feasible] at hinc ⊢
    rintro ⟨x, hcube, hx⟩
    rw [satAll_append] at hx
    refine hinc ⟨x, hcube, fun r hr => ?_⟩
    rcases List.mem_cons.1 hr with rfl | hr
    · exact h x hcube hx.1
    · exact hx.2 r hr

/-- **Incompatibility entailment coincides with certificate entailment** on the rational row
language, relative to the cube. -/
theorem incEntails_iff_certEntails (Γ : List (Row d)) (g : Row d) :
    IncEntails Γ g ↔ CertEntails Γ g := by
  rw [incEntails_iff_sem, certEntails_iff_sem]

/-- The row `s · x φ ≤ v`. -/
def boundRow (φ : Fin d) (s v : ℚ) : Row d := ⟨fun j => if j = φ then s else 0, v⟩

theorem boundRow_sat (φ : Fin d) (s v : ℚ) (x : Fin d → ℚ) :
    (boundRow φ s v).Sat x ↔ s * x φ ≤ v := by
  simp [boundRow, Row.Sat]

theorem boundRow_satR (φ : Fin d) (s v : ℚ) (x : Fin d → ℝ) :
    (boundRow φ s v).SatR x ↔ (s : ℝ) * x φ ≤ (v : ℝ) :=
  single_satR φ s v x

/-- A bound certificate is an entailment certificate for the row `s · x φ ≤ value`. -/
def ofBoundCert {m : ℕ} {φ : Fin d} {s : ℚ} (c : BoundCert d m φ s) :
    EntailCert d m (boundRow φ s c.value) :=
  ⟨c.mult, c.row, c.mult_nonneg, c.coeff_sum, le_rfl⟩

/-- An entailment certificate for `s · x φ ≤ v` is a bound certificate of value at most `v`. -/
def toBoundCert {m : ℕ} {φ : Fin d} {s v : ℚ} (c : EntailCert d m (boundRow φ s v)) :
    BoundCert d m φ s :=
  ⟨c.mult, c.row, c.mult_nonneg, c.coeff_sum⟩

theorem toBoundCert_value {m : ℕ} {φ : Fin d} {s v : ℚ} (c : EntailCert d m (boundRow φ s v)) :
    (toBoundCert c).value ≤ v := c.const_le

/-! ## 3. Item 118: certificate completeness and rational attainment -/

section Item118

variable {A : Type*}

/-- **Every valid lower bound on a forced region is certified.** -/
theorem lowerBound_certified (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) (φ : Fin d) (c : ℚ) (h : LowerBound S W st F φ c) :
    ∃ m, ∃ cert : BoundCert d m φ (-1),
      (∀ i, (forcedBundle S W st F).Allowed (cert.row i)) ∧ c ≤ -cert.value := by
  have hsem : SemEntails ((forcedBundle S W st F).map CitedRow.row) (boundRow φ (-1) (-c)) := by
    intro x hcube hx
    have hreg : forcedRegion S W st F x :=
      (region_iff_satAll _ x).2 ((satAll_append _ _ _).2 ⟨hx, (cubeRows_sat_iff x).2 hcube⟩)
    have := h x hreg
    rw [boundRow_sat]
    linarith
  obtain ⟨m, cert, hall⟩ := (certEntails_iff_sem _ _).2 hsem
  refine ⟨m, toBoundCert cert, fun i => (allowed_bundle _ _).1 (hall i), ?_⟩
  have := toBoundCert_value cert
  linarith

/-- **Every valid upper bound on a forced region is certified.** -/
theorem upperBound_certified (S : Seed d A) (W : List (SubItem d)) (st : DocketState)
    (F : Settlement d) (φ : Fin d) (c : ℚ) (h : UpperBound S W st F φ c) :
    ∃ m, ∃ cert : BoundCert d m φ 1,
      (∀ i, (forcedBundle S W st F).Allowed (cert.row i)) ∧ cert.value ≤ c := by
  have hsem : SemEntails ((forcedBundle S W st F).map CitedRow.row) (boundRow φ 1 c) := by
    intro x hcube hx
    have hreg : forcedRegion S W st F x :=
      (region_iff_satAll _ x).2 ((satAll_append _ _ _).2 ⟨hx, (cubeRows_sat_iff x).2 hcube⟩)
    have := h x hreg
    rw [boundRow_sat]
    linarith
  obtain ⟨m, cert, hall⟩ := (certEntails_iff_sem _ _).2 hsem
  exact ⟨m, toBoundCert cert, fun i => (allowed_bundle _ _).1 (hall i), toBoundCert_value cert⟩

/-- A real point of a bundle's region at which coordinate `φ` takes a rational value `v` gives
a rational one. -/
theorem exists_rat_point_at {Q : Type*} (B : Bundle Q d) (φ : Fin d) (v : ℚ)
    (h : ∃ x : Fin d → ℝ, B.RegionR x ∧ x φ = (v : ℝ)) : ∃ x : Fin d → ℚ, B.Region x ∧ x φ = v := by
  obtain ⟨x, hx, hv⟩ := h
  have hreal : ∃ x : Fin d → ℝ, ∀ r ∈ (B.map CitedRow.row ++ cubeRows d) ++
      [boundRow φ 1 v, boundRow φ (-1) (-v)], r.SatR x := by
    refine ⟨x, fun r hr => ?_⟩
    rcases List.mem_append.1 hr with hr | hr
    · exact (regionR_iff_satR B x).1 hx r hr
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · rw [boundRow_satR, hv]; push_cast; linarith
      · rw [boundRow_satR, hv]; push_cast; linarith
  obtain ⟨y, hy⟩ := exists_rat_of_real _ hreal
  rw [satAll_append] at hy
  refine ⟨y, (region_iff_satAll B y).2 hy.1, ?_⟩
  have h1 := hy.2 (boundRow φ 1 v) (by simp)
  have h2 := hy.2 (boundRow φ (-1) (-v)) (by simp)
  rw [boundRow_sat] at h1 h2
  linarith

/-- **The computed forced interval inhabits the rational predicate**: where the real forced
region is nonempty, the endpoints `forcedInterval` computes are valid bounds attained at
rational points. -/
theorem forcedInterval_isForcedInterval {m : ℕ} (S : Seed (m + 1) A)
    (W : List (SubItem (m + 1))) (st : DocketState) (F : Settlement (m + 1)) (φ : Fin (m + 1))
    (hne : ∃ x, forcedRegionR S W st F x) :
    IsForcedInterval S W st F φ (forcedInterval S W st F φ).1 (forcedInterval S W st F φ).2 := by
  obtain ⟨hlo, hhi⟩ := forcedInterval_bounds S W st F φ hne
  obtain ⟨-, hlo_mem, hhi_mem⟩ := forcedInterval_spec S W st F φ hne
  exact ⟨hlo, hhi, exists_rat_point_at (forcedBundle S W st F) φ _ hlo_mem,
    exists_rat_point_at (forcedBundle S W st F) φ _ hhi_mem⟩

/-- The hypothesis of `lowerBound_certified` inhabited: on `SeedStatics.widenSeed` the valid
lower bound `1/2` has a certificate. -/
theorem lowerBound_witness :
    ∃ m, ∃ cert : BoundCert 1 m 0 (-1),
      (∀ i, (forcedBundle widenSeed [] DocketState.quiet (Settlement.empty 1)).Allowed
        (cert.row i)) ∧ (1/2 : ℚ) ≤ -cert.value :=
  lowerBound_certified widenSeed [] DocketState.quiet (Settlement.empty 1) 0 (1/2) defeat_widens.1

/-- The hypothesis of `forcedInterval_isForcedInterval` inhabited: `widenSeed`'s real forced
region contains `1/2`, so its computed interval is a forced interval at rational points. -/
theorem forcedInterval_witness :
    IsForcedInterval widenSeed [] DocketState.quiet (Settlement.empty 1) 0
      (forcedInterval widenSeed [] DocketState.quiet (Settlement.empty 1) 0).1
      (forcedInterval widenSeed [] DocketState.quiet (Settlement.empty 1) 0).2 :=
  forcedInterval_isForcedInterval _ _ _ _ _
    ⟨fun _ => ((1/2 : ℚ) : ℝ), forcedRegionR_of_forcedRegion widenSeed [] DocketState.quiet
      (Settlement.empty 1) (x := fun _ => 1/2) (by decide +kernel)⟩

end Item118

/-! ## 4. The Form language alone is degenerate -/

/-- **Forms of strength at most one are jointly feasible**: the all-ones point satisfies each. -/
theorem humble_forms_feasible (X : List (Form d)) (h : ∀ f ∈ X, f.c ≤ 1) :
    Feasible (X.map Form.row) := by
  refine ⟨fun _ => 1, fun _ => by norm_num, fun r hr => ?_⟩
  obtain ⟨f, hf, rfl⟩ := List.mem_map.1 hr
  cases f with
  | premise X c =>
    have hc : c ≤ 1 := h _ hf
    rw [Form.premise_sat_iff]; exact hc
  | applicability X XA c =>
    have hc : c ≤ 1 := h _ hf
    rw [Form.applicability_sat_iff]; simpa using hc
  | strength XA XAY c =>
    have hc : c ≤ 1 := h _ hf
    rw [Form.strength_sat_iff]; simpa using hc

/-- Incompatibility entailment restricted to contexts of forms of strength at most one. -/
def FormIncEntails (f g : Form d) : Prop :=
  ∀ X : List (Form d), (∀ h ∈ X, h.c ≤ 1) →
    Incompatible ((g :: X).map Form.row) → Incompatible ((f :: X).map Form.row)

/-- **Restricted to form contexts, every form entails every form of strength at most one**:
nothing is incompatible with it. -/
theorem formIncEntails_total (f g : Form d) (hg : g.c ≤ 1) : FormIncEntails f g := by
  intro X hX hinc
  exact absurd (humble_forms_feasible (g :: X) (by
    intro h hh
    rcases List.mem_cons.1 hh with rfl | hh
    · exact hg
    · exact hX h hh)) ((incompatible_iff_not_feasible _).1 hinc)

/-- **The role of a form is its role among rows**: `P(X) ≥ 1/2` entails `P(X) ≥ 3/4` in form
contexts and not in row contexts. -/
theorem form_role_needs_rows :
    FormIncEntails (Form.premise (0 : Fin 1) (1/2)) (Form.premise 0 (3/4)) ∧
      ¬ IncEntails [(Form.premise (0 : Fin 1) (1/2)).row] (Form.premise 0 (3/4)).row := by
  refine ⟨formIncEntails_total _ _ (by norm_num [Form.c]), ?_⟩
  rw [incEntails_iff_sem]
  intro h
  have := h (fun _ => 1/2) (fun _ => by norm_num) (fun r hr => by
    simp only [List.mem_singleton] at hr
    subst hr
    rw [Form.premise_sat_iff])
  rw [Form.premise_sat_iff] at this
  norm_num at this

/-! ## Axiom audit -/

#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.Allowed
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.allowed_iff_mem
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.allowed_bundle
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.Allowed.mono
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.Incompatible
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.incompatible_iff_conflict
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.Feasible
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.feasible_iff
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.incompatible_iff_not_feasible
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.IncEntails
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.EntailCert
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.EntailCert.sound
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.CertEntails
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.SemEntails
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.certEntails_sem
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.semEntails_cert_of_feasible
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.cube_bound
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.certEntails_of_incompatible
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.certEntails_iff_sem
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.incEntails_iff_sem
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.incEntails_iff_certEntails
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.boundRow
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.boundRow_sat
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.boundRow_satR
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.ofBoundCert
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.toBoundCert
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.toBoundCert_value
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.lowerBound_certified
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.upperBound_certified
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.exists_rat_point_at
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.forcedInterval_isForcedInterval
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.lowerBound_witness
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.forcedInterval_witness
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.humble_forms_feasible
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.FormIncEntails
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.formIncEntails_total
#print axioms Workspace.Normativity.Contrib.IncompatibilitySemantics.form_role_needs_rows

end Workspace.Normativity.Contrib.IncompatibilitySemantics
