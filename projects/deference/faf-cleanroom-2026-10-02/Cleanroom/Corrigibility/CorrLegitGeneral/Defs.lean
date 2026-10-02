import Cleanroom.Found.LitDdbFrames.Local
import Cleanroom.Corrigibility.CorrReflectFrames.Legit

/-!
# corr-legit-general — definitions of record

Package `corr-legit-general` (faf-cleanroom run, 2026-10-01). Legitimacy-conditioned deference
over `lit-ddb-frames`' finite frames, in the local (question-relative) form the corrigibility
workflows converged on: `L`-conditioned Total Trust with respect to a question `Q`.

Conventions (binding, from the mandate): conditioning on `L` is always `restrict π L`
(`corr-reflect-frames`), never a normalized conditional; every DDB predicate is homogeneous of
degree one in the deferrer, so "`Φ` conditional on `L`" *is* `Φ (restrict π L) F`, and a theorem
that needs a simplex point is reached through `restrict_normalize_mem`. **Every `L`-conditioned
headline carries `0 < mass π L`**: at `L = ∅` the restricted deferrer is `0` and every predicate
holds vacuously (`legitTotalTrustWrt_empty`, the package's first vacuity trap). The global form is
not redefined: it is `corr-reflect-frames`' `LegitimizingTT` (`legitTotalTrustWrt_id_iff`).
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

/-! ## The criterion of record and its relatives -/

/-- **Legitimacy-conditioned Total Trust with respect to `Q`** (the criterion of record):
the deferrer restricted to `L` totally trusts the frame on every `Q`-measurable variable, in
product form — for every `Q`-measurable `X` and threshold `s`,
`0 ≤ ∑ w, π w · 𝟙_L w · (X w − s) · 𝟙[s ≤ E_{P_w}(X)]`. Off `π`-null events this is
`E_π(X | L ∧ [E_P(X) ≥ s]) ≥ s`, the above-threshold inequality of [[legitimacy]] R5.1 and
[[legitimacy-general-final]] Statement 1; the below-threshold inequality is its dual
(`legitTotalTrustWrt_dual`). Two vacuity traps: `L = ∅` makes the deferrer `0`
(`legitTotalTrustWrt_empty`; hence `0 < mass π L` on every conditioned headline), and a one-cell
`Q` makes every `Q`-measurable `X` constant (`legitTotalTrustWrt_const_question`, `Vacuity.lean`;
hence every local witness shows two positive-mass `Q`-cells).
Source: [[legitimacy]] R5.1 ll. 96–97, §2.11 l. 129; [[legitimacy-general-final]] Statement 1 l. 43
Kind: D
Fidelity: exact (unnormalized restriction; homogeneity makes it the conditional form) -/
def LegitTotalTrustWrt (Q : W → C) (π : W → ℝ) (F : Frame W) (L : Finset W) : Prop :=
  TotalTrustWrt Q (restrict π L) F

/-- **Legitimacy-conditioned Value with respect to `Q`**: the deferrer restricted to `L` values
the frame on every nonempty menu of `Q`-measurable options.
Source: [[legitimacy]] R5.1 l. 98 ("legitimacy-conditioned Value"); [[ddb]] I5.1 l. 127
Kind: D
Fidelity: exact -/
def LegitValuesWrt (Q : W → C) (π : W → ℝ) (F : Frame W) (L : Finset W) : Prop :=
  ValuesWrt Q (restrict π L) F

/-- **Legitimacy-conditioned Reflection with respect to `Q`**: the equality form
`π(q | L ∧ [P = ρ]) = ρ(q)` for every partial answer `q` to `Q`, in product form.
Source: [[legitimacy]] R2.3 l. 58 (local equality form); [[ddb]] I5.1 l. 127
Kind: D
Fidelity: exact -/
def LegitReflectsWrt (Q : W → C) (π : W → ℝ) (F : Frame W) (L : Finset W) : Prop :=
  ReflectsWrt Q (restrict π L) F

/-- **Legitimacy-conditioned Value** (global): the deferrer restricted to `L` values the frame.
Source: [[ddb]] I5.1 l. 127 ("Value conditional on `L`"); [[mm]] I5.1 l. 146
Kind: D
Fidelity: exact -/
def LegitValue (π : W → ℝ) (F : Frame W) (L : Finset W) : Prop :=
  Value (restrict π L) F

/-- The global form is not a new definition: Total Trust w.r.t. the finest question `id`,
conditional on `L`, is `corr-reflect-frames`' `LegitimizingTT`.
Source: mandate, Representation of record
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem legitTotalTrustWrt_id_iff {π : W → ℝ} {F : Frame W} {L : Finset W} :
    LegitTotalTrustWrt (id : W → W) π F L ↔ LegitimizingTT π F L :=
  totalTrust_iff_totalTrustWrt_id.symm

/-- Global legitimacy-conditioned Total Trust implies the local form for every question.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem LegitimizingTT.wrt {π : W → ℝ} {F : Frame W} {L : Finset W} (h : LegitimizingTT π F L)
    (Q : W → C) : LegitTotalTrustWrt Q π F L :=
  TotalTrust.wrt h Q

/-! ## The restricted deferrer: support, candidates, vacuity -/

/-- Restriction to the empty event is the zero deferrer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_empty (π : W → ℝ) : restrict π ∅ = 0 := by
  funext w; simp [restrict_apply]

/-- **Vacuity at `L = ∅`**: the empty event is trivially legitimizing, for every question.
This is why every `L`-conditioned headline carries `0 < mass π L`.
Source: mandate, Known issues 1 (not in the sources)
Kind: N-
Fidelity: n/a -/
theorem legitTotalTrustWrt_empty (Q : W → C) (π : W → ℝ) (F : Frame W) :
    LegitTotalTrustWrt Q π F ∅ := by
  intro X _ s
  simp [restrict_empty]

/-- The support of the restricted deferrer is the legitimate part of the support:
`supp (restrict π L) = L ∩ supp π`.
Source: [[ddb]] I5.3 l. 129 ("whose support is `L ∩ W_π`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem supp_restrict (π : W → ℝ) (L : Finset W) : supp (restrict π L) = L ∩ supp π := by
  ext w
  simp only [supp, mem_filter, mem_univ, true_and, mem_inter, restrict_apply]
  split_ifs with h <;> simp [h]

/-- The legitimate candidates are the rows at the legitimate support worlds.
Source: [[ddb]] I5.2(c) l. 128 (`C_{π_L} = {P_w : w ∈ L, π(w) > 0}`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem cands_restrict (F : Frame W) (π : W → ℝ) (L : Finset W) :
    F.cands (restrict π L) = (L ∩ supp π).image F.P := by
  rw [Frame.cands, supp_restrict]

/-- Total mass of the restricted deferrer is the mass of `L`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem mass_restrict_univ (π : W → ℝ) (L : Finset W) : mass (restrict π L) univ = mass π L := by
  rw [mass_restrict, univ_inter]

/-- A positive-mass legitimate world is in the support of the restricted deferrer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem restrict_pos_of_mem {π : W → ℝ} {L : Finset W} {w : W} (hw : w ∈ L) (hπ : 0 < π w) :
    0 < restrict π L w := by
  rw [restrict_apply, if_pos hw]; exact hπ

/-! ## Homogeneity and additivity of the local predicates -/

/-- Total Trust with respect to `Q` is homogeneous of degree one in the deferrer.
Source: none: infrastructure (mandate T6(a))
Kind: L
Fidelity: n/a -/
theorem totalTrustWrt_smul_iff {c : ℝ} (hc : 0 < c) (Q : W → C) (π : W → ℝ) (F : Frame W) :
    TotalTrustWrt Q (c • π) F ↔ TotalTrustWrt Q π F := by
  unfold TotalTrustWrt
  have key : ∀ (X : W → ℝ) (s : ℝ),
      ∑ w, (c • π) w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) =
        c * ∑ w, π w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) := by
    intro X s; rw [mul_sum]; apply sum_congr rfl; intro w _
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp only [key, mul_nonneg_iff_of_pos_left hc]

/-- Total Trust with respect to `Q` is additive in the deferrer.
Source: none: infrastructure (mandate T6(a), `totalTrust_add` generalised to `Wrt`)
Kind: L
Fidelity: n/a -/
theorem totalTrustWrt_add {Q : W → C} {π₁ π₂ : W → ℝ} {F : Frame W} (h₁ : TotalTrustWrt Q π₁ F)
    (h₂ : TotalTrustWrt Q π₂ F) : TotalTrustWrt Q (π₁ + π₂) F := by
  intro X hX s
  have h := add_nonneg (h₁ X hX s) (h₂ X hX s)
  have e : ∑ w, (π₁ + π₂) w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) =
      ∑ w, π₁ w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) +
        ∑ w, π₂ w * (X w - s) * (if s ≤ E (F.P w) X then 1 else 0) := by
    rw [← sum_add_distrib]; apply sum_congr rfl; intro w _; simp only [Pi.add_apply]; ring
  rw [e]; exact h

/-- Total Trust with respect to `Q` is closed under nonnegative scaling (the zero deferrer
trusts trivially).
Source: none: infrastructure (mandate T6(a))
Kind: L
Fidelity: n/a -/
theorem totalTrustWrt_smul {c : ℝ} (hc : 0 ≤ c) {Q : W → C} {π : W → ℝ} {F : Frame W}
    (h : TotalTrustWrt Q π F) : TotalTrustWrt Q (c • π) F := by
  rcases hc.lt_or_eq with hc' | rfl
  · exact (totalTrustWrt_smul_iff hc' Q π F).2 h
  · intro X _ s; simp

/-- **The mixture lemma**: Total Trust with respect to `Q` is closed under nonnegative linear
combinations of deferrers — the set of deferrers trusting a frame on `Q` is a convex cone
([[legitimacy-general-final]] Statement 9(b): "every threshold inequality is linear in the
deferrer, so the set of trusting deferrers is convex").
Source: [[legitimacy-general-final]] Statement 9(b) l. 67, Proofs l. 140
Kind: P
Fidelity: exact (cone form; the convex-combination form is the case `∑ c = 1`)
Hyps: (a) none -/
theorem totalTrustWrt_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (ρ : ι → W → ℝ) (Q : W → C)
    (F : Frame W) (hc : ∀ i ∈ s, 0 ≤ c i) (h : ∀ i ∈ s, TotalTrustWrt Q (ρ i) F) :
    TotalTrustWrt Q (∑ i ∈ s, c i • ρ i) F := by
  classical
  induction s using Finset.induction_on with
  | empty => intro X _ t; simp
  | insert a s ha ih =>
    rw [sum_insert ha]
    exact totalTrustWrt_add (totalTrustWrt_smul (hc a (mem_insert_self a s)) (h a (mem_insert_self a s)))
      (ih (fun i hi => hc i (mem_insert_of_mem hi)) (fun i hi => h i (mem_insert_of_mem hi)))

/-- Value with respect to `Q` is homogeneous of degree one in the deferrer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem valuesWrt_smul_iff {c : ℝ} (hc : 0 < c) (Q : W → C) (π : W → ℝ) (F : Frame W) :
    ValuesWrt Q (c • π) F ↔ ValuesWrt Q π F := by
  unfold ValuesWrt
  simp only [E_smul_left, stratValue_smul, mul_le_mul_iff_right₀ hc]

/-- Reflection with respect to `Q` is homogeneous of degree one in the deferrer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem reflectsWrt_smul_iff {c : ℝ} (hc : 0 < c) (Q : W → C) (π : W → ℝ) (F : Frame W) :
    ReflectsWrt Q (c • π) F ↔ ReflectsWrt Q π F := by
  unfold ReflectsWrt
  rw [cands_smul F hc]
  simp only [mass_smul, mul_assoc, mul_right_inj' hc.ne']

/-- **The dual (below-threshold) form** of Total Trust with respect to `Q`: for every
`Q`-measurable `X` and `s`, `∑ w, π w · (X w − s) · 𝟙[E_{P_w}(X) ≤ s] ≤ 0` (substitute `−X, −s`;
`−X` is `Q`-measurable with `X`).
Source: [[legitimacy]] R5.1 l. 97 (the below-threshold inequality)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem totalTrustWrt_iff_dual {Q : W → C} {π : W → ℝ} {F : Frame W} :
    TotalTrustWrt Q π F ↔ ∀ X : W → ℝ, MeasurableWrt Q X →
      ∀ s : ℝ, ∑ w, π w * (X w - s) * (if E (F.P w) X ≤ s then 1 else 0) ≤ 0 := by
  have key : ∀ (X : W → ℝ) (s : ℝ),
      ∑ w, π w * ((-X) w - -s) * (if -s ≤ E (F.P w) (-X) then 1 else 0) =
        -∑ w, π w * (X w - s) * (if E (F.P w) X ≤ s then 1 else 0) := by
    intro X s
    rw [← sum_neg_distrib]; apply sum_congr rfl; intro w _
    rw [E_neg_right]
    have : (-s ≤ -E (F.P w) X) ↔ (E (F.P w) X ≤ s) := neg_le_neg_iff
    simp only [Pi.neg_apply, this]; split_ifs <;> ring
  have hneg : ∀ X : W → ℝ, MeasurableWrt Q X → MeasurableWrt Q (-X) := by
    intro X hX w v h; simp only [Pi.neg_apply, hX w v h]
  constructor
  · intro h X hX s
    have := h (-X) (hneg X hX) (-s)
    rw [key] at this; linarith
  · intro h X hX s
    have := h (-X) (hneg X hX) (-s)
    have e := key (-X) (-s)
    simp only [neg_neg] at e
    rw [e]; linarith

/-- The dual form for the legitimacy-conditioned local criterion.
Source: [[legitimacy]] R5.1 l. 97
Kind: L
Fidelity: exact -/
theorem legitTotalTrustWrt_dual {Q : W → C} {π : W → ℝ} {F : Frame W} {L : Finset W}
    (h : LegitTotalTrustWrt Q π F L) (X : W → ℝ) (hX : MeasurableWrt Q X) (s : ℝ) :
    ∑ w, restrict π L w * (X w - s) * (if E (F.P w) X ≤ s then 1 else 0) ≤ 0 :=
  totalTrustWrt_iff_dual.1 h X hX s

/-! ## Measurability helpers -/

/-- Constants are measurable with respect to every question.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurableWrt_const (Q : W → C) (s : ℝ) : MeasurableWrt Q (fun _ => s) := fun _ _ _ => rfl

/-- Negation preserves `Q`-measurability.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem MeasurableWrt.neg {Q : W → C} {X : W → ℝ} (hX : MeasurableWrt Q X) :
    MeasurableWrt Q (-X) := fun w v h => by simp only [Pi.neg_apply, hX w v h]

/-- Sums preserve `Q`-measurability.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem MeasurableWrt.add {Q : W → C} {X Y : W → ℝ} (hX : MeasurableWrt Q X)
    (hY : MeasurableWrt Q Y) : MeasurableWrt Q (X + Y) :=
  fun w v h => by simp only [Pi.add_apply, hX w v h, hY w v h]

/-- Scalar multiples preserve `Q`-measurability.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem MeasurableWrt.smul {Q : W → C} {X : W → ℝ} (hX : MeasurableWrt Q X) (c : ℝ) :
    MeasurableWrt Q (c • X) := fun w v h => by simp only [Pi.smul_apply, hX w v h]

/-- A partial answer's indicator is `Q`-measurable.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurableWrt_ind_answer (Q : W → C) (T : Finset C) :
    MeasurableWrt Q (ind (answer Q T)) := by
  intro w v h
  simp only [ind, answer, mem_filter, mem_univ, true_and, h]

/-- Measurability with respect to a question is the same as being a function of the answer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem measurableWrt_iff_exists_comp (Q : W → C) (X : W → ℝ) :
    MeasurableWrt Q X ↔ ∃ x : C → ℝ, X = x ∘ Q := by
  classical
  constructor
  · intro hX
    refine ⟨fun c => if h : ∃ w, Q w = c then X h.choose else 0, ?_⟩
    funext w
    have hex : ∃ v, Q v = Q w := ⟨w, rfl⟩
    simp only [Function.comp, dif_pos hex]
    exact hX _ _ hex.choose_spec.symm
  · rintro ⟨x, rfl⟩ w v h
    simp only [Function.comp, h]

end

end Cleanroom.Corrigibility.CorrLegitGeneral
