import Cleanroom.Trust.TtFiniteFrames.Collapse
import Cleanroom.Found.LitDdbFrames.TotalTrust
import Mathlib.Algebra.CharZero.Infinite

/-!
# Soft ⟹ hard: the spectral-gap step of the finite collapse

Package `tt-finite-frames`, Target I2 (load-bearing 5), Mathlib-only abstract form. The FAF
instantiation with `LogicalInduction.Properties.SelfTrust.ctsInd` is the isolated file
`SoftCollapseCtsInd.lean`.

**Claim.** On a finite frame, if the *soft* conditional-martingale identity
`∑ w, π w · X w · ι_δ(E_{P_w}(X) > t) = ∑ w, π w · E_{P_w}(X) · ι_δ(E_{P_w}(X) > t)`
holds for every `X`, every threshold `t` and every ramp width `δ` below the spectral gap of `X`
(the least distance between distinct values of `w ↦ E_{P_w}(X)`), then the expert is immodest at
every world of positive prior probability.

**Proof of record** (the mandate's; three steps).
1. For `δ < gap` and `t` a value minus `δ`, the ramp equals the hard indicator `𝟙[E_w X ≥ value]`,
   so the hard threshold identity `∑_{E_w X ≥ c} π (X − E_w X) = 0` holds at every `c`; taking
   differences, the level-set identity `∑_{E_w X = a} π (X − a) = 0` holds at every attained `a`.
2. A separating `X*` with `E_v X* = E_w X* ↔ P_v = P_w` exists (the rows are finitely many distinct
   vectors; `X*` avoids finitely many hyperplanes — built by induction, no measure theory).
3. For arbitrary `Y` and large `λ`, the level sets of `Z = Y + λ X*` are exactly the cells;
   subtracting `λ ·` (the identity for `X*`) from the identity for `Z` gives
   `∑_{cell} π (Y − E_w Y) = 0` — the conditional martingale of I1 at every supported world.

The core theorem takes the form of the hypothesis the proof uses — *for each `X`, some* width
below the gap with an indicator that is `0` at or below the threshold and `1` at or above
threshold-plus-width, for all thresholds — and the headline forms (all widths below the gap; all
rational widths; one fixed width for all `X`, by rescaling) are corollaries. **The forms are
equivalent** (repair round 2, `softCore_iff_condMartingaleAt_all`, `softCM_iff_condMartingaleAt_all`,
`softCM_fixed_width_iff_condMartingaleAt_all`, `softCM_hyp_iff_fixed_width`): each is equivalent
to the hard conditional-martingale identity at **every** world, `∀ w, CondMartingaleAt π F w`,
for any ramp family, any fixed width and any prior (no sign condition) — the corpus's own
intermediate claim "the hypothesis collapses to `E(X) = E_π(X ∣ 𝒫)`" as a theorem. So none of the
forms is stronger or weaker than another: they are syntactically incomparable (a fixed width says
nothing at other widths; the gap form says nothing at widths above the gap) and semantically the
same proposition. The exported hard step is `condMartingaleAt_all_of_soft_core` (no positivity of
`π w`); the headlines add only I1. The value of `gap` when all estimates of `X` coincide (`1`) is
never used: only `0 < gap` and `gap ≤ |E_v X − E_w X|` for distinct values enter.
-/

namespace Cleanroom.Trust.TtFiniteFrames

open Finset Cleanroom.Found.LitDdbFrames

noncomputable section

set_option linter.unusedSectionVars false

variable {W : Type} [Fintype W] [DecidableEq W]

/-! ## The spectral gap -/

/-- The pairs of worlds at which the expert's estimates of `X` differ.
Source: none: infrastructure (I2)
Kind: D
Fidelity: n/a -/
def Frame.gapPairs (F : Frame W) (X : W → ℝ) : Finset (W × W) :=
  (univ ×ˢ univ).filter (fun p => E (F.P p.1) X ≠ E (F.P p.2) X)

/-- **The spectral gap of `X`**: the least positive distance between distinct values of
`w ↦ E_{P_w}(X)`; `1` when all values coincide (any positive number would do — the theorems below
use only `0 < gap` and `gap ≤ |E_v X − E_w X|` for distinct values).
Source: trust-lab-005 ("spectral gap `γ > 0`"); [[deference-in-logical-induction-v6]] §2.2
Kind: D
Fidelity: exact (with the stated convention when all values coincide) -/
def Frame.gap (F : Frame W) (X : W → ℝ) : ℝ :=
  if h : (Frame.gapPairs F X).Nonempty then
    (Frame.gapPairs F X).inf' h (fun p => |E (F.P p.1) X - E (F.P p.2) X|)
  else 1

/-- The gap is positive.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.gap_pos (F : Frame W) (X : W → ℝ) : 0 < Frame.gap F X := by
  unfold Frame.gap
  split_ifs with h
  · rw [Finset.lt_inf'_iff]
    intro p hp
    rw [Frame.gapPairs, mem_filter] at hp
    exact abs_pos.2 (sub_ne_zero.2 hp.2)
  · exact one_pos

/-- Distinct values of `X` differ by at least the gap.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Frame.gap_le (F : Frame W) (X : W → ℝ) {v w : W} (h : E (F.P v) X ≠ E (F.P w) X) :
    Frame.gap F X ≤ |E (F.P v) X - E (F.P w) X| := by
  have hmem : (v, w) ∈ Frame.gapPairs F X := by simp [Frame.gapPairs, h]
  unfold Frame.gap
  rw [dif_pos ⟨_, hmem⟩]
  exact Finset.inf'_le _ hmem

/-! ## Step 1: hard threshold and level-set identities from one soft width -/

/-- **Hard threshold identity from the soft one.** For a fixed `X`, a width `0 < δ < gap` and an
indicator `J` that is `0` at or below its threshold and `1` at or above threshold plus `δ`, the
soft identity at all thresholds gives `∑_{w : c ≤ E_w X} π w (X w − E_w X) = 0` for every real
`c`: take the least attained value `c* ≥ c` and threshold `t = c* − δ`; the ramp is then the hard
indicator of `[E(X) ≥ c]`.
Source: trust-lab-005; [[deference-in-logical-induction-v6]] §2.2 ("for `δ` below it the soft
indicator equals the hard one")
Kind: P
Fidelity: n/a (step 1 of I2)
Hyps: (a) as stated -/
theorem hard_threshold_of_soft {π : W → ℝ} {F : Frame W} (X : W → ℝ) {δ : ℝ} {J : ℝ → ℝ → ℝ}
    (hδ : 0 < δ) (hgap : δ < Frame.gap F X) (hJ0 : ∀ t x, x ≤ t → J t x = 0)
    (hJ1 : ∀ t x, t + δ ≤ x → J t x = 1)
    (hsoft : ∀ t, ∑ w, π w * X w * J t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * J t (E (F.P w) X))
    (c : ℝ) : ∑ w ∈ F.estEvent X c, π w * (X w - E (F.P w) X) = 0 := by
  set A := F.estEvent X c with hA
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · rw [hAe, sum_empty]
  obtain ⟨v, hvA, hvmin⟩ := exists_min_image A (fun w => E (F.P w) X) hAne
  have hvc : c ≤ E (F.P v) X := Frame.mem_estEvent.1 hvA
  set t := E (F.P v) X - δ with ht
  have hind : ∀ w, J t (E (F.P w) X) = if w ∈ A then 1 else 0 := by
    intro w
    split_ifs with hw
    · apply hJ1
      have := hvmin w hw
      linarith
    · apply hJ0
      have hlt : E (F.P w) X < c := not_le.1 (fun h => hw (Frame.mem_estEvent.2 h))
      have hne : E (F.P v) X ≠ E (F.P w) X := by linarith
      have hg := Frame.gap_le F X hne
      rw [abs_of_pos (by linarith)] at hg
      linarith
  have h := hsoft t
  simp only [hind, mul_ite, mul_one, mul_zero] at h
  rw [← sum_filter, ← sum_filter] at h
  have hfilt : univ.filter (fun w => w ∈ A) = A := by ext; simp
  rw [hfilt] at h
  have h' : ∑ a ∈ A, π a * X a - ∑ a ∈ A, π a * E (F.P a) X = 0 := sub_eq_zero.2 h
  rw [← h', ← sum_sub_distrib]
  apply sum_congr rfl
  intro w _
  ring

/-- **Level-set identity.** Under the hypotheses of `hard_threshold_of_soft`, at every attained
value `a = E_v X`: `∑_{w : E_w X = a} π w (X w − a) = 0`. The level set is
`[E(X) ≥ a] \ [E(X) ≥ a + gap/2]`.
Source: trust-lab-005 ("the hard identity at each fiber")
Kind: P
Fidelity: n/a (step 1 of I2)
Hyps: (a) as stated -/
theorem level_set_identity_of_soft {π : W → ℝ} {F : Frame W} (X : W → ℝ) {δ : ℝ}
    {J : ℝ → ℝ → ℝ} (hδ : 0 < δ) (hgap : δ < Frame.gap F X) (hJ0 : ∀ t x, x ≤ t → J t x = 0)
    (hJ1 : ∀ t x, t + δ ≤ x → J t x = 1)
    (hsoft : ∀ t, ∑ w, π w * X w * J t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * J t (E (F.P w) X))
    (v : W) :
    ∑ w ∈ univ.filter (fun w => E (F.P w) X = E (F.P v) X), π w * (X w - E (F.P v) X) = 0 := by
  set a := E (F.P v) X with ha
  have hg := Frame.gap_pos F X
  have h1 := hard_threshold_of_soft X hδ hgap hJ0 hJ1 hsoft a
  have h2 := hard_threshold_of_soft X hδ hgap hJ0 hJ1 hsoft (a + Frame.gap F X / 2)
  have hsub : F.estEvent X (a + Frame.gap F X / 2) ⊆ F.estEvent X a := by
    intro w hw
    rw [Frame.mem_estEvent] at hw ⊢
    linarith
  have hsdiff : F.estEvent X a \ F.estEvent X (a + Frame.gap F X / 2) =
      univ.filter (fun w => E (F.P w) X = a) := by
    ext w
    simp only [mem_sdiff, Frame.mem_estEvent, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨h₁, h₂⟩
      by_contra hne
      have hne' : E (F.P w) X ≠ E (F.P v) X := hne
      have := Frame.gap_le F X hne'
      rw [abs_of_pos (by rw [← ha]; exact sub_pos.2 (lt_of_le_of_ne h₁ (Ne.symm hne)))] at this
      apply h₂
      linarith
    · intro h
      refine ⟨h.ge, ?_⟩
      rw [h]
      linarith
  have h3 := sum_sdiff hsub (f := fun w => π w * (X w - E (F.P w) X))
  rw [h1, h2, add_zero, hsdiff] at h3
  rw [← h3]
  apply sum_congr rfl
  intro w hw
  rw [mem_filter] at hw
  rw [hw.2]

/-! ## Step 2: a separating variable -/

/-- **Finitely many nonzero vectors admit a common non-annihilated direction**: for a finite set
`D` of nonzero `d : W → ℝ` there is `X` with `⟨d, X⟩ ≠ 0` for all `d ∈ D`. Induction on `D`: given
`X` for `D`, perturb along the new `d` by a real `s` outside the finitely many values that kill
some `⟨d', X + s d⟩`.
Source: none: infrastructure (I2, step 2)
Kind: P
Fidelity: n/a -/
theorem exists_forall_sum_mul_ne_zero (D : Finset (W → ℝ)) (hD : ∀ d ∈ D, d ≠ 0) :
    ∃ X : W → ℝ, ∀ d ∈ D, ∑ w, d w * X w ≠ 0 := by
  haveI : DecidableEq (W → ℝ) := Classical.decEq _
  induction D using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert d D _ ih =>
    obtain ⟨X, hX⟩ := ih (fun d' hd' => hD d' (mem_insert_of_mem hd'))
    have hd : d ≠ 0 := hD d (mem_insert_self d D)
    have hdd : 0 < ∑ w, d w * d w := by
      have : ∃ w, d w ≠ 0 := by
        by_contra h
        push Not at h
        exact hd (funext h)
      obtain ⟨w, hw⟩ := this
      exact sum_pos' (fun w _ => mul_self_nonneg (d w)) ⟨w, mem_univ w, mul_self_pos.2 hw⟩
    set bad : Finset ℝ :=
      (insert d D).image (fun d' => -(∑ w, d' w * X w) / (∑ w, d' w * d w)) with hbad
    obtain ⟨s, hs⟩ := Infinite.exists_notMem_finset bad
    refine ⟨X + s • d, ?_⟩
    intro d' hd'
    have hexp : ∑ w, d' w * (X + s • d) w = ∑ w, d' w * X w + s * ∑ w, d' w * d w := by
      rw [mul_sum, ← sum_add_distrib]
      apply sum_congr rfl
      intro w _
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hexp]
    intro h0
    by_cases hc : ∑ w, d' w * d w = 0
    · rw [hc, mul_zero, add_zero] at h0
      rcases mem_insert.1 hd' with rfl | hd'D
      · exact hdd.ne' hc
      · exact hX d' hd'D h0
    · apply hs
      rw [hbad, mem_image]
      refine ⟨d', hd', ?_⟩
      rw [div_eq_iff hc]
      linarith

/-- **A separating variable exists**: some `X*` has `E_v X* = E_w X* ↔ P_v = P_w` — its level
sets are exactly the cells of the frame.
Source: mandate I2 step 2 ("pick `X*` off finitely many hyperplanes")
Kind: P
Fidelity: n/a -/
theorem Frame.exists_separating (F : Frame W) :
    ∃ X : W → ℝ, ∀ v w, E (F.P v) X = E (F.P w) X ↔ F.P v = F.P w := by
  classical
  set D : Finset (W → ℝ) :=
    ((univ ×ˢ univ).filter (fun p : W × W => F.P p.1 ≠ F.P p.2)).image
      (fun p => F.P p.1 - F.P p.2) with hD
  have hD0 : ∀ d ∈ D, d ≠ 0 := by
    intro d hd
    rw [hD, mem_image] at hd
    obtain ⟨p, hp, rfl⟩ := hd
    rw [mem_filter] at hp
    exact sub_ne_zero.2 hp.2
  obtain ⟨X, hX⟩ := exists_forall_sum_mul_ne_zero D hD0
  refine ⟨X, fun v w => ⟨fun h => ?_, fun h => by rw [h]⟩⟩
  by_contra hne
  have hmem : F.P v - F.P w ∈ D := by
    rw [hD, mem_image]
    exact ⟨(v, w), by simp [hne], rfl⟩
  apply hX _ hmem
  simp only [Pi.sub_apply, sub_mul, sum_sub_distrib]
  exact sub_eq_zero.2 h

/-! ## Step 3: the hard step at every world, and the core theorem -/

/-- **Soft ⟹ hard, literally (the exported step 3).** If for every `X` there is a width `δ` below
the spectral gap of `X` and an indicator `J` (zero at or below its threshold, one at or above
threshold plus `δ`) with the soft conditional-martingale identity at every threshold, then the
hard conditional-martingale identity `CondMartingaleAt π F w` holds at **every** world `w` —
supported or not, with no sign condition on `π`. This is the corpus's intermediate claim "the
hypothesis collapses to `E(X) = E_π(X ∣ 𝒫)`" as a theorem; the headline forms below add only I1
(`CondMartingaleAt.selfMass_eq_one`) at the supported worlds.
Source: trust-lab-005 (Q3 / D8); root-deference-011 (the prose step);
[[deference-in-logical-induction-v1]] §5.2 (the proof's intermediate step, l. 225);
[[deference-in-logical-induction-v6]] §2.2 (l. 316); exported in repair round 2 (audit r2
fidelity N2 / adversarial N1)
Kind: P
Fidelity: exact (the intermediate step the sources state and this package's proof of record
establishes en route)
Hyps: (a) `hsoft` (the soft identity, in the stated form); no full support, no sign condition -/
theorem condMartingaleAt_all_of_soft_core {π : W → ℝ} {F : Frame W}
    (hsoft : ∀ X : W → ℝ, ∃ (δ : ℝ) (J : ℝ → ℝ → ℝ), 0 < δ ∧ δ < Frame.gap F X ∧
      (∀ t x, x ≤ t → J t x = 0) ∧ (∀ t x, t + δ ≤ x → J t x = 1) ∧
      ∀ t, ∑ w, π w * X w * J t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * J t (E (F.P w) X)) :
    ∀ w, CondMartingaleAt π F w := by
  -- the level-set identity for every `X` and world
  have hlevel : ∀ (X : W → ℝ) (v : W),
      ∑ w ∈ univ.filter (fun w => E (F.P w) X = E (F.P v) X), π w * (X w - E (F.P v) X) = 0 := by
    intro X v
    obtain ⟨δ, J, hδ, hgap, hJ0, hJ1, hs⟩ := hsoft X
    exact level_set_identity_of_soft X hδ hgap hJ0 hJ1 hs v
  obtain ⟨Xs, hXs⟩ := Frame.exists_separating F
  intro w₀
  unfold CondMartingaleAt
  intro Y
  -- the scale `λ`: larger than every estimate difference of `Y`, divided by the gap of `Xs`
  have hg := Frame.gap_pos F Xs
  obtain ⟨p, -, hp⟩ := exists_max_image (univ ×ˢ univ)
    (fun p : W × W => |E (F.P p.1) Y - E (F.P p.2) Y|) ⟨(w₀, w₀), by simp⟩
  set M := |E (F.P p.1) Y - E (F.P p.2) Y| with hM
  have hMle : ∀ v w, |E (F.P v) Y - E (F.P w) Y| ≤ M := fun v w => hp (v, w) (by simp)
  have hM0 : 0 ≤ M := abs_nonneg _
  set lam := (M + 1) / Frame.gap F Xs with hlam
  have hlampos : 0 < lam := div_pos (by linarith) hg
  set Z : W → ℝ := Y + lam • Xs with hZ
  have hEZ : ∀ v, E (F.P v) Z = E (F.P v) Y + lam * E (F.P v) Xs := fun v => by
    rw [hZ, E_add_right, E_smul_right]
  -- level sets of `Z` and of `Xs` at `w₀` are the cell of `w₀`
  have hsep : ∀ v, E (F.P v) Z = E (F.P w₀) Z → F.P v = F.P w₀ := by
    intro v hv
    by_contra hne
    have hXne : E (F.P v) Xs ≠ E (F.P w₀) Xs := fun h => hne ((hXs v w₀).1 h)
    have hgle := Frame.gap_le F Xs hXne
    rw [hEZ, hEZ] at hv
    have h1 : E (F.P v) Y - E (F.P w₀) Y = -(lam * (E (F.P v) Xs - E (F.P w₀) Xs)) := by
      linarith
    have h2 : |E (F.P v) Y - E (F.P w₀) Y| = lam * |E (F.P v) Xs - E (F.P w₀) Xs| := by
      rw [h1, abs_neg, abs_mul, abs_of_pos hlampos]
    have h3 : lam * Frame.gap F Xs ≤ lam * |E (F.P v) Xs - E (F.P w₀) Xs| :=
      mul_le_mul_of_nonneg_left hgle hlampos.le
    have h4 : lam * Frame.gap F Xs = M + 1 := by
      rw [hlam, div_mul_cancel₀ _ hg.ne']
    have h5 := hMle v w₀
    linarith
  have hcellZ : univ.filter (fun w => E (F.P w) Z = E (F.P w₀) Z) = F.cell (F.P w₀) := by
    ext v
    simp only [mem_filter, mem_univ, true_and, Frame.mem_cell]
    exact ⟨hsep v, fun h => by rw [h]⟩
  have hcellX : univ.filter (fun w => E (F.P w) Xs = E (F.P w₀) Xs) = F.cell (F.P w₀) := by
    ext v
    simp only [mem_filter, mem_univ, true_and, Frame.mem_cell]
    exact hXs v w₀
  have hZ0 := hlevel Z w₀
  have hX0 := hlevel Xs w₀
  rw [hcellZ] at hZ0
  rw [hcellX] at hX0
  -- subtract `lam ·` the `Xs` identity from the `Z` identity
  have hY0 : ∑ w ∈ F.cell (F.P w₀), π w * (Y w - E (F.P w₀) Y) = 0 := by
    have : ∀ w, π w * (Y w - E (F.P w₀) Y) =
        π w * (Z w - E (F.P w₀) Z) - lam * (π w * (Xs w - E (F.P w₀) Xs)) := by
      intro w
      rw [hEZ, hZ]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    simp only [this, sum_sub_distrib, ← mul_sum, hZ0, hX0, mul_zero, sub_zero]
  -- conclude the product-form conditional martingale
  have hsum : ∑ w ∈ F.cell (F.P w₀), π w * (Y w - E (F.P w₀) Y) =
      ∑ w ∈ F.cell (F.P w₀), π w * Y w - E (F.P w₀) Y * mass π (F.cell (F.P w₀)) := by
    rw [mass, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro w _
    ring
  rw [hsum] at hY0
  linarith

/-- **I2, core form.** If for every `X` there is a width `δ` below the spectral gap of `X` and an
indicator `J` (zero at or below its threshold, one at or above threshold plus `δ`) with the soft
conditional-martingale identity at every threshold, then the expert is immodest at every world
of positive prior probability: the hard step `condMartingaleAt_all_of_soft_core` at every world,
then I1 at the supported ones. This is the form of the hypothesis the proof of record uses; the
corpus's "for all `δ` below the gap" (`softCM_immodest`), the rational-width form
(`softCM_immodest_rat`) and the fixed-width form (`softCM_immodest_fixed_width`) are corollaries,
and all four hypothesis forms are equivalent (`softCore_iff_condMartingaleAt_all` and the
equivalences after it).
Source: trust-lab-005 (Q3 / D8); root-deference-011 (the prose step);
[[deference-in-logical-induction-v6]] §2.2
Kind: P
Fidelity: variant: hypothesis quantified existentially over the width (per `X`) rather than
universally below the gap — equivalent to the headline's hypothesis
(`softCore_iff_condMartingaleAt_all`, `softCM_iff_condMartingaleAt_all`), so this is the headline
stated at the form the proof consumes, not a stronger theorem (relabelled in repair round 2)
Hyps: (a) `hsoft` (the soft identity, in the stated form); no full support is assumed — the
conclusion is on the support -/
theorem softCM_immodest_core {π : W → ℝ} {F : Frame W}
    (hsoft : ∀ X : W → ℝ, ∃ (δ : ℝ) (J : ℝ → ℝ → ℝ), 0 < δ ∧ δ < Frame.gap F X ∧
      (∀ t x, x ≤ t → J t x = 0) ∧ (∀ t x, t + δ ≤ x → J t x = 1) ∧
      ∀ t, ∑ w, π w * X w * J t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * J t (E (F.P w) X)) :
    ∀ w, 0 < π w → F.selfMass (F.P w) = 1 :=
  fun w hw => CondMartingaleAt.selfMass_eq_one hw (condMartingaleAt_all_of_soft_core hsoft w)

/-! ## The headline forms -/

/-- A **ramp family** `ι δ t x` (`= Ind_δ(x > t)`): `0` for `x ≤ t` and `1` for `x ≥ t + δ`, for
every positive width; the values in between are irrelevant.
Source: mandate I2 (abstract ramp); FAF `ctsInd` is the instance (`SoftCollapseCtsInd.lean`)
Kind: D
Fidelity: exact -/
structure IsRamp (ι : ℝ → ℝ → ℝ → ℝ) : Prop where
  /-- off below the threshold -/
  zero_of_le : ∀ δ t x, 0 < δ → x ≤ t → ι δ t x = 0
  /-- on above threshold plus width -/
  one_of_ge : ∀ δ t x, 0 < δ → t + δ ≤ x → ι δ t x = 1

/-- The gap-form hypothesis (all widths below the gap, for a ramp family) gives the core
hypothesis: at each `X` take the width `gap F X / 2` and the ramp itself as the indicator.
Source: none: infrastructure (I2)
Kind: L
Fidelity: n/a -/
theorem softCore_of_gap_form {π : W → ℝ} {F : Frame W} {ι : ℝ → ℝ → ℝ → ℝ} (hι : IsRamp ι)
    (hsoft : ∀ (X : W → ℝ) (t δ : ℝ), 0 < δ → δ < Frame.gap F X →
      ∑ w, π w * X w * ι δ t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * ι δ t (E (F.P w) X)) :
    ∀ X : W → ℝ, ∃ (δ : ℝ) (J : ℝ → ℝ → ℝ), 0 < δ ∧ δ < Frame.gap F X ∧
      (∀ t x, x ≤ t → J t x = 0) ∧ (∀ t x, t + δ ≤ x → J t x = 1) ∧
      ∀ t, ∑ w, π w * X w * J t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * J t (E (F.P w) X) :=
  fun X =>
    ⟨Frame.gap F X / 2, ι (Frame.gap F X / 2), half_pos (Frame.gap_pos F X), half_lt_self (Frame.gap_pos F X),
      fun t x hx => hι.zero_of_le _ t x (half_pos (Frame.gap_pos F X)) hx,
      fun t x hx => hι.one_of_ge _ t x (half_pos (Frame.gap_pos F X)) hx,
      fun t => hsoft X t _ (half_pos (Frame.gap_pos F X)) (half_lt_self (Frame.gap_pos F X))⟩

/-- **I2 (load-bearing 5). Soft ⟹ hard, the spectral-gap step.** For a ramp family `ι`, if the
soft conditional-martingale identity
`∑ w, π w · X w · ι δ t (E_w X) = ∑ w, π w · E_w X · ι δ t (E_w X)` holds for every `X`, every
threshold `t` and every width `0 < δ < gap F X`, then the expert is immodest at every world of
positive prior probability. Every finite frame has a positive gap, so there is no finite
"gap → 0" near-miss: the theorem excludes finitely many gapped values, not countably many. The
hypothesis is equivalent to the hard identity at every world (`softCM_iff_condMartingaleAt_all`),
so for a full-support prior its inhabitants are exactly T1's partition experts.
Source: trust-lab-005; root-deference-011; [[deference-in-logical-induction-v6]] §2.2
Kind: P
Fidelity: exact (the corpus's "for all `δ` below the gap"; proved through the core form)
Hyps: (a) `hι` (ramp shape), `hsoft`; no full support — conclusion on the support -/
theorem softCM_immodest {π : W → ℝ} {F : Frame W} {ι : ℝ → ℝ → ℝ → ℝ} (hι : IsRamp ι)
    (hsoft : ∀ (X : W → ℝ) (t δ : ℝ), 0 < δ → δ < Frame.gap F X →
      ∑ w, π w * X w * ι δ t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * ι δ t (E (F.P w) X)) :
    ∀ w, 0 < π w → F.selfMass (F.P w) = 1 :=
  softCM_immodest_core (softCore_of_gap_form hι hsoft)

/-- **I2, the hard step at the headline's hypothesis.** The gap-form soft identity for a ramp
family gives the hard conditional-martingale identity at every world (no positivity).
Source: trust-lab-005 ("hard identity at each fiber"); audit r2 adversarial N1
Kind: L
Fidelity: exact -/
theorem softCM_condMartingaleAt {π : W → ℝ} {F : Frame W} {ι : ℝ → ℝ → ℝ → ℝ} (hι : IsRamp ι)
    (hsoft : ∀ (X : W → ℝ) (t δ : ℝ), 0 < δ → δ < Frame.gap F X →
      ∑ w, π w * X w * ι δ t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * ι δ t (E (F.P w) X)) :
    ∀ w, CondMartingaleAt π F w :=
  condMartingaleAt_all_of_soft_core (softCore_of_gap_form hι hsoft)

/-- **I2, rational widths.** The same with the width ranging over the positive rationals below
the gap (as FAF's `ctsInd` takes `δ : ℚ`): a rational width below the gap exists by density.
Source: mandate I2 ("quantify `hsoft` over rational `δ`")
Kind: P
Fidelity: variant: widths rational
Hyps: (a) `hι0`, `hι1` (ramp shape at rational widths), `hsoft` -/
theorem softCM_immodest_rat {π : W → ℝ} {F : Frame W} {ι : ℚ → ℝ → ℝ → ℝ}
    (hι0 : ∀ (δ : ℚ) (t x : ℝ), 0 < δ → x ≤ t → ι δ t x = 0)
    (hι1 : ∀ (δ : ℚ) (t x : ℝ), 0 < δ → t + δ ≤ x → ι δ t x = 1)
    (hsoft : ∀ (X : W → ℝ) (t : ℝ) (δ : ℚ), 0 < δ → (δ : ℝ) < Frame.gap F X →
      ∑ w, π w * X w * ι δ t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * ι δ t (E (F.P w) X)) :
    ∀ w, 0 < π w → F.selfMass (F.P w) = 1 :=
  softCM_immodest_core fun X => by
    obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (Frame.gap_pos F X)
    have hq0' : (0 : ℚ) < q := by exact_mod_cast hq0
    exact ⟨q, ι q, hq0, hq1, fun t x hx => hι0 q t x hq0' hx, fun t x hx => hι1 q t x hq0' hx,
      fun t => hsoft X t q hq0' hq1⟩

/-- **I2, corollary via I1**: under the soft identity the frame is immodest on the support.
Source: trust-lab-005 ("hence immodesty")
Kind: L
Fidelity: exact -/
theorem immodest_on_supp_of_softCM {π : W → ℝ} {F : Frame W} {ι : ℝ → ℝ → ℝ → ℝ} (hι : IsRamp ι)
    (hsoft : ∀ (X : W → ℝ) (t δ : ℝ), 0 < δ → δ < Frame.gap F X →
      ∑ w, π w * X w * ι δ t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * ι δ t (E (F.P w) X)) :
    ∀ w ∈ supp π, F.selfMass (F.P w) = 1 :=
  fun w hw => softCM_immodest hι hsoft w (by simpa [supp] using hw)

/-- The fixed-width hypothesis (one width `δ₀ > 0` for all `X`, all thresholds) gives the core
hypothesis, by rescaling: at `λ = 2δ₀ / gap F X` the ramp of width `δ₀` on `λ X` (with
`E_w(λX) = λ E_w X`) is a `0/1`-shaped indicator of width `gap F X / 2` on `X`.
Source: none: infrastructure (I2; the rescaling of repair round 1)
Kind: L
Fidelity: n/a -/
theorem softCore_of_fixed_width {π : W → ℝ} {F : Frame W} {ι : ℝ → ℝ → ℝ → ℝ}
    (hι : IsRamp ι) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hsoft : ∀ (X : W → ℝ) (t : ℝ),
      ∑ w, π w * X w * ι δ₀ t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * ι δ₀ t (E (F.P w) X)) :
    ∀ X : W → ℝ, ∃ (δ : ℝ) (J : ℝ → ℝ → ℝ), 0 < δ ∧ δ < Frame.gap F X ∧
      (∀ t x, x ≤ t → J t x = 0) ∧ (∀ t x, t + δ ≤ x → J t x = 1) ∧
      ∀ t, ∑ w, π w * X w * J t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * J t (E (F.P w) X) := by
  intro X
  have hg := Frame.gap_pos F X
  have hg' := hg.ne'
  set lam := 2 * δ₀ / Frame.gap F X with hlam
  have hlampos : 0 < lam := by positivity
  have hlamgap : lam * (Frame.gap F X / 2) = δ₀ := by
    rw [hlam]; field_simp
  refine ⟨Frame.gap F X / 2, fun t x => ι δ₀ (lam * t) (lam * x), half_pos hg, half_lt_self hg,
    ?_, ?_, ?_⟩
  · intro t x hx
    exact hι.zero_of_le δ₀ _ _ hδ₀ (mul_le_mul_of_nonneg_left hx hlampos.le)
  · intro t x hx
    apply hι.one_of_ge δ₀ _ _ hδ₀
    calc lam * t + δ₀ = lam * (t + Frame.gap F X / 2) := by rw [mul_add, hlamgap]
      _ ≤ lam * x := mul_le_mul_of_nonneg_left hx hlampos.le
  · intro t
    have h := hsoft (lam • X) (lam * t)
    have hE : ∀ w, E (F.P w) (lam • X) = lam * E (F.P w) X := fun w => E_smul_right _ _ _
    simp only [hE, Pi.smul_apply, smul_eq_mul] at h
    have h' : lam * ∑ w, π w * X w * ι δ₀ (lam * t) (lam * E (F.P w) X) =
        lam * ∑ w, π w * E (F.P w) X * ι δ₀ (lam * t) (lam * E (F.P w) X) := by
      rw [mul_sum, mul_sum]
      calc ∑ w, lam * (π w * X w * ι δ₀ (lam * t) (lam * E (F.P w) X))
          = ∑ w, π w * (lam * X w) * ι δ₀ (lam * t) (lam * E (F.P w) X) := by
            apply sum_congr rfl; intro w _; ring
        _ = ∑ w, π w * (lam * E (F.P w) X) * ι δ₀ (lam * t) (lam * E (F.P w) X) := h
        _ = ∑ w, lam * (π w * E (F.P w) X * ι δ₀ (lam * t) (lam * E (F.P w) X)) := by
            apply sum_congr rfl; intro w _; ring
    exact mul_left_cancel₀ hlampos.ne' h'

/-- **I2, one fixed width suffices.** The soft identity at a *single* width `δ₀ > 0`, for all
`X` and all thresholds, already forces immodesty on the support — with no mention of the gap
(`softCore_of_fixed_width`, by rescaling). So on a finite frame the spectral gap is not what makes
the reduction work: the scale-freedom of the hypothesis is (finding F-I2c). This theorem is
neither stronger nor weaker than `softCM_immodest`: the two hypotheses are syntactically
incomparable (this one says nothing at widths other than `δ₀`; the gap form says nothing at
`δ₀` for an `X` whose gap is at most `δ₀`) and semantically equivalent — both are the hard
identity at every world (`softCM_hyp_iff_fixed_width`). It is the headline with the redundant
gap clause removed.
Source: none: agenda push (audit r1 fidelity N2); relabelled in repair round 2 (audit r2
adversarial B1 / fidelity N2)
Kind: P
Fidelity: variant: one fixed width for all `X`, no gap clause — hypothesis equivalent to the
headline's (`softCM_hyp_iff_fixed_width`)
Hyps: (a) `hι` (ramp shape), `hδ₀`, `hsoft`; no full support — conclusion on the support -/
theorem softCM_immodest_fixed_width {π : W → ℝ} {F : Frame W} {ι : ℝ → ℝ → ℝ → ℝ}
    (hι : IsRamp ι) {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hsoft : ∀ (X : W → ℝ) (t : ℝ),
      ∑ w, π w * X w * ι δ₀ t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * ι δ₀ t (E (F.P w) X)) :
    ∀ w, 0 < π w → F.selfMass (F.P w) = 1 :=
  softCM_immodest_core (softCore_of_fixed_width hι hδ₀ hsoft)

/-- The hard indicator `𝟙[t < x]` is a ramp family (any width): the abstract theorem covers the
hard conditional martingale too. N− as a witness of the ramp hypothesis alone — it is the
degenerate ramp with an empty transition region; the genuinely soft inhabitant is `linearRamp`
(`linearRamp_isRamp`, N+), and FAF's `ctsInd` (`SoftCollapseCtsInd`), whose width is rational,
enters through `softCM_immodest_rat`'s shape lemmas. The witness of the *full* package of
`softCM_immodest` is `T4.FA_witness` (`Witnesses.lean`).
Source: none: infrastructure
Kind: N−
Fidelity: n/a -/
theorem isRamp_hardIndicator : IsRamp (fun _ t x => if t < x then (1 : ℝ) else 0) where
  zero_of_le := fun _ t x _ hx => by simp [not_lt.2 hx]
  one_of_ge := fun δ t x hδ hx => by simp [show t < x by linarith]

/-- The **linear ramp** of width `δ` at threshold `t`: `min 1 (max 0 ((x − t)/δ))` — the
real-width analogue of FAF's `ctsInd` (whose width is rational).
Source: none: infrastructure (audit r2 adversarial N2, probe Q1)
Kind: D
Fidelity: n/a -/
def linearRamp : ℝ → ℝ → ℝ → ℝ := fun δ t x => min 1 (max 0 ((x - t) / δ))

/-- The linear ramp is a ramp family, and it is genuinely soft: at the midpoint of its transition
region (`δ = 2`, `t = 0`, `x = 1`) it is `1/2`. The N+ inhabitant of `IsRamp`.
Source: none: audit r2 adversarial N2 (probe Q1, moved into the library)
Kind: N+
Fidelity: n/a -/
theorem linearRamp_isRamp : IsRamp linearRamp ∧ linearRamp 2 0 1 = 1 / 2 := by
  refine ⟨⟨fun δ t x hδ hx => ?_, fun δ t x hδ hx => ?_⟩, ?_⟩
  · unfold linearRamp
    have : (x - t) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
    rw [max_eq_left this, min_eq_right zero_le_one]
  · unfold linearRamp
    have : 1 ≤ (x - t) / δ := by rw [le_div_iff₀ hδ]; linarith
    rw [max_eq_right (by linarith), min_eq_left this]
  · unfold linearRamp; norm_num

/-! ## The hypothesis forms are equivalent

Each of the four soft hypothesis forms — core (some width below the gap per `X`), gap form (all
widths below the gap), fixed width (one `δ₀` for all `X`), and the hard identity at every world —
implies the others, for any ramp family, any `δ₀ > 0` and any prior. The direction "hard ⟹ soft"
holds for *every* weight function of the estimate, not only ramps: regroup by cells. -/

/-- **Hard ⟹ soft, for any indicator family.** If the conditional-martingale identity holds at
every world, then for every `ρ : ℝ → ℝ → ℝ → ℝ` whatsoever (no ramp shape), every `X`, `t`, `δ`,
the soft identity holds: regroup by the frame's cells, on which the estimate and hence the
indicator are constant. (`ofPartition_soft_identity` in `Witnesses.lean` is the partition-expert
case.)
Source: [[deference-in-logical-induction-v1]] §5.2 (the converse of the proof's intermediate
step); audit r2 (fidelity P1 / adversarial Q3, moved into the library)
Kind: P
Fidelity: exact
Hyps: (a) `hCM` -/
theorem soft_identity_of_condMartingaleAt_all {π : W → ℝ} {F : Frame W}
    (hCM : ∀ w, CondMartingaleAt π F w) (ρ : ℝ → ℝ → ℝ → ℝ) (X : W → ℝ) (t δ : ℝ) :
    ∑ w, π w * X w * ρ δ t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * ρ δ t (E (F.P w) X) := by
  classical
  -- regroup any sum over `W` by the frame's cells (the fibres of `F.P`)
  have hsplit : ∀ g : W → ℝ, ∑ w, g w = ∑ r ∈ univ.image F.P, ∑ w ∈ F.cell r, g w := by
    intro g
    rw [← sum_fiberwise_of_maps_to (g := F.P) (t := univ.image F.P)
      (fun w _ => mem_image_of_mem F.P (mem_univ w))]
    apply sum_congr rfl
    intro r _
    apply sum_congr _ (fun _ _ => rfl)
    ext w
    simp only [mem_filter, mem_univ, true_and, Frame.mem_cell]
  rw [hsplit, hsplit]
  apply sum_congr rfl
  intro r hr
  obtain ⟨v, _, rfl⟩ := mem_image.1 hr
  have hrow : ∀ w ∈ F.cell (F.P v), F.P w = F.P v := fun w hw => Frame.mem_cell.1 hw
  calc ∑ w ∈ F.cell (F.P v), π w * X w * ρ δ t (E (F.P w) X)
      = ρ δ t (E (F.P v) X) * ∑ w ∈ F.cell (F.P v), π w * X w := by
        rw [mul_sum]; apply sum_congr rfl; intro w hw; rw [hrow w hw]; ring
    _ = ρ δ t (E (F.P v) X) * (E (F.P v) X * mass π (F.cell (F.P v))) := by
        rw [← hCM v X]
    _ = ∑ w ∈ F.cell (F.P v), π w * E (F.P w) X * ρ δ t (E (F.P w) X) := by
        rw [mass, mul_sum, mul_sum]; apply sum_congr rfl; intro w hw; rw [hrow w hw]; ring

/-- **The core hypothesis ⟺ the hard identity at every world.** (⟸) at each `X` take the width
`gap F X / 2` and the hard indicator `𝟙[t < x]`.
Source: audit r2 (fidelity N2 / adversarial B1); the corpus's "the hypothesis collapses to
`E(X) = E_π(X ∣ 𝒫)`" ([[deference-in-logical-induction-v1]] §5.2, v6 §2.2)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem softCore_iff_condMartingaleAt_all {π : W → ℝ} {F : Frame W} :
    (∀ X : W → ℝ, ∃ (δ : ℝ) (J : ℝ → ℝ → ℝ), 0 < δ ∧ δ < Frame.gap F X ∧
      (∀ t x, x ≤ t → J t x = 0) ∧ (∀ t x, t + δ ≤ x → J t x = 1) ∧
      ∀ t, ∑ w, π w * X w * J t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * J t (E (F.P w) X)) ↔
    ∀ w, CondMartingaleAt π F w := by
  refine ⟨condMartingaleAt_all_of_soft_core, fun hCM X => ?_⟩
  have hg := Frame.gap_pos F X
  refine ⟨Frame.gap F X / 2, fun t x => if t < x then (1 : ℝ) else 0, half_pos hg,
    half_lt_self hg, fun t x hx => by simp [not_lt.2 hx],
    fun t x hx => by simp [show t < x by linarith], fun t => ?_⟩
  exact soft_identity_of_condMartingaleAt_all hCM (fun _ t x => if t < x then (1 : ℝ) else 0)
    X t (Frame.gap F X / 2)

/-- **The gap-form hypothesis ⟺ the hard identity at every world**, for any ramp family.
Source: audit r2 (fidelity P3 / adversarial Q4); the corpus's intermediate claim (v1 §5.2, v6 §2.2)
Kind: P
Fidelity: exact
Hyps: (a) `hι` -/
theorem softCM_iff_condMartingaleAt_all {π : W → ℝ} {F : Frame W} {ι : ℝ → ℝ → ℝ → ℝ}
    (hι : IsRamp ι) :
    (∀ (X : W → ℝ) (t δ : ℝ), 0 < δ → δ < Frame.gap F X →
      ∑ w, π w * X w * ι δ t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * ι δ t (E (F.P w) X)) ↔
    ∀ w, CondMartingaleAt π F w :=
  ⟨softCM_condMartingaleAt hι,
    fun hCM X t δ _ _ => soft_identity_of_condMartingaleAt_all hCM ι X t δ⟩

/-- **The fixed-width hypothesis ⟺ the hard identity at every world**, for any ramp family and
any `δ₀ > 0`.
Source: audit r2 (fidelity P4 / adversarial Q4)
Kind: P
Fidelity: exact
Hyps: (a) `hι`, `hδ₀` -/
theorem softCM_fixed_width_iff_condMartingaleAt_all {π : W → ℝ} {F : Frame W}
    {ι : ℝ → ℝ → ℝ → ℝ} (hι : IsRamp ι) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    (∀ (X : W → ℝ) (t : ℝ),
      ∑ w, π w * X w * ι δ₀ t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * ι δ₀ t (E (F.P w) X)) ↔
    ∀ w, CondMartingaleAt π F w :=
  ⟨fun hsoft => condMartingaleAt_all_of_soft_core (softCore_of_fixed_width hι hδ₀ hsoft),
    fun hCM X t => soft_identity_of_condMartingaleAt_all hCM ι X t δ₀⟩

/-- **The gap-form and fixed-width hypotheses are equivalent** (any ramp family, any `δ₀ > 0`,
any prior): neither `softCM_immodest` nor `softCM_immodest_fixed_width` is stronger than the
other — they are one theorem under two spellings of its hypothesis.
Source: audit r2 (fidelity P5 / adversarial Q4)
Kind: P
Fidelity: exact
Hyps: (a) `hι`, `hδ₀` -/
theorem softCM_hyp_iff_fixed_width {π : W → ℝ} {F : Frame W} {ι : ℝ → ℝ → ℝ → ℝ}
    (hι : IsRamp ι) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    (∀ (X : W → ℝ) (t δ : ℝ), 0 < δ → δ < Frame.gap F X →
      ∑ w, π w * X w * ι δ t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * ι δ t (E (F.P w) X)) ↔
    (∀ (X : W → ℝ) (t : ℝ),
      ∑ w, π w * X w * ι δ₀ t (E (F.P w) X) = ∑ w, π w * E (F.P w) X * ι δ₀ t (E (F.P w) X)) :=
  (softCM_iff_condMartingaleAt_all hι).trans
    (softCM_fixed_width_iff_condMartingaleAt_all hι hδ₀).symm

end

end Cleanroom.Trust.TtFiniteFrames
