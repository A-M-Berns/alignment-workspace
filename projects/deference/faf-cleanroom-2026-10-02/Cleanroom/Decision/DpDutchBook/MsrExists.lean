import Cleanroom.Decision.DpDutchBook.MsrValues
import Cleanroom.Found.FixKakutani.Transport
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.OrderClosed

/-!
# T7(b)–(d): continuity of the tremble-pinned value and MSR existence by Kakutani (over `ℝ`)

* `rawProc C d x` — the weights of `C[d ↦ x]` as a raw dependent function of the label
  `x : acts d → ℝ`; `rawQ`, `rawNu` — `Q_a` and `R` as functions of the raw label, continuous
  everywhere (`rawQ_continuous`, `rawNu_continuous`: products and sums of coordinate functions).
* `r3Raw a x := rawQ a x / rawNu x` — the tremble-pinned act value as a function of the raw
  label; `r3Val_eq_r3Raw` identifies it with `r3Val` on the simplex under the standing
  hypothesis, and `r3Raw_continuousOn` is T7(b)'s continuity.
* `brRaw x` — Definition 18's best-response face against `x` as a set of raw labels; it maps
  the simplex into itself with nonempty convex values and a **closed graph, proved**
  (`brRaw_hasClosedGraphOn`, by the sequential criterion and the continuity above).
* `msrAtD4_exists` — **T7(d), MSR existence without trembles**: under F3′ (structural), disjoint
  action events and the standing hypothesis `∀ m, 0 < ν_{C[d↦m]}(O_d)`, some label `m` has
  `MsrAtD4 (C[d ↦ m]) B d`, by `fix-kakutani`'s `kakutani_findim` (grade (a)).
  `adviceEdt_clause_exists` restates the conclusion as the `d`-clause of `dp-calibration`'s D4.
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpDutchBook

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Decision.DpCalibration
open Cleanroom.Found.FixKakutani
open Finset Filter Topology

variable {Ω ι : Type} [Fintype Ω] [DecidableEq Ω] {acts : ι → Type} [∀ d, Fintype (acts d)]
  [∀ d, DecidableEq (acts d)] [DecidableEq ι] [∀ d, Nonempty (acts d)]

variable (obs : ι → Finset Ω) (actEv : (d : ι) → acts d → Finset Ω)

/-! ## Raw labels -/

section raw

variable (C : Proc ι acts ℝ) (d : ι)

/-- The weights of `C[d ↦ x]` as a raw dependent function of the label `x`.
Source: none: infrastructure
Kind: D -/
def rawProc (x : acts d → ℝ) : (e : ι) → acts e → ℝ :=
  Function.update (fun e => (C e).w) d x

/-- A point of the standard simplex as a `FinDistr`. Source: none: infrastructure. Kind: D -/
def toDistr (x : acts d → ℝ) (hx : x ∈ stdSimplex ℝ (acts d)) : FinDistr ℝ (acts d) :=
  ⟨x, hx.1, hx.2⟩

/-- The weights of a deviation are the raw weights of its label.
Source: none: infrastructure. Kind: L -/
theorem deviate_w (m : FinDistr ℝ (acts d)) (e : ι) :
    ((C.deviate d m) e).w = rawProc C d m.w e := by
  unfold rawProc
  by_cases h : e = d
  · subst h; simp [Proc.deviate]
  · simp [Proc.deviate, Function.update_of_ne h]

/-- The raw draw-product with one `⟨d, a⟩` factor erased.
Source: none: infrastructure. Kind: D -/
noncomputable def rawReduced (W : (e : ι) → acts e → ℝ) (a : acts d) (B : Tree Ω ι acts ℝ) (ℓ : B.Leaves) :
    ℝ :=
  (((draws B ℓ).erase ⟨d, a⟩).map fun x => W x.1 x.2).prod

/-- `Q_a` as a function of the raw label. Source: none: infrastructure. Kind: D -/
noncomputable def rawQ (a : acts d) (B : Tree Ω ι acts ℝ) (Y : Finset Ω) (x : acts d → ℝ) : ℝ :=
  ∑ ℓ ∈ worldEv B Y, chanceWeight B ℓ * rawReduced d (rawProc C d x) a B ℓ * payoff B ℓ

/-- The run law as a function of raw weights (the same recursion as `leafLaw`).
Source: none: infrastructure. Kind: D -/
noncomputable def rawLeafLaw (W : (e : ι) → acts e → ℝ) : (B : Tree Ω ι acts ℝ) → B.Leaves → ℝ
  | .leaf _ _, _ => 1
  | .chance _ β child, ⟨i, ℓ⟩ => β.w i * rawLeafLaw W (child i) ℓ
  | .decision e child, ⟨a, ℓ⟩ => W e a * rawLeafLaw W (child a) ℓ

/-- `leafLaw` is `rawLeafLaw` of the weights. Source: none: infrastructure. Kind: L -/
theorem leafLaw_eq_rawLeafLaw (C' : Proc ι acts ℝ) :
    (B : Tree Ω ι acts ℝ) → ∀ ℓ, leafLaw C' B ℓ = rawLeafLaw (fun e => (C' e).w) B ℓ
  | .leaf _ _, _ => rfl
  | .chance _ β child, ⟨i, ℓ⟩ => by
      simp only [leafLaw_chance, rawLeafLaw, leafLaw_eq_rawLeafLaw C' (child i) ℓ]
  | .decision e child, ⟨a, ℓ⟩ => by
      simp only [leafLaw_decision, rawLeafLaw, leafLaw_eq_rawLeafLaw C' (child a) ℓ]

/-- `R` as a function of the raw label. Source: none: infrastructure. Kind: D -/
noncomputable def rawNu (B : Tree Ω ι acts ℝ) (X : Finset Ω) (x : acts d → ℝ) : ℝ :=
  ∑ ℓ ∈ worldEv B X, rawLeafLaw (rawProc C d x) B ℓ

/-- `ν_{C[d↦m]}(X) = rawNu m.w`. Source: none: infrastructure. Kind: L -/
theorem nu_deviate_eq_rawNu (m : FinDistr ℝ (acts d)) (B : Tree Ω ι acts ℝ) (X : Finset Ω) :
    nu (C.deviate d m) B X = rawNu C d B X m.w := by
  unfold nu mass rawNu
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  rw [leafLaw_eq_rawLeafLaw]
  congr 1
  funext e
  exact deviate_w C d m e

/-- `qSum (C[d↦m]) = rawQ m.w`. Source: none: infrastructure. Kind: L -/
theorem qSum_deviate_eq_rawQ (m : FinDistr ℝ (acts d)) (a : acts d) (B : Tree Ω ι acts ℝ)
    (Y : Finset Ω) : qSum (C.deviate d m) d a B Y = rawQ C d a B Y m.w := by
  unfold qSum rawQ reducedWeight rawReduced
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  congr 2
  apply congrArg List.prod
  apply List.map_congr_left
  intro x _
  rw [deviate_w C d m x.1]

/-- Each raw weight is a continuous function of the label.
Source: none: infrastructure. Kind: L -/
theorem rawProc_continuous (e : ι) (b : acts e) :
    Continuous (fun x : acts d → ℝ => rawProc C d x e b) := by
  unfold rawProc
  by_cases h : e = d
  · subst h
    simp only [Function.update_self]
    exact continuous_apply b
  · simp only [Function.update_of_ne h]
    exact continuous_const

/-- `rawReduced` is continuous in the label (a finite product of continuous factors).
Source: none: infrastructure. Kind: L -/
theorem rawReduced_continuous (a : acts d) (B : Tree Ω ι acts ℝ) (ℓ : B.Leaves) :
    Continuous (fun x : acts d → ℝ => rawReduced d (rawProc C d x) a B ℓ) := by
  unfold rawReduced
  exact continuous_list_prod _ fun i _ => rawProc_continuous C d i.1 i.2

/-- `rawLeafLaw` is continuous in the label. Source: none: infrastructure. Kind: L -/
theorem rawLeafLaw_continuous :
    (B : Tree Ω ι acts ℝ) → ∀ ℓ, Continuous (fun x : acts d → ℝ => rawLeafLaw (rawProc C d x) B ℓ)
  | .leaf _ _, _ => by simp only [rawLeafLaw]; exact continuous_const
  | .chance _ β child, ⟨i, ℓ⟩ => by
      simp only [rawLeafLaw]
      exact continuous_const.mul (rawLeafLaw_continuous (child i) ℓ)
  | .decision e child, ⟨a, ℓ⟩ => by
      simp only [rawLeafLaw]
      exact (rawProc_continuous C d e a).mul (rawLeafLaw_continuous (child a) ℓ)

/-- `rawQ` is continuous in the label. Source: mandate T7(b). Kind: L -/
theorem rawQ_continuous (a : acts d) (B : Tree Ω ι acts ℝ) (Y : Finset Ω) :
    Continuous (rawQ C d a B Y) := by
  unfold rawQ
  exact continuous_finsetSum _ fun ℓ _ =>
    (continuous_const.mul (rawReduced_continuous C d a B ℓ)).mul continuous_const

/-- `rawNu` is continuous in the label. Source: mandate T7(b). Kind: L -/
theorem rawNu_continuous (B : Tree Ω ι acts ℝ) (X : Finset Ω) : Continuous (rawNu C d B X) := by
  unfold rawNu
  exact continuous_finsetSum _ fun ℓ _ => rawLeafLaw_continuous C d B ℓ

/-- The tremble-pinned act value as a function of the raw label: `Q_a(x) / R(x)`.
Source: mandate T7(b)
Kind: D -/
noncomputable def r3Raw (B : Tree Ω ι acts ℝ) (a : acts d) (x : acts d → ℝ) : ℝ :=
  rawQ C d a B (actEv d a ∩ obs d) x / rawNu C d B (obs d) x

/-- **T7(b), continuity**: under the standing hypothesis, `r3Raw a` is continuous on the simplex.
Source: `repair/C2.md` line 72 (C2-7: "`v(·; m)` is continuous on the simplex"); mandate T7(b)
Kind: P
Fidelity: exact
Hyps: (a) the standing hypothesis `∀ m, 0 < ν_{C[d↦m]}(O_d)` -/
theorem r3Raw_continuousOn (B : Tree Ω ι acts ℝ)
    (hStand : ∀ m : FinDistr ℝ (acts d), 0 < nu (C.deviate d m) B (obs d)) (a : acts d) :
    ContinuousOn (r3Raw obs actEv C d B a) (stdSimplex ℝ (acts d)) := by
  unfold r3Raw
  refine ContinuousOn.div (rawQ_continuous C d a B _).continuousOn
    (rawNu_continuous C d B _).continuousOn fun x hx => ?_
  have := hStand (toDistr d x hx)
  rw [nu_deviate_eq_rawNu] at this
  exact this.ne'

/-- **`r3Val` on the simplex is `r3Raw`** (T7(b) transported to `FinDistr`).
Source: mandate T7(b)
Kind: L
Hyps: (a) `ActRecordingStruct`, (a) disjoint action events, (a) the standing hypothesis at `m` -/
theorem r3Val_eq_r3Raw {B : Tree Ω ι acts ℝ} (h : ActRecordingStruct obs actEv B d)
    (hdisj : DisjointActEv actEv d) (m : FinDistr ℝ (acts d))
    (hR : 0 < nu (C.deviate d m) B (obs d)) (a : acts d) :
    r3Val obs actEv C B d m a = r3Raw obs actEv C d B a m.w := by
  rw [r3Val_eq_qSum_div obs actEv h hdisj C m a hR, r3Raw, qSum_deviate_eq_rawQ,
    nu_deviate_eq_rawNu]

end raw

/-! ## The best-response correspondence and Kakutani -/

section kakutani

variable (C : Proc ι acts ℝ) (d : ι) (B : Tree Ω ι acts ℝ)

/-- Definition 18's best-response face against the raw label `x`: the simplex points whose
support lies in `argmax_a r3Raw a x`.
Source: `repair/C2.md` line 72 (C2-7); [[decision-problems-v2]] §4 Definition 18
Kind: D -/
def brRaw (x : acts d → ℝ) : Set (acts d → ℝ) :=
  {y | y ∈ stdSimplex ℝ (acts d) ∧
    ∀ a, 0 < y a → ∀ b, r3Raw obs actEv C d B b x ≤ r3Raw obs actEv C d B a x}

/-- `brRaw` maps into the simplex. Source: none: infrastructure. Kind: L -/
theorem brRaw_maps : ∀ x ∈ stdSimplex ℝ (acts d), brRaw obs actEv C d B x ⊆ stdSimplex ℝ (acts d) :=
  fun _ _ _ hy => hy.1

/-- `brRaw x` is nonempty: a point mass on a maximiser.
Source: `repair/C2.md` line 72 (C2-7: "nonempty … values"). Kind: L -/
theorem brRaw_nonempty : ∀ x ∈ stdSimplex ℝ (acts d), (brRaw obs actEv C d B x).Nonempty := by
  intro x _
  obtain ⟨a₀, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (acts d))
    (fun a => r3Raw obs actEv C d B a x) Finset.univ_nonempty
  refine ⟨Pi.single a₀ 1, single_mem_stdSimplex ℝ a₀, fun a ha b => ?_⟩
  have : a = a₀ := by
    by_contra hne
    rw [Pi.single_apply, if_neg hne] at ha
    exact lt_irrefl _ ha
  subst this
  exact hmax b (Finset.mem_univ b)

/-- `brRaw x` is convex: a face of the simplex.
Source: `repair/C2.md` line 72 (C2-7: "convex … values"). Kind: L -/
theorem brRaw_convex : ∀ x ∈ stdSimplex ℝ (acts d), Convex ℝ (brRaw obs actEv C d B x) := by
  intro x _ y hy z hz s t hs ht hst
  refine ⟨convex_stdSimplex ℝ (acts d) hy.1 hz.1 hs ht hst, fun a ha b => ?_⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ha
  have hy0 := hy.1.1 a
  have hz0 := hz.1.1 a
  by_cases hya : 0 < y a
  · exact hy.2 a hya b
  · have hya' : y a = 0 := le_antisymm (not_lt.mp hya) hy0
    have hza : 0 < z a := by
      by_contra hc
      have hza' : z a = 0 := le_antisymm (not_lt.mp hc) hz0
      rw [hya', hza'] at ha; simp at ha
    exact hz.2 a hza b

/-- **The graph of `brRaw` over the simplex is closed** (proved by the sequential criterion:
a supported act stays supported along a tail of the sequence, where it maximises; weak
inequalities pass to the limit by T7(b)'s continuity).
Source: `repair/C2.md` line 72 (C2-7: "UHC"); mandate T7(d) ("closed graph *proved*")
Kind: P
Fidelity: exact
Hyps: (a) the standing hypothesis -/
theorem brRaw_hasClosedGraphOn
    (hStand : ∀ m : FinDistr ℝ (acts d), 0 < nu (C.deviate d m) B (obs d)) :
    HasClosedGraphOn (brRaw obs actEv C d B) (stdSimplex ℝ (acts d)) := by
  rw [hasClosedGraphOn_iff_seq_of_isClosed (isClosed_stdSimplex ℝ (acts d))]
  intro xs ys x y hmem hxs hys
  have hxK : x ∈ stdSimplex ℝ (acts d) :=
    (isClosed_stdSimplex ℝ (acts d)).mem_of_tendsto hxs (Eventually.of_forall fun n => (hmem n).1)
  have hyK : y ∈ stdSimplex ℝ (acts d) :=
    (isClosed_stdSimplex ℝ (acts d)).mem_of_tendsto hys
      (Eventually.of_forall fun n => (hmem n).2.1)
  refine ⟨hyK, fun a ha b => ?_⟩
  -- the values converge along `xs`
  have hxsK : Tendsto xs atTop (𝓝[stdSimplex ℝ (acts d)] x) :=
    tendsto_nhdsWithin_iff.2 ⟨hxs, Eventually.of_forall fun n => (hmem n).1⟩
  have hconv : ∀ c, Tendsto (fun n => r3Raw obs actEv C d B c (xs n)) atTop
      (𝓝 (r3Raw obs actEv C d B c x)) := fun c =>
    ((r3Raw_continuousOn obs actEv C d B hStand c).continuousWithinAt hxK).tendsto.comp hxsK
  -- `a` is eventually supported
  have hya : Tendsto (fun n => ys n a) atTop (𝓝 (y a)) := tendsto_pi_nhds.1 hys a
  have hev : ∀ᶠ n in atTop, 0 < ys n a := hya.eventually (lt_mem_nhds ha)
  refine le_of_tendsto_of_tendsto (hconv b) (hconv a) ?_
  filter_upwards [hev] with n hn
  exact (hmem n).2.2 a hn b

/-- **T7(d): MSR existence without trembles.** At a point with F3′-structural act-recording,
disjoint action events and the standing hypothesis `∀ m, 0 < ν_{C[d↦m]}(O_d)`, some label `m`
is D4-approved at its own deviation: `MsrAtD4 (C[d ↦ m]) B d`. Kakutani (`kakutani_findim`,
grade (a) from `fix-kakutani`) on the simplex with the best-response face `brRaw`; the
closed-graph hypothesis is `brRaw_hasClosedGraphOn`, proved.
Source: `repair/C2.md` line 72 (C2-7: "existence without trembles"); `sl-defensible-claims.md`
S10; mandate T7(d)
Kind: C
Fidelity: exact (one point; D4 values; the standing hypothesis as stated in C2-7)
Hyps: (a) `ActRecordingStruct`, (a) disjoint action events, (a) the standing hypothesis -/
theorem msrAtD4_exists (h : ActRecordingStruct obs actEv B d) (hdisj : DisjointActEv actEv d)
    (hStand : ∀ m : FinDistr ℝ (acts d), 0 < nu (C.deviate d m) B (obs d)) :
    ∃ m : FinDistr ℝ (acts d), MsrAtD4 obs actEv (C.deviate d m) B d := by
  obtain ⟨x, hxK, hxF⟩ := kakutani_findim (isCompact_stdSimplex ℝ (acts d))
    (convex_stdSimplex ℝ (acts d))
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary (acts d))⟩
    (brRaw obs actEv C d B) (brRaw_maps obs actEv C d B) (brRaw_nonempty obs actEv C d B)
    (brRaw_convex obs actEv C d B) (brRaw_hasClosedGraphOn obs actEv C d B hStand)
  refine ⟨toDistr d x hxK, ?_⟩
  rw [msrAtD4_deviate_iff]
  intro a ha b
  have hR := hStand (toDistr d x hxK)
  rw [r3Val_eq_r3Raw obs actEv C d h hdisj _ hR, r3Val_eq_r3Raw obs actEv C d h hdisj _ hR]
  exact hxF.2 a ha b

/-- **T7(d) in `dp-calibration`'s vocabulary**: the fixed point satisfies the `d`-clause of
`AdviceEdt` (D4) for `C[d ↦ m]` — every supported act is tremble-realizable within `O_d` and
dominates every realizable act in `limitVal`.
Source: mandate T7(d) ("via §3.3's lemma; the escape clauses hold by `hStand`")
Kind: C
Fidelity: exact
Hyps: (a) as `msrAtD4_exists` -/
theorem adviceEdt_clause_exists (h : ActRecordingStruct obs actEv B d)
    (hdisj : DisjointActEv actEv d)
    (hStand : ∀ m : FinDistr ℝ (acts d), 0 < nu (C.deviate d m) B (obs d)) :
    ∃ m : FinDistr ℝ (acts d), ∀ a, 0 < ((C.deviate d m) d).w a →
      nuPoly (C.deviate d m) B (actEv d a ∩ obs d) ≠ 0 ∧
      ∀ b, nuPoly (C.deviate d m) B (actEv d b ∩ obs d) ≠ 0 →
        limitVal (C.deviate d m) B (actEv d b ∩ obs d) ≤
          limitVal (C.deviate d m) B (actEv d a ∩ obs d) := by
  obtain ⟨m, hm⟩ := msrAtD4_exists obs actEv C d B h hdisj hStand
  refine ⟨m, ?_⟩
  have hO : nuPoly (C.deviate d m) B (obs d) ≠ 0 :=
    (natTrailingDegree_nuPoly_eq_zero _ B (obs d) (hStand m)).2
  exact (msrAtD4_iff_adviceEdt_clause obs actEv _ B d
    (nuPoly_actEv_inter_obs_ne_zero obs actEv h hdisj _ hO)).mp hm

end kakutani

end Cleanroom.Decision.DpDutchBook
