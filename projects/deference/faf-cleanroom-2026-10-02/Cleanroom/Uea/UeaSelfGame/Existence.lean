import Cleanroom.Uea.UeaSelfGame.Repaired
import Cleanroom.Found.FixKakutani
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.Lattice

/-!
# Mixed fixed points exist for every instance (Kakutani under the continuous extension)

On `dom := ∏_s Δ(A)` the fixed-coordinate value `Ucoord` and the mixed value `Umix` are polynomials in `σ`
(continuous everywhere), and the extended conditional `Fext σ s a` is continuous on `dom`: when
`δ p_a = 0` it equals `Ucoord σ s a` identically (`Fext_eq_Ucoord_of_δ_mul_pa_eq_zero`), and when
`δ p_a > 0` its denominator is `≥ δ p_a > 0` on `dom`, so the ratio is continuous. The best-response
correspondence `σ ↦ ∏_s Δ(argmax_a Fext σ s ·)` (and the floored one, by the sign of the residual with
the convex-hull rule at equality) has nonempty convex values in `dom` and a closed graph (an action that
is not an argmax at the limit is eventually not an argmax), so `kakutani_pi_stdSimplex` (grade (a)) gives
a fixed point: `exists_isFPext`, `exists_isFlooredFPext`. The pattern is `uea-cole-shadow`'s
`Existence.lean`, restated over `S` (no import from that package).

Scope: finite updateless self-game — product self-hypothesis for mixed policies, continuous extension at
null actions (`Fext`); not rOSI, not the sequential model of `uea-cole-shadow`.

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset Filter Topology Set
open Cleanroom.Found.FixKakutani

section Generic

variable (S A : Type*) [Fintype A]

/-- The domain `∏_s Δ(A)` of mixed policies, as a set of `S → A → ℝ`.
Source: [[updateless-self-game]] §6 ("Kakutani")
Kind: D
Fidelity: exact
Hyps: n/a -/
def dom : Set (S → A → ℝ) := Set.univ.pi (fun _ : S => stdSimplex ℝ A)

variable {S A}
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem mem_dom {σ : S → A → ℝ} : σ ∈ dom S A ↔ IsMixed σ := by
  simp [dom, IsMixed]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem isClosed_dom : IsClosed (dom S A) := isClosed_set_pi fun _ _ => isClosed_stdSimplex ℝ A

omit [Fintype A] in
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem continuous_coord (t : S) (b : A) : Continuous (fun σ : S → A → ℝ => σ t b) :=
  (continuous_apply b).comp (continuous_apply t)
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem tendsto_of_continuousOn {f : (S → A → ℝ) → ℝ} (hf : ContinuousOn f (dom S A))
    {xs : ℕ → S → A → ℝ} {x : S → A → ℝ} (hxs : ∀ n, xs n ∈ dom S A) (hx : x ∈ dom S A)
    (hlim : Tendsto xs atTop (𝓝 x)) : Tendsto (fun n => f (xs n)) atTop (𝓝 (f x)) :=
  (hf x hx).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hxs⟩)

/-! ### Best-response correspondences with prescribed allowed sets (restated over `S`) -/

/-- The face of the simplex supported on the allowed actions `P`.
Source: [[updateless-self-game]] §6; `uea-cole-shadow` `simplexOn`, restated
Kind: D
Fidelity: exact
Hyps: n/a -/
def simplexOn (P : A → Prop) : Set (A → ℝ) := {σ | σ ∈ stdSimplex ℝ A ∧ ∀ a, ¬ P a → σ a = 0}
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem convex_simplexOn (P : A → Prop) : Convex ℝ (simplexOn P) := by
  intro y hy z hz s t hs ht hst
  refine ⟨convex_stdSimplex ℝ A hy.1 hz.1 hs ht hst, fun a ha => ?_⟩
  simp [hy.2 a ha, hz.2 a ha]

/-- The correspondence `σ ↦ ∏_s Δ(P σ s)`.
Source: [[updateless-self-game]] §6
Kind: D
Fidelity: exact
Hyps: n/a -/
def corrOf (P : (S → A → ℝ) → S → A → Prop) (σ : S → A → ℝ) : Set (S → A → ℝ) :=
  Set.univ.pi (fun s => simplexOn (P σ s))
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem mem_corrOf {P : (S → A → ℝ) → S → A → Prop} {σ τ : S → A → ℝ} :
    τ ∈ corrOf P σ ↔ ∀ s, τ s ∈ simplexOn (P σ s) := by
  simp [corrOf]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem corrOf_subset_dom (P : (S → A → ℝ) → S → A → Prop) (σ : S → A → ℝ) : corrOf P σ ⊆ dom S A :=
  fun τ hτ => by
    rw [mem_dom]; exact fun s => ((mem_corrOf.1 hτ) s).1
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem corrOf_nonempty [DecidableEq A] (P : (S → A → ℝ) → S → A → Prop) (σ : S → A → ℝ)
    (hP : ∀ s, ∃ a, P σ s a) : (corrOf P σ).Nonempty := by
  refine ⟨fun s => Pi.single (Classical.choose (hP s)) 1, mem_corrOf.2 fun s =>
    ⟨single_mem_stdSimplex ℝ _, fun a ha => ?_⟩⟩
  apply Pi.single_eq_of_ne
  intro hac
  exact ha (hac ▸ Classical.choose_spec (hP s))
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem corrOf_convex (P : (S → A → ℝ) → S → A → Prop) (σ : S → A → ℝ) : Convex ℝ (corrOf P σ) :=
  convex_pi fun s _ => convex_simplexOn (P σ s)

/-- **Closed graph of a best-response correspondence** with upper hemicontinuous allowed sets.
Source: [[updateless-self-game]] §6; `uea-cole-shadow` `hasClosedGraphOn_corrOf`, restated over `S`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem hasClosedGraphOn_corrOf [Fintype S] (P : (S → A → ℝ) → S → A → Prop)
    (hP : ∀ (xs : ℕ → S → A → ℝ) (x : S → A → ℝ), (∀ n, xs n ∈ dom S A) → x ∈ dom S A →
      Tendsto xs atTop (𝓝 x) → ∀ s a, ¬ P x s a → ∀ᶠ n in atTop, ¬ P (xs n) s a) :
    HasClosedGraphOn (corrOf P) (dom S A) := by
  rw [hasClosedGraphOn_iff_seq_of_isClosed isClosed_dom]
  intro xs ys x y hmem hxs hys
  have hxdom : x ∈ dom S A := isClosed_dom.mem_of_tendsto hxs (Eventually.of_forall fun n => (hmem n).1)
  refine mem_corrOf.2 fun s => ⟨?_, fun a ha => ?_⟩
  · exact (isClosed_stdSimplex ℝ A).mem_of_tendsto (tendsto_pi_nhds.1 hys s)
      (Eventually.of_forall fun n => ((mem_corrOf.1 (hmem n).2) s).1)
  · have hev := hP xs x (fun n => (hmem n).1) hxdom hxs s a ha
    have h1 : Tendsto (fun n => ys n s a) atTop (𝓝 (y s a)) := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hys s) a
    have h2 : Tendsto (fun n => ys n s a) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun n hn => (((mem_corrOf.1 (hmem n).2) s).2 a hn).symm)
    exact tendsto_nhds_unique h1 h2

/-- **Kakutani for a best-response correspondence** over `∏_s Δ(A)` (`kakutani_pi_stdSimplex`, grade (a)).
Source: [[updateless-self-game]] §6
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exists_fixedPoint_corrOf [Fintype S] [DecidableEq A] [Nonempty A]
    (P : (S → A → ℝ) → S → A → Prop) (hne : ∀ σ ∈ dom S A, ∀ s, ∃ a, P σ s a)
    (hP : ∀ (xs : ℕ → S → A → ℝ) (x : S → A → ℝ), (∀ n, xs n ∈ dom S A) → x ∈ dom S A →
      Tendsto xs atTop (𝓝 x) → ∀ s a, ¬ P x s a → ∀ᶠ n in atTop, ¬ P (xs n) s a) :
    ∃ σ ∈ dom S A, σ ∈ corrOf P σ :=
  kakutani_pi_stdSimplex (A := fun _ : S => A) (corrOf P) (fun σ _ => corrOf_subset_dom P σ)
    (fun σ hσ => corrOf_nonempty P σ (hne σ hσ)) (fun σ _ => corrOf_convex P σ)
    (hasClosedGraphOn_corrOf P hP)

end Generic

namespace Game

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A] (G : Game S A)

/-! ### Continuity -/

/-- `σ ↦ U_a(σ)` is continuous (a polynomial in the entries of `σ`).
Source: [[updateless-self-game]] §6
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem continuous_Ucoord (s : S) (a : A) : Continuous (fun σ : S → A → ℝ => G.Ucoord σ s a) := by
  unfold Ucoord
  refine continuous_finsetSum _ fun π' _ => ?_
  split_ifs
  · exact (continuous_finsetProd _ fun t _ => continuous_coord t (π' t)).mul continuous_const
  · exact continuous_const

omit [DecidableEq A] in
/-- `σ ↦ U(σ)` is continuous.
Source: [[updateless-self-game]] §6
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem continuous_Umix : Continuous (fun σ : S → A → ℝ => G.Umix σ) := by
  unfold Umix prodW
  exact continuous_finsetSum _ fun π' _ =>
    (continuous_finsetProd _ fun t _ => continuous_coord t (π' t)).mul continuous_const
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem continuous_denMix (s : S) (a : A) : Continuous (fun σ : S → A → ℝ => G.denMix σ s a) := by
  unfold denMix
  exact (continuous_const.mul (continuous_coord s a)).add continuous_const

/-- **The extension is the identity `Fext = Ucoord` whenever `δ p_a = 0`** (both branches agree), for every
`σ` — the case split that makes `Fext` continuous.
Source: [[updateless-self-game]] §6 ("the limit as `σ_s(a) ↓ 0`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Fext_eq_Ucoord_of_δ_mul_pa_eq_zero (σ : S → A → ℝ) {s : S} {a : A} (h : G.δ * G.pa s a = 0) :
    G.Fext σ s a = G.Ucoord σ s a := by
  rcases mul_eq_zero.1 h with hδ | hpa
  · unfold Fext denMix
    rw [hδ]
    split_ifs with hd
    · rfl
    · rw [div_eq_iff hd]; ring
  · exact G.Fext_eq_Ucoord_of_pa_eq_zero σ hpa
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem δ_mul_pa_le_denMix {σ : S → A → ℝ} (hσ : IsMixed σ) (s : S) (a : A) :
    G.δ * G.pa s a ≤ G.denMix σ s a := by
  unfold denMix
  have := G.one_sub_δ_pos; have := hσ.nonneg s a
  nlinarith

/-- **`σ ↦ Fext σ s a` is continuous on `dom`**: identically `Ucoord` when `δ p_a = 0`; otherwise a ratio
with denominator `≥ δ p_a > 0` on `dom`.
Source: [[updateless-self-game]] §6 ("the conditionals are continuous in `σ` and Kakutani should go through")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem continuousOn_Fext (s : S) (a : A) : ContinuousOn (fun σ : S → A → ℝ => G.Fext σ s a) (dom S A) := by
  by_cases h : G.δ * G.pa s a = 0
  · have : (fun σ : S → A → ℝ => G.Fext σ s a) = fun σ => G.Ucoord σ s a :=
      funext fun σ => G.Fext_eq_Ucoord_of_δ_mul_pa_eq_zero σ h
    rw [this]
    exact (G.continuous_Ucoord s a).continuousOn
  · have hpos : 0 < G.δ * G.pa s a :=
      lt_of_le_of_ne (mul_nonneg G.δ_nonneg (G.pa_nonneg s a)) (Ne.symm h)
    have hden : ∀ σ ∈ dom S A, G.denMix σ s a ≠ 0 := fun σ hσ =>
      ne_of_gt (lt_of_lt_of_le hpos (G.δ_mul_pa_le_denMix (mem_dom.1 hσ) s a))
    have hratio : ContinuousOn (fun σ : S → A → ℝ =>
        ((1 - G.δ) * σ s a * G.Ucoord σ s a + G.δ * G.pva s a) / G.denMix σ s a) (dom S A) := by
      refine ContinuousOn.div ?_ (G.continuous_denMix s a).continuousOn hden
      exact (((continuous_const.mul (continuous_coord s a)).mul (G.continuous_Ucoord s a)).add
        continuous_const).continuousOn
    refine hratio.congr fun σ hσ => ?_
    exact G.Fext_eq_of_availMix (lt_of_le_of_ne (G.denMix_nonneg (mem_dom.1 hσ) s a) (Ne.symm (hden σ hσ)))

/-! ### The plain and floored maps -/

section Maps

variable [Nonempty A]

/-- Allowed actions of the plain agent: the argmax of `Fext σ s ·`.
Source: [[updateless-self-game]] §1, §6
Kind: D
Fidelity: exact
Hyps: n/a -/
def Splain (σ : S → A → ℝ) (s : S) (a : A) : Prop := G.Fext σ s a = G.maxF σ s

/-- Allowed actions of the floored agent: `{piStar s}` if `resid < 0`, the argmax if `resid > 0`, their
union if `resid = 0` — written `(a = piStar s ∧ resid ≤ 0) ∨ (a ∈ argmax ∧ 0 ≤ resid)`.
Source: [[updateless-self-game]] §1 ("Floored agent"); `floored_allowed`
Kind: D
Fidelity: exact
Hyps: n/a -/
def Sfloor (σ : S → A → ℝ) (s : S) (a : A) : Prop :=
  (a = G.piStar s ∧ G.resid σ s ≤ 0) ∨ (G.Fext σ s a = G.maxF σ s ∧ 0 ≤ G.resid σ s)
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Splain_nonempty (σ : S → A → ℝ) (s : S) : ∃ a, G.Splain σ s a := G.exists_Fext_eq_maxF σ s
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Sfloor_nonempty (σ : S → A → ℝ) (s : S) : ∃ a, G.Sfloor σ s a := by
  rcases le_or_gt 0 (G.resid σ s) with h | h
  · obtain ⟨a, ha⟩ := G.exists_Fext_eq_maxF σ s
    exact ⟨a, Or.inr ⟨ha, h⟩⟩
  · exact ⟨G.piStar s, Or.inl ⟨rfl, h.le⟩⟩

/-- Fixed points of the plain map are exactly the extension fixed points.
Source: [[updateless-self-game]] §1, §6
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem isFPext_iff_mem_corrOf_Splain {σ : S → A → ℝ} (hσ : σ ∈ dom S A) :
    G.IsFPext σ ↔ σ ∈ corrOf G.Splain σ := by
  have hm : IsMixed σ := mem_dom.1 hσ
  rw [mem_corrOf]
  constructor
  · intro h s
    refine ⟨hm s, fun a ha => ?_⟩
    by_contra hne
    have hpos : 0 < σ s a := lt_of_le_of_ne (hm.nonneg s a) (Ne.symm hne)
    apply ha
    obtain ⟨b, hb⟩ := G.exists_Fext_eq_maxF σ s
    exact le_antisymm (G.Fext_le_maxF σ s a) (hb ▸ h.2 s a hpos b)
  · intro h
    refine ⟨hm, fun s a ha b => ?_⟩
    have hmax : G.Splain σ s a := by
      by_contra hne
      exact absurd ((h s).2 a hne) (ne_of_gt ha)
    unfold Splain at hmax
    rw [hmax]; exact G.Fext_le_maxF σ s b

/-- Fixed points of the floored map are exactly the floored extension fixed points.
Source: [[updateless-self-game]] §1 ("Floored agent"); `is_floored_fixed_point`
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem isFlooredFPext_iff_mem_corrOf_Sfloor {σ : S → A → ℝ} (hσ : σ ∈ dom S A) :
    G.IsFlooredFPext σ ↔ σ ∈ corrOf G.Sfloor σ := by
  have hm : IsMixed σ := mem_dom.1 hσ
  rw [mem_corrOf]
  constructor
  · rintro ⟨_, h⟩ s
    refine ⟨hm s, fun a ha => ?_⟩
    by_contra hne
    have hpos : 0 < σ s a := lt_of_le_of_ne (hm.nonneg s a) (Ne.symm hne)
    obtain ⟨h1, h2, h3⟩ := h s
    unfold Sfloor at ha
    push Not at ha
    rcases lt_trichotomy (G.resid σ s) 0 with hr | hr | hr
    · exact absurd (h1 hr a hpos) (fun e => by have := ha.1 e; linarith)
    · rcases h3 hr a hpos with hmax | hpi
      · exact (ha.2 hmax).not_ge hr.ge
      · exact (ha.1 hpi).not_ge hr.le
    · exact (ha.2 (h2 hr a hpos)).not_ge hr.le
  · intro h
    refine ⟨hm, fun s => ⟨fun hr a ha => ?_, fun hr a ha => ?_, fun hr a ha => ?_⟩⟩
    · have hS : G.Sfloor σ s a := by
        by_contra hne; exact absurd ((h s).2 a hne) (ne_of_gt ha)
      rcases hS with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · exact absurd hr (not_lt.2 h2)
    · have hS : G.Sfloor σ s a := by
        by_contra hne; exact absurd ((h s).2 a hne) (ne_of_gt ha)
      rcases hS with ⟨_, h2⟩ | ⟨h1, _⟩
      · exact absurd hr (not_lt.2 h2)
      · exact h1
    · have hS : G.Sfloor σ s a := by
        by_contra hne; exact absurd ((h s).2 a hne) (ne_of_gt ha)
      rcases hS with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inr h1
      · exact Or.inl h1

/-- Along a convergent sequence in `dom`, an action that is not an argmax at the limit is eventually not an
argmax (upper hemicontinuity of the argmax).
Source: [[updateless-self-game]] §6; `uea-cole-shadow` `eventually_not_argmax`, restated
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem eventually_not_argmax {xs : ℕ → S → A → ℝ} {x : S → A → ℝ} (hxs : ∀ n, xs n ∈ dom S A)
    (hx : x ∈ dom S A) (hlim : Tendsto xs atTop (𝓝 x)) (s : S) {a : A}
    (ha : G.Fext x s a ≠ G.maxF x s) : ∀ᶠ n in atTop, G.Fext (xs n) s a ≠ G.maxF (xs n) s := by
  obtain ⟨b, hb⟩ := G.exists_Fext_eq_maxF x s
  have hlt : G.Fext x s a < G.Fext x s b := by
    rw [hb]; exact lt_of_le_of_ne (G.Fext_le_maxF x s a) ha
  have ta := tendsto_of_continuousOn (G.continuousOn_Fext s a) hxs hx hlim
  have tb := tendsto_of_continuousOn (G.continuousOn_Fext s b) hxs hx hlim
  refine (ta.eventually_lt tb hlt).mono fun n hn => ?_
  exact ne_of_lt (lt_of_lt_of_le hn (G.Fext_le_maxF (xs n) s b))
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem eventually_resid_neg {xs : ℕ → S → A → ℝ} {x : S → A → ℝ} (hxs : ∀ n, xs n ∈ dom S A)
    (hx : x ∈ dom S A) (hlim : Tendsto xs atTop (𝓝 x)) (s : S) (hr : G.resid x s < 0) :
    ∀ᶠ n in atTop, G.resid (xs n) s < 0 := by
  unfold resid at hr ⊢
  have hall : ∀ b, G.Fext x s b < G.thr := fun b =>
    lt_of_le_of_lt (G.Fext_le_maxF x s b) (by linarith)
  have hev : ∀ᶠ n in atTop, ∀ b, G.Fext (xs n) s b < G.thr := by
    rw [eventually_all]
    intro b
    exact (tendsto_of_continuousOn (G.continuousOn_Fext s b) hxs hx hlim).eventually_lt
      tendsto_const_nhds (hall b)
  refine hev.mono fun n hn => ?_
  have : G.maxF (xs n) s < G.thr := by
    unfold maxF
    rw [Finset.sup'_lt_iff]
    intro b _
    exact hn b
  linarith
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem eventually_resid_pos {xs : ℕ → S → A → ℝ} {x : S → A → ℝ} (hxs : ∀ n, xs n ∈ dom S A)
    (hx : x ∈ dom S A) (hlim : Tendsto xs atTop (𝓝 x)) (s : S) (hr : 0 < G.resid x s) :
    ∀ᶠ n in atTop, 0 < G.resid (xs n) s := by
  unfold resid at hr ⊢
  obtain ⟨b, hb⟩ := G.exists_Fext_eq_maxF x s
  have hlt : G.thr < G.Fext x s b := by rw [hb]; linarith
  have tb := tendsto_of_continuousOn (G.continuousOn_Fext s b) hxs hx hlim
  refine (tendsto_const_nhds.eventually_lt tb hlt).mono fun n hn => ?_
  linarith [G.Fext_le_maxF (xs n) s b]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem eventually_not_Splain {xs : ℕ → S → A → ℝ} {x : S → A → ℝ} (hxs : ∀ n, xs n ∈ dom S A)
    (hx : x ∈ dom S A) (hlim : Tendsto xs atTop (𝓝 x)) (s : S) (a : A) (ha : ¬ G.Splain x s a) :
    ∀ᶠ n in atTop, ¬ G.Splain (xs n) s a :=
  G.eventually_not_argmax hxs hx hlim s ha

/-- The three-way case split for the floored map: an action disallowed at the limit is eventually
disallowed.
Source: [[updateless-self-game]] §1 ("at equality either"); `uea-cole-shadow` `eventually_not_Sfloor`, restated
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem eventually_not_Sfloor {xs : ℕ → S → A → ℝ} {x : S → A → ℝ} (hxs : ∀ n, xs n ∈ dom S A)
    (hx : x ∈ dom S A) (hlim : Tendsto xs atTop (𝓝 x)) (s : S) (a : A) (ha : ¬ G.Sfloor x s a) :
    ∀ᶠ n in atTop, ¬ G.Sfloor (xs n) s a := by
  unfold Sfloor at ha ⊢
  push Not at ha
  obtain ⟨h1, h2⟩ := ha
  by_cases hQ : G.Fext x s a = G.maxF x s
  · have hr : G.resid x s < 0 := lt_of_not_ge fun h => absurd (h2 hQ) (not_lt.2 h)
    have hne : a ≠ G.piStar s := fun h => absurd (h1 h) (not_lt.2 hr.le)
    refine (G.eventually_resid_neg hxs hx hlim s hr).mono fun n hn => ?_
    push Not
    exact ⟨fun h => absurd h hne, fun _ => hn⟩
  · have hev := G.eventually_not_argmax hxs hx hlim s hQ
    by_cases hne : a = G.piStar s
    · have hr : 0 < G.resid x s := h1 hne
      refine ((G.eventually_resid_pos hxs hx hlim s hr).and hev).mono fun n hn => ?_
      push Not
      exact ⟨fun _ => hn.1, fun h => absurd h hn.2⟩
    · refine hev.mono fun n hn => ?_
      push Not
      exact ⟨fun h => absurd h hne, fun h => absurd h hn⟩

/-- The plain best-response map has a closed graph over `∏_s Δ(A)`.
Source: [[updateless-self-game]] §6
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem hasClosedGraphOn_plain : HasClosedGraphOn (corrOf G.Splain) (dom S A) :=
  hasClosedGraphOn_corrOf G.Splain fun _ _ hxs hx hlim s a ha => G.eventually_not_Splain hxs hx hlim s a ha

/-- The floored best-response map has a closed graph over `∏_s Δ(A)`.
Source: [[updateless-self-game]] §1, §6
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem hasClosedGraphOn_floor : HasClosedGraphOn (corrOf G.Sfloor) (dom S A) :=
  hasClosedGraphOn_corrOf G.Sfloor fun _ _ hxs hx hlim s a ha => G.eventually_not_Sfloor hxs hx hlim s a ha

/-- **Mixed fixed points exist for every instance under the continuous extension** (Kakutani on
`∏_s Δ(A)` with the closed graph proved). Resolves the note's CONJECTURE. The witness is real, not
rational, in general (`Witness8801.lean`).
Scope: finite updateless self-game — product self-hypothesis, continuous extension at null actions
(`Fext`); not rOSI, not the sequential model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §6 ("CONJECTURE: mixed fixed points exist for every instance under the
continuous extension"); [[uea-inventory]] 029; [[uea-2-inventory]] 2-015
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exists_isFPext : ∃ σ, G.IsFPext σ := by
  obtain ⟨σ, hσ, hfix⟩ := exists_fixedPoint_corrOf G.Splain (fun σ _ s => G.Splain_nonempty σ s)
    (fun xs x hxs hx hlim s a ha => G.eventually_not_Splain hxs hx hlim s a ha)
  exact ⟨σ, (G.isFPext_iff_mem_corrOf_Splain hσ).2 hfix⟩

/-- **Floored mixed fixed points exist for every instance** (Kakutani; the closed graph comes from the
three-way case split with the convex-hull rule at equality).
Scope: finite updateless self-game — continuous extension at null actions; not rOSI, not the sequential
model of `uea-cole-shadow`.
Source: [[updateless-self-game]] §7 ("needs mixed existence, which is CONJECTURE"); [[uea-inventory]] 029
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exists_isFlooredFPext : ∃ σ, G.IsFlooredFPext σ := by
  obtain ⟨σ, hσ, hfix⟩ := exists_fixedPoint_corrOf G.Sfloor (fun σ _ s => G.Sfloor_nonempty σ s)
    (fun xs x hxs hx hlim s a ha => G.eventually_not_Sfloor hxs hx hlim s a ha)
  exact ⟨σ, (G.isFlooredFPext_iff_mem_corrOf_Sfloor hσ).2 hfix⟩

/-- Every instance has a Herrmann mixed fixed point too (`FP_ext ⊆ FP_Herr`).
Source: [[updateless-self-game]] §6
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exists_isFPherr : ∃ σ, G.IsFPherr σ :=
  let ⟨σ, h⟩ := G.exists_isFPext; ⟨σ, h.isFPherr⟩

end Maps

end Game

end Cleanroom.Uea.UeaSelfGame
