import Cleanroom.Uea.UeaColeShadow.Facts
import Cleanroom.Found.FixKakutani
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.Lattice

/-!
# Existence of fixed points by Kakutani (continuous extension)

Points of the product of simplices `dom := Set.univ.pi (fun _ : M.NT => stdSimplex ℝ A)` are read as
policies by `ofPoint`. Under the continuous extension at `ξ`-null nodes, `x ↦ Q_ξ(h,a)` and `x ↦ w_h` are
continuous on `dom` (`V^*_ξ` is constant), and the best-response correspondences
`corrOf S x := ∏_p Δ(S x p)` (the simplex on the allowed actions `S x p`) have nonempty convex values in
`dom` and a closed graph over `dom` whenever the allowed sets are upper hemicontinuous
(`¬ S x p a ⇒ eventually ¬ S (xs n) p a` along sequences in `dom`). The plain map (`S = 𝒜_h`) and the floored
map (`S = {π⋆}` / `𝒜_h` / `𝒜_h ∪ {π⋆}` by the sign of `r_h`) both qualify; `kakutani_pi_stdSimplex` gives fixed
points, which are exactly the plain and floored fixed points of `Defs.lean`.

Source: [[sequential-self-game]] §4.5; [[oracle-side-gaps-reaudit]] Q5. Scope: finite shadow of rOSI —
finite horizon and hypothesis class, fixed points for oracles, continuous extension at `ξ`-null nodes
([[sequential-self-game]] §7); the continuous extension is the finite model's convention, not rOSI's, and
without it the graph is not closed.
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset Filter Topology Set
open Cleanroom.Found.FixKakutani

namespace Model

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)

/-! ### Points as policies -/

section Points
variable [DecidableEq A] [DecidableEq E]

/-- The space of points: one action vector per decision node.
Source: [[sequential-self-game]] §4.5
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev Pt := M.NT → A → ℝ

/-- The product of simplices `∏_h Δ(A)` over the decision nodes.
Source: [[sequential-self-game]] §4.5
Kind: D
Fidelity: exact
Hyps: n/a -/
def dom : Set M.Pt := Set.univ.pi (fun _ : M.NT => stdSimplex ℝ A)

theorem mem_dom {x : M.Pt} : x ∈ M.dom ↔ ∀ p, x p ∈ stdSimplex ℝ A := by
  simp [dom, Set.mem_univ_pi]

theorem isClosed_dom : IsClosed M.dom := isClosed_set_pi fun _ _ => isClosed_stdSimplex ℝ A

/-- Read a point as a policy (`0` off the decision nodes).
Source: [[sequential-self-game]] §4.5
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def ofPoint (x : M.Pt) : Policy A E := fun n h a =>
  if hnt : M.nonterminal n h then x ⟨⟨⟨n, Nat.lt_succ_of_lt hnt.1⟩, h⟩, hnt⟩ a else 0

theorem ofPoint_apply (x : M.Pt) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    M.ofPoint x n h = x ⟨⟨⟨n, Nat.lt_succ_of_lt hnt.1⟩, h⟩, hnt⟩ := by
  funext a
  simp [ofPoint, hnt]

theorem ofPoint_nt (x : M.Pt) (p : M.NT) : M.ofPoint x p.depth p.hist = x p := by
  rw [M.ofPoint_apply x p.nonterminal]
  rfl

theorem ofPoint_isPolicy {x : M.Pt} (hx : x ∈ M.dom) : M.IsPolicy (M.ofPoint x) := by
  intro n h hnt
  rw [M.ofPoint_apply x hnt]
  exact (M.mem_dom.1 hx) _

theorem continuous_ofPoint (n : ℕ) (h : Hist A E n) (a : A) :
    Continuous (fun x : M.Pt => M.ofPoint x n h a) := by
  by_cases hnt : M.nonterminal n h
  · have : (fun x : M.Pt => M.ofPoint x n h a) =
        fun x => x ⟨⟨⟨n, Nat.lt_succ_of_lt hnt.1⟩, h⟩, hnt⟩ a := by
      funext x
      simp [ofPoint, hnt]
    rw [this]
    exact (continuous_apply a).comp (continuous_apply _)
  · have : (fun x : M.Pt => M.ofPoint x n h a) = fun _ => 0 := by
      funext x
      simp [ofPoint, hnt]
    rw [this]
    exact continuous_const

/-! ### Continuity of the mixture in the point -/

theorem continuous_xiS : ∀ (n : ℕ) (h : Hist A E n), Continuous (fun x : M.Pt => M.xiS (M.ofPoint x) n h) := by
  intro n
  induction n with
  | zero => intro h; simp only [xiS_zero]; exact continuous_const
  | succ n ih =>
    intro h
    simp only [xiS]
    exact ((ih _).mul (M.continuous_ofPoint _ _ _)).mul continuous_const

theorem continuous_xi (n : ℕ) (h : Hist A E n) : Continuous (fun x : M.Pt => M.xi (M.ofPoint x) n h) := by
  unfold xi
  exact (continuous_const.mul (M.continuous_xiS n h)).add continuous_const

theorem continuous_xiA (n : ℕ) (h : Hist A E n) (a : A) :
    Continuous (fun x : M.Pt => M.xiA (M.ofPoint x) n h a) := by
  unfold xiA
  exact continuous_finsetSum _ fun e _ => M.continuous_xi _ _

theorem xi_ne_zero_of_mem_dom {x : M.Pt} (hx : x ∈ M.dom) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h)
    (hs : M.xins n h ≠ 0) : M.xi (M.ofPoint x) n h ≠ 0 := by
  intro h0
  exact hs (M.xins_eq_zero_of_xi_eq_zero (M.ofPoint_isPolicy hx) hnt h0)

/-- `x ↦ ξ(a|h)` is continuous on the product of simplices (the continuous extension is what makes the
`ξ_{-S}`-null case continuous: there `ξ(a|h) = π(a|h)` identically).
Source: [[sequential-self-game]] §4.5
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem continuousOn_xia {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) (a : A) :
    ContinuousOn (fun x : M.Pt => M.xia (M.ofPoint x) n h a) M.dom := by
  by_cases hs : M.xins n h = 0
  · have : (fun x : M.Pt => M.xia (M.ofPoint x) n h a) = fun x => M.ofPoint x n h a := by
      funext x
      exact M.xia_eq_of_xins_eq_zero hnt hs a
    rw [this]
    exact (M.continuous_ofPoint n h a).continuousOn
  · have hcont : ContinuousOn (fun x : M.Pt => M.xiA (M.ofPoint x) n h a / M.xi (M.ofPoint x) n h) M.dom :=
      ContinuousOn.div₀ (M.continuous_xiA n h a).continuousOn (M.continuous_xi n h).continuousOn
        fun x hx => M.xi_ne_zero_of_mem_dom hx hnt hs
    refine ContinuousOn.congr hcont ?_
    intro x hx
    simp only [xia, M.xi_ne_zero_of_mem_dom hx hnt hs, if_false]

/-- `x ↦ V_ξ(h)` is continuous on the product of simplices, at every history.
Source: [[sequential-self-game]] §4.5
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem continuousOn_Vxi : ∀ (n : ℕ) (h : Hist A E n),
    ContinuousOn (fun x : M.Pt => M.Vxi (M.ofPoint x) n h) M.dom := by
  refine M.depth_induction (fun n h => ContinuousOn (fun x : M.Pt => M.Vxi (M.ofPoint x) n h) M.dom) ?_ ?_
  · intro n h hnt
    have : (fun x : M.Pt => M.Vxi (M.ofPoint x) n h) = fun _ => 0 := by
      funext x
      exact M.Vxi_of_not_nonterminal hnt
    rw [this]
    exact continuousOn_const
  · intro n h hnt ih
    have : (fun x : M.Pt => M.Vxi (M.ofPoint x) n h) = fun x => ∑ a, M.xia (M.ofPoint x) n h a *
        ∑ e, M.xie n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vxi (M.ofPoint x) (n + 1) (ext h a e)) := by
      funext x
      rw [M.Vxi_eq hnt]
      rfl
    rw [this]
    refine continuousOn_finsetSum _ fun a _ => (M.continuousOn_xia hnt a).mul ?_
    exact continuousOn_finsetSum _ fun e _ => continuousOn_const.mul (continuousOn_const.add (ih a e))

theorem continuousOn_Qxi (n : ℕ) (h : Hist A E n) (a : A) :
    ContinuousOn (fun x : M.Pt => M.Qxi (M.ofPoint x) n h a) M.dom := by
  have : (fun x : M.Pt => M.Qxi (M.ofPoint x) n h a) = fun x =>
      ∑ e, M.xie n h a e * (M.γ ^ n * M.r n (ext h a e) + M.Vxi (M.ofPoint x) (n + 1) (ext h a e)) := by
    funext x; rfl
  rw [this]
  exact continuousOn_finsetSum _ fun e _ => continuousOn_const.mul (continuousOn_const.add (M.continuousOn_Vxi _ _))

/-- `x ↦ w_h` is continuous on the product of simplices (identically `1` where `ξ_{-S}(h) = 0`).
Source: [[sequential-self-game]] §4.5
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem continuousOn_wS {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) :
    ContinuousOn (fun x : M.Pt => M.wS (M.ofPoint x) n h) M.dom := by
  by_cases hs : M.xins n h = 0
  · refine ContinuousOn.congr (continuousOn_const (c := (1:ℝ))) ?_
    intro x hx
    exact (M.wS_eq_one_iff (M.ofPoint_isPolicy hx) hnt).2 hs
  · have hnum : Continuous (fun x : M.Pt => (1 - M.δ) * M.xiS (M.ofPoint x) n h) :=
      continuous_const.mul (M.continuous_xiS n h)
    have hcont : ContinuousOn (fun x : M.Pt => (1 - M.δ) * M.xiS (M.ofPoint x) n h / M.xi (M.ofPoint x) n h)
        M.dom :=
      ContinuousOn.div₀ hnum.continuousOn (M.continuous_xi n h).continuousOn
        fun x hx => M.xi_ne_zero_of_mem_dom hx hnt hs
    refine ContinuousOn.congr hcont ?_
    intro x hx
    exact wS_of_xi_ne_zero M (M.xi_ne_zero_of_mem_dom hx hnt hs)

theorem tendsto_of_continuousOn {f : M.Pt → ℝ} (hf : ContinuousOn f M.dom) {xs : ℕ → M.Pt} {x : M.Pt}
    (hxs : ∀ n, xs n ∈ M.dom) (hx : x ∈ M.dom) (hlim : Tendsto xs atTop (𝓝 x)) :
    Tendsto (fun n => f (xs n)) atTop (𝓝 (f x)) :=
  (hf x hx).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hxs⟩)

/-! ### Best-response correspondences with prescribed allowed sets -/

/-- The face of the simplex supported on the allowed actions `S`.
Source: [[sequential-self-game]] §4.5 (`Δ(𝒜_h)`, `conv({δ_{a⋆}} ∪ Δ(𝒜_h)) = Δ(𝒜_h ∪ {a⋆})`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def simplexOn (S : A → Prop) : Set (A → ℝ) := {σ | σ ∈ stdSimplex ℝ A ∧ ∀ a, ¬ S a → σ a = 0}

theorem convex_simplexOn (S : A → Prop) : Convex ℝ (simplexOn S) := by
  intro y hy z hz s t hs ht hst
  refine ⟨convex_stdSimplex ℝ A hy.1 hz.1 hs ht hst, fun a ha => ?_⟩
  simp [hy.2 a ha, hz.2 a ha]

/-- The correspondence `x ↦ ∏_p Δ(S x p)`.
Source: [[sequential-self-game]] §4.5
Kind: D
Fidelity: exact
Hyps: n/a -/
def corrOf (S : M.Pt → M.NT → A → Prop) (x : M.Pt) : Set M.Pt :=
  Set.univ.pi (fun p => simplexOn (S x p))

theorem mem_corrOf {S : M.Pt → M.NT → A → Prop} {x y : M.Pt} :
    y ∈ M.corrOf S x ↔ ∀ p, y p ∈ simplexOn (S x p) := by
  simp [corrOf, Set.mem_univ_pi]

theorem corrOf_subset_dom (S : M.Pt → M.NT → A → Prop) (x : M.Pt) : M.corrOf S x ⊆ M.dom :=
  fun y hy => M.mem_dom.2 fun p => ((M.mem_corrOf.1 hy) p).1

theorem corrOf_nonempty (S : M.Pt → M.NT → A → Prop) (x : M.Pt) (hS : ∀ p, ∃ a, S x p a) :
    (M.corrOf S x).Nonempty := by
  refine ⟨fun p => Pi.single (Classical.choose (hS p)) 1, M.mem_corrOf.2 fun p => ⟨single_mem_stdSimplex ℝ _,
    fun a ha => ?_⟩⟩
  apply Pi.single_eq_of_ne
  intro hac
  exact ha (hac ▸ Classical.choose_spec (hS p))

theorem corrOf_convex (S : M.Pt → M.NT → A → Prop) (x : M.Pt) : Convex ℝ (M.corrOf S x) :=
  convex_pi fun p _ => convex_simplexOn (S x p)

/-- **Closed graph of a best-response correspondence** with upper hemicontinuous allowed sets: if along every
convergent sequence in `dom` an action disallowed at the limit is eventually disallowed, the graph of
`x ↦ ∏_p Δ(S x p)` over `dom` is closed (`fix-kakutani`'s `HasClosedGraphOn`).
Source: [[sequential-self-game]] §4.5 ("Closed graph")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem hasClosedGraphOn_corrOf (S : M.Pt → M.NT → A → Prop)
    (hS : ∀ (xs : ℕ → M.Pt) (x : M.Pt), (∀ n, xs n ∈ M.dom) → x ∈ M.dom → Tendsto xs atTop (𝓝 x) →
      ∀ p a, ¬ S x p a → ∀ᶠ n in atTop, ¬ S (xs n) p a) :
    HasClosedGraphOn (M.corrOf S) M.dom := by
  rw [hasClosedGraphOn_iff_seq_of_isClosed M.isClosed_dom]
  intro xs ys x y hmem hxs hys
  have hxdom : x ∈ M.dom := M.isClosed_dom.mem_of_tendsto hxs (Eventually.of_forall fun n => (hmem n).1)
  refine M.mem_corrOf.2 fun p => ⟨?_, fun a ha => ?_⟩
  · exact (isClosed_stdSimplex ℝ A).mem_of_tendsto (tendsto_pi_nhds.1 hys p)
      (Eventually.of_forall fun n => ((M.mem_corrOf.1 (hmem n).2) p).1)
  · have hev := hS xs x (fun n => (hmem n).1) hxdom hxs p a ha
    have h1 : Tendsto (fun n => ys n p a) atTop (𝓝 (y p a)) := tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hys p) a
    have h2 : Tendsto (fun n => ys n p a) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun n hn => (((M.mem_corrOf.1 (hmem n).2) p).2 a hn).symm)
    exact tendsto_nhds_unique h1 h2

/-- **Kakutani for a best-response correspondence**: nonempty allowed sets and upper hemicontinuity give a
fixed point `x ∈ dom` with `x ∈ ∏_p Δ(S x p)` (`kakutani_pi_stdSimplex`, grade (a)).
Source: [[sequential-self-game]] §4.5
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exists_fixedPoint_corrOf (S : M.Pt → M.NT → A → Prop) (hne : ∀ x ∈ M.dom, ∀ p, ∃ a, S x p a)
    (hS : ∀ (xs : ℕ → M.Pt) (x : M.Pt), (∀ n, xs n ∈ M.dom) → x ∈ M.dom → Tendsto xs atTop (𝓝 x) →
      ∀ p a, ¬ S x p a → ∀ᶠ n in atTop, ¬ S (xs n) p a) :
    ∃ x ∈ M.dom, x ∈ M.corrOf S x :=
  kakutani_pi_stdSimplex (M.corrOf S) (fun x _ => M.corrOf_subset_dom S x)
    (fun x hx => M.corrOf_nonempty S x (hne x hx)) (fun x _ => M.corrOf_convex S x)
    (M.hasClosedGraphOn_corrOf S hS)

/-! ### The plain and floored maps -/

/-- Allowed actions of the plain agent: the EDT argmax `𝒜_h`.
Source: [[sequential-self-game]] §4.5
Kind: D
Fidelity: exact
Hyps: n/a -/
def Splain (x : M.Pt) (p : M.NT) (a : A) : Prop :=
  M.Qxi (M.ofPoint x) p.depth p.hist a = M.Mx (M.ofPoint x) p.depth p.hist

/-- Allowed actions of the floored agent `π†`: `{π⋆}` if `r_h < 0`, `𝒜_h` if `r_h > 0`, `𝒜_h ∪ {π⋆}` if
`r_h = 0` — written as `(a = π⋆ ∧ r_h ≤ 0) ∨ (a ∈ 𝒜_h ∧ 0 ≤ r_h)`. Its face `Δ(S)` is
`conv({δ_{π⋆}} ∪ Δ(𝒜_h))` at equality nodes.
Source: [[sequential-self-game]] §4.5; [[oracle-side-gaps-reaudit]] Q5
Kind: D
Fidelity: exact
Hyps: n/a -/
def Sfloor (x : M.Pt) (p : M.NT) (a : A) : Prop :=
  (a = M.piStar p.depth p.hist ∧ M.resid (M.ofPoint x) p.depth p.hist ≤ 0) ∨
    (M.Qxi (M.ofPoint x) p.depth p.hist a = M.Mx (M.ofPoint x) p.depth p.hist ∧
      0 ≤ M.resid (M.ofPoint x) p.depth p.hist)

/-- Fixed points of the plain map are exactly the plain fixed points.
Source: [[sequential-self-game]] §4.5
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem isPlainFP_ofPoint_iff {x : M.Pt} (hx : x ∈ M.dom) :
    M.IsPlainFP (M.ofPoint x) ↔ x ∈ M.corrOf M.Splain x := by
  constructor
  · intro hfp
    refine M.mem_corrOf.2 fun p => ⟨(M.mem_dom.1 hx) p, fun a ha => ?_⟩
    by_contra hne
    have hpos : 0 < x p a := lt_of_le_of_ne ((M.mem_dom.1 hx p).1 a) (Ne.symm hne)
    rw [← M.ofPoint_nt x p] at hpos
    exact ha (hfp.2 _ _ p.nonterminal a hpos)
  · intro hmem
    refine ⟨M.ofPoint_isPolicy hx, fun n h hnt a ha => ?_⟩
    have := ((M.mem_corrOf.1 hmem) ⟨⟨⟨n, Nat.lt_succ_of_lt hnt.1⟩, h⟩, hnt⟩).2 a
    rw [M.ofPoint_apply x hnt] at ha
    by_contra hne
    exact absurd (this hne) ha.ne'

/-- Fixed points of the floored map are exactly the floored fixed points ("honest for the floored agent").
Source: [[sequential-self-game]] §4.5; [[oracle-side-gaps-reaudit]] Q5
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem isFlooredFP_ofPoint_iff {x : M.Pt} (hx : x ∈ M.dom) :
    M.IsFlooredFP (M.ofPoint x) ↔ x ∈ M.corrOf M.Sfloor x := by
  constructor
  · intro hfp
    refine M.mem_corrOf.2 fun p => ⟨(M.mem_dom.1 hx) p, fun a ha => ?_⟩
    by_contra hne
    have hpos : 0 < x p a := lt_of_le_of_ne ((M.mem_dom.1 hx p).1 a) (Ne.symm hne)
    rw [← M.ofPoint_nt x p] at hpos
    obtain ⟨h1, h2, h3⟩ := hfp.2 _ _ p.nonterminal
    unfold Sfloor at ha
    rcases lt_trichotomy (M.resid (M.ofPoint x) p.depth p.hist) 0 with hr | hr | hr
    · exact ha (Or.inl ⟨h1 hr a hpos, hr.le⟩)
    · rcases h3 hr a hpos with h4 | h4
      · exact ha (Or.inr ⟨h4, hr.ge⟩)
      · exact ha (Or.inl ⟨h4, hr.le⟩)
    · exact ha (Or.inr ⟨h2 hr a hpos, hr.le⟩)
  · intro hmem
    refine ⟨M.ofPoint_isPolicy hx, fun n h hnt => ?_⟩
    have key : ∀ a, 0 < M.ofPoint x n h a → M.Sfloor x ⟨⟨⟨n, Nat.lt_succ_of_lt hnt.1⟩, h⟩, hnt⟩ a := by
      intro a ha
      rw [M.ofPoint_apply x hnt] at ha
      by_contra hne
      exact absurd (((M.mem_corrOf.1 hmem) _).2 a hne) ha.ne'
    refine ⟨fun hr a ha => ?_, fun hr a ha => ?_, fun hr a ha => ?_⟩
    · rcases key a ha with h4 | h4
      · exact h4.1
      · exact absurd h4.2 (not_le.2 hr)
    · rcases key a ha with h4 | h4
      · exact absurd h4.2 (not_le.2 hr)
      · exact h4.1
    · rcases key a ha with h4 | h4
      · exact Or.inr h4.1
      · exact Or.inl h4.1

theorem Splain_nonempty (x : M.Pt) (p : M.NT) : ∃ a, M.Splain x p a := M.exists_Qxi_eq_Mx _ _

theorem Sfloor_nonempty (x : M.Pt) (p : M.NT) : ∃ a, M.Sfloor x p a := by
  rcases le_or_gt (M.resid (M.ofPoint x) p.depth p.hist) 0 with hr | hr
  · exact ⟨_, Or.inl ⟨rfl, hr⟩⟩
  · obtain ⟨a, ha⟩ := M.exists_Qxi_eq_Mx (π := M.ofPoint x) p.depth p.hist
    exact ⟨a, Or.inr ⟨ha, hr.le⟩⟩

/-- Along a convergent sequence in `dom`, an action that is not EDT-optimal at the limit is eventually not
EDT-optimal (upper hemicontinuity of the argmax: `𝒜_h(x_n) ⊆ 𝒜_h(x)` eventually).
Source: [[sequential-self-game]] §4.5
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem eventually_not_argmax {xs : ℕ → M.Pt} {x : M.Pt} (hxs : ∀ n, xs n ∈ M.dom) (hx : x ∈ M.dom)
    (hlim : Tendsto xs atTop (𝓝 x)) (p : M.NT) {a : A}
    (ha : M.Qxi (M.ofPoint x) p.depth p.hist a ≠ M.Mx (M.ofPoint x) p.depth p.hist) :
    ∀ᶠ n in atTop, M.Qxi (M.ofPoint (xs n)) p.depth p.hist a ≠ M.Mx (M.ofPoint (xs n)) p.depth p.hist := by
  obtain ⟨b, hb⟩ := M.exists_Qxi_eq_Mx (π := M.ofPoint x) p.depth p.hist
  have hlt : M.Qxi (M.ofPoint x) p.depth p.hist a < M.Qxi (M.ofPoint x) p.depth p.hist b := by
    rw [hb]
    exact lt_of_le_of_ne (M.Qxi_le_Mx _ _ a) ha
  have ta := M.tendsto_of_continuousOn (M.continuousOn_Qxi p.depth p.hist a) hxs hx hlim
  have tb := M.tendsto_of_continuousOn (M.continuousOn_Qxi p.depth p.hist b) hxs hx hlim
  refine (ta.eventually_lt tb hlt).mono fun n hn => ?_
  exact ne_of_lt (lt_of_lt_of_le hn (M.Qxi_le_Mx _ _ b))

theorem eventually_resid_neg {xs : ℕ → M.Pt} {x : M.Pt} (hxs : ∀ n, xs n ∈ M.dom) (hx : x ∈ M.dom)
    (hlim : Tendsto xs atTop (𝓝 x)) (p : M.NT) (hr : M.resid (M.ofPoint x) p.depth p.hist < 0) :
    ∀ᶠ n in atTop, M.resid (M.ofPoint (xs n)) p.depth p.hist < 0 := by
  unfold resid at hr ⊢
  have hall : ∀ b, M.Qxi (M.ofPoint x) p.depth p.hist b < M.wS (M.ofPoint x) p.depth p.hist * M.Vstar p.depth p.hist :=
    fun b => lt_of_le_of_lt (M.Qxi_le_Mx _ _ b) (by linarith)
  have tw := (M.tendsto_of_continuousOn (M.continuousOn_wS p.nonterminal) hxs hx hlim).mul_const
    (M.Vstar p.depth p.hist)
  have hev : ∀ᶠ n in atTop, ∀ b, M.Qxi (M.ofPoint (xs n)) p.depth p.hist b <
      M.wS (M.ofPoint (xs n)) p.depth p.hist * M.Vstar p.depth p.hist := by
    rw [eventually_all]
    intro b
    exact (M.tendsto_of_continuousOn (M.continuousOn_Qxi p.depth p.hist b) hxs hx hlim).eventually_lt tw (hall b)
  refine hev.mono fun n hn => ?_
  have : M.Mx (M.ofPoint (xs n)) p.depth p.hist < M.wS (M.ofPoint (xs n)) p.depth p.hist * M.Vstar p.depth p.hist := by
    unfold Mx
    rw [Finset.sup'_lt_iff]
    intro b _
    exact hn b
  linarith

theorem eventually_resid_pos {xs : ℕ → M.Pt} {x : M.Pt} (hxs : ∀ n, xs n ∈ M.dom) (hx : x ∈ M.dom)
    (hlim : Tendsto xs atTop (𝓝 x)) (p : M.NT) (hr : 0 < M.resid (M.ofPoint x) p.depth p.hist) :
    ∀ᶠ n in atTop, 0 < M.resid (M.ofPoint (xs n)) p.depth p.hist := by
  unfold resid at hr ⊢
  obtain ⟨b, hb⟩ := M.exists_Qxi_eq_Mx (π := M.ofPoint x) p.depth p.hist
  have hlt : M.wS (M.ofPoint x) p.depth p.hist * M.Vstar p.depth p.hist < M.Qxi (M.ofPoint x) p.depth p.hist b := by
    rw [hb]; linarith
  have tw := (M.tendsto_of_continuousOn (M.continuousOn_wS p.nonterminal) hxs hx hlim).mul_const
    (M.Vstar p.depth p.hist)
  have tb := M.tendsto_of_continuousOn (M.continuousOn_Qxi p.depth p.hist b) hxs hx hlim
  refine (tw.eventually_lt tb hlt).mono fun n hn => ?_
  linarith [M.Qxi_le_Mx (π := M.ofPoint (xs n)) p.depth p.hist b]

theorem eventually_not_Splain {xs : ℕ → M.Pt} {x : M.Pt} (hxs : ∀ n, xs n ∈ M.dom) (hx : x ∈ M.dom)
    (hlim : Tendsto xs atTop (𝓝 x)) (p : M.NT) (a : A) (ha : ¬ M.Splain x p a) :
    ∀ᶠ n in atTop, ¬ M.Splain (xs n) p a :=
  M.eventually_not_argmax hxs hx hlim p ha

/-- The three-way case split of [[sequential-self-game]] §4.5: an action disallowed by the floored map at the
limit is eventually disallowed along the sequence (at an equality node every branch of `x_n` lands in the
hull `Δ(𝒜_h ∪ {π⋆})`).
Source: [[sequential-self-game]] §4.5
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem eventually_not_Sfloor {xs : ℕ → M.Pt} {x : M.Pt} (hxs : ∀ n, xs n ∈ M.dom) (hx : x ∈ M.dom)
    (hlim : Tendsto xs atTop (𝓝 x)) (p : M.NT) (a : A) (ha : ¬ M.Sfloor x p a) :
    ∀ᶠ n in atTop, ¬ M.Sfloor (xs n) p a := by
  unfold Sfloor at ha ⊢
  push_neg at ha
  obtain ⟨h1, h2⟩ := ha
  by_cases hQ : M.Qxi (M.ofPoint x) p.depth p.hist a = M.Mx (M.ofPoint x) p.depth p.hist
  · -- then `r_h < 0` and `a ≠ π⋆`
    have hr : M.resid (M.ofPoint x) p.depth p.hist < 0 := lt_of_not_ge fun h => absurd (h2 hQ) (not_lt.2 h)
    have hne : a ≠ M.piStar p.depth p.hist := fun h => absurd (h1 h) (not_lt.2 hr.le)
    refine (M.eventually_resid_neg hxs hx hlim p hr).mono fun n hn => ?_
    push_neg
    exact ⟨fun h => absurd h hne, fun _ => hn⟩
  · have hev := M.eventually_not_argmax hxs hx hlim p hQ
    by_cases hne : a = M.piStar p.depth p.hist
    · have hr : 0 < M.resid (M.ofPoint x) p.depth p.hist := h1 hne
      refine ((M.eventually_resid_pos hxs hx hlim p hr).and hev).mono fun n hn => ?_
      push_neg
      exact ⟨fun _ => hn.1, fun h => absurd h hn.2⟩
    · refine hev.mono fun n hn => ?_
      push_neg
      exact ⟨fun h => absurd h hne, fun h => absurd h hn⟩

/-- The plain best-response map has a closed graph over the product of simplices.
Source: [[sequential-self-game]] §4.5
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem hasClosedGraphOn_plain : HasClosedGraphOn (M.corrOf M.Splain) M.dom :=
  M.hasClosedGraphOn_corrOf M.Splain fun xs x hxs hx hlim p a ha => M.eventually_not_Splain hxs hx hlim p a ha

/-- The floored best-response map has a closed graph over the product of simplices.
Source: [[sequential-self-game]] §4.5; [[oracle-side-gaps-reaudit]] Q5
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem hasClosedGraphOn_floor : HasClosedGraphOn (M.corrOf M.Sfloor) M.dom :=
  M.hasClosedGraphOn_corrOf M.Sfloor fun xs x hxs hx hlim p a ha => M.eventually_not_Sfloor hxs hx hlim p a ha

end Points

/-- **Plain (mixed) fixed points exist for every model** (Kakutani on `∏_h Δ(A)` under the continuous
extension). Scope: finite shadow of rOSI ([[sequential-self-game]] §7).
Source: [[sequential-self-game]] §4.5 ("mixed fixed points of the plain agent for every instance");
[[uea-inventory]] 013, [[uea-2-inventory]] 2-015
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exists_isPlainFP : ∃ π, M.IsPlainFP π := by
  classical
  obtain ⟨x, hx, hfix⟩ := M.exists_fixedPoint_corrOf M.Splain (fun x _ p => M.Splain_nonempty x p)
    (fun xs x hxs hx hlim p a ha => M.eventually_not_Splain hxs hx hlim p a ha)
  exact ⟨M.ofPoint x, (M.isPlainFP_ofPoint_iff hx).2 hfix⟩

/-- **Floored (mixed) fixed points exist for every model** (Kakutani; the closed graph comes from the
three-way case split at equality nodes and the continuous extension). Scope: finite shadow of rOSI
([[sequential-self-game]] §7).
Source: [[sequential-self-game]] §4.5; [[uea-inventory]] 013
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem exists_isFlooredFP : ∃ π, M.IsFlooredFP π := by
  classical
  obtain ⟨x, hx, hfix⟩ := M.exists_fixedPoint_corrOf M.Sfloor (fun x _ p => M.Sfloor_nonempty x p)
    (fun xs x hxs hx hlim p a ha => M.eventually_not_Sfloor hxs hx hlim p a ha)
  exact ⟨M.ofPoint x, (M.isFlooredFP_ofPoint_iff hx).2 hfix⟩

end Model

end Cleanroom.Uea.UeaColeShadow
