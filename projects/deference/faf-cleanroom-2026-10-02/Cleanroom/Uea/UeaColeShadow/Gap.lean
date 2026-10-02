import Cleanroom.Uea.UeaColeShadow.Existence
import Cleanroom.Uea.UeaColeShadow.Instances

/-!
# Gap 1: the strict-reset map, its missing closed graph, and the soundness of the contradiction argument

The **strict-reset correspondence** of [[oracle-side-gaps-reaudit]] Q5 (the finite shadow of the post's
modified `f`): at a node some prefix of which has `r_{h'} = M(h') - w_{h'} V^*_ξ(h') < 0`, the agent is reset
to `π⋆(h)`; elsewhere it best-responds (`Δ(𝒜_h)`). A fixed point of it (`IsStrictResetFP`) is **sound**: no
node is reset, the policy is a plain fixed point and the trust bound holds everywhere (target 6b, the post's
contradiction argument, [[lesswrong-post--live-2026-08-22]] lines 218–221). But on Instance B the map has **no
fixed point** at all (its hypothesis is empty there), and its graph over the product of simplices is **not
closed**: along `(j, k) = (1, 1 - 1/(n+2)) → (1, 1)` the values are the full reset `(1, 1)`, which is not in the
value at the limit `(1, 0)`. Per the `fix-kakutani` report this is stated as "the hypothesis `hF_graph` of
`kakutani_pi_stdSimplex` fails", not as a failure of Kakutani.

Source: [[oracle-side-gaps-reaudit]] Q1, Q5, Q6; [[uea-inventory]] 007, 009. Scope: finite shadow of rOSI
([[sequential-self-game]] §7).
-/

namespace Cleanroom.Uea.UeaColeShadow

open Finset Filter Topology Set
open Cleanroom.Found.FixKakutani

/-- The prefix of depth `m` of a history of depth `n ≥ m`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def prefixH {A E : Type*} {n : ℕ} (h : Hist A E n) (m : ℕ) (hm : m ≤ n) : Hist A E m :=
  fun i => h (Fin.castLE hm i)

theorem prefixH_self {A E : Type*} {n : ℕ} (h : Hist A E n) : prefixH h n le_rfl = h := rfl

theorem prefixH_ext {A E : Type*} {n : ℕ} (h : Hist A E n) (a : A) (e : E) (m : ℕ) (hm : m ≤ n) :
    prefixH (ext h a e) m (Nat.le_succ_of_le hm) = prefixH h m hm := by
  funext i
  have hi : (i : ℕ) < n := lt_of_lt_of_le i.2 hm
  simp [prefixH, ext, Fin.snoc, hi]
  rfl

theorem prefixH_zero {A E : Type*} {n : ℕ} (h : Hist A E n) (h₀ : Hist A E 0) : prefixH h 0 (Nat.zero_le n) = h₀ :=
  funext fun i => Fin.elim0 i

namespace Model

variable {A E ι : Type*} [Fintype A] [Fintype E] [Fintype ι] [Nonempty A] (M : Model A E ι)
  {π : Policy A E}

/-- `h ⪯ h'`: `h` is the depth-`n` prefix of `h'`. -/
def IsPrefixOf {n n' : ℕ} (h : Hist A E n) (h' : Hist A E n') : Prop :=
  ∃ hle : n ≤ n', prefixH h' n hle = h

theorem IsPrefixOf.ext {n n' : ℕ} {h : Hist A E n} {h' : Hist A E n'} (hp : IsPrefixOf h h') (a : A) (e : E) :
    IsPrefixOf h (ext h' a e) := by
  obtain ⟨hle, hpre⟩ := hp
  exact ⟨Nat.le_succ_of_le hle, by rw [prefixH_ext h' a e n hle, hpre]⟩

theorem IsPrefixOf.refl {n : ℕ} (h : Hist A E n) : IsPrefixOf h h := ⟨le_rfl, rfl⟩

/-- A strict reset fires at `h` if some prefix `h' ⪯ h` (including `h`) has `r_{h'} < 0`.
Source: [[oracle-side-gaps-reaudit]] Q5 (the strict-reset map `F`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def hasStrictReset (π : Policy A E) (n : ℕ) (h : Hist A E n) : Prop :=
  ∃ m, ∃ hm : m ≤ n, M.resid π m (prefixH h m hm) < 0

/-- **Fixed point of the strict-reset map**: a policy with `supp π(·|h) = {π⋆(h)}` at reset nodes and
`supp π(·|h) ⊆ 𝒜_h` elsewhere. On Instance B this predicate is empty (`InstB.not_isStrictResetFP`).
Source: [[oracle-side-gaps-reaudit]] Q5, Q6
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsStrictResetFP (π : Policy A E) : Prop :=
  M.IsPolicy π ∧ ∀ n h, M.nonterminal n h →
    (M.hasStrictReset π n h → ∀ a, 0 < π n h a → a = M.piStar n h) ∧
    (¬ M.hasStrictReset π n h → ∀ a, 0 < π n h a → M.Qxi π n h a = M.Mx π n h)

theorem eq_one_of_supp_subset (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) {a₀ : A}
    (hsub : ∀ a, 0 < π n h a → a = a₀) : π n h a₀ = 1 := by
  have h0 : ∀ a, a ≠ a₀ → π n h a = 0 := fun a ha =>
    le_antisymm (not_lt.1 fun hpos => ha (hsub a hpos)) (hπ.nonneg hnt a)
  rw [← hπ.sum hnt, Finset.sum_eq_single a₀ (fun a _ ha => h0 a ha) (fun h => absurd (Finset.mem_univ a₀) h)]

/-- At a decision node where the agent plays `a` surely, the posterior after `a` is at least the posterior
before (`w_{ha} ≥ w_h`; F2).
Source: [[sequential-self-game]] §1 (F2 consequence); [[oracle-side-gaps-reaudit]] Q6
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem wS_le_wA_of_eq_one (hπ : M.IsPolicy π) {n : ℕ} {h : Hist A E n} (hnt : M.nonterminal n h) {a : A}
    (ha : π n h a = 1) : M.wS π n h ≤ M.wA π n h a := by
  by_cases hA : M.xiA π n h a = 0
  · have hwA : M.wA π n h a = 1 := by simp [wA, hA]
    rw [hwA]
    exact M.wS_le_one hπ hnt
  · by_cases hx : M.xi π n h = 0
    · exfalso
      apply hA
      rw [xiA_eq, M.xiS_eq_zero_of_xi_eq_zero hπ hnt hx,
        M.xinsA_eq_zero_of_xins_eq_zero (M.xins_eq_zero_of_xi_eq_zero hπ hnt hx)]
      ring
    · rw [wS_of_xi_ne_zero M hx, M.wA_of_xiA_ne_zero hA, ha, mul_one]
      have hApos : 0 < M.xiA π n h a := lt_of_le_of_ne (M.xiA_nonneg hπ hnt a) (Ne.symm hA)
      have hnum : 0 ≤ (1 - M.δ) * M.xiS π n h :=
        mul_nonneg (by linarith [M.δ_lt_one]) (M.xiS_nonneg hπ n h hnt)
      apply div_le_div_of_nonneg_left hnum hApos
      rw [xiA_eq, ha, mul_one]
      unfold xi
      linarith [M.xinsA_le_xins n h a]

/-- Below a reset node of a strict-reset fixed point the policy is `π⋆` and its value is optimal.
Source: [[oracle-side-gaps-reaudit]] Q6 ("at a minimal reset `h`, `π = π⋆` below `h`")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem IsStrictResetFP.Vpi_eq_Vstar_of_prefix {M : Model A E ι} (hfp : M.IsStrictResetFP π) {n : ℕ}
    {h : Hist A E n} (hneg : M.resid π n h < 0) :
    ∀ n' (h' : Hist A E n'), IsPrefixOf h h' → M.nonterminal n' h' → M.Vpi π n' h' = M.Vstar n' h' := by
  have hπ := hfp.1
  refine M.depth_induction (fun n' h' => IsPrefixOf h h' → M.nonterminal n' h' →
    M.Vpi π n' h' = M.Vstar n' h') ?_ ?_
  · intro n' h' hnt hpre hnt'
    exact absurd hnt' hnt
  · intro n' h' hnt ih hpre _
    have hreset : M.hasStrictReset π n' h' := ⟨n, hpre.1, by rw [hpre.2]; exact hneg⟩
    have hone := M.eq_one_of_supp_subset hπ hnt ((hfp.2 n' h' hnt).1 hreset)
    have hchild : ∀ e, M.Vpi π (n' + 1) (ext h' (M.piStar n' h') e) = M.Vstar (n' + 1) (ext h' (M.piStar n' h') e) := by
      intro e
      by_cases hc : M.nonterminal (n' + 1) (ext h' (M.piStar n' h') e)
      · exact ih _ e (hpre.ext _ e) hc
      · rw [M.Vpi_of_not_nonterminal hc, M.Vstar_of_not_nonterminal hc]
    have hzero : ∀ a ∈ (Finset.univ : Finset A), a ≠ M.piStar n' h' → π n' h' a * M.Qpi π n' h' a = 0 := by
      intro a _ ha
      rw [le_antisymm (not_lt.1 fun hpos => ha ((hfp.2 n' h' hnt).1 hreset a hpos)) (hπ.nonneg hnt a), zero_mul]
    rw [M.Vpi_eq hnt, Finset.sum_eq_single (M.piStar n' h') hzero (fun h => absurd (Finset.mem_univ _) h), hone,
      one_mul, M.Vstar_eq_Qstar_piStar hnt, Qpi_eq_sum, Qstar_eq_sum]
    exact sum_congr rfl fun e _ => by rw [hchild e]

/-- **Soundness of the contradiction argument (Q6)**: at a fixed point of the strict-reset map no node has
`r_h < 0`. At a reset node `h`, `π = π⋆` on the subtree, so `Q^π_ξ(h, π⋆(h)) = V^*_ξ(h)`; `π(π⋆(h)|h) = 1`
gives `w_{hπ⋆} ≥ w_h` (F2), and Lemma A's lower half gives `M(h) ≥ Q_ξ(h,π⋆) ≥ w_{hπ⋆} V^*_ξ(h) ≥ w_h V^*_ξ(h)`,
contradicting the strict violation. Its hypothesis is empty on Instance B (`InstB.not_isStrictResetFP`) —
that is the point.
Source: [[oracle-side-gaps-reaudit]] Q6; [[lesswrong-post--live-2026-08-22]] lines 218–221; [[uea-inventory]] 009
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem IsStrictResetFP.resid_nonneg {M : Model A E ι} (hfp : M.IsStrictResetFP π) {n : ℕ} {h : Hist A E n}
    (hnt : M.nonterminal n h) : 0 ≤ M.resid π n h := by
  have hπ := hfp.1
  by_contra hneg
  push_neg at hneg
  set a := M.piStar n h with ha_def
  have hone : π n h a = 1 := M.eq_one_of_supp_subset hπ hnt ((hfp.2 n h hnt).1 ⟨n, le_rfl, hneg⟩)
  -- children along `π⋆` are optimal
  have hchild : ∀ e, M.Vpi π (n + 1) (ext h a e) = M.Vstar (n + 1) (ext h a e) := by
    intro e
    by_cases hc : M.nonterminal (n + 1) (ext h a e)
    · exact hfp.Vpi_eq_Vstar_of_prefix hneg _ _ ((IsPrefixOf.refl h).ext a e) hc
    · rw [M.Vpi_of_not_nonterminal hc, M.Vstar_of_not_nonterminal hc]
  have hQpi : M.Qpi π n h a = M.Vstar n h := by
    rw [M.Vstar_eq_Qstar_piStar hnt, Qpi_eq_sum, Qstar_eq_sum]
    exact sum_congr rfl fun e _ => by rw [hchild e]
  have hV0 := M.Vstar_nonneg n h
  have hMx : M.wS π n h * M.Vstar n h ≤ M.Mx π n h := by
    refine le_trans ?_ (M.Qxi_le_Mx n h a)
    by_cases hA : M.xiA π n h a = 0
    · -- the children are `ξ`-null: `Q_ξ(h,π⋆) = Q^π(h,π⋆) = V^*`
      have hQxi : M.Qxi π n h a = M.Qpi π n h a := by
        rw [Qxi_eq_sum, Qpi_eq_sum]
        refine sum_congr rfl fun e _ => ?_
        have hx0 : M.xi π (n + 1) (ext h a e) = 0 := by rw [xi_ext, hA, mul_zero]
        by_cases hc : M.nonterminal (n + 1) (ext h a e)
        · rw [M.Vxi_eq_Vpi_of_xins_eq_zero _ _ (M.xins_eq_zero_of_xi_eq_zero hπ hc hx0)]
        · rw [M.Vxi_of_not_nonterminal hc, M.Vpi_of_not_nonterminal hc]
      rw [hQxi, hQpi]
      exact mul_le_of_le_one_left hV0 (M.wS_le_one hπ hnt)
    · calc M.wS π n h * M.Vstar n h ≤ M.wA π n h a * M.Vstar n h :=
            mul_le_mul_of_nonneg_right (M.wS_le_wA_of_eq_one hπ hnt hone) hV0
        _ = M.wA π n h a * M.Qpi π n h a := by rw [hQpi]
        _ ≤ M.Qxi π n h a := M.wA_mul_Qpi_le_Qxi hπ hnt hA
  unfold resid at hneg
  linarith

/-- A fixed point of the strict-reset map resets no node, is a plain fixed point, and satisfies the trust
bound everywhere (target 6b).
Source: [[oracle-side-gaps-reaudit]] Q6; [[uea-inventory]] 009
Kind: C
Fidelity: exact
Hyps: (a) -/
theorem IsStrictResetFP.sound {M : Model A E ι} (hfp : M.IsStrictResetFP π) :
    (∀ n h, M.nonterminal n h → ¬ M.hasStrictReset π n h) ∧ M.IsPlainFP π ∧
      ∀ n h, M.nonterminal n h → M.TB π n h := by
  have hnores : ∀ n h, M.nonterminal n h → ¬ M.hasStrictReset π n h := by
    intro n h hnt ⟨m, hm, hlt⟩
    have hntm : M.nonterminal m (prefixH h m hm) := by
      refine ⟨lt_of_le_of_lt hm hnt.1, ?_⟩
      -- prefixes of alive histories are alive
      have key : ∀ k (h : Hist A E k), M.alive k h = true → ∀ m (hm : m ≤ k), M.alive m (prefixH h m hm) = true := by
        intro k
        induction k with
        | zero =>
          intro h hh m hm
          have : m = 0 := by omega
          subst this
          exact hh
        | succ k ih =>
          intro h hh m hm
          rcases Nat.lt_or_ge m (k + 1) with hlt | hge
          · have hi := M.alive_init k h hh
            have := ih (Fin.init h) hi m (by omega)
            convert this using 2
            funext i
            simp [prefixH, Fin.init]
          · have : m = k + 1 := by omega
            subst this
            exact hh
      exact key n h hnt.2 m hm
    exact absurd hlt (not_lt.2 (hfp.resid_nonneg hntm))
  refine ⟨hnores, ⟨hfp.1, fun n h hnt a ha => (hfp.2 n h hnt).2 (hnores n h hnt) a ha⟩, fun n h hnt => ?_⟩
  have := hfp.resid_nonneg hnt
  unfold resid at this
  unfold TB
  linarith

end Model

/-! ### Instance B: the strict-reset map has no fixed point and no closed graph -/

namespace InstB

open Model

/-- **On Instance B the strict-reset map has no fixed point** (its hypothesis is empty): a fixed point would
be a plain fixed point with the trust bound at the root, which Instance B refutes.
Source: [[oracle-side-gaps-reaudit]] line 42 ("`F` has no fixed point"); [[uea-inventory]] 007
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem not_isStrictResetFP : ¬ ∃ π, model.IsStrictResetFP π := by
  rintro ⟨π, hfp⟩
  obtain ⟨_, hplain, htb⟩ := hfp.sound
  exact not_TB_root_of_isPlainFP π hplain (htb 0 root nt_root)

/-- The strict reset fires at the root of Instance B unless `(j, k, s) = (1, 1, 1)`.
Source: [[oracle-side-gaps-reaudit]] line 40
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem resid_root_neg (π : Policy (Fin 2) Unit) (hπ : model.IsPolicy π)
    (hne : ¬ (π 0 root 1 = 1 ∧ π 1 n1 1 = 1 ∧ π 2 water 0 = 1)) : model.resid π 0 root < 0 := by
  have hlt : model.Qxi π 0 root 1 < 4 / 5 :=
    lt_of_le_of_ne (Qxi_root_1_le π hπ) fun h => hne ((Qxi_root_1_eq_iff π hπ).1 h)
  unfold Model.resid
  rw [wS_root, Vstar_root, model.Mx_fin_two, Qxi_root_0, mul_one, sub_neg, max_lt_iff]
  constructor <;> linarith

theorem resid_root_eq_zero (π : Policy (Fin 2) Unit) (hπ : model.IsPolicy π)
    (h111 : π 0 root 1 = 1 ∧ π 1 n1 1 = 1 ∧ π 2 water 0 = 1) : model.resid π 0 root = 0 := by
  unfold Model.resid
  rw [wS_root, Vstar_root, model.Mx_fin_two, Qxi_root_0, (Qxi_root_1_eq_iff π hπ).2 h111]
  norm_num

theorem resid_n1_pos (π : Policy (Fin 2) Unit) (hπ : model.IsPolicy π) : 0 < model.resid π 1 n1 := by
  unfold Model.resid
  rw [Mx_n1 π hπ, Vstar_n1, mul_one]
  linarith [wS_n1_le π hπ]

/-- Every decision node of Instance B has the root as a prefix, so once the reset fires at the root it fires
everywhere. -/
theorem hasStrictReset_of_root (π : Policy (Fin 2) Unit) (hroot : model.resid π 0 root < 0) (n : ℕ)
    (h : Hist (Fin 2) Unit n) : model.hasStrictReset π n h :=
  ⟨0, Nat.zero_le n, by rw [prefixH_zero h root]; exact hroot⟩

/-- The point `(j, k, s)` of `∏_h Δ(Fin 2)`: `π(go|root) = j`, `π(jump|n₁) = k`, `π(swim|water) = s`. -/
noncomputable def pointB (j k s : ℝ) : model.Pt := fun p a =>
  if p.depth = 0 then (if a = 0 then 1 - j else j)
  else if p.depth = 1 then (if a = 0 then 1 - k else k)
  else (if a = 0 then s else 1 - s)

theorem pointB_mem_dom {j k s : ℝ} (hj : 0 ≤ j ∧ j ≤ 1) (hk : 0 ≤ k ∧ k ≤ 1) (hs : 0 ≤ s ∧ s ≤ 1) :
    pointB j k s ∈ model.dom := by
  refine model.mem_dom.2 fun p => ⟨fun a => ?_, ?_⟩
  · unfold pointB; split_ifs <;> linarith
  · unfold pointB
    split_ifs <;> simp [Fin.sum_univ_two]

theorem ofPoint_pointB_root (j k s : ℝ) : model.ofPoint (pointB j k s) 0 root = fun a => if a = 0 then 1 - j else j := by
  rw [model.ofPoint_apply _ nt_root]
  funext a
  simp [pointB, NT.depth]

theorem ofPoint_pointB_n1 (j k s : ℝ) : model.ofPoint (pointB j k s) 1 n1 = fun a => if a = 0 then 1 - k else k := by
  rw [model.ofPoint_apply _ nt_n1]
  funext a
  simp [pointB, NT.depth]

theorem ofPoint_pointB_water (j k s : ℝ) : model.ofPoint (pointB j k s) 2 water = fun a => if a = 0 then s else 1 - s := by
  rw [model.ofPoint_apply _ nt_water]
  funext a
  simp [pointB, NT.depth]

/-- Allowed actions of the strict-reset map. -/
def Sstrict (x : model.Pt) (p : model.NT) (a : Fin 2) : Prop :=
  (model.hasStrictReset (model.ofPoint x) p.depth p.hist ∧ a = model.piStar p.depth p.hist) ∨
    (¬ model.hasStrictReset (model.ofPoint x) p.depth p.hist ∧
      model.Qxi (model.ofPoint x) p.depth p.hist a = model.Mx (model.ofPoint x) p.depth p.hist)

/-- The full-reset point `(1, 1)` with `swim`: the image of every `(j, k) ≠ (1, 1)` under the strict-reset map. -/
noncomputable def resetPoint : model.Pt := pointB 1 1 1

theorem resetPoint_mem_dom : resetPoint ∈ model.dom := pointB_mem_dom (by norm_num) (by norm_num) (by norm_num)

/-- Every decision node of Instance B is the root, `n₁` or the water, and `π⋆` there is go / jump / swim. -/
theorem piStar_cases (p : model.NT) :
    (p.depth = 0 ∧ model.piStar p.depth p.hist = 1) ∨ (p.depth = 1 ∧ model.piStar p.depth p.hist = 1) ∨
      (p.depth = 2 ∧ model.piStar p.depth p.hist = 0) := by
  obtain ⟨⟨⟨m, hm⟩, hist⟩, prf⟩ := p
  match m with
  | 0 => exact Or.inl ⟨rfl, by show model.piStar 0 hist = 1; rw [eq_root hist]; exact piStar_root⟩
  | 1 => exact Or.inr (Or.inl ⟨rfl, by show model.piStar 1 hist = 1; rw [eq_n1_of_nonterminal hist prf]; exact piStar_n1⟩)
  | 2 => exact Or.inr (Or.inr ⟨rfl, by show model.piStar 2 hist = 0; rw [eq_water_of_nonterminal hist prf]; exact piStar_water⟩)
  | m + 3 => exact absurd prf (not_nonterminal_ge_three (m + 3) (by omega) hist)

/-- For `(j, k, s) ≠ (1, 1, 1)` in the simplex, the strict-reset map's value at `pointB j k s` contains the
full-reset point (`F(j,k) = {(1,1)}` — here the membership half, which is what the closed-graph failure
needs).
Source: [[oracle-side-gaps-reaudit]] line 42
Kind: P
Fidelity: exact (membership of the reset point; the value is the singleton `{δ_{π⋆}}` at every node by
definition)
Hyps: (a) -/
theorem resetPoint_mem_strict {j k s : ℝ} (hj : 0 ≤ j ∧ j ≤ 1) (hk : 0 ≤ k ∧ k ≤ 1) (hs : 0 ≤ s ∧ s ≤ 1)
    (hne : ¬ (j = 1 ∧ k = 1 ∧ s = 1)) : resetPoint ∈ model.corrOf Sstrict (pointB j k s) := by
  have hπ := model.ofPoint_isPolicy (pointB_mem_dom hj hk hs)
  have hroot : model.resid (model.ofPoint (pointB j k s)) 0 root < 0 := by
    apply resid_root_neg _ hπ
    rw [ofPoint_pointB_root, ofPoint_pointB_n1, ofPoint_pointB_water]
    simpa using hne
  refine model.mem_corrOf.2 fun p => ⟨(model.mem_dom.1 resetPoint_mem_dom) p, fun a ha => ?_⟩
  have hne : a ≠ model.piStar p.depth p.hist := fun h => ha (Or.inl ⟨hasStrictReset_of_root _ hroot _ _, h⟩)
  rcases piStar_cases p with ⟨hd, hp⟩ | ⟨hd, hp⟩ | ⟨hd, hp⟩ <;>
    · rw [hp] at hne
      unfold resetPoint pointB
      simp only [hd]
      fin_cases a <;> simp_all

/-- The full-reset point is **not** in the strict-reset map's value at itself: at `(1,1,1)` no reset fires at
`n₁` (the root has `r = 0`, `n₁` has `r > 0`), so the value at `n₁` is `Δ(𝒜_{n₁}) = {δ_stay}`, but the reset point
plays `jump` there. Hence `F(1,1) = {(1,0)} ∌ (1,1)`.
Source: [[oracle-side-gaps-reaudit]] line 42
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem resetPoint_not_mem_strict_self : resetPoint ∉ model.corrOf Sstrict resetPoint := by
  intro hmem
  have hπ := model.ofPoint_isPolicy resetPoint_mem_dom
  have h111 : model.ofPoint resetPoint 0 root 1 = 1 ∧ model.ofPoint resetPoint 1 n1 1 = 1 ∧
      model.ofPoint resetPoint 2 water 0 = 1 := by
    unfold resetPoint
    rw [ofPoint_pointB_root, ofPoint_pointB_n1, ofPoint_pointB_water]
    simp
  have hnores : ¬ model.hasStrictReset (model.ofPoint resetPoint) 1 n1 := by
    rintro ⟨m, hm, hlt⟩
    match m with
    | 0 =>
      rw [prefixH_zero n1 root, resid_root_eq_zero _ hπ h111] at hlt
      exact lt_irrefl _ hlt
    | 1 =>
      rw [prefixH_self] at hlt
      linarith [resid_n1_pos _ hπ]
  let p : model.NT := ⟨⟨⟨1, by norm_num⟩, n1⟩, nt_n1⟩
  have := ((model.mem_corrOf.1 hmem) p).2 1
  have hne : ¬ model.Qxi (model.ofPoint resetPoint) 1 n1 1 = model.Mx (model.ofPoint resetPoint) 1 n1 := by
    rw [Mx_n1 _ hπ]
    linarith [Qxi_n1_1_le _ hπ]
  have h0 := this (fun hS => hS.elim (fun h1 => hnores h1.1) (fun h2 => hne h2.2))
  have : resetPoint p 1 = 1 := by
    show pointB 1 1 1 p 1 = 1
    simp [pointB, p, NT.depth]
  rw [this] at h0
  exact one_ne_zero h0

/-- **Gap 1 in the finite shadow**: the strict-reset map on Instance B does **not** have a closed graph over the
product of simplices — the hypothesis `hF_graph` of `kakutani_pi_stdSimplex` fails (not Kakutani). Witness: along
`x_n = (1, 1 - 1/(n+2), swim) → (1, 1, swim)` the reset point `(1, 1, swim) ∈ F(x_n)` for every `n`, but
`(1, 1, swim) ∉ F(1, 1, swim)`.
Source: [[oracle-side-gaps-reaudit]] Q1, line 42; [[uea-inventory]] 007
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem not_hasClosedGraphOn_strict : ¬ HasClosedGraphOn (model.corrOf Sstrict) model.dom := by
  intro hcg
  let xs : ℕ → model.Pt := fun n => pointB 1 (1 - 1 / ((n : ℝ) + 2)) 1
  have hk : ∀ n : ℕ, 0 ≤ 1 - 1 / ((n : ℝ) + 2) ∧ 1 - 1 / ((n : ℝ) + 2) ≤ 1 := by
    intro n
    have h2 : (0:ℝ) < (n : ℝ) + 2 := by positivity
    constructor
    · rw [sub_nonneg, div_le_one h2]; linarith
    · linarith [div_pos one_pos h2]
  have hmem : ∀ᶠ n in atTop, xs n ∈ model.dom ∧ resetPoint ∈ model.corrOf Sstrict (xs n) := by
    refine Eventually.of_forall fun n => ⟨pointB_mem_dom (by norm_num) (hk n) (by norm_num), ?_⟩
    refine resetPoint_mem_strict (by norm_num) (hk n) (by norm_num) ?_
    rintro ⟨_, hk1, _⟩
    have h2 : (0:ℝ) < (n : ℝ) + 2 := by positivity
    have : (1 : ℝ) / ((n : ℝ) + 2) = 0 := by linarith
    exact absurd this (div_ne_zero one_ne_zero h2.ne')
  have hlim : Tendsto xs atTop (𝓝 resetPoint) := by
    rw [tendsto_pi_nhds]
    intro p
    rw [tendsto_pi_nhds]
    intro a
    have h0 : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have h1 : Tendsto (fun n : ℕ => 1 - (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub h0
    show Tendsto (fun n : ℕ => pointB 1 (1 - 1 / ((n : ℝ) + 2)) 1 p a) atTop (𝓝 (pointB 1 1 1 p a))
    unfold pointB
    split_ifs
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
    · simpa using h0
    · exact h1
    · exact tendsto_const_nhds
    · exact tendsto_const_nhds
  have := hcg.mem_of_tendsto hmem hlim tendsto_const_nhds
  exact resetPoint_not_mem_strict_self this.2

end InstB

end Cleanroom.Uea.UeaColeShadow
