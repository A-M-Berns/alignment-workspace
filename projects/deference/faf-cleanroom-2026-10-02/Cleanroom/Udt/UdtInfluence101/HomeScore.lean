import Cleanroom.Udt.UdtInfluence101.Two
import Cleanroom.Udt.UdtInfluence101.Witnesses

/-!
# The score at the homework node is not constant in the action (`Home`, N+ companion of the `hH` tie)

Repair round 2 (2026-10-02): the audit r2 (adversarial) probe `HomeScore.lean` promoted into the
library (adv. N2, fid. N7). In `Home.homeModel`, for the pure actions `ofAct a` at the homework node
`hT`, the expected utility along the ε-family is `1/2 − ε/4 + ε·p(a)/2` with `p(true) = 3/4`,
`p(false) = 1/4` (the tails branch contributes `1/4` for every `ε`; the heads branch reads the
ε-mixed profile), so `𝕀^𝔼_∅(ofAct true, hT) = 1/8` and `𝕀^𝔼_∅(ofAct false, hT) = −1/8` at the
witness world `ω₀` (`IE_true`, `IE_false`). Through Theorem 1, with every hypothesis discharged by
the package's own `Home.*` facts, this gives a positive world reaching `hT` at which
`f^0_{hT,S̄}(true) ≠ f^0_{hT,S̄}(false)` (`score_hT_nonconst`): the N+ companion of
`HomeTie.two_udt101_hH` is in the library, and `Home` is a model where UDT1.01 is unique at one node
(`hT`) and not at another (`hH`). It also gives `Home.theorem1_home` a machine-checked influence gap
between algorithms (`IE_true ≠ IE_false`).

Namespace `HomeScore`.
-/

namespace Cleanroom.Udt.UdtInfluence101.HomeScore

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree
open Cleanroom.Udt.UdtInfluence101.Home ProfileModel

noncomputable section

/-- The ice-cream probability when the predicted answer is `a`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def p (a : Bool) : ℝ := if a then 3 / 4 else 1 / 4

/-- Supporting lemma `pn_root`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pn_root : homeModel.pn root = root := by
  show (if root = hH then hT else root) = root
  rw [if_neg root_ne_hH]

/-- Supporting lemma `pn_hT`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pn_hT : homeModel.pn hT = root := by
  show (if hT = hH then hT else root) = root
  rw [if_neg hT_ne_hH]

/-- Supporting lemma `pn_hH`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pn_hH : homeModel.pn hH = hT := by
  show (if hH = hH then hT else root) = hT
  rw [if_pos rfl]

/-- Supporting lemma `hB`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hB : ∀ (m : Node Bool 2) (s : Fin (m.1.val + 1) → Bool) (b : Bool),
    (homeModel.B m s).w b = 1 / 2 := fun _ _ b => fair_w b

/-- Supporting lemma `hπ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hπ : ∀ (m : Node Bool 2) (b : Bool), (homeModel.π₀ m).w b = 1 / 2 := fun _ b => fair_w b

/-- Supporting lemma `hκ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hκ : ∀ (w : Unit) (k : Fin 2) (obs : Fin k.val → Bool) (s : Fin (k.val + 1) → Bool)
    (b o ξ : Bool), (homeModel.κ w k obs s b o).w ξ = 1 / 2 := fun _ _ _ _ _ _ ξ => fair_w ξ

/-- Supporting lemma `prof_ofAct_hT`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prof_ofAct_hT (a : Bool) : homeModel.prof (ofAct a) hT = FinDist.delta a :=
  homeModel.prof_ofAct hreach a

/-- Supporting lemma `F_node0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_node0 (a : Bool) (ε : ℝ) (r : Unit × Bool) (x : Letter Bool Bool Bool) :
    homeModel.F (ofAct a) hT ε r (node0 _) x = 1 / 8 := by
  have h0 : oNode (node0 (Letter Bool Bool Bool)) = root := oNode_node0
  have heA : ∀ (obs : Fin (node0 (Letter Bool Bool Bool)).1.val → Bool)
      (acts : Fin (node0 (Letter Bool Bool Bool)).1.val → Bool) (b a' o : Bool),
      (homeModel.eA r.1 (node0 (Letter Bool Bool Bool)).1 obs acts b a').w o = 1 / 2 := by
    intro obs acts b a' o
    simp [homeModel, node0]
  simp only [ProfileModel.F, ProfileModel.algW, ProfileModel.profW, h0, if_neg root_ne_hT, pn_root,
    hB, hπ, heA, hκ, Fintype.sum_bool]
  norm_num

/-- Supporting lemma `F_node1_T`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_node1_T (a : Bool) (ε : ℝ) (r : Unit × Bool) (a₀ ξ₁ : Bool) (y : Letter Bool Bool Bool) :
    homeModel.F (ofAct a) hT ε r (node1 (a₀, true, ξ₁)) y =
      ((1 - ε) / 2 + ε * (if y.1 = a then 1 else 0)) * (1 / 4) := by
  have h1 : oNode (node1 (a₀, true, ξ₁) : Node (Letter Bool Bool Bool) 2) = hT := by
    rw [oNode_node1]; rfl
  have heA : ∀ (b a' o : Bool),
      (homeModel.eA r.1 (node1 (a₀, true, ξ₁) : Node (Letter Bool Bool Bool) 2).1
        (obsPre (node1 (a₀, true, ξ₁))) (actPre (node1 (a₀, true, ξ₁))) b a').w o = 1 / 2 := by
    intro b a' o
    simp [homeModel, node1, obsPre]
  simp only [ProfileModel.F, ProfileModel.algW, ProfileModel.profW, h1, if_true, pn_hT,
    if_neg root_ne_hT, hB, hπ, heA, hκ, Fintype.sum_bool, ofAct, ofDist, FinDist.delta_w]
  ring

/-- Supporting lemma `F_node1_H`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_node1_H (a : Bool) (ε : ℝ) (r : Unit × Bool) (a₀ ξ₁ : Bool) (y : Letter Bool Bool Bool) :
    homeModel.F (ofAct a) hT ε r (node1 (a₀, false, ξ₁)) y =
      (1 / 2) * ((1 - ε) / 2 + ε * (if y.2.1 then p a else 1 - p a)) * (1 / 2) := by
  have h1 : oNode (node1 (a₀, false, ξ₁) : Node (Letter Bool Bool Bool) 2) = hH := by
    rw [oNode_node1]; rfl
  have heA : ∀ (b a' o : Bool),
      (homeModel.eA r.1 (node1 (a₀, false, ξ₁) : Node (Letter Bool Bool Bool) 2).1
        (obsPre (node1 (a₀, false, ξ₁))) (actPre (node1 (a₀, false, ξ₁))) b a').w o =
        if o then (if a' then 3 / 4 else 1 / 4) else 1 - (if a' then 3 / 4 else 1 / 4) := by
    intro b a' o
    simp [homeModel, node1, obsPre, coin_w]
  obtain ⟨a₁, o₁, ξ₂⟩ := y
  simp only [ProfileModel.F, ProfileModel.algW, ProfileModel.profW, h1, if_neg hT_ne_hH.symm, pn_hH,
    if_true, hB, hπ, heA, hκ, Fintype.sum_bool, prof_ofAct_hT, FinDist.delta_w, p]
  cases a <;> cases o₁ <;> norm_num <;> ring

/-- Supporting lemma `inner_T`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem inner_T (a : Bool) (ε : ℝ) (r : Unit × Bool) (a₀ ξ₁ : Bool) :
    ∑ y, homeModel.F (ofAct a) hT ε r (node1 (a₀, true, ξ₁)) y *
        homeModel.U (r, ![(a₀, true, ξ₁), y]) =
      (1 - ε) / 2 + ε * (if ξ₁ = a then 1 else 0) := by
  rw [sum_letter]
  simp only [F_node1_T]
  simp only [homeModel, Matrix.cons_val_zero, Matrix.cons_val_one, Fintype.sum_bool]
  cases ξ₁ <;> cases a <;> norm_num <;> ring

/-- Supporting lemma `inner_H`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem inner_H (a : Bool) (ε : ℝ) (r : Unit × Bool) (a₀ ξ₁ : Bool) :
    ∑ y, homeModel.F (ofAct a) hT ε r (node1 (a₀, false, ξ₁)) y *
        homeModel.U (r, ![(a₀, false, ξ₁), y]) =
      (1 - ε) / 2 + ε * p a := by
  rw [sum_letter]
  simp only [F_node1_H]
  simp only [homeModel, Matrix.cons_val_zero, Matrix.cons_val_one, Fintype.sum_bool]
  cases a <;> norm_num [p] <;> ring

/-- Supporting lemma `root_w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem root_w (r : Unit × Bool) : homeModel.root.w r = if r.2 then 0 else 1 := by
  obtain ⟨⟨⟩, ξ⟩ := r
  cases ξ <;> simp [homeModel]

/-- **`𝔼^ε[U]` along the ε-family of a pure action at `hT`**: `1/2 − ε/4 + ε·p(a)/2`.
Source: audit r2 (adversarial) probe `HomeScore.lean`; mandate T5(ii) (N+ companion of the tie); [[diffractor-synthesis]] l. 67
Kind: P
Fidelity: exact
Hyps: none -/
theorem total (a : Bool) (ε : ℝ) :
    ∑ ω, homeModel.lawW (ofAct a) hT ε ω * homeModel.U ω = 1 / 2 - ε / 4 + ε * p a / 2 := by
  rw [sum_pworld_two]
  have key : ∀ (r : Unit × Bool) (x : Letter Bool Bool Bool),
      ∑ y, homeModel.lawW (ofAct a) hT ε (r, ![x, y]) * homeModel.U (r, ![x, y]) =
        homeModel.root.w r * (1 / 8) *
          (if x.2.1 then (1 - ε) / 2 + ε * (if x.2.2 = a then 1 else 0)
            else (1 - ε) / 2 + ε * p a) := by
    intro r x
    obtain ⟨a₀, o₀, ξ₁⟩ := x
    have hfac : ∀ y, homeModel.lawW (ofAct a) hT ε (r, ![(a₀, o₀, ξ₁), y]) *
        homeModel.U (r, ![(a₀, o₀, ξ₁), y]) =
        homeModel.root.w r * (1 / 8) *
          (homeModel.F (ofAct a) hT ε r (node1 (a₀, o₀, ξ₁)) y * homeModel.U (r, ![(a₀, o₀, ξ₁), y])) := by
      intro y
      rw [homeModel.lawW_two, F_node0]
      ring
    simp only [hfac, ← Finset.mul_sum]
    cases o₀
    · rw [inner_H]; simp
    · rw [inner_T]; simp
  simp only [key, root_w]
  simp only [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
  cases a <;> simp [p] <;> ring

/-- Supporting lemma `mem_atom0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_atom0 (ω : PWorld Bool Bool Bool Unit 2) : ω ∈ Home.S.atom 0 ω₀ ↔ ω.1.2 = false := by
  rw [PlaySpace.mem_atom]
  constructor
  · rintro ⟨_, hs⟩
    have := hs 0 le_rfl
    exact this.symm
  · intro h
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => ?_⟩
    have hi0 : i = 0 := Fin.ext (Nat.le_zero.1 hi)
    subst hi0
    exact h.symm

/-- Supporting lemma `lawW_eq_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem lawW_eq_zero (a : Bool) (ε : ℝ) {ω : PWorld Bool Bool Bool Unit 2} (h : ω.1.2 = true) :
    homeModel.lawW (ofAct a) hT ε ω = 0 := by
  unfold ProfileModel.lawW
  have : homeModel.root.w ω.1 = 0 := by rw [root_w, h]; rfl
  rw [this, zero_mul]

/-- Supporting lemma `sum_atom0_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_atom0_eq (a : Bool) (ε : ℝ) (f : PWorld Bool Bool Bool Unit 2 → ℝ) :
    ∑ ω ∈ Home.S.atom 0 ω₀ ∩ univ, homeModel.lawW (ofAct a) hT ε ω * f ω =
      ∑ ω, homeModel.lawW (ofAct a) hT ε ω * f ω := by
  rw [Finset.inter_univ]
  refine Finset.sum_subset (Finset.subset_univ _) fun ω _ hω => ?_
  rw [mem_atom0] at hω
  rw [lawW_eq_zero a ε (by simpa using hω), zero_mul]

/-- Supporting lemma `mass_atom0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_atom0 (a : Bool) (ε : ℝ) :
    mass (homeModel.lawW (ofAct a) hT ε) (Home.S.atom 0 ω₀ ∩ univ) = 1 := by
  unfold mass
  rw [Finset.inter_univ]
  rw [Finset.sum_subset (Finset.subset_univ _) fun ω _ hω => by
    rw [mem_atom0] at hω
    exact lawW_eq_zero a ε (by simpa using hω)]
  exact Home.S.law_sum (ofAct a) hT ε

/-- Supporting lemma `cexp0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp0 (a : Bool) (ε : ℝ) :
    Home.S.cexp (homeModel.lawW (ofAct a) hT ε) 0 univ homeModel.U ω₀ =
      1 / 2 - ε / 4 + ε * p a / 2 := by
  unfold PlaySpace.cexp condExpJunk
  rw [mass_atom0, if_neg one_ne_zero, div_one, sum_atom0_eq, total]

/-- **The time-`0` influence of a pure action at `hT`**: `−1/4 + p(a)/2`.
Source: audit r2 (adversarial) probe `HomeScore.lean`; mandate T5(ii) (N+ companion of the tie); [[diffractor-synthesis]] l. 67
Kind: P
Fidelity: exact
Hyps: none -/
theorem IE_hT (a : Bool) : Home.S.IE 0 (ofAct a) hT ω₀ = -1 / 4 + p a / 2 := by
  unfold PlaySpace.IE
  have hf : (fun ε => Home.S.cexp (Home.S.law (ofAct a) hT ε) 0 univ Home.S.U ω₀) =
      fun ε => 1 / 2 - ε / 4 + ε * p a / 2 := funext fun ε => cexp0 a ε
  rw [hf]
  have h1 : HasDerivAt (fun ε : ℝ => 1 / 2 - ε / 4) (-(1 / 4)) 0 :=
    ((hasDerivAt_id' (x := (0 : ℝ))).div_const 4).const_sub (1 / 2)
  have h2 : HasDerivAt (fun ε : ℝ => ε * p a / 2) (1 * p a / 2) 0 :=
    ((hasDerivAt_id' (x := (0 : ℝ))).mul_const (p a)).div_const 2
  have key : HasDerivAt (fun ε : ℝ => 1 / 2 - ε / 4 + ε * p a / 2) (-(1 / 4) + 1 * p a / 2) 0 :=
    h1.add h2
  rw [key.deriv]
  ring

/-- **`𝕀^𝔼_∅(δ answer-true, hT) = 1/8`** at `ω₀`.
Source: audit r2 (adversarial) probe `HomeScore.lean`; mandate T5(ii) (N+ companion of the tie); [[diffractor-synthesis]] l. 67
Kind: P
Fidelity: exact
Hyps: none -/
theorem IE_true : Home.S.IE 0 (ofAct true) hT ω₀ = 1 / 8 := by
  rw [IE_hT]; norm_num [p]

/-- **`𝕀^𝔼_∅(δ answer-false, hT) = −1/8`** at `ω₀`.
Source: audit r2 (adversarial) probe `HomeScore.lean`; mandate T5(ii) (N+ companion of the tie); [[diffractor-synthesis]] l. 67
Kind: P
Fidelity: exact
Hyps: none -/
theorem IE_false : Home.S.IE 0 (ofAct false) hT ω₀ = -1 / 8 := by
  rw [IE_hT]; norm_num [p]

/-- **`f^0_{hT,S̄}` is not constant in the action at a positive world reaching `hT`** — the N+ companion of the `hH` tie (`HomeTie.two_udt101_hH`), through Theorem 1 with every hypothesis discharged.
Source: audit r2 (adversarial) probe `HomeScore.lean`; mandate T5(ii) (N+ companion of the tie); [[diffractor-synthesis]] l. 67
Kind: N+
Fidelity: exact
Hyps: none -/
theorem score_hT_nonconst : ∃ ω, 0 < homeModel.baseW ω ∧ ω ∈ pReach hT ∧
    Home.S.fS hT (FinDist.delta true) 0 ω ≠ Home.S.fS hT (FinDist.delta false) 0 ω := by
  by_contra hcon
  push Not at hcon
  have ht := Home.S.theorem1 homeModel.smoothLaw hall (homeModel.A3 hT) (homeModel.A4 hT hatoms)
    (homeModel.A5_model hone hreach hall hcoh) hRP (ofAct true) 0 (Nat.zero_le _) ω₀ ω₀_pos ω₀_reach
  have hf := Home.S.theorem1 homeModel.smoothLaw hall (homeModel.A3 hT) (homeModel.A4 hT hatoms)
    (homeModel.A5_model hone hreach hall hcoh) hRP (ofAct false) 0 (Nat.zero_le _) ω₀ ω₀_pos ω₀_reach
  have heq : Home.S.cexp Home.S.ℙ.w 0 (Home.S.reach hT)
      (fun ω' => Home.S.fS hT (Home.S.play (ofAct true) hT ω') 0 ω') ω₀ =
      Home.S.cexp Home.S.ℙ.w 0 (Home.S.reach hT)
      (fun ω' => Home.S.fS hT (Home.S.play (ofAct false) hT ω') 0 ω') ω₀ :=
    Home.S.cexp_congr_on_pos fun ω' hω' hpos => hcon ω' hpos (Finset.mem_inter.1 hω').2
  have : Home.S.IE 0 (ofAct true) hT ω₀ = Home.S.IE 0 (ofAct false) hT ω₀ := by rw [ht, hf, heq]
  rw [IE_true, IE_false] at this
  norm_num at this

end

end Cleanroom.Udt.UdtInfluence101.HomeScore
