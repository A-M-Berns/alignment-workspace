import Cleanroom.Udt.UdtInfluence101.Two
import Cleanroom.Udt.UdtInfluence101.Witnesses

/-!
# The tie instance: an action-irrelevant node where UDT1.01 is not unique

The witness the mandate asked for in T5(ii) ("a T7 instance with an action-irrelevant node; N+:
`f^0` non-constant elsewhere"), built in repair round 1 (2026-10-02) after audit r1 found that
`PlaySpace.exists_two_isUDT101` shipped no inhabitant of its tie hypothesis.

**The model** (`tieModel`, sixteen worlds, all positive): `O = Act = Bool`, no unplannable
information (`Ξ = W = Unit`), horizon `2`. The root action pays: `U = [a₀ = true]`. The
depth-`1` node `hT` is read by nobody (`pn ≡ hH`: every node formally reads `hH`'s profile, a read
that is inert because `eA` is constant in the predicted action), the observation kernel is a fair
coin and the state kernel is trivial, so the action at `hT = ⟨1, ![true]⟩` enters nothing: `hT` is
**inert**
(`Two.lean`), every influence at `hT` is zero, Post 8's score `f^0_{hT,S̄}` is identically zero, and
both constant algorithms are UDT1.01 at `hT` (`two_udt101_hT`, through
`PlaySpace.exists_two_isUDT101`). At the root the score is **not** constant: `f^0_root(a) =
[a = true] − 1/2` (`score_root`), so `ofAct true` is UDT1.01 at the root and `ofAct false` is not
(`not_isUDT101_ofAct_false_root`). That is the N+ grade: the tie is real at one node and absent at
another, in one model.
-/

namespace Cleanroom.Udt.UdtInfluence101

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree
open Home (fair fair_w hT hH root root_ne_hT root_ne_hH hT_ne_hH leafExt_hT_iff)
open ProfileModel

namespace Tie

noncomputable section

/-- **The tie model**: the root action pays, the depth-one actions do nothing, nobody reads `hT`'s
profile (`pn ≡ hH`; the formal read of `hH`'s profile is inert because `eA` ignores the predicted
action).
Source: mandate T5(ii) ("a T7 instance with an action-irrelevant node")
Kind: D
Fidelity: n/a (an instance built for the witness)
Hyps: n/a -/
def tieModel : ProfileModel Bool Bool Unit Unit 2 where
  root := FinDist.delta ((), ())
  κ := fun _ _ _ _ _ _ => FinDist.delta ()
  eA := fun _ _ _ _ _ _ => fair
  pn := fun _ => hH
  B := fun _ _ => fair
  π₀ := fun _ => fair
  U := fun ω => if (ω.2 0).1 then 1 else 0

/-- The play space of the tie model.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev S : PlaySpace Bool Bool Unit 2 (PWorld Bool Bool Unit Unit 2) := tieModel.toPlaySpace

/-- **`hT` is inert**: nobody reads its profile and the kernels ignore the current action.
Source: mandate T5(ii)
Kind: L
Fidelity: exact
Hyps: none -/
theorem inert_hT : tieModel.Inert hT :=
  ⟨rfl, fun _ => hT_ne_hH.symm, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩

/-- **The utility is blind to the action at `hT`** (it reads the root action only).
Source: mandate T5(ii)
Kind: L
Fidelity: exact
Hyps: none -/
theorem ublind_hT : tieModel.UBlind hT := fun _ _ _ _ _ _ _ => rfl

/-! ### Every world is positive -/

/-- Supporting lemma `baseF_eq` (every baseline step factor is `1/4`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseF_eq (r : Unit × Unit) (m : Node (Letter Bool Bool Unit) 2) (ℓ : Letter Bool Bool Unit) :
    tieModel.baseF r m ℓ = 1 / 4 := by
  simp only [ProfileModel.baseF, tieModel, fair_w, Fintype.sum_bool, FinDist.delta_w]
  norm_num

/-- **Every world has baseline weight `1/16`.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseW_eq (ω : PWorld Bool Bool Unit Unit 2) : tieModel.baseW ω = 1 / 16 := by
  unfold ProfileModel.baseW pathLaw
  rw [Fin.prod_univ_two, baseF_eq, baseF_eq]
  have : tieModel.root.w ω.1 = 1 := by simp [tieModel]
  rw [this]
  norm_num

/-- Supporting lemma `baseW_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseW_pos (ω : PWorld Bool Bool Unit Unit 2) : 0 < tieModel.baseW ω := by
  rw [baseW_eq]; norm_num

/-- The witness world: both letters `(true, true, ())`; it reaches `hT`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ω₀ : PWorld Bool Bool Unit Unit 2 := (((), ()), fun _ => (true, true, ()))

/-- Supporting lemma `ω₀_reach`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ω₀_reach : ω₀ ∈ pReach hT := by
  show ω₀ ∈ event (fun ω => LeafExt hT (pObs ω))
  rw [mem_event, leafExt_hT_iff]
  rfl

/-- Supporting lemma `mem_pReach_root` (every world reaches the root).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_pReach_root (ω : PWorld Bool Bool Unit Unit 2) : ω ∈ pReach root := by
  show ω ∈ event (fun ω => LeafExt root (pObs ω))
  rw [mem_event]
  show prefixOf' (pObs ω) 0 _ = ![]
  funext i
  exact i.elim0

/-! ### The tie at `hT` -/

/-- **Both constant algorithms are UDT1.01 at `hT`.**
Source: mandate T5(ii); [[diffractor-synthesis]] ll. 67, 194 (udt-rep-083)
Kind: P
Fidelity: exact
Hyps: none -/
theorem isUDT101_ofAct_hT (a : Bool) : S.IsUDT101 (ofAct a) hT :=
  tieModel.isUDT101_ofAct_of_inert inert_hT ublind_hT a

/-- **UDT1.01 is not unique at `hT`**: `PlaySpace.exists_two_isUDT101` instantiated on the tie
model — two distinct UDT1.01 algorithms at `hT`. Together with `score_root` /
`not_isUDT101_ofAct_false_root` (the score is not constant at the root of the same model) this is
the N+ witness for the refutation of the corpus's uniqueness glosses.
Source: [[diffractor-synthesis]] ll. 67, 194 (udt-rep-083, 2-002(c)); mandate T5(ii), (iv)
Kind: N+
Fidelity: exact (refutation of the uniqueness reading, ATTRIBUTION-UNVETTED)
Hyps: none -/
theorem two_udt101_hT : ∃ A₁ A₂ : Alg Bool Bool Unit 2, S.IsUDT101 A₁ hT ∧ S.IsUDT101 A₂ hT ∧ A₁ ≠ A₂ :=
  tieModel.exists_two_isUDT101_of_inert inert_hT ublind_hT (baseW_pos ω₀) ω₀_reach (show (true : Bool) ≠ false by decide)

/-- **The score at `hT` is identically zero.**
Source: mandate T5(ii)
Kind: P
Fidelity: exact
Hyps: none -/
theorem score_hT (μ : FinDist Bool) (ω : PWorld Bool Bool Unit Unit 2) : S.fS hT μ 0 ω = 0 :=
  tieModel.fS_eq_zero_of_inert inert_hT ublind_hT μ 1 0 rfl ω

/-! ### The score is not constant at the root -/

/-- Supporting lemma `F_root_eq` (the root step factor under ε-play of `ofAct a` at the root).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_root_eq (a : Bool) (ε : ℝ) (r : Unit × Unit) (a₀ o₀ : Bool) (ξ : Unit) :
    tieModel.F (ofAct a) root ε r (node0 _) (a₀, o₀, ξ) =
      ((1 - ε) / 2 + ε * (if a₀ = a then 1 else 0)) * (1 / 2) := by
  have h0 : oNode (node0 (Letter Bool Bool Unit)) = root := oNode_node0
  simp only [ProfileModel.F, ProfileModel.algW, ProfileModel.profW, h0, tieModel, fair_w,
    FinDist.delta_w, Fintype.sum_bool, ofAct, ofDist, if_neg root_ne_hH.symm, if_true]
  ring

/-- Supporting lemma `atom_zero_eq_univ` (there is no unplannable information at time `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atom_zero_eq_univ (ω : PWorld Bool Bool Unit Unit 2) : S.atom 0 ω = univ := by
  ext ω'
  simp only [PlaySpace.mem_atom, Finset.mem_univ, iff_true]
  exact ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun _ _ => rfl⟩

/-- Supporting lemma `cexp_root_eq` (the expected utility under ε-play of `ofAct a` at the root,
for every `ε`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_root_eq (a : Bool) (ε : ℝ) (ω : PWorld Bool Bool Unit Unit 2) :
    S.cexp (tieModel.lawW (ofAct a) root ε) 0 univ tieModel.U ω =
      (1 - ε) / 2 + ε * (if a then 1 else 0) := by
  unfold PlaySpace.cexp condExpJunk
  rw [atom_zero_eq_univ, Finset.univ_inter]
  have hm : mass (tieModel.lawW (ofAct a) root ε) univ = 1 := S.law_sum (ofAct a) root ε
  rw [hm, if_neg one_ne_zero, div_one]
  have := tieModel.sum_lawW_mul_fst (ofAct a) root ε (fun _ x => if x.1 then 1 else 0)
  rw [show (∑ x, tieModel.lawW (ofAct a) root ε x * tieModel.U x) =
      ∑ ω, tieModel.lawW (ofAct a) root ε ω * (fun _ (x : Letter Bool Bool Unit) =>
        if x.1 then (1 : ℝ) else 0) ω.1 (ω.2 0) from rfl, this]
  simp only [Fintype.sum_prod_type, F_root_eq]
  simp only [Fintype.sum_unique, Fintype.sum_bool, tieModel, FinDist.delta_w]
  cases a <;> simp <;> ring

/-- **The time-`0` influence of a constant algorithm at the root**: `[a = true] − 1/2`.
Source: mandate T5(ii) (N+: "`f^0` non-constant elsewhere")
Kind: P
Fidelity: exact
Hyps: none -/
theorem IE_root (a : Bool) (ω : PWorld Bool Bool Unit Unit 2) :
    S.IE 0 (ofAct a) root ω = (if a then 1 else 0) - 1 / 2 := by
  unfold PlaySpace.IE
  have hf : (fun ε => S.cexp (S.law (ofAct a) root ε) 0 univ S.U ω) =
      fun ε => (1 - ε) / 2 + ε * (if a then 1 else 0) := funext fun ε => cexp_root_eq a ε ω
  rw [hf]
  have h1 : HasDerivAt (fun ε : ℝ => (1 - ε) / 2) (-1 / 2) 0 :=
    ((hasDerivAt_id' (x := (0 : ℝ))).const_sub 1).div_const 2
  have h2 : HasDerivAt (fun ε : ℝ => ε * (if a then 1 else 0)) (1 * (if a then 1 else 0)) 0 :=
    (hasDerivAt_id' (x := (0 : ℝ))).mul_const (if a then (1 : ℝ) else 0)
  have key : HasDerivAt (fun ε : ℝ => (1 - ε) / 2 + ε * (if a then 1 else 0))
      (-1 / 2 + 1 * (if a then 1 else 0)) 0 := h1.add h2
  rw [key.deriv]
  ring

/-- Supporting lemma `posObs_root` (both observations are possible at time `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem posObs_root (ω : PWorld Bool Bool Unit Unit 2) : S.PosObs 0 ω := by
  intro o
  refine mass_pos_of_mem S.ℙ.nonneg (Finset.mem_inter.2 ⟨?_, ?_⟩)
    (baseW_pos (((), ()), ![(true, o, ()), (true, true, ())]))
  · rw [atom_zero_eq_univ]; exact Finset.mem_univ _
  · rw [S.mem_nextObs (by norm_num)]
    rfl

/-- **Post 8's score at the root is `[a = true] − 1/2`**: not constant in the action.
Source: mandate T5(ii) (N+: "`f^0` non-constant elsewhere")
Kind: P
Fidelity: exact
Hyps: none -/
theorem score_root (a : Bool) (ω : PWorld Bool Bool Unit Unit 2) :
    S.fS root (FinDist.delta a) 0 ω = (if a then 1 else 0) - 1 / 2 := by
  rw [S.fS_of_ge root _ (Nat.lt_irrefl 0)]
  exact (S.lemma1_split tieModel.smoothLaw (by norm_num) (posObs_root ω) (ofAct a) root).symm.trans
    (IE_root a ω)

/-- **`ofAct false` is not UDT1.01 at the root** (the score prefers `true` by `1`).
Source: mandate T5(ii) (N+: the tie is absent at the root)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem not_isUDT101_ofAct_false_root : ¬ S.IsUDT101 (ofAct false) root := by
  intro hU
  obtain ⟨a, ha, hmax⟩ := hU ω₀ (baseW_pos ω₀) (mem_pReach_root ω₀)
  have haf : a = false := (PlaySpace.delta_injective ha).symm
  subst haf
  have := hmax true
  change S.fS root (FinDist.delta true) 0 ω₀ ≤ S.fS root (FinDist.delta false) 0 ω₀ at this
  rw [score_root, score_root] at this
  norm_num at this

/-- **`ofAct true` is UDT1.01 at the root.**
Source: mandate T5(ii)
Kind: P
Fidelity: exact
Hyps: none -/
theorem isUDT101_ofAct_true_root : S.IsUDT101 (ofAct true) root := by
  intro ω _ _
  refine ⟨true, rfl, fun a' => ?_⟩
  show S.fS root (FinDist.delta a') 0 ω ≤ S.fS root (FinDist.delta true) 0 ω
  rw [score_root, score_root]
  cases a' <;> norm_num

end

end Tie

/-! ### The tie inside the homework instance: `hH` is inert in `Home.homeModel` -/

namespace HomeTie

open Home

/-- **`hH` is inert in the homework model**: `pn m ∈ {hT, root}` so nobody reads `hH`'s profile; the
mom kernel and the state kernel ignore the current action.
Source: audit r1 (adversarial) B1, route (ii); mandate T5(ii)
Kind: L
Fidelity: exact
Hyps: none -/
theorem inert_hH : homeModel.Inert hH := by
  refine ⟨rfl, fun m => ?_, fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  show (if m = hH then hT else root) ≠ hH
  split_ifs
  · exact hT_ne_hH
  · exact root_ne_hH

/-- **The homework utility is blind to the action at `hH`**: on the heads branch it reads `o₁` only.
Source: audit r1 (adversarial) B1, route (ii)
Kind: L
Fidelity: exact
Hyps: none -/
theorem ublind_hH : homeModel.UBlind hH := by
  intro r x hx a a' o ξ
  have hx' : x.2.1 = false := by
    rw [oNode_node1] at hx
    exact (node1_eq_iff _ _).1 hx
  show (if (![x, (a, o, ξ)] 0).2.1 then (if (![x, (a, o, ξ)] 1).1 = (![x, (a, o, ξ)] 0).2.2 then (1 : ℝ)
      else 0) else (if (![x, (a, o, ξ)] 1).2.1 then 1 else 0)) =
    (if (![x, (a', o, ξ)] 0).2.1 then (if (![x, (a', o, ξ)] 1).1 = (![x, (a', o, ξ)] 0).2.2 then (1 : ℝ)
      else 0) else (if (![x, (a', o, ξ)] 1).2.1 then 1 else 0))
  simp [hx']

/-- A positive world reaching `hH` (root state `false`, first observation `false`).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ω₁ : PWorld Bool Bool Bool Unit 2 := (((), false), fun _ => (true, false, true))

/-- Supporting lemma `ω₁_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ω₁_pos : 0 < homeModel.baseW ω₁ := (baseW_pos_iff ω₁).2 rfl

/-- Supporting lemma `ω₁_reach`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ω₁_reach : ω₁ ∈ pReach hH := by
  show ω₁ ∈ event (fun ω => LeafExt hH (pObs ω))
  rw [mem_event, leafExt_hH_iff]
  rfl

/-- **Both constant algorithms are UDT1.01 at `hH` in the homework model**, and UDT1.01 is not unique
there: the mandate's own instance (I) has a tie node. (The N+ companion — `f^0_{hT}` non-constant
in the same model — is by hand: `f^0_{hT,S̄}(true) = 3/8`, `(false) = −3/8` when `ξ₁ = true`; the
machine-checked N+ pair is in the tie model, `Tie.two_udt101_hT` with `Tie.score_root`.)
Source: audit r1 (adversarial) B1, route (ii); [[diffractor-synthesis]] ll. 67, 194 (udt-rep-083)
Kind: N+
Fidelity: exact
Hyps: none -/
theorem two_udt101_hH :
    ∃ A₁ A₂ : Alg Bool Bool Bool 2, Home.S.IsUDT101 A₁ hH ∧ Home.S.IsUDT101 A₂ hH ∧ A₁ ≠ A₂ :=
  homeModel.exists_two_isUDT101_of_inert inert_hH ublind_hH ω₁_pos ω₁_reach
    (show (true : Bool) ≠ false by decide)

/-- **The score at `hH` is identically zero in the homework model.**
Source: audit r1 (adversarial) B1, route (ii)
Kind: P
Fidelity: exact
Hyps: none -/
theorem score_hH (μ : FinDist Bool) (ω : PWorld Bool Bool Bool Unit 2) : Home.S.fS hH μ 0 ω = 0 :=
  homeModel.fS_eq_zero_of_inert inert_hH ublind_hH μ 1 0 rfl ω

end HomeTie

end Cleanroom.Udt.UdtInfluence101
