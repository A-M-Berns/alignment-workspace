import Cleanroom.Udt.UdtInfluence101.ProfileA5
import Cleanroom.Udt.UdtInfluence101.Tiling

/-!
# Two-step profile models: marginalization lemmas and inert nodes

Infrastructure for the horizon-`2` instances of the `udt-influence-101` package (repair round 1,
2026-10-02). A world of a profile model with `N = 2` is a root draw and two letters; sums over worlds
are iterated sums over the root draw and the two letters (`sum_pworld_two`), and the ε-law of a
world is the root weight times the two step factors (`lawW_two`).

Two marginalizations follow, both from "every row of the step kernel sums to one":

* **Letter 1 marginalized** (`sum_lawW_mul_fst`): the ε-mass of a function of the root draw and
  the first letter is the sum over those of the root weight times the root step factor. This is how
  the Omega instance's conditional expectations are computed as explicit rationals.
* **Inert node** (`sum_lawW_eq_baseW_of_inert`): if nobody reads node `h`'s profile and the
  step-`1` kernels ignore the current action, then ε-play at a depth-`1` node `h` leaves the ε-mass
  of every function blind to the action at `h` at its baseline value, for every `ε` and every
  algorithm. Hence every influence at `h` vanishes (`IP_eq_zero_of_inert`, …) and so does Post 8's
  score `f^n_{h,S̄_h}` (`fS_eq_zero_of_inert`): `h` is a tie node for UDT1.01.
-/

namespace Cleanroom.Udt.UdtInfluence101

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree

noncomputable section

/-! ### Two-letter leaves -/

/-- The root node of a depth-`2` tree.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def node0 (X : Type) : Node X 2 := ⟨0, ![]⟩

/-- The depth-`1` node of a depth-`2` tree after the letter `x`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def node1 {X : Type} (x : X) : Node X 2 := ⟨1, ![x]⟩

/-- Supporting lemma `sum_leaf_two` (a sum over two-letter leaves as an iterated sum).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_leaf_two {X : Type} [Fintype X] (f : Leaf X 2 → ℝ) :
    ∑ l, f l = ∑ x, ∑ y, f ![x, y] := by
  rw [← (finTwoArrowEquiv X).symm.sum_comp, Fintype.sum_prod_type]
  rfl

/-- Supporting lemma `prefixOf_two_zero`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prefixOf_two_zero {X : Type} (x y : X) : prefixOf ![x, y] 0 = node0 X := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  exact i.elim0

/-- Supporting lemma `prefixOf_two_one`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prefixOf_two_one {X : Type} (x y : X) : prefixOf ![x, y] 1 = node1 x := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  fin_cases i
  rfl

/-- Supporting lemma `pathLaw_two` (the path law of a two-letter leaf is the product of its two step
factors).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pathLaw_two {X : Type} (F : Node X 2 → X → ℝ) (x y : X) :
    pathLaw F ![x, y] = F (node0 X) x * F (node1 x) y := by
  unfold pathLaw
  rw [Fin.prod_univ_two, prefixOf_two_zero, prefixOf_two_one]
  rfl

/-- Supporting lemma `oNode_node0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem oNode_node0 {O Act Ξ : Type} : oNode (node0 (Letter O Act Ξ)) = node0 O := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  exact i.elim0

/-- Supporting lemma `oNode_node1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem oNode_node1 {O Act Ξ : Type} (x : Letter O Act Ξ) : oNode (node1 x) = node1 x.2.1 := by
  refine Sigma.ext rfl (heq_of_eq ?_)
  funext i
  fin_cases i
  rfl

/-- Supporting lemma `node0_ne_depth_one` (a depth-`1` node is not the root).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem node0_ne_of_depth_one {O : Type} {h : Node O 2} (hh : h.1.val = 1) : node0 O ≠ h := by
  intro heq
  have := congrArg (fun x : Node O 2 => x.1.val) heq
  simp [node0] at this
  omega

variable {O Act Ξ W : Type} [Fintype O] [DecidableEq O] [Fintype Act] [DecidableEq Act]
  [Fintype Ξ] [DecidableEq Ξ] [Fintype W] [DecidableEq W]

namespace ProfileModel

variable (M : ProfileModel O Act Ξ W 2)

/-- Supporting lemma `sum_pworld_two` (a sum over worlds of a two-step model as an iterated sum
over the root draw and the two letters).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_pworld_two (G : PWorld O Act Ξ W 2 → ℝ) :
    ∑ ω, G ω = ∑ r, ∑ x, ∑ y, G (r, ![x, y]) := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun r _ => sum_leaf_two (fun l => G (r, l))

/-- Supporting lemma `lawW_two` (the ε-law of a two-step world is the root weight times the two step
factors).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem lawW_two (A : Alg O Act Ξ 2) (h : Node O 2) (ε : ℝ) (r : W × Ξ) (x y : Letter O Act Ξ) :
    M.lawW A h ε (r, ![x, y]) =
      M.root.w r * (M.F A h ε r (node0 _) x * M.F A h ε r (node1 x) y) := by
  unfold lawW
  rw [pathLaw_two]

/-- Supporting lemma `baseW_two`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseW_two (r : W × Ξ) (x y : Letter O Act Ξ) :
    M.baseW (r, ![x, y]) = M.root.w r * (M.baseF r (node0 _) x * M.baseF r (node1 x) y) := by
  unfold baseW
  rw [pathLaw_two]

/-- **Letter 1 marginalized**: the ε-mass of a function of the root draw and the first letter is
the sum over those of the root weight times the root step factor (the second step's row sums to one).
Source: none: infrastructure (mandate T7: "the action factor telescopes")
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_lawW_mul_fst (A : Alg O Act Ξ 2) (h : Node O 2) (ε : ℝ)
    (G : W × Ξ → Letter O Act Ξ → ℝ) :
    ∑ ω, M.lawW A h ε ω * G ω.1 (ω.2 0) =
      ∑ r, ∑ x, M.root.w r * M.F A h ε r (node0 _) x * G r x := by
  rw [sum_pworld_two]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [lawW_two, Matrix.cons_val_zero]
  calc ∑ y, M.root.w r * (M.F A h ε r (node0 _) x * M.F A h ε r (node1 x) y) * G r x
      = (M.root.w r * M.F A h ε r (node0 _) x * G r x) * ∑ y, M.F A h ε r (node1 x) y := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun y _ => by ring
    _ = _ := by rw [M.F_rowSum, mul_one]

/-! ### Inert depth-one nodes -/

/-- **An inert depth-`1` node**: no node reads `h`'s profile, and the observation and state kernels
ignore the current action (at every step; only step `1` matters, but the instances satisfy it
everywhere). ε-play at such an `h` changes only the law of the action at `h`, which nothing else sees.
Source: mandate T5(ii) ("a T7 instance with an action-irrelevant node")
Kind: D
Fidelity: n/a
Hyps: n/a -/
structure Inert (h : Node O 2) : Prop where
  /-- `h` has depth one. -/
  depth : h.1.val = 1
  /-- No node reads `h`'s profile. -/
  no_read : ∀ m, M.pn m ≠ h
  /-- The observation kernel ignores the current action. -/
  eA_blind : ∀ w k obs acts a a' b, M.eA w k obs acts a b = M.eA w k obs acts a' b
  /-- The state kernel ignores the current action. -/
  κ_blind : ∀ w k obs s a a' o, M.κ w k obs s a o = M.κ w k obs s a' o

/-- The action-independent part of the step-`1` factor at an inert node, evaluated with the default
action `a₀` (observation factor with the baseline profile, times the state factor).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def restF (r : W × Ξ) (x : Letter O Act Ξ) (a₀ : Act) (o : O) (ξ : Ξ) : ℝ :=
  (∑ a'', (M.π₀ (M.pn (oNode (node1 x)))).w a'' *
      (M.eA r.1 (node1 x).1 (obsPre (node1 x)) (actPre (node1 x)) a₀ a'').w o) *
    (M.κ r.1 (node1 x).1 (obsPre (node1 x)) (statePre r.2 (node1 x)) a₀ o).w ξ

/-- Supporting lemma `F_node1_inert` (at an inert node the step-`1` ε-factor is the ε-mixed action
weight times an action-independent rest).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_node1_inert {h : Node O 2} (hi : M.Inert h) (A : Alg O Act Ξ 2) (ε : ℝ) (r : W × Ξ)
    (x : Letter O Act Ξ) (a a₀ : Act) (o : O) (ξ : Ξ) :
    M.F A h ε r (node1 x) (a, o, ξ) =
      M.algW A h ε (oNode (node1 x)) (statePre r.2 (node1 x)) a * M.restF r x a₀ o ξ := by
  simp only [F, restF, profW, if_neg (hi.no_read _), hi.κ_blind r.1 _ _ _ a a₀,
    hi.eA_blind r.1 _ _ _ a a₀]
  ring

/-- Supporting lemma `baseF_node1_inert`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseF_node1_inert {h : Node O 2} (hi : M.Inert h) (r : W × Ξ) (x : Letter O Act Ξ)
    (a a₀ : Act) (o : O) (ξ : Ξ) :
    M.baseF r (node1 x) (a, o, ξ) =
      (M.B (oNode (node1 x)) (statePre r.2 (node1 x))).w a * M.restF r x a₀ o ξ := by
  simp only [baseF, restF, hi.κ_blind r.1 _ _ _ a a₀, hi.eA_blind r.1 _ _ _ a a₀]
  ring

/-- Supporting lemma `sum_F_node1_inert` (the action at an inert node marginalizes out of the
ε-weighted sum of any action-blind function of the step-`1` letter).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_F_node1_inert [Nonempty Act] {h : Node O 2} (hi : M.Inert h) (A : Alg O Act Ξ 2) (ε : ℝ)
    (r : W × Ξ) (x : Letter O Act Ξ) (g : Letter O Act Ξ → ℝ)
    (hg : ∀ a a' o ξ, g (a, o, ξ) = g (a', o, ξ)) :
    ∑ y, M.F A h ε r (node1 x) y * g y = ∑ y, M.baseF r (node1 x) y * g y := by
  obtain ⟨a₀⟩ := (inferInstance : Nonempty Act)
  rw [sum_letter, sum_letter]
  have key : ∀ (K : Act → ℝ), (∑ a, K a) = 1 → ∀ (Fa : Act → O → Ξ → ℝ),
      (∀ a o ξ, Fa a o ξ = K a * (M.restF r x a₀ o ξ * g (a₀, o, ξ))) →
      ∑ a, ∑ o, ∑ ξ, Fa a o ξ = ∑ o, ∑ ξ, M.restF r x a₀ o ξ * g (a₀, o, ξ) := by
    intro K hK Fa hFa
    simp only [hFa, ← Finset.mul_sum]
    rw [← Finset.sum_mul, hK, one_mul]
  rw [key (fun a => M.algW A h ε (oNode (node1 x)) (statePre r.2 (node1 x)) a)
      (M.algW_sum A h ε _ _) _
      (fun a o ξ => by rw [M.F_node1_inert hi A ε r x a a₀ o ξ, hg a a₀ o ξ]; ring),
    key (fun a => (M.B (oNode (node1 x)) (statePre r.2 (node1 x))).w a) (M.B _ _).sum_one _
      (fun a o ξ => by rw [M.baseF_node1_inert hi r x a a₀ o ξ, hg a a₀ o ξ]; ring)]

/-- Supporting lemma `not_epsSens_node0_of_inert`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem not_epsSens_node0_of_inert {h : Node O 2} (hi : M.Inert h) :
    ¬ M.EpsSens h (node0 (Letter O Act Ξ)) := by
  rintro (h1 | h2)
  · rw [oNode_node0] at h1
    exact node0_ne_of_depth_one hi.depth h1
  · exact hi.no_read _ h2

/-- **ε-play at an inert node is invisible to action-blind functions**: for every algorithm and every
`ε`, the ε-weighted sum of a function blind to the action at `h` (on `h`'s branch) is its baseline
value.
Source: mandate T5(ii) (the mechanism of an action-irrelevant node)
Kind: P
Fidelity: exact
Hyps: none -/
theorem sum_lawW_eq_baseW_of_inert [Nonempty Act] {h : Node O 2} (hi : M.Inert h)
    (A : Alg O Act Ξ 2) (ε : ℝ) (g : PWorld O Act Ξ W 2 → ℝ)
    (hg : ∀ r x, oNode (node1 x) = h →
      ∀ a a' o ξ, g (r, ![x, (a, o, ξ)]) = g (r, ![x, (a', o, ξ)])) :
    ∑ ω, M.lawW A h ε ω * g ω = ∑ ω, M.baseW ω * g ω := by
  rw [sum_pworld_two, sum_pworld_two]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [lawW_two, baseW_two, M.F_eq_baseF_of_not_sens A ε r (M.not_epsSens_node0_of_inert hi)]
  by_cases hx : oNode (node1 x) = h
  · have key := M.sum_F_node1_inert hi A ε r x (fun y => g (r, ![x, y])) (hg r x hx)
    calc ∑ y, M.root.w r * (M.baseF r (node0 _) x * M.F A h ε r (node1 x) y) * g (r, ![x, y])
        = (M.root.w r * M.baseF r (node0 _) x) *
            ∑ y, M.F A h ε r (node1 x) y * g (r, ![x, y]) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
      _ = (M.root.w r * M.baseF r (node0 _) x) *
            ∑ y, M.baseF r (node1 x) y * g (r, ![x, y]) := by rw [key]
      _ = _ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun y _ => by ring
  · have hns : ¬ M.EpsSens h (node1 x) := by
      rintro (h1 | h2)
      · exact hx h1
      · exact hi.no_read _ h2
    simp only [M.F_eq_baseF_of_not_sens A ε r hns]

/-! ### Every influence at an inert node vanishes; the node is a tie node -/

/-- Supporting lemma `toPlaySpace_obs`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem toPlaySpace_obs : M.toPlaySpace.obs = pObs := rfl

/-- Supporting lemma `toPlaySpace_states`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem toPlaySpace_states : M.toPlaySpace.states = pStates := rfl

/-- Supporting lemma `pObs_act` (the observations of a two-step world do not depend on the step-`1`
action).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pObs_act (r : W × Ξ) (x : Letter O Act Ξ) (a a' : Act) (o : O) (ξ : Ξ) :
    pObs (W := W) (r, ![x, (a, o, ξ)]) = pObs (r, ![x, (a', o, ξ)]) := by
  funext k
  fin_cases k <;> rfl

/-- Supporting lemma `pStates_act`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pStates_act (r : W × Ξ) (x : Letter O Act Ξ) (a a' : Act) (o : O) (ξ : Ξ) :
    pStates (W := W) (r, ![x, (a, o, ξ)]) = pStates (r, ![x, (a', o, ξ)]) := by
  funext k
  fin_cases k <;> rfl

/-- A set of worlds is **action-blind** when membership does not depend on the step-`1` action.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ActBlindSet (E : Finset (PWorld O Act Ξ W 2)) : Prop :=
  ∀ (r : W × Ξ) (x : Letter O Act Ξ) (a a' : Act) (o : O) (ξ : Ξ),
    (r, ![x, (a, o, ξ)]) ∈ E ↔ (r, ![x, (a', o, ξ)]) ∈ E

/-- The utility is blind to the action at `h` **on `h`'s branch**.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def UBlind (h : Node O 2) : Prop :=
  ∀ (r : W × Ξ) (x : Letter O Act Ξ), oNode (node1 x) = h →
    ∀ (a a' : Act) (o : O) (ξ : Ξ), M.U (r, ![x, (a, o, ξ)]) = M.U (r, ![x, (a', o, ξ)])

/-- Supporting lemma `actBlind_atom`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem actBlind_atom (n : ℕ) (ω : PWorld O Act Ξ W 2) : ActBlindSet (M.toPlaySpace.atom n ω) := by
  intro r x a a' o ξ
  simp only [PlaySpace.mem_atom, PlaySpace.AtomEq, toPlaySpace_obs, toPlaySpace_states,
    pObs_act r x a a' o ξ, pStates_act r x a a' o ξ]

/-- Supporting lemma `actBlind_nextObs`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem actBlind_nextObs (n : ℕ) (o : O) : ActBlindSet (M.toPlaySpace.nextObs n o) := by
  intro r x a a' o' ξ
  by_cases hn : n < 2
  · simp only [M.toPlaySpace.mem_nextObs hn, toPlaySpace_obs, pObs_act r x a a' o' ξ]
  · simp [PlaySpace.nextObs, hn]

/-- Supporting lemma `actBlind_reach`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem actBlind_reach (h : Node O 2) : ActBlindSet (M.toPlaySpace.reach h) := by
  intro r x a a' o ξ
  simp only [PlaySpace.mem_reach, toPlaySpace_obs, pObs_act r x a a' o ξ]

/-- Supporting lemma `actBlind_univ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem actBlind_univ : ActBlindSet (univ : Finset (PWorld O Act Ξ W 2)) := fun _ _ _ _ _ _ => by simp

/-- Supporting lemma `actBlind_inter`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem actBlind_inter {E E' : Finset (PWorld O Act Ξ W 2)} (h1 : ActBlindSet E)
    (h2 : ActBlindSet E') : ActBlindSet (E ∩ E') := fun r x a a' o ξ => by
  simp only [Finset.mem_inter, h1 r x a a' o ξ, h2 r x a a' o ξ]

/-- Supporting lemma `mass_eq_sum_ite`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_eq_sum_ite (w : PWorld O Act Ξ W 2 → ℝ) (E : Finset (PWorld O Act Ξ W 2)) :
    mass w E = ∑ ω, w ω * (if ω ∈ E then 1 else 0) := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  rfl

/-- Supporting lemma `sum_mul_eq_sum_ite`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_mul_eq_sum_ite (w f : PWorld O Act Ξ W 2 → ℝ) (E : Finset (PWorld O Act Ξ W 2)) :
    ∑ ω ∈ E, w ω * f ω = ∑ ω, w ω * (if ω ∈ E then f ω else 0) := by
  simp only [mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- **The ε-mass of an action-blind event at an inert node is its baseline mass**, for every `ε`.
Source: mandate T5(ii)
Kind: L
Fidelity: exact
Hyps: none -/
theorem mass_lawW_eq_of_inert [Nonempty Act] {h : Node O 2} (hi : M.Inert h) (A : Alg O Act Ξ 2)
    (ε : ℝ) {E : Finset (PWorld O Act Ξ W 2)} (hE : ActBlindSet E) :
    mass (M.lawW A h ε) E = mass M.baseW E := by
  rw [mass_eq_sum_ite (M.lawW A h ε), mass_eq_sum_ite M.baseW]
  exact M.sum_lawW_eq_baseW_of_inert hi A ε _ fun r x _ a a' o ξ => by
    simp only [hE r x a a' o ξ]

/-- Supporting lemma `sum_lawW_mul_eq_of_inert`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_lawW_mul_eq_of_inert [Nonempty Act] {h : Node O 2} (hi : M.Inert h)
    (A : Alg O Act Ξ 2) (ε : ℝ) {E : Finset (PWorld O Act Ξ W 2)} (hE : ActBlindSet E)
    (f : PWorld O Act Ξ W 2 → ℝ)
    (hf : ∀ r x, oNode (node1 x) = h →
      ∀ a a' o ξ, f (r, ![x, (a, o, ξ)]) = f (r, ![x, (a', o, ξ)])) :
    ∑ ω ∈ E, M.lawW A h ε ω * f ω = ∑ ω ∈ E, M.baseW ω * f ω := by
  rw [sum_mul_eq_sum_ite (M.lawW A h ε), sum_mul_eq_sum_ite M.baseW]
  exact M.sum_lawW_eq_baseW_of_inert hi A ε _ fun r x hx a a' o ξ => by
    simp only [hE r x a a' o ξ, hf r x hx a a' o ξ]

/-- Supporting lemma `cexp_lawW_eq_of_inert`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_lawW_eq_of_inert [Nonempty Act] {h : Node O 2} (hi : M.Inert h) (A : Alg O Act Ξ 2)
    (ε : ℝ) (n : ℕ) {E : Finset (PWorld O Act Ξ W 2)} (hE : ActBlindSet E)
    (f : PWorld O Act Ξ W 2 → ℝ)
    (hf : ∀ r x, oNode (node1 x) = h →
      ∀ a a' o ξ, f (r, ![x, (a, o, ξ)]) = f (r, ![x, (a', o, ξ)]))
    (ω : PWorld O Act Ξ W 2) :
    M.toPlaySpace.cexp (M.lawW A h ε) n E f ω = M.toPlaySpace.cexp M.baseW n E f ω := by
  unfold PlaySpace.cexp condExpJunk
  rw [M.mass_lawW_eq_of_inert hi A ε (actBlind_inter (M.actBlind_atom n ω) hE),
    M.sum_lawW_mul_eq_of_inert hi A ε (actBlind_inter (M.actBlind_atom n ω) hE) f hf]

/-- Supporting lemma `pr_lawW_eq_of_inert`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pr_lawW_eq_of_inert [Nonempty Act] {h : Node O 2} (hi : M.Inert h) (A : Alg O Act Ξ 2)
    (ε : ℝ) (n : ℕ) {F : Finset (PWorld O Act Ξ W 2)} (hF : ActBlindSet F)
    (ω : PWorld O Act Ξ W 2) :
    M.toPlaySpace.pr (M.lawW A h ε) n F ω = M.toPlaySpace.pr M.baseW n F ω := by
  unfold PlaySpace.pr condProbJunk
  rw [M.mass_lawW_eq_of_inert hi A ε (M.actBlind_atom n ω),
    M.mass_lawW_eq_of_inert hi A ε (actBlind_inter hF (M.actBlind_atom n ω))]

/-- **Every influence on probability at an inert node is zero.**
Source: mandate T5(ii)
Kind: P
Fidelity: exact
Hyps: none -/
theorem IP_eq_zero_of_inert [Nonempty Act] {h : Node O 2} (hi : M.Inert h) (n : ℕ)
    (A : Alg O Act Ξ 2) (o : O) (ω : PWorld O Act Ξ W 2) : M.toPlaySpace.IP n A h o ω = 0 := by
  unfold PlaySpace.IP
  have : (fun ε => M.toPlaySpace.pr (M.toPlaySpace.law A h ε) n (M.toPlaySpace.nextObs n o) ω) =
      fun _ => M.toPlaySpace.pr M.toPlaySpace.ℙ.w n (M.toPlaySpace.nextObs n o) ω :=
    funext fun ε => M.pr_lawW_eq_of_inert hi A ε n (M.actBlind_nextObs n o) ω
  rw [this, deriv_const]

/-- **Every influence on conditional expected utility at an inert node is zero** (utility blind to
the action at `h` on its branch).
Source: mandate T5(ii)
Kind: P
Fidelity: exact
Hyps: none -/
theorem IEo_eq_zero_of_inert [Nonempty Act] {h : Node O 2} (hi : M.Inert h) (hU : M.UBlind h)
    (n : ℕ) (A : Alg O Act Ξ 2) (o : O) (ω : PWorld O Act Ξ W 2) :
    M.toPlaySpace.IEo n A h o ω = 0 := by
  unfold PlaySpace.IEo
  have : (fun ε => M.toPlaySpace.cexp (M.toPlaySpace.law A h ε) n (M.toPlaySpace.nextObs n o)
      M.toPlaySpace.U ω) =
      fun _ => M.toPlaySpace.cexp M.toPlaySpace.ℙ.w n (M.toPlaySpace.nextObs n o) M.toPlaySpace.U ω :=
    funext fun ε => M.cexp_lawW_eq_of_inert hi A ε n (M.actBlind_nextObs n o) M.U hU ω
  rw [this, deriv_const]

/-- **Every influence on expected utility at an inert node is zero.**
Source: mandate T5(ii)
Kind: P
Fidelity: exact
Hyps: none -/
theorem IE_eq_zero_of_inert [Nonempty Act] {h : Node O 2} (hi : M.Inert h) (hU : M.UBlind h)
    (n : ℕ) (A : Alg O Act Ξ 2) (ω : PWorld O Act Ξ W 2) : M.toPlaySpace.IE n A h ω = 0 := by
  unfold PlaySpace.IE
  have : (fun ε => M.toPlaySpace.cexp (M.toPlaySpace.law A h ε) n univ M.toPlaySpace.U ω) =
      fun _ => M.toPlaySpace.cexp M.toPlaySpace.ℙ.w n univ M.toPlaySpace.U ω :=
    funext fun ε => M.cexp_lawW_eq_of_inert hi A ε n actBlind_univ M.U hU ω
  rw [this, deriv_const]

/-- Supporting lemma `fBase_eq_zero_of_inert`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem fBase_eq_zero_of_inert [Nonempty Act] {h : Node O 2} (hi : M.Inert h) (hU : M.UBlind h)
    (μ : FinDist Act) (n : ℕ) (ω : PWorld O Act Ξ W 2) : M.toPlaySpace.fBase h μ n ω = 0 := by
  unfold PlaySpace.fBase
  simp only [M.IEo_eq_zero_of_inert hi hU, M.IP_eq_zero_of_inert hi, mul_zero, zero_mul, add_zero,
    Finset.sum_const_zero]

/-- Supporting lemma `fMid_eq_zero_of_inert`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem fMid_eq_zero_of_inert [Nonempty Act] {h : Node O 2} (hi : M.Inert h) (hU : M.UBlind h)
    (μ : FinDist Act) (n : ℕ) (hn : n < h.1.val) (ω : PWorld O Act Ξ W 2) :
    M.toPlaySpace.fMid h μ n hn ω = 0 := by
  unfold PlaySpace.fMid
  have : (fun ω' => M.toPlaySpace.IE (n + 1) (ofDist μ) h ω') = fun _ => (0 : ℝ) :=
    funext fun ω' => M.IE_eq_zero_of_inert hi hU (n + 1) _ ω'
  rw [this]
  simp [PlaySpace.cexp, condExpJunk]

/-- **Post 8's score vanishes identically at an inert node**: `f^n_{h,S̄_h}(μ) = 0` for every mixed
action, time `n ≤ |h|` and world.
Source: mandate T5(ii)
Kind: P
Fidelity: exact
Hyps: none -/
theorem fS_eq_zero_of_inert [Nonempty Act] {h : Node O 2} (hi : M.Inert h) (hU : M.UBlind h)
    (μ : FinDist Act) : ∀ (k n : ℕ), n + k = h.1.val → ∀ ω, M.toPlaySpace.fS h μ n ω = 0 := by
  intro k
  induction k with
  | zero =>
    intro n hn ω
    rw [M.toPlaySpace.fS_of_ge h μ (by omega)]
    exact M.fBase_eq_zero_of_inert hi hU μ n ω
  | succ k ih =>
    intro n hn ω
    rw [M.toPlaySpace.fS_of_lt h μ (by omega), M.fBase_eq_zero_of_inert hi hU,
      M.fMid_eq_zero_of_inert hi hU, ih (n + 1) (by omega) ω]
    ring

/-- **Every constant algorithm is UDT1.01 at an inert node** (the score is identically zero, so every
action is a maximizer).
Source: mandate T5(ii)
Kind: P
Fidelity: exact
Hyps: none -/
theorem isUDT101_ofAct_of_inert [Nonempty Act] {h : Node O 2} (hi : M.Inert h) (hU : M.UBlind h)
    (a : Act) : M.toPlaySpace.IsUDT101 (ofAct a) h := by
  intro ω _ _
  refine ⟨a, rfl, fun a' => ?_⟩
  show M.toPlaySpace.fS h (FinDist.delta a') 0 ω ≤ M.toPlaySpace.fS h (FinDist.delta a) 0 ω
  rw [M.fS_eq_zero_of_inert hi hU _ h.1.val 0 (by omega) ω,
    M.fS_eq_zero_of_inert hi hU _ h.1.val 0 (by omega) ω]

/-- **`exists_two_isUDT101` instantiated at an inert node**: given a positive world reaching `h` and
two distinct actions, there are two distinct UDT1.01 algorithms at `h`.
Source: [[diffractor-synthesis]] ll. 67, 194 (udt-rep-083); mandate T5(ii)
Kind: N+
Fidelity: exact (the hypothesis package of `exists_two_isUDT101` is inhabited)
Hyps: none -/
theorem exists_two_isUDT101_of_inert [Nonempty Act] {h : Node O 2} (hi : M.Inert h)
    (hU : M.UBlind h) {ω₀ : PWorld O Act Ξ W 2} (hω₀ : 0 < M.baseW ω₀) (hr : ω₀ ∈ pReach h)
    {a₁ a₂ : Act} (hne : a₁ ≠ a₂) :
    ∃ A₁ A₂ : Alg O Act Ξ 2, M.toPlaySpace.IsUDT101 A₁ h ∧ M.toPlaySpace.IsUDT101 A₂ h ∧ A₁ ≠ A₂ :=
  M.toPlaySpace.exists_two_isUDT101 h hω₀ hr hne
    (fun a' => by
      show M.toPlaySpace.fS h (FinDist.delta a') 0 ω₀ ≤ M.toPlaySpace.fS h (FinDist.delta a₁) 0 ω₀
      rw [M.fS_eq_zero_of_inert hi hU _ h.1.val 0 (by omega) ω₀,
        M.fS_eq_zero_of_inert hi hU _ h.1.val 0 (by omega) ω₀])
    (fun a' => by
      show M.toPlaySpace.fS h (FinDist.delta a') 0 ω₀ ≤ M.toPlaySpace.fS h (FinDist.delta a₂) 0 ω₀
      rw [M.fS_eq_zero_of_inert hi hU _ h.1.val 0 (by omega) ω₀,
        M.fS_eq_zero_of_inert hi hU _ h.1.val 0 (by omega) ω₀])

end ProfileModel

end

end Cleanroom.Udt.UdtInfluence101
