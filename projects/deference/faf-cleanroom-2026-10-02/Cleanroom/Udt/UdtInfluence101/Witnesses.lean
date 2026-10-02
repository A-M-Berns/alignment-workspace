import Cleanroom.Udt.UdtInfluence101.ProfileA5
import Cleanroom.Udt.UdtInfluence101.Tiling

/-!
# `Cleanroom.Udt.UdtInfluence101.Witnesses`: the homework instance

Target T7 of [[udt-influence-101-mandate]], instance (I) — **Counterfactual Mugging With Homework**
(Post 6 §1.2), in the model of record with `N = 2`, all alphabets `Bool`, no separate latent world
(`W = Unit`; the answer is the unplannable state `ξ₁`):

* time 0: the coin is tossed (observation `o₀`; `true` = "tails", the homework branch `h`), and the
  answer `ξ₁` is revealed to the agent as its unplannable state;
* time 1 on the tails branch (`h`): the agent answers (`a₁`), utility `1` iff `a₁ = ξ₁`;
* time 1 on the heads branch: the environment reads the agent's **profile at `h`** and hands out ice
  cream (`o₁ = true`, utility `1`) with probability `3/4` if the predicted answer is `true` and `1/4`
  otherwise — the diffuse prediction of Post 6 §1.2.

The algorithm of interest `homeA` answers `ξ₁` at `h`; the baseline `B` and the predictor's baseline
belief `π₀` are uniform. The escape clause bites: `homeA` is not its own average at time 0
(`homeA_ne_avg`). Every hypothesis of `theorem1` is discharged by the general theorems of the model
plus the structural regularity facts proved here, so Theorem 1 and Theorem 2 instantiate (`theorem1_home`,
`theorem2_home`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtInfluence101

noncomputable section

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree

namespace Home

open ProfileModel

/-- A biased coin on `Bool` with `P(true) = p`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def coin (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : FinDist Bool := FinDist.bern p h0 h1 true false

/-- Supporting lemma `coin_w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem coin_w (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) (b : Bool) :
    (coin p h0 h1).w b = if b then p else 1 - p := by
  cases b <;> simp [coin, FinDist.bern_w]

/-- The fair coin.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def fair : FinDist Bool := coin (1 / 2) (by norm_num) (by norm_num)

/-- Supporting lemma `fair_w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem fair_w (b : Bool) : fair.w b = 1 / 2 := by cases b <;> norm_num [fair]

/-- The tails node `h` (depth 1, first observation `true`): the homework branch.
Source: `references/udt101/06-basics-of-algorithm.md` §1.2
Kind: D
Fidelity: n/a
Hyps: n/a -/
def hT : Node Bool 2 := ⟨1, ![true]⟩

/-- The heads node (depth 1, first observation `false`): the ice-cream branch, which reads the profile at `h`.
Source: `references/udt101/06-basics-of-algorithm.md` §1.2
Kind: D
Fidelity: n/a
Hyps: n/a -/
def hH : Node Bool 2 := ⟨1, ![false]⟩

/-- The root node.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def root : Node Bool 2 := ⟨0, ![]⟩

/-- Supporting lemma `node1_eq_iff` (depth-one nodes are determined by their one observation).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem node1_eq_iff (x y : Bool) : ((⟨1, ![x]⟩ : Node Bool 2) = ⟨1, ![y]⟩) ↔ x = y := by
  constructor
  · intro h
    have := congrArg (fun m : Node Bool 2 => if hm : m.1.val = 1 then m.2 ⟨0, by omega⟩ else true) h
    simpa using this
  · rintro rfl; rfl

/-- Supporting lemma `hT_ne_hH`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hT_ne_hH : hT ≠ hH := fun h => by simp [hT, hH, node1_eq_iff] at h

/-- Supporting lemma `root_ne_hT`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem root_ne_hT : root ≠ hT := fun h => by
  have := congrArg (fun m : Node Bool 2 => m.1.val) h
  simp [root, hT] at this

/-- Supporting lemma `root_ne_hH`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem root_ne_hH : root ≠ hH := fun h => by
  have := congrArg (fun m : Node Bool 2 => m.1.val) h
  simp [root, hH] at this

/-- **The homework model** (instance (I) of record): see the module docstring.
Source: `references/udt101/06-basics-of-algorithm.md` §1.2 (Counterfactual Mugging With Homework); mandate T7 (I)
Kind: D
Fidelity: variant: the "mom" predictor reads the agent's profile at the homework node and rewards
the predicted answer `true` with probability `3/4`, `false` with `1/4` (a diffuse prediction); the
answer is the unplannable state `ξ₁`, uniform
Hyps: n/a -/
def homeModel : ProfileModel Bool Bool Bool Unit 2 where
  root := FinDist.delta ((), false)
  κ := fun _ _ _ _ _ _ => fair
  eA := fun _ k obs _ _ a' =>
    if hk : k.val = 0 then fair
    else if obs ⟨0, by omega⟩ then fair
    else coin (if a' then 3 / 4 else 1 / 4) (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
  pn := fun m => if m = hH then hT else root
  B := fun _ _ => fair
  π₀ := fun _ => fair
  U := fun ω => if (ω.2 0).2.1 then (if (ω.2 1).1 = (ω.2 0).2.2 then 1 else 0)
    else (if (ω.2 1).2.1 then 1 else 0)

/-- **The algorithm that answers the revealed answer**: at `h` it plays the point mass on `ξ₁`
(the state received at time 1), elsewhere the fair coin.
Source: `references/udt101/06-basics-of-algorithm.md` §1.2 ("do fast mental math here")
Kind: D
Fidelity: exact
Hyps: n/a -/
def homeA : Alg Bool Bool Bool 2 := fun m s =>
  if hm : m = hT then FinDist.delta (s ⟨1, by rw [hm]; simp [hT]⟩) else fair

/-- The play space of the homework model.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev S : PlaySpace Bool Bool Bool 2 (PWorld Bool Bool Bool Unit 2) := homeModel.toPlaySpace

/-! ### Positivity structure: a world is positive iff its root state is `false` -/

/-- Supporting lemma `eA_w_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem eA_w_pos (w : Unit) (k : Fin 2) (obs : Fin k.val → Bool) (acts : Fin k.val → Bool) (a a' o : Bool) :
    0 < (homeModel.eA w k obs acts a a').w o := by
  simp only [homeModel]
  split_ifs <;> cases o <;> simp <;> norm_num

/-- Supporting lemma `baseF_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseF_pos (r : Unit × Bool) (m : Node (Letter Bool Bool Bool) 2) (ℓ : Letter Bool Bool Bool) :
    0 < homeModel.baseF r m ℓ := by
  unfold ProfileModel.baseF
  have h1 : (0 : ℝ) < (homeModel.B (oNode m) (statePre r.2 m)).w ℓ.1 := by
    simp [homeModel]
  have h3 : (0 : ℝ) < (homeModel.κ r.1 m.1 (obsPre m) (statePre r.2 m) ℓ.1 ℓ.2.1).w ℓ.2.2 := by
    simp [homeModel]
  have h2 : (0 : ℝ) < ∑ a', (homeModel.π₀ (homeModel.pn (oNode m))).w a' *
      (homeModel.eA r.1 m.1 (obsPre m) (actPre m) ℓ.1 a').w ℓ.2.1 := by
    refine Finset.sum_pos (fun a' _ => mul_pos ?_ (eA_w_pos _ _ _ _ _ _ _)) Finset.univ_nonempty
    simp [homeModel]
  positivity

/-- **Positive worlds**: a world has positive baseline weight iff its root state is `false`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseW_pos_iff (ω : PWorld Bool Bool Bool Unit 2) : 0 < homeModel.baseW ω ↔ ω.1.2 = false := by
  unfold ProfileModel.baseW
  have hroot : homeModel.root.w ω.1 = if ω.1.2 = false then 1 else 0 := by
    simp only [homeModel, FinDist.delta_w]
    obtain ⟨⟨⟩, ξ⟩ := ω.1
    cases ξ <;> simp
  rw [hroot]
  have hpath : 0 < pathLaw (homeModel.baseF ω.1) ω.2 := Finset.prod_pos fun k _ => baseF_pos _ _ _
  constructor
  · intro h
    by_contra hne
    rw [if_neg hne, zero_mul] at h
    exact lt_irrefl _ h
  · intro h
    rw [if_pos h, one_mul]
    exact hpath

/-! ### Editing one observation of a world -/

/-- The world `ω` with the observation at step `k` replaced by `o` (action and next state kept).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def setObs (ω : PWorld Bool Bool Bool Unit 2) (k : Fin 2) (o : Bool) : PWorld Bool Bool Bool Unit 2 :=
  (ω.1, Function.update ω.2 k ((ω.2 k).1, o, (ω.2 k).2.2))

/-- Supporting lemma `setObs_fst`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem setObs_fst (ω : PWorld Bool Bool Bool Unit 2) (k : Fin 2) (o : Bool) :
    (setObs ω k o).1 = ω.1 := rfl

/-- Supporting lemma `setObs_obs_self`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem setObs_obs_self (ω : PWorld Bool Bool Bool Unit 2) (k : Fin 2) (o : Bool) :
    pObs (setObs ω k o) k = o := by
  simp [pObs, setObs]

/-- Supporting lemma `setObs_obs_ne`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem setObs_obs_ne (ω : PWorld Bool Bool Bool Unit 2) {k j : Fin 2} (hjk : j ≠ k) (o : Bool) :
    pObs (setObs ω k o) j = pObs ω j := by
  simp [pObs, setObs, Function.update_of_ne hjk]

/-- Supporting lemma `setObs_states`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem setObs_states (ω : PWorld Bool Bool Bool Unit 2) (k : Fin 2) (o : Bool) :
    pStates (setObs ω k o) = pStates ω := by
  funext i
  unfold pStates
  refine Fin.cases rfl (fun j => ?_) i
  simp only [Fin.cases_succ, setObs]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [Function.update_of_ne hjk]

/-- Supporting lemma `atomEq_setObs` (editing the observation at step `k ≥ n` keeps the time-`n` atom).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atomEq_setObs (ω : PWorld Bool Bool Bool Unit 2) {n : ℕ} {k : Fin 2} (hnk : n ≤ k.val) (o : Bool) :
    S.AtomEq n ω (setObs ω k o) := by
  refine ⟨fun i hi => ?_, fun i _ => ?_⟩
  · show pObs ω i = pObs (setObs ω k o) i
    rw [setObs_obs_ne ω (fun h => by subst h; omega) o]
  · show pStates ω i = pStates (setObs ω k o) i
    rw [setObs_states]

/-- Supporting lemma `baseW_setObs_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseW_setObs_pos {ω : PWorld Bool Bool Bool Unit 2} (hω : 0 < homeModel.baseW ω) (k : Fin 2)
    (o : Bool) : 0 < homeModel.baseW (setObs ω k o) := by
  rw [baseW_pos_iff] at hω ⊢
  simpa using hω

/-! ### Reaching the two depth-one nodes -/

/-- Supporting lemma `leafExt_hT_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem leafExt_hT_iff (l : Leaf Bool 2) : LeafExt hT l ↔ l 0 = true := by
  change prefixOf' l 1 (by omega) = ![true] ↔ l 0 = true
  constructor
  · intro h
    have := congrFun h 0
    simpa [prefixOf'] using this
  · intro h
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simpa [prefixOf'] using h

/-- Supporting lemma `leafExt_hH_iff`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem leafExt_hH_iff (l : Leaf Bool 2) : LeafExt hH l ↔ l 0 = false := by
  change prefixOf' l 1 (by omega) = ![false] ↔ l 0 = false
  constructor
  · intro h
    have := congrFun h 0
    simpa [prefixOf'] using this
  · intro h
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simpa [prefixOf'] using h

/-- Supporting lemma `mem_pReach_hT`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_pReach_hT (ω : PWorld Bool Bool Bool Unit 2) : ω ∈ pReach hT ↔ pObs ω 0 = true := by
  unfold pReach
  rw [mem_event, leafExt_hT_iff]

/-- A positive world reaching `h`: root state `false`, every letter `(true, true, true)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ω₀ : PWorld Bool Bool Bool Unit 2 := (((), false), fun _ => (true, true, true))

/-- Supporting lemma `ω₀_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ω₀_pos : 0 < homeModel.baseW ω₀ := (baseW_pos_iff ω₀).2 rfl

/-- Supporting lemma `ω₀_reach`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ω₀_reach : ω₀ ∈ pReach hT := (mem_pReach_hT ω₀).2 rfl

/-- **`reach h` is positive.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hreach : 0 < mass homeModel.baseW (pReach hT) :=
  mass_pos_of_mem homeModel.baseW_nonneg ω₀_reach ω₀_pos

/-! ### Regularity: full support of the next observation, reachability, positive atoms -/

/-- Supporting lemma `baseW_eq_of_atomEq` (worlds of one atom have the same root state, hence the
same positivity).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pos_of_atomEq {n : ℕ} {ω ω' : PWorld Bool Bool Bool Unit 2} (hω : 0 < homeModel.baseW ω)
    (h : S.AtomEq n ω ω') : 0 < homeModel.baseW ω' := by
  rw [baseW_pos_iff] at hω ⊢
  have := h.2 0 (Nat.zero_le n)
  simpa [PlaySpace.states, ProfileModel.toPlaySpace, pStates] using this.symm.trans hω

/-- **Every next observation is possible at every positive atom** (`AllPosObs`).
Source: mandate T7 (regularity of the instance)
Kind: L
Fidelity: exact
Hyps: none -/
theorem hall : S.AllPosObs := by
  intro n hn ω hω o
  refine mass_pos_of_mem S.ℙ.nonneg (Finset.mem_inter.2 ⟨?_, ?_⟩) (baseW_setObs_pos hω ⟨n, hn⟩ o)
  · exact S.mem_atom.2 (atomEq_setObs ω (k := ⟨n, hn⟩) le_rfl o)
  · rw [S.mem_nextObs hn]
    exact setObs_obs_self ω ⟨n, hn⟩ o

/-- **Every positive atom along `h` can still reach `h`** (`ReachPos hT`).
Source: mandate T7 (regularity of the instance)
Kind: L
Fidelity: exact
Hyps: none -/
theorem hRP : S.ReachPos hT := by
  intro n hn ω hω hal
  refine mass_pos_of_mem S.ℙ.nonneg (Finset.mem_inter.2 ⟨?_, ?_⟩) (baseW_setObs_pos hω 0 true)
  · rw [S.mem_atom]
    refine ⟨fun i hi => ?_, fun i _ => ?_⟩
    · have hi0 : i = 0 := Fin.ext (by have := i.isLt; have : n ≤ 1 := hn; omega)
      subst hi0
      show pObs ω 0 = pObs (setObs ω 0 true) 0
      rw [setObs_obs_self]
      have h0 : pObs ω 0 = true := by
        have := hal 0 hi
        simp [hT] at this
        exact this
      exact h0
    · show pStates ω i = pStates (setObs ω 0 true) i
      rw [setObs_states]
  · show setObs ω 0 true ∈ pReach hT
    rw [mem_pReach_hT, setObs_obs_self]

/-- **Positive time-`(n+1)` atoms below `h_{n+1}`** (the hypothesis of the model's `A4`).
Source: mandate T7 (regularity of the instance)
Kind: L
Fidelity: exact
Hyps: none -/
theorem hatoms : ∀ (n : ℕ) (hn : n < hT.1.val) (ω : PWorld Bool Bool Bool Unit 2),
    0 < homeModel.baseW ω → ω ∈ pReach hT →
    ∀ ω' ∈ S.atom n ω ∩ S.nextObs n (hT.2 ⟨n, hn⟩), 0 < mass homeModel.baseW (S.atom (n + 1) ω') := by
  intro n hn ω hω _ ω' hω'
  have hpos : 0 < homeModel.baseW ω' := pos_of_atomEq hω (S.mem_atom.1 (Finset.mem_inter.1 hω').1)
  exact mass_pos_of_mem homeModel.baseW_nonneg (S.self_mem_atom (n + 1) ω') hpos

/-! ### One ε-sensitive step per world; profile coherence -/

/-- Supporting lemma `oNode_depth`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem oNode_fst_val (ω : PWorld Bool Bool Bool Unit 2) (j : Fin 2) :
    (oNode (prefixOf ω.2 j)).1.val = j.val := rfl

/-- Supporting lemma `not_sens_zero` (the root step is never ε-sensitive for `h`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem not_sens_zero (ω : PWorld Bool Bool Bool Unit 2) : ¬ homeModel.EpsSens hT (prefixOf ω.2 0) := by
  intro h
  have hne : oNode (prefixOf ω.2 0) ≠ hT := fun e => by
    have := congrArg (fun m : Node Bool 2 => m.1.val) e
    simp [oNode_fst_val, hT] at this
  have hneH : oNode (prefixOf ω.2 0) ≠ hH := fun e => by
    have := congrArg (fun m : Node Bool 2 => m.1.val) e
    simp [oNode_fst_val, hH] at this
  rcases h with h | h
  · exact hne h
  · simp only [homeModel, hneH, if_false] at h
    exact root_ne_hT h

/-- **One ε-sensitive step per world** in the homework model.
Source: mandate T7 (regularity of the instance)
Kind: L
Fidelity: exact
Hyps: none -/
theorem hone : homeModel.OneEps hT := by
  refine ⟨fun ω j j' hj hj' => ?_, ?_⟩
  · have h0 : ∀ i : Fin 2, homeModel.EpsSens hT (prefixOf ω.2 i) → i = 1 := by
      intro i hi
      fin_cases i
      · exact absurd hi (not_sens_zero ω)
      · rfl
    rw [h0 j hj, h0 j' hj']
  · show (if hT = hH then hT else root) ≠ hT
    rw [if_neg hT_ne_hH]
    exact root_ne_hT

/-- Supporting lemma `condExpJunk_const_on_pos` (a conditional expectation of a function constant
on the positive-mass worlds of a positive event is that constant).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem _root_.Cleanroom.Udt.UdtPolicyCalc.condExpJunk_const_on_pos {X : Type} {w f : X → ℝ}
    (hw : ∀ x, 0 ≤ w x) {E : Finset X} {c : ℝ} (hpos : 0 < mass w E)
    (hc : ∀ x ∈ E, 0 < w x → f x = c) : condExpJunk w f E 0 = c := by
  rw [condExpJunk_of_pos hpos]
  have : ∑ x ∈ E, w x * f x = c * mass w E := by
    rw [mass, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    rcases (hw x).lt_or_eq with h0 | h0
    · rw [hc x hx h0, mul_comm]
    · rw [← h0, zero_mul, mul_zero]
  rw [this, mul_div_assoc, div_self hpos.ne', mul_one]

/-- **Profile coherence** in the homework model: the only profile reads of `h` happen at the heads
node, which no world of a time-`1` atom along `h` visits; at time `0` the atom is every positive
world, so a time-`0` precommitment's profile is its action.
Source: mandate T7 (regularity of the instance); finding F4
Kind: L
Fidelity: exact
Hyps: none -/
theorem hcoh : homeModel.ProfCoherent hT := by
  intro n hn A ω hω hal hconst ω' hω' j hpn
  -- the read happens at the heads node, so `ω'` is on the heads branch
  have hmH : oNode (prefixOf ω'.2 j) = hH := by
    by_contra hne
    simp only [homeModel, hne, if_false] at hpn
    exact root_ne_hT hpn
  have hH' : ω' ∈ pReach hH := reach_of_oNode_prefixOf_eq hmH
  rw [pReach, mem_event, leafExt_hH_iff] at hH'
  rcases Nat.lt_or_ge n 1 with hn0 | hn1
  · -- `n = 0`: the atom is every positive world
    have hn0' : n = 0 := by omega
    subst hn0'
    apply FinDist.ext
    intro a
    rw [homeModel.prof_w_of_pos _ hreach]
    refine condExpJunk_const_on_pos homeModel.baseW_nonneg hreach fun ω'' _ hω'' => ?_
    have hat : S.AtomEq 0 ω ω'' := by
      refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => ?_⟩
      have hi0 : i = 0 := Fin.ext (by simpa using hi)
      subst hi0
      show pStates ω 0 = pStates ω'' 0
      have h1 := (baseW_pos_iff ω).1 hω
      have h2 := (baseW_pos_iff ω'').1 hω''
      simp [pStates, h1, h2]
    exact congrArg (fun μ : FinDist Bool => μ.w a) (hconst ω'' (S.mem_atom.2 hat))
  · -- `n = 1`: along `h` the first observation is `true`, contradicting the heads branch
    exfalso
    have hn1' : n = 1 := by omega
    subst hn1'
    have hat := S.mem_atom.1 hω'
    have h0 := hal 0 (by simp)
    have h0' := hat.1 0 (by simp)
    simp only [hT] at h0
    change pObs ω 0 = pObs ω' 0 at h0'
    change pObs ω 0 = true at h0
    rw [← h0', h0] at hH'
    exact Bool.noConfusion hH'

/-! ### The escape clause bites: `homeA` is not its own average -/

/-- Supporting lemma `ω₀_mem_avgEvent`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ω₀_mem_avgEvent : ω₀ ∈ S.avgEvent hT 0 ![false, true] := by
  rw [S.mem_avgEvent]
  refine ⟨fun i hi hi' => ?_, ω₀_reach⟩
  have hi0 : i = 0 := Fin.ext (by simpa using hi)
  subst hi0
  rfl

/-- **`homeA` is not its own time-`0` average**: the average cannot read the answer, `homeA` does
(Post 6 §1.2: "the strategy of running 'do fast mental math' here would have outperformed …").
This is what makes the instance an `N+` witness for Theorem 1 rather than the degenerate case
`A = Ā_{h,n}` where every predicate is trivial.
Source: `references/udt101/06-basics-of-algorithm.md` §1.2; mandate T7 (I) ("do not let the instances have A = avg A h n everywhere")
Kind: N+
Fidelity: exact
Hyps: none -/
theorem homeA_ne_avg : homeA ≠ S.avg homeA hT 0 := by
  intro heq
  have h1 := congrFun (congrFun heq hT) ![false, true]
  have h2 := congrFun (congrFun heq hT) ![false, false]
  have hev : S.avgEvent hT 0 ![false, true] = S.avgEvent hT 0 ![false, false] :=
    S.avgEvent_congr fun i hi => by
      have hi0 : i = 0 := Fin.ext (by simpa using hi)
      subst hi0
      rfl
  have hpos : 0 < mass S.ℙ.w (S.avgEvent hT 0 ![false, true]) :=
    mass_pos_of_mem S.ℙ.nonneg ω₀_mem_avgEvent ω₀_pos
  have hav : S.avg homeA hT 0 hT ![false, true] = S.avg homeA hT 0 hT ![false, false] := by
    rw [S.avg_apply_self, S.avg_apply_self]
    apply FinDist.ext
    intro a
    rw [S.avgDist_w_of_pos hpos, S.avgDist_w_of_pos (hev ▸ hpos), hev]
  rw [← h1, ← h2] at hav
  simp only [homeA, dif_pos rfl] at hav
  have := PlaySpace.delta_injective hav
  simp at this

/-! ### Theorems 1 and 2 instantiated -/

/-- **Post 8 Theorem 1 holds in the homework model** for the answer-reading algorithm `homeA` at the
homework node, at every time `n ≤ 1` and every positive world reaching it: every hypothesis of
`theorem1` is a theorem of the model (`smoothLaw`, `A3`, `A4`, `A5_model`) or a regularity fact of
the instance (`hall`, `hRP`, `hatoms`, `hone`, `hcoh`, `hreach`). The instance is non-degenerate:
`homeA ≠ Ā_{h,0}` (`homeA_ne_avg`).
Source: `references/udt101/08-actual-algorithm.md` Theorem 1; mandate T4 (witness), T7 (I)
Kind: N+
Fidelity: exact
Hyps: (a) all discharged -/
theorem theorem1_home (n : ℕ) (hn : n ≤ hT.1.val) (ω : PWorld Bool Bool Bool Unit 2)
    (hω : 0 < homeModel.baseW ω) (hr : ω ∈ pReach hT) :
    S.IE n homeA hT ω = S.cexp S.ℙ.w n (S.reach hT) (fun ω' => S.fS hT (S.play homeA hT ω') n ω') ω :=
  S.theorem1 homeModel.smoothLaw hall (homeModel.A3 hT) (homeModel.A4 hT hatoms)
    (homeModel.A5_model hone hreach hall hcoh) hRP homeA n hn ω hω hr

/-- **Post 8 Theorem 2 holds in the homework model**: any UDT1.01 algorithm at the homework node
weakly dominates every algorithm (in particular `homeA`) in time-0 influence.
Source: `references/udt101/08-actual-algorithm.md` Theorem 2; mandate T5 (witness)
Kind: N+
Fidelity: exact
Hyps: (a) all discharged -/
theorem theorem2_home {A' : Alg Bool Bool Bool 2} (hU : S.IsUDT101 A' hT) (A : Alg Bool Bool Bool 2)
    (ω : PWorld Bool Bool Bool Unit 2) (hω : 0 < homeModel.baseW ω) (hr : ω ∈ pReach hT) :
    S.IE 0 A hT ω ≤ S.IE 0 A' hT ω :=
  S.theorem2_tiling homeModel.smoothLaw hall (homeModel.A3 hT) (homeModel.A4 hT hatoms)
    (homeModel.A5_model hone hreach hall hcoh) hRP hU A hω hr

end Home

end

end Cleanroom.Udt.UdtInfluence101
