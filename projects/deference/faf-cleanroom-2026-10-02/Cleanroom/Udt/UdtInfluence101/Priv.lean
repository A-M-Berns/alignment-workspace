import Cleanroom.Udt.UdtInfluence101.Two
import Cleanroom.Udt.UdtInfluence101.Witnesses

/-!
# Post 8's Theorem 1 is false under its stated assumptions: the private-signal model

Repair round 2 (2026-10-02), fixing audit r2 (fidelity) B1. The audit's probe `A5Fails.lean` is
promoted into the library and completed: in a profile model where the agent carries **private
time-`0` information that the profile-reading predictor lacks**, Post 8's Assumption 5 as the post
states it (constant algorithms, `A5Lit`) holds, Assumptions 3 and 4 hold (theorems of every profile
model), the regularity hypotheses of `theorem1` hold (`smoothLaw`, `hall`, `hRP`), the
time-`n`-precommitment form `PlaySpace.A5` that `theorem1` needs **fails** (`not_A5`), and **Post 8's
Theorem 1 itself fails** (`theorem1_fails`): the left side is `0`, the right side `1/2`.

**The model** (`privModel`): `O = Act = Ξ = Bool`, `W = Unit`, horizon `2`. The root state `ξ₀` is a
fair coin — the agent's private signal. A single, always-smart Omega at the root fills the box
(`o₀ = true`) iff the action it draws from the profile at `hT` is one-boxing (`eA = δ a'` at step `0`,
`pn root = hT`); the box node `hT` is the full-box branch. Everything else is a fair coin;
`U = [o₀ = true]`. All `128` worlds have weight `1/128`.

**The algorithm** (`privA`): one-box at `hT` when `ξ₀ = false`, two-box when `ξ₀ = true`. On each
time-`0` atom it is a precommitment (`δ one-box` on `ξ₀ = false`), but its *global* profile is fair
(`prof_privA`), so Omega's prediction does not move under ε-play of `privA`, while it does move under
ε-play of `δ one-box`. That is the whole mechanism: the precommitment form of Assumption 5 asserts the
influences of a time-`0` precommitment are those of the constant it agrees with on the atom, and a
diffuse predictor reading the global profile (Post 7 Sub-Assumption 4) cannot tell the two apart
*there* but weights them differently *globally*.

**Theorem 1's failure.** At `ω₀` (`ξ₀ = false`, full box), `n = 0`: `𝕀^𝔼_∅(privA, hT) = 0`
(`IE_privA`: the expected utility given the atom is `ℙ^ε(full | ξ₀ = false) = 1/2` for every `ε`),
while Post 8's right-hand side `𝔼_∅[f^0_{hT,S̄}(privA(hT, S̄)) | reach hT] = 1/2` (`rhs_eq_half`: on
the atom `privA` plays `δ one-box`, and `f^0_{hT}(δ one-box) = fBase − fMid + ratio·f^1 =
1/2 − 0 + ratio·0`, with `fBase = 𝕀^𝔼_∅(one-box, hT) = 1/2` by Lemma 1, `fMid = 0` and `f^1 = 0`
because `U` is fixed by the time-`1` epistemic state). Every hypothesis of `theorem1` other than
the precommitment-form `A5` is proved in this module, so `theorem1_fails` is a genuine counterexample
to Post 8's Theorem 1 **as stated** (with Assumption 5 as stated, `A5Lit_at_zero` /
`A5Lit`), not to the Lean `theorem1`, whose stronger `A5` fails here (`not_A5`). Finding F4 of
[[udt-influence-101-findings]].

Namespace `Priv`; `S` is the play space of the model.
-/

namespace Cleanroom.Udt.UdtInfluence101

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree
open Home (fair fair_w hT hH root root_ne_hT root_ne_hH hT_ne_hH leafExt_hT_iff mem_pReach_hT
  setObs setObs_obs_self setObs_obs_ne setObs_states)
open ProfileModel

section Literal

variable {O Act Ξ : Type} [Fintype O] [DecidableEq O] [Fintype Act] [DecidableEq Act]
  [Fintype Ξ] [DecidableEq Ξ] {N : ℕ} {Ω : Type} [Fintype Ω] [DecidableEq Ω]

namespace PlaySpace

variable (S : PlaySpace O Act Ξ N Ω)

/-- **Post 8's Assumption 5 exactly as the post states it** ("the algorithm which just selects an
action from the probability distribution `μ`"): for every constant algorithm `ofDist μ`, at every
positive world along `h`, both influences are the `μ`-average of the pure-action influences. This is
the conclusion of `A5_ofDist`; `PlaySpace.A5` (the hypothesis `theorem1` needs) is strictly stronger
(`Priv.not_A5` with `Priv.A5Lit_priv`).
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 (udt-rep-081), verbatim scope
Kind: D
Fidelity: exact (quantified over the epistemic states along `h`, as the posts do)
Hyps: n/a -/
def A5Lit (h : Node O N) : Prop :=
  ∀ (n : ℕ) (hn : n ≤ h.1.val) (μ : FinDist Act) (ω : Ω), 0 < S.ℙ.w ω → S.Along h n hn ω →
    ∀ o, S.IP n (ofDist μ) h o ω = ∑ a, μ.w a * S.IP n (ofAct a) h o ω ∧
      S.IEo n (ofDist μ) h o ω = ∑ a, μ.w a * S.IEo n (ofAct a) h o ω

/-- The precommitment form implies the literal form (restating `A5_ofDist`).
Source: `references/udt101/08-actual-algorithm.md` Assumption 5
Kind: L
Fidelity: exact
Hyps: (b) `A5` -/
theorem A5Lit_of_A5 {h : Node O N} (hA5 : S.A5 h) : S.A5Lit h :=
  fun _ hn μ _ hω hal o => S.A5_ofDist hA5 hn μ hω hal o

end PlaySpace

end Literal

namespace Priv

noncomputable section

/-- Root draw: `W = Unit`, `ξ₀` fair (the agent's private signal).
Source: audit r2 (fidelity) B1, probe `A5Fails.lean`; mandate T7 (the profile model)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def rootDist : FinDist (Unit × Bool) where
  w := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  sum_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool]
    norm_num

/-- **The private-signal model** (module docstring): fair private root state, an always-smart Omega
at the root reading the profile at `hT`, fair coins elsewhere, `U = [o₀ = true]`.
Source: audit r2 (fidelity) B1; `references/udt101/07-conservation-of-expected-gain.md` Sub-Assumption 4 (the diffuse predictor reads the global profile)
Kind: D
Fidelity: variant: a profile model (`ProfileModel`'s disclosed variant); the predictor is always smart
Hyps: n/a -/
def privModel : ProfileModel Bool Bool Bool Unit 2 where
  root := rootDist
  κ := fun _ _ _ _ _ _ => fair
  eA := fun _ k _ _ _ a' => if k.val = 0 then FinDist.delta a' else fair
  pn := fun m => if m = root then hT else root
  B := fun _ _ => fair
  π₀ := fun _ => fair
  U := fun ω => if (ω.2 0).2.1 then 1 else 0

/-- The play space of the private-signal model.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev S : PlaySpace Bool Bool Bool 2 (PWorld Bool Bool Bool Unit 2) := privModel.toPlaySpace

/-- **The private-signal algorithm**: one-box at `hT` iff the private root state is `false`; fair
elsewhere. A time-`0` precommitment on each time-`0` atom with global profile `fair`.
Source: audit r2 (fidelity) B1
Kind: D
Fidelity: n/a
Hyps: n/a -/
def privA : Alg Bool Bool Bool 2 := fun m s =>
  if m = hT then (if s ⟨0, Nat.succ_pos _⟩ then FinDist.delta false else FinDist.delta true)
  else fair

/-- Witness world: `ξ₀ = false`, full box, every letter `(true, true, true)`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ω₀ : PWorld Bool Bool Bool Unit 2 := (((), false), fun _ => (true, true, true))

/-- Supporting lemma `root_w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem root_w (r : Unit × Bool) : privModel.root.w r = 1 / 2 := rfl

/-- Supporting lemma `obsFactor_eq` (the baseline observation factor is `1/2` at every step: Omega
reads a fair profile at the root, the step-`1` observation is a fair coin).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem obsFactor_eq (m' : Node Bool 2) (u : Unit) (k : Fin 2) (obs : Fin k.val → Bool)
    (acts : Fin k.val → Bool) (a o : Bool) :
    ∑ a', (privModel.π₀ m').w a' * (privModel.eA u k obs acts a a').w o = 1 / 2 := by
  simp only [privModel, fair_w, Fintype.sum_bool]
  split_ifs <;> cases o <;> simp <;> norm_num

/-- Supporting lemma `baseF_eq` (every baseline step factor is `1/8`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseF_eq (r : Unit × Bool) (m : Node (Letter Bool Bool Bool) 2) (ℓ : Letter Bool Bool Bool) :
    privModel.baseF r m ℓ = 1 / 8 := by
  unfold ProfileModel.baseF
  rw [obsFactor_eq]
  have hB : (privModel.B (oNode m) (statePre r.2 m)).w ℓ.1 = 1 / 2 := fair_w _
  have hκ : (privModel.κ r.1 m.1 (obsPre m) (statePre r.2 m) ℓ.1 ℓ.2.1).w ℓ.2.2 = 1 / 2 := fair_w _
  rw [hB, hκ]
  norm_num

/-- **Every world has baseline weight `1/128`.**
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseW_eq (ω : PWorld Bool Bool Bool Unit 2) : privModel.baseW ω = 1 / 128 := by
  unfold ProfileModel.baseW pathLaw
  rw [Fin.prod_univ_two, baseF_eq, baseF_eq, root_w]
  norm_num

/-- Supporting lemma `baseW_pos` (every world is positive).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseW_pos (ω : PWorld Bool Bool Bool Unit 2) : 0 < privModel.baseW ω := by
  rw [baseW_eq]; norm_num

/-- Supporting lemma `ω₀_reach`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ω₀_reach : ω₀ ∈ pReach hT := (mem_pReach_hT ω₀).2 rfl

/-- Supporting lemma `hreach` (`reach hT` has positive baseline mass).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hreach : 0 < mass privModel.baseW (pReach hT) :=
  mass_pos_of_mem privModel.baseW_nonneg ω₀_reach (baseW_pos ω₀)

/-- **The root step factor under ε-play of any `A` at `hT`**: Omega's predicted one-boxing rate is
the ε-mixed global profile `(1−ε)/2 + ε·prof(A)(one-box)`.
Source: none: infrastructure (the mechanism of the module docstring)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_node0_eq (A : Alg Bool Bool Bool 2) (ε : ℝ) (r : Unit × Bool) (a₀ o₀ ξ₁ : Bool) :
    privModel.F A hT ε r (node0 _) (a₀, o₀, ξ₁) =
      (1 / 2) * ((1 - ε) / 2 + ε * (privModel.prof A hT).w o₀) * (1 / 2) := by
  have h0 : oNode (node0 (Letter Bool Bool Bool)) = root := oNode_node0
  have hpn : privModel.pn root = hT := by
    show (if root = root then hT else root) = hT
    rw [if_pos rfl]
  have hB : ∀ (m : Node Bool 2) (s : Fin (m.1.val + 1) → Bool) (a : Bool),
      (privModel.B m s).w a = 1 / 2 := fun _ _ a => fair_w a
  have hπ : ∀ (m : Node Bool 2) (a : Bool), (privModel.π₀ m).w a = 1 / 2 := fun _ a => fair_w a
  have heA : ∀ (u : Unit) (obs : Fin (node0 (Letter Bool Bool Bool)).1.val → Bool)
      (acts : Fin (node0 (Letter Bool Bool Bool)).1.val → Bool) (a a' : Bool),
      privModel.eA u (node0 (Letter Bool Bool Bool)).1 obs acts a a' = FinDist.delta a' :=
    fun u obs acts a a' => by
      show (if ((node0 (Letter Bool Bool Bool)).1).val = 0 then FinDist.delta a' else fair) = _
      exact if_pos rfl
  have hκ : ∀ (u : Unit) (k : Fin 2) (obs : Fin k.val → Bool) (s : Fin (k.val + 1) → Bool)
      (a o ξ : Bool), (privModel.κ u k obs s a o).w ξ = 1 / 2 := fun _ _ _ _ _ _ ξ => fair_w ξ
  simp only [ProfileModel.F, ProfileModel.algW, ProfileModel.profW, h0, if_neg root_ne_hT, hpn,
    FinDist.delta_w, hB, hπ, heA, hκ, Fintype.sum_bool]
  cases o₀ <;> simp <;> ring

/-! ### Time-`0` atoms and the events of the computation -/

/-- Supporting lemma `mem_atom0_iff` (the time-`0` atom of `ω` is "same private signal").
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_atom0_iff (ω ω' : PWorld Bool Bool Bool Unit 2) : ω' ∈ S.atom 0 ω ↔ ω'.1.2 = ω.1.2 := by
  rw [S.mem_atom]
  constructor
  · intro hat
    exact (hat.2 0 le_rfl).symm
  · intro h1
    refine ⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => ?_⟩
    have hi0 : i = 0 := Fin.ext (Nat.le_zero.1 hi)
    subst hi0
    exact h1.symm

/-- Supporting lemma `mem_nextObs0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_nextObs0 (ω : PWorld Bool Bool Bool Unit 2) (o : Bool) :
    ω ∈ S.nextObs 0 o ↔ (ω.2 0).2.1 = o := by
  rw [S.mem_nextObs (show (0 : ℕ) < 2 by norm_num)]
  rfl

/-- Supporting lemma `atom0_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atom0_eq (ω : PWorld Bool Bool Bool Unit 2) : S.atom 0 ω =
    univ.filter (fun ω' : PWorld Bool Bool Bool Unit 2 => ω'.1.2 = ω.1.2) := by
  ext ω'
  rw [Finset.mem_filter, mem_atom0_iff]
  simp only [Finset.mem_univ, true_and]

/-- Supporting lemma `E_eq` (the time-`0` atom of `ω` and the next observation `o`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem E_eq (ω : PWorld Bool Bool Bool Unit 2) (o : Bool) : S.atom 0 ω ∩ S.nextObs 0 o =
    univ.filter (fun ω' : PWorld Bool Bool Bool Unit 2 => ω'.1.2 = ω.1.2 ∧ (ω'.2 0).2.1 = o) := by
  ext ω'
  rw [Finset.mem_inter, Finset.mem_filter, mem_atom0_iff, mem_nextObs0]
  simp only [Finset.mem_univ, true_and]

/-- Supporting lemma `pReach_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pReach_eq : pReach hT =
    univ.filter (fun ω : PWorld Bool Bool Bool Unit 2 => (ω.2 0).2.1 = true) := by
  ext ω
  rw [Finset.mem_filter, mem_pReach_hT]
  simp only [Finset.mem_univ, true_and]
  rfl

/-- Indicator summand of the time-`0` atom with private signal `ξ`, as a function of the root draw
and the first letter (named so `rw` matches).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Gatom (ξ : Bool) (r : Unit × Bool) (_ : Letter Bool Bool Bool) : ℝ := if r.2 = ξ then 1 else 0

/-- Indicator summand of "private signal `ξ` and next observation `o`".
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def GE (ξ o : Bool) (r : Unit × Bool) (x : Letter Bool Bool Bool) : ℝ :=
  if r.2 = ξ ∧ x.2.1 = o then 1 else 0

/-- Indicator summand of `reach hT`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Greach (_ : Unit × Bool) (x : Letter Bool Bool Bool) : ℝ := if x.2.1 = true then 1 else 0

/-- Summand of the profile numerator of `privA` (one-boxing weight on `reach hT`).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Gnum (r : Unit × Bool) (x : Letter Bool Bool Bool) : ℝ :=
  if x.2.1 = true then (if r.2 then 0 else 1) else 0

/-- Supporting lemma `prof_sum`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prof_sum (A : Alg Bool Bool Bool 2) :
    (privModel.prof A hT).w true + (privModel.prof A hT).w false = 1 := by
  have := (privModel.prof A hT).sum_one
  simpa [Fintype.sum_bool] using this

/-- **`ℙ^ε(atom_0(ω)) = 1/2` for every `A` and `ε`** (the profile sums to one).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem den_eq (A : Alg Bool Bool Bool 2) (ε : ℝ) (ω : PWorld Bool Bool Bool Unit 2) :
    mass (privModel.lawW A hT ε) (S.atom 0 ω) = 1 / 2 := by
  unfold mass
  rw [atom0_eq, Finset.sum_filter]
  have hG : ∀ ω' : PWorld Bool Bool Bool Unit 2,
      (if ω'.1.2 = ω.1.2 then privModel.lawW A hT ε ω' else 0) =
      privModel.lawW A hT ε ω' * Gatom ω.1.2 ω'.1 (ω'.2 0) := by
    intro ω'
    simp only [Gatom]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun ω' _ => hG ω', privModel.sum_lawW_mul_fst A hT ε (Gatom ω.1.2)]
  simp only [Gatom, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool, F_node0_eq, root_w]
  have hp := prof_sum A
  cases ω.1.2 <;> norm_num <;> linear_combination (ε / 2) * hp

/-- **`ℙ^ε(atom_0(ω) ∩ {o₀ = o}) = (1/2)·((1−ε)/2 + ε·prof(A)(o))`** for every `A`, `ε`, `ω`, `o`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem num_eq (A : Alg Bool Bool Bool 2) (ε : ℝ) (ω : PWorld Bool Bool Bool Unit 2) (o : Bool) :
    mass (privModel.lawW A hT ε) (S.atom 0 ω ∩ S.nextObs 0 o) =
      (1 / 2) * ((1 - ε) / 2 + ε * (privModel.prof A hT).w o) := by
  unfold mass
  rw [E_eq, Finset.sum_filter]
  have hG : ∀ ω' : PWorld Bool Bool Bool Unit 2,
      (if ω'.1.2 = ω.1.2 ∧ (ω'.2 0).2.1 = o then privModel.lawW A hT ε ω' else 0) =
      privModel.lawW A hT ε ω' * GE ω.1.2 o ω'.1 (ω'.2 0) := by
    intro ω'
    simp only [GE]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun ω' _ => hG ω', privModel.sum_lawW_mul_fst A hT ε (GE ω.1.2 o)]
  simp only [GE, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool, F_node0_eq, root_w]
  cases ω.1.2 <;> cases o <;> norm_num <;> ring

/-! ### Time-`0` influences for every algorithm: the profile is all Omega sees -/

/-- **`ℙ^ε_∅(o₀ = o)` along the ε-family of any `A`** at any world: `(1−ε)/2 + ε·prof(A)(o)`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pr_eq (A : Alg Bool Bool Bool 2) (ε : ℝ) (ω : PWorld Bool Bool Bool Unit 2) (o : Bool) :
    S.pr (privModel.lawW A hT ε) 0 (S.nextObs 0 o) ω =
      (1 - ε) / 2 + ε * (privModel.prof A hT).w o := by
  unfold PlaySpace.pr condProbJunk
  rw [den_eq, Finset.inter_comm, num_eq, if_neg (by norm_num)]
  ring

/-- Supporting lemma `hasDerivAt_affine` (the derivative at `0` of `(1−ε)/2 + ε·p`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hasDerivAt_affine (p : ℝ) :
    HasDerivAt (fun ε : ℝ => (1 - ε) / 2 + ε * p) (-1 / 2 + 1 * p) 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => (1 - ε) / 2) (-1 / 2) 0 :=
    ((hasDerivAt_id' (x := (0 : ℝ))).const_sub 1).div_const 2
  have h2 : HasDerivAt (fun ε : ℝ => ε * p) (1 * p) 0 := (hasDerivAt_id' (x := (0 : ℝ))).mul_const p
  exact h1.add h2

/-- **The influence of any `A` on the probability of `o₀ = o` is `prof(A)(o) − 1/2`**, at every world:
Omega sees the algorithm only through its global profile.
Source: audit r2 (fidelity) B1 (`IP_eq`); `references/udt101/07-conservation-of-expected-gain.md` Sub-Assumption 4
Kind: P
Fidelity: exact
Hyps: none -/
theorem IP_eq (A : Alg Bool Bool Bool 2) (ω : PWorld Bool Bool Bool Unit 2) (o : Bool) :
    S.IP 0 A hT o ω = (privModel.prof A hT).w o - 1 / 2 := by
  unfold PlaySpace.IP
  have hf : (fun ε => S.pr (S.law A hT ε) 0 (S.nextObs 0 o) ω) =
      fun ε => (1 - ε) / 2 + ε * (privModel.prof A hT).w o := funext fun ε => pr_eq A ε ω o
  rw [hf, (hasDerivAt_affine _).deriv]
  ring

/-- The profile of a constant algorithm is itself.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prof_ofDist (μ : FinDist Bool) : privModel.prof (ofDist μ) hT = μ := by
  apply FinDist.ext
  intro b
  rw [privModel.prof_w_of_pos _ hreach]
  exact condExpJunk_const_on (fun _ _ => rfl) hreach

/-- Supporting lemma `IP_ofAct` (`𝕀^ℙ_∅(δ a, hT, o) = [a = o] − 1/2`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IP_ofAct (a : Bool) (ω : PWorld Bool Bool Bool Unit 2) (o : Bool) :
    S.IP 0 (ofAct a) hT o ω = (if o = a then 1 else 0) - 1 / 2 := by
  rw [IP_eq, ofAct, prof_ofDist, FinDist.delta_w]

/-- Supporting lemma `IP_ofAct_true` (`𝕀^ℙ_∅(δ one-box, hT, full) = 1/2`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IP_ofAct_true (ω : PWorld Bool Bool Bool Unit 2) : S.IP 0 (ofAct true) hT true ω = 1 / 2 := by
  rw [IP_ofAct, if_pos rfl]
  norm_num

/-- Supporting lemma `lawW_zero_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem lawW_zero_eq (A : Alg Bool Bool Bool 2) : privModel.lawW A hT 0 = privModel.baseW := by
  funext ω
  simp only [ProfileModel.lawW, ProfileModel.baseW, privModel.F_zero]

/-- Supporting lemma `pStatesAlong_zero` (the first state along `hT` is the root state).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pStatesAlong_zero (ω : PWorld Bool Bool Bool Unit 2) :
    pStatesAlong ω hT 0 = ω.1.2 := rfl

/-- **The global profile of `privA` is fair**: the private signal is fair and independent of the box
under the baseline, so Omega, reading the profile, sees a coin flip.
Source: audit r2 (fidelity) B1 (`prof_privA`)
Kind: P
Fidelity: exact
Hyps: none -/
theorem prof_privA : (privModel.prof privA hT).w true = 1 / 2 := by
  rw [privModel.prof_w_of_pos _ hreach, condExpJunk_of_pos hreach]
  have hnum : ∑ ω ∈ pReach hT, privModel.baseW ω * (privA hT (pStatesAlong ω hT)).w true = 1 / 4 := by
    rw [pReach_eq, Finset.sum_filter, ← lawW_zero_eq privA]
    have hG : ∀ ω : PWorld Bool Bool Bool Unit 2,
        (if (ω.2 0).2.1 = true then privModel.lawW privA hT 0 ω * (privA hT (pStatesAlong ω hT)).w true
          else 0) =
        privModel.lawW privA hT 0 ω * Gnum ω.1 (ω.2 0) := by
      intro ω
      by_cases h1 : (ω.2 0).2.1 = true <;> by_cases h2 : ω.1.2 = true <;>
        simp [Gnum, privA, pStatesAlong_zero, h1, h2]
    rw [Finset.sum_congr rfl fun ω _ => hG ω, privModel.sum_lawW_mul_fst privA hT 0 Gnum]
    simp only [Gnum, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool, F_node0_eq, root_w]
    norm_num
  have hden : mass privModel.baseW (pReach hT) = 1 / 2 := by
    unfold mass
    rw [pReach_eq, Finset.sum_filter, ← lawW_zero_eq privA]
    have hG : ∀ ω : PWorld Bool Bool Bool Unit 2,
        (if (ω.2 0).2.1 = true then privModel.lawW privA hT 0 ω else 0) =
        privModel.lawW privA hT 0 ω * Greach ω.1 (ω.2 0) := by
      intro ω
      simp only [Greach]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun ω _ => hG ω, privModel.sum_lawW_mul_fst privA hT 0 Greach]
    simp only [Greach, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool, F_node0_eq, root_w]
    norm_num
  rw [hnum, hden]
  norm_num

/-- **`privA` has influence `0` on the probability of a full box** (its profile is fair).
Source: audit r2 (fidelity) B1
Kind: P
Fidelity: exact
Hyps: none -/
theorem IP_privA (ω : PWorld Bool Bool Bool Unit 2) : S.IP 0 privA hT true ω = 0 := by
  rw [IP_eq, prof_privA]; norm_num

/-- Supporting lemma `statesAlong_zero_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem statesAlong_zero_eq (ω : PWorld Bool Bool Bool Unit 2) :
    S.statesAlong ω hT ⟨0, Nat.succ_pos _⟩ = ω.1.2 := rfl

/-- **`privA` is a time-`0` precommitment at every world**: constant on the time-`0` atom (the atom
fixes the private signal, which is all `privA` reads).
Source: audit r2 (fidelity) B1 (`constOnAtom_privA`)
Kind: L
Fidelity: exact
Hyps: none -/
theorem constOnAtom_privA (ω : PWorld Bool Bool Bool Unit 2) : S.ConstOnAtom 0 privA hT ω := by
  intro ω' hω'
  have h0 : ω'.1.2 = ω.1.2 := (mem_atom0_iff ω ω').1 hω'
  show privA hT (S.statesAlong ω' hT) = privA hT (S.statesAlong ω hT)
  unfold privA
  rw [if_pos rfl, if_pos rfl, statesAlong_zero_eq, statesAlong_zero_eq, h0]

/-- Supporting lemma `play_privA_ω₀` (`privA` one-boxes at `ω₀`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem play_privA_ω₀ : S.play privA hT ω₀ = FinDist.delta true := by
  show privA hT (S.statesAlong ω₀ hT) = _
  have hs : S.statesAlong ω₀ hT ⟨0, Nat.succ_pos _⟩ = false := rfl
  simp only [privA, hs, Bool.false_eq_true, if_false, if_true]

/-- **Assumption 5 in the time-`n`-precommitment form (`PlaySpace.A5`, the hypothesis of `theorem1`)
fails in the private-signal model**: the time-`0` precommitment `privA` has influence `0` on the
probability of a full box (its global profile is fair, so Omega's prediction does not move) while
the `δ one-box`-average of the pure-action influences is `1/2`.
Source: audit r2 (fidelity) B1 (`not_A5`); `references/udt101/08-actual-algorithm.md` Assumption 5 and the proof of Theorem 1
Kind: P
Fidelity: exact (refutation of the extended form at `n = 0`, `o = full`, `ω₀`)
Hyps: none -/
theorem not_A5 : ¬ S.A5 hT := by
  intro h5
  have := (h5 0 (Nat.zero_le _) privA ω₀ (baseW_pos ω₀) (fun i hi => absurd hi (Nat.not_lt_zero _))
    (constOnAtom_privA ω₀) true).1
  rw [IP_privA, play_privA_ω₀, PlaySpace.sum_delta_mul, IP_ofAct_true] at this
  norm_num at this

/-! ### Regularity: the hypotheses of `theorem1` other than `A5` -/

/-- Supporting lemma `atomEq_setObs` (editing the observation at step `k ≥ n` keeps the time-`n`
atom; the homework instance's helper, re-proved for this model's play space).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atomEq_setObs (ω : PWorld Bool Bool Bool Unit 2) {n : ℕ} {k : Fin 2} (hnk : n ≤ k.val)
    (o : Bool) : S.AtomEq n ω (setObs ω k o) := by
  refine ⟨fun i hi => ?_, fun i _ => ?_⟩
  · show pObs ω i = pObs (setObs ω k o) i
    rw [setObs_obs_ne ω (fun h => by subst h; omega) o]
  · show pStates ω i = pStates (setObs ω k o) i
    rw [setObs_states]

/-- **Every next observation is possible at every positive atom** (`AllPosObs`).
Source: mandate T7 (regularity of the instance)
Kind: L
Fidelity: exact
Hyps: none -/
theorem hall : S.AllPosObs := by
  intro n hn ω _ o
  refine mass_pos_of_mem S.ℙ.nonneg (Finset.mem_inter.2 ⟨?_, ?_⟩) (baseW_pos (setObs ω ⟨n, hn⟩ o))
  · exact S.mem_atom.2 (atomEq_setObs ω (k := ⟨n, hn⟩) le_rfl o)
  · rw [S.mem_nextObs hn]
    exact setObs_obs_self ω ⟨n, hn⟩ o

/-- **Every positive atom along `hT` can still reach `hT`** (`ReachPos hT`).
Source: mandate T7 (regularity of the instance)
Kind: L
Fidelity: exact
Hyps: none -/
theorem hRP : S.ReachPos hT := by
  intro n hn ω _ hal
  refine mass_pos_of_mem S.ℙ.nonneg (Finset.mem_inter.2 ⟨?_, ?_⟩) (baseW_pos (setObs ω 0 true))
  · rw [S.mem_atom]
    refine ⟨fun i hi => ?_, fun i _ => ?_⟩
    · have hi0 : i = 0 := Fin.ext (by have := i.isLt; have : n ≤ 1 := hn; omega)
      subst hi0
      show pObs ω 0 = pObs (setObs ω 0 true) 0
      rw [setObs_obs_self]
      exact hal 0 hi
    · show pStates ω i = pStates (setObs ω 0 true) i
      rw [setObs_states]
  · show setObs ω 0 true ∈ pReach hT
    rw [mem_pReach_hT, setObs_obs_self]

/-- **Assumption 3 holds in the private-signal model** (a theorem of every profile model).
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 3
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem A3_priv : S.A3 hT := privModel.A3 hT

/-- **Assumption 4 holds in the private-signal model** (every atom is positive).
Source: `references/udt101/07-conservation-of-expected-gain.md` Assumption 4
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem A4_priv : S.A4 hT :=
  privModel.A4 hT fun _ _ _ _ _ ω' _ =>
    mass_pos_of_mem privModel.baseW_nonneg (S.self_mem_atom _ ω') (baseW_pos ω')

/-! ### The time-`0` influence on expected utility: `U` is the indicator of a full box -/

/-- Supporting lemma `sumU_eq` (the ε-weighted utility on the time-`0` atom is the ε-mass of "full
box" there).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sumU_eq (A : Alg Bool Bool Bool 2) (ε : ℝ) (ω : PWorld Bool Bool Bool Unit 2) :
    ∑ ω' ∈ S.atom 0 ω, privModel.lawW A hT ε ω' * privModel.U ω' =
      (1 / 2) * ((1 - ε) / 2 + ε * (privModel.prof A hT).w true) := by
  rw [atom0_eq, Finset.sum_filter]
  have hG : ∀ ω' : PWorld Bool Bool Bool Unit 2,
      (if ω'.1.2 = ω.1.2 then privModel.lawW A hT ε ω' * privModel.U ω' else 0) =
      privModel.lawW A hT ε ω' * GE ω.1.2 true ω'.1 (ω'.2 0) := by
    intro ω'
    simp only [GE, privModel]
    split_ifs <;> simp_all
  rw [Finset.sum_congr rfl fun ω' _ => hG ω', privModel.sum_lawW_mul_fst A hT ε (GE ω.1.2 true)]
  simp only [GE, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_bool, F_node0_eq, root_w]
  cases ω.1.2 <;> norm_num <;> ring

/-- **`𝔼^ε_∅[U]` along the ε-family of any `A`**: `(1−ε)/2 + ε·prof(A)(one-box)`, at every world.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_univ_eq (A : Alg Bool Bool Bool 2) (ε : ℝ) (ω : PWorld Bool Bool Bool Unit 2) :
    S.cexp (privModel.lawW A hT ε) 0 univ S.U ω = (1 - ε) / 2 + ε * (privModel.prof A hT).w true := by
  unfold PlaySpace.cexp condExpJunk
  rw [Finset.inter_univ, den_eq, if_neg (by norm_num)]
  show (∑ ω' ∈ S.atom 0 ω, privModel.lawW A hT ε ω' * privModel.U ω') / (1 / 2) = _
  rw [sumU_eq]
  ring

/-- **The time-`0` influence of any `A` on expected utility is `prof(A)(one-box) − 1/2`**, at every
world: the agent is paid iff the box is full, and Omega fills it according to the global profile.
Source: audit r2 (fidelity) B1 (the "by hand" left side of Theorem 1, now in Lean)
Kind: P
Fidelity: exact
Hyps: none -/
theorem IE_eq (A : Alg Bool Bool Bool 2) (ω : PWorld Bool Bool Bool Unit 2) :
    S.IE 0 A hT ω = (privModel.prof A hT).w true - 1 / 2 := by
  unfold PlaySpace.IE
  have hf : (fun ε => S.cexp (S.law A hT ε) 0 univ S.U ω) =
      fun ε => (1 - ε) / 2 + ε * (privModel.prof A hT).w true := funext fun ε => cexp_univ_eq A ε ω
  rw [hf, (hasDerivAt_affine _).deriv]
  ring

/-- **The left side of Theorem 1 for `privA` at `ω₀` is `0`**: its global profile is fair.
Source: audit r2 (fidelity) B1
Kind: P
Fidelity: exact
Hyps: none -/
theorem IE_privA : S.IE 0 privA hT ω₀ = 0 := by
  rw [IE_eq, prof_privA]; norm_num

/-- Supporting lemma `IE_ofAct_true` (`𝕀^𝔼_∅(δ one-box, hT) = 1/2` at every world).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IE_ofAct_true (ω : PWorld Bool Bool Bool Unit 2) : S.IE 0 (ofAct true) hT ω = 1 / 2 := by
  rw [IE_eq, ofAct, prof_ofDist, FinDist.delta_w, if_pos rfl]
  norm_num

/-! ### The time-`1` influence on expected utility vanishes: `U` is fixed by the time-`1` state -/

/-- Supporting lemma `U_eq_of_mem_atom1` (`U` reads the first observation, which the time-`1` atom
fixes).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem U_eq_of_mem_atom1 {ω' ω'' : PWorld Bool Bool Bool Unit 2} (h : ω'' ∈ S.atom 1 ω') :
    S.U ω'' = S.U ω' := by
  have hat := S.mem_atom.1 h
  have hs : (ω''.2 0).2.1 = (ω'.2 0).2.1 := (hat.1 0 (by norm_num)).symm
  show (if (ω''.2 0).2.1 then (1 : ℝ) else 0) = if (ω'.2 0).2.1 then 1 else 0
  rw [hs]

/-- **The time-`1` influence of every algorithm on expected utility is `0`** at every world: the
payoff `[o₀ = true]` is constant on every time-`1` atom.
Source: audit r2 (fidelity) B1 (`f^1 = 0`)
Kind: P
Fidelity: exact
Hyps: none -/
theorem IE_one_eq_zero (A : Alg Bool Bool Bool 2) (ω' : PWorld Bool Bool Bool Unit 2) :
    S.IE 1 A hT ω' = 0 := by
  unfold PlaySpace.IE
  have hpos : 0 < mass S.ℙ.w (S.atom 1 ω' ∩ univ) := by
    rw [Finset.inter_univ]
    exact mass_pos_of_mem privModel.baseW_nonneg (S.self_mem_atom 1 ω') (baseW_pos ω')
  have hconst : ∀ ω'' ∈ S.atom 1 ω' ∩ univ, S.U ω'' = S.U ω' := fun ω'' h =>
    U_eq_of_mem_atom1 (Finset.mem_inter.1 h).1
  have hev := S.eventually_mass_pos privModel.smoothLaw A hT hpos
  have heq : (fun ε => S.cexp (S.law A hT ε) 1 univ S.U ω') =ᶠ[nhds 0] fun _ => S.U ω' := by
    filter_upwards [hev] with ε hε
    exact condExpJunk_const_on hconst hε
  rw [heq.deriv_eq, deriv_const]

/-! ### Post 8's score of `δ one-box` at time `0` is `1/2` everywhere -/

/-- **`f^1_{hT}(δ one-box) = 0`** at every world (Lemma 1 turns the causal term into the time-`1`
influence, which vanishes).
Source: audit r2 (fidelity) B1
Kind: C
Fidelity: exact
Hyps: none -/
theorem fBase_one_eq_zero (ω' : PWorld Bool Bool Bool Unit 2) :
    S.fBase hT (FinDist.delta true) 1 ω' = 0 := by
  have h := S.lemma1_split privModel.smoothLaw (show (1 : ℕ) < 2 by norm_num)
    (hall 1 (by norm_num) ω' (baseW_pos ω')) (ofAct true) hT
  rw [IE_one_eq_zero] at h
  exact h.symm

/-- **The causal term `fBase^0_{hT}(δ one-box) = 1/2`** at every world (Lemma 1: it is the time-`0`
influence of `δ one-box` on expected utility).
Source: audit r2 (fidelity) B1 (`fBase(0) = 1/2`)
Kind: C
Fidelity: exact
Hyps: none -/
theorem fBase_zero_eq_half (ω : PWorld Bool Bool Bool Unit 2) :
    S.fBase hT (FinDist.delta true) 0 ω = 1 / 2 := by
  have h := S.lemma1_split privModel.smoothLaw (show (0 : ℕ) < 2 by norm_num)
    (hall 0 (by norm_num) ω (baseW_pos ω)) (ofAct true) hT
  rw [IE_ofAct_true] at h
  exact h.symm

/-- **The deferral-correction term `fMid^0_{hT}(δ one-box) = 0`** at every world (the time-`1`
influence vanishes).
Source: audit r2 (fidelity) B1 (`fMid(0) = 0`)
Kind: C
Fidelity: exact
Hyps: none -/
theorem fMid_zero_eq_zero (hn : 0 < hT.1.val) (ω : PWorld Bool Bool Bool Unit 2) :
    S.fMid hT (FinDist.delta true) 0 hn ω = 0 := by
  unfold PlaySpace.fMid
  have hpos : 0 < mass S.ℙ.w (S.atom 0 ω ∩ S.nextObs 0 (hT.2 ⟨0, hn⟩)) :=
    hall 0 (by norm_num) ω (baseW_pos ω) _
  have h0 : S.cexp S.ℙ.w 0 (S.nextObs 0 (hT.2 ⟨0, hn⟩))
      (fun ω' => S.IE 1 (ofDist (FinDist.delta true)) hT ω') ω = 0 := by
    unfold PlaySpace.cexp
    exact condExpJunk_const_on (fun ω' _ => IE_one_eq_zero _ ω') hpos
  rw [h0, mul_zero]

/-- **Post 8's score of one-boxing at time `0` is `1/2`** at every world:
`f^0_{hT}(δ one-box) = fBase − fMid + ratio·f^1 = 1/2 − 0 + ratio·0`.
Source: audit r2 (fidelity) B1 (the "by hand" right side of Theorem 1, now in Lean)
Kind: C
Fidelity: exact
Hyps: none -/
theorem fS_zero_eq_half (ω : PWorld Bool Bool Bool Unit 2) :
    S.fS hT (FinDist.delta true) 0 ω = 1 / 2 := by
  rw [S.fS_of_lt hT _ (show 0 < hT.1.val by decide), S.fS_of_ge hT _ (show ¬ (1 < hT.1.val) by decide),
    fBase_one_eq_zero, mul_zero, add_zero, fBase_zero_eq_half, fMid_zero_eq_zero]
  norm_num

/-- **The right side of Post 8's Theorem 1 for `privA` at `ω₀` is `1/2`**: on the time-`0` atom of
`ω₀`, `privA` plays `δ one-box`, whose score is `1/2`.
Source: audit r2 (fidelity) B1
Kind: C
Fidelity: exact
Hyps: none -/
theorem rhs_eq_half :
    S.cexp S.ℙ.w 0 (S.reach hT) (fun ω' => S.fS hT (S.play privA hT ω') 0 ω') ω₀ = 1 / 2 := by
  unfold PlaySpace.cexp
  have hpos : 0 < mass S.ℙ.w (S.atom 0 ω₀ ∩ S.reach hT) :=
    mass_pos_of_mem S.ℙ.nonneg (Finset.mem_inter.2 ⟨S.self_mem_atom 0 ω₀, ω₀_reach⟩) (baseW_pos ω₀)
  refine condExpJunk_const_on (fun ω' hω' => ?_) hpos
  have hat := (Finset.mem_inter.1 hω').1
  rw [constOnAtom_privA ω₀ ω' hat, play_privA_ω₀]
  exact fS_zero_eq_half ω'

/-- **Post 8's Theorem 1 fails in the private-signal model**: at `ω₀`, `n = 0`, the influence of
`privA` on expected utility is `0` while the conditional expectation of its score given `reach hT`
is `1/2`. Every hypothesis of `theorem1` other than the precommitment-form `A5` holds here
(`privModel.smoothLaw`, `hall`, `hRP`, `A3_priv`, `A4_priv`), and so does Post 8's Assumption 5 as
stated (`A5Lit_priv`); what fails is `A5` in the form the proof needs (`not_A5`). So the theorem of
Post 8 — under the assumptions Post 8 states — is false ([[udt-influence-101-findings]] F4).
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 (udt-rep-082), refuted under its stated Assumption 5; audit r2 (fidelity) B1
Kind: N+
Fidelity: exact (the conclusion of `theorem1` at `n = 0`, `ω₀`, negated; the model has `128` positive
worlds, a live acausal channel — `IE_eq` is not constant in `A` — and `privA ≠ Ā_{hT,0}` on the support)
Hyps: none -/
theorem theorem1_fails :
    S.IE 0 privA hT ω₀ ≠
      S.cexp S.ℙ.w 0 (S.reach hT) (fun ω' => S.fS hT (S.play privA hT ω') 0 ω') ω₀ := by
  rw [IE_privA, rhs_eq_half]
  norm_num

/-! ### Post 8's literal Assumption 5 holds: time `0` -/

/-- **The time-`0` influence of any `A` on conditional expected utility given `o₀ = o` is `0`**: the
payoff is decided by `o₀`.
Source: none: infrastructure (the `IEo` clause of `A5Lit` at `n = 0`)
Kind: L
Fidelity: n/a
Hyps: none -/
theorem IEo_zero_eq_zero (A : Alg Bool Bool Bool 2) (ω : PWorld Bool Bool Bool Unit 2) (o : Bool) :
    S.IEo 0 A hT o ω = 0 := by
  unfold PlaySpace.IEo
  have hpos : 0 < mass S.ℙ.w (S.atom 0 ω ∩ S.nextObs 0 o) := hall 0 (by norm_num) ω (baseW_pos ω) o
  have hconst : ∀ ω'' ∈ S.atom 0 ω ∩ S.nextObs 0 o, S.U ω'' = if o then (1 : ℝ) else 0 := by
    intro ω'' h
    have ho : (ω''.2 0).2.1 = o := (mem_nextObs0 ω'' o).1 (Finset.mem_inter.1 h).2
    show (if (ω''.2 0).2.1 then (1 : ℝ) else 0) = _
    rw [ho]
  have hev := S.eventually_mass_pos privModel.smoothLaw A hT hpos
  have heq : (fun ε => S.cexp (S.law A hT ε) 0 (S.nextObs 0 o) S.U ω) =ᶠ[nhds 0]
      fun _ => if o then (1 : ℝ) else 0 := by
    filter_upwards [hev] with ε hε
    exact condExpJunk_const_on hconst hε
  rw [heq.deriv_eq, deriv_const]

/-- **Post 8's literal Assumption 5 holds at time `0`**, both clauses, for every constant `μ`, at
every world and observation.
Source: `references/udt101/08-actual-algorithm.md` Assumption 5; audit r2 (fidelity) B1 (`literal_A5_IP`)
Kind: P
Fidelity: exact
Hyps: none -/
theorem A5Lit_at_zero (μ : FinDist Bool) (ω : PWorld Bool Bool Bool Unit 2) (o : Bool) :
    S.IP 0 (ofDist μ) hT o ω = ∑ a, μ.w a * S.IP 0 (ofAct a) hT o ω ∧
      S.IEo 0 (ofDist μ) hT o ω = ∑ a, μ.w a * S.IEo 0 (ofAct a) hT o ω := by
  constructor
  · simp only [IP_eq, ofAct, prof_ofDist, FinDist.delta_w, Fintype.sum_bool]
    have := μ.sum_one
    simp only [Fintype.sum_bool] at this
    cases o <;> norm_num <;> linear_combination (1 / 2) * this
  · simp only [IEo_zero_eq_zero, mul_zero, Finset.sum_const_zero]

/-! ### Post 8's literal Assumption 5 holds: time `1` (every influence vanishes, for every algorithm) -/

/-- Supporting lemma `mem_atom1_iff` (the time-`1` atom fixes the private signal, the box and the
first state).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_atom1_iff (ω' ω : PWorld Bool Bool Bool Unit 2) :
    ω ∈ S.atom 1 ω' ↔
      ω.1.2 = ω'.1.2 ∧ (ω.2 0).2.1 = (ω'.2 0).2.1 ∧ (ω.2 0).2.2 = (ω'.2 0).2.2 := by
  rw [S.mem_atom]
  constructor
  · intro hat
    exact ⟨(hat.2 0 (Nat.zero_le _)).symm, (hat.1 0 (by decide)).symm, (hat.2 1 le_rfl).symm⟩
  · rintro ⟨h0, h1, h2⟩
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · have hi0 : i = 0 := Fin.ext (Nat.lt_one_iff.1 hi)
      subst hi0
      exact h1.symm
    · fin_cases i
      · exact h0.symm
      · exact h2.symm
      · simp at hi

/-- Supporting lemma `mem_nextObs1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_nextObs1 (ω : PWorld Bool Bool Bool Unit 2) (o : Bool) :
    ω ∈ S.nextObs 1 o ↔ (ω.2 1).2.1 = o := by
  rw [S.mem_nextObs (show (1 : ℕ) < 2 by norm_num)]
  rfl

/-- Supporting lemma `atom1_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atom1_eq (ω' : PWorld Bool Bool Bool Unit 2) : S.atom 1 ω' =
    univ.filter (fun ω : PWorld Bool Bool Bool Unit 2 =>
      ω.1.2 = ω'.1.2 ∧ (ω.2 0).2.1 = (ω'.2 0).2.1 ∧ (ω.2 0).2.2 = (ω'.2 0).2.2) := by
  ext ω
  rw [Finset.mem_filter, mem_atom1_iff]
  simp only [Finset.mem_univ, true_and]

/-- Supporting lemma `atom1_obs_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atom1_obs_eq (ω' : PWorld Bool Bool Bool Unit 2) (o : Bool) :
    S.nextObs 1 o ∩ S.atom 1 ω' =
    univ.filter (fun ω : PWorld Bool Bool Bool Unit 2 => (ω.2 1).2.1 = o ∧
      (ω.1.2 = ω'.1.2 ∧ (ω.2 0).2.1 = (ω'.2 0).2.1 ∧ (ω.2 0).2.2 = (ω'.2 0).2.2)) := by
  ext ω
  rw [Finset.mem_inter, Finset.mem_filter, mem_atom1_iff, mem_nextObs1]
  simp only [Finset.mem_univ, true_and]

/-- Indicator summand of the time-`1` atom of `ω'`, as a function of the root draw and the first letter.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Gq (ω' : PWorld Bool Bool Bool Unit 2) (r : Unit × Bool) (x : Letter Bool Bool Bool) : ℝ :=
  if r.2 = ω'.1.2 ∧ x.2.1 = (ω'.2 0).2.1 ∧ x.2.2 = (ω'.2 0).2.2 then 1 else 0

/-- Indicator of "the second observation is `o`", as a function of the second letter.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def Hobs (o : Bool) (y : Letter Bool Bool Bool) : ℝ := if y.2.1 = o then 1 else 0

/-- **The step-`1` ε-factor** at any depth-one node: the ε-mixed action weight times `1/4` (the
second observation and state are fair coins).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_node1_eq (A : Alg Bool Bool Bool 2) (ε : ℝ) (r : Unit × Bool) (x : Letter Bool Bool Bool)
    (a o' ξ : Bool) :
    privModel.F A hT ε r (node1 x) (a, o', ξ) =
      privModel.algW A hT ε (oNode (node1 x)) (statePre r.2 (node1 x)) a * (1 / 4) := by
  have heA : ∀ (a a' : Bool),
      privModel.eA r.1 (node1 x).1 (obsPre (node1 x)) (actPre (node1 x)) a a' = fair := by
    intro a a'
    show (if ((node1 x).1).val = 0 then FinDist.delta a' else fair) = fair
    exact if_neg (by simp [node1])
  have hκ : ∀ ξ : Bool,
      (privModel.κ r.1 (node1 x).1 (obsPre (node1 x)) (statePre r.2 (node1 x)) a o').w ξ = 1 / 2 :=
    fun ξ => fair_w ξ
  simp only [ProfileModel.F, heA, fair_w, hκ, ← Finset.sum_mul, privModel.profW_sum]
  ring

/-- **The step-`1` factor summed against "the second observation is `o`" is `1/2`**, for every
algorithm, `ε`, root draw and first letter.
Source: none: infrastructure (audit r2 N2/N3: "the step-`1` sums are type- and algorithm-independent")
Kind: L
Fidelity: n/a
Hyps: none -/
theorem F_node1_sum_obs (A : Alg Bool Bool Bool 2) (ε : ℝ) (r : Unit × Bool)
    (x : Letter Bool Bool Bool) (o : Bool) :
    ∑ y, privModel.F A hT ε r (node1 x) y * Hobs o y = 1 / 2 := by
  rw [sum_letter]
  have h : ∀ a o' ξ : Bool, privModel.F A hT ε r (node1 x) (a, o', ξ) * Hobs o (a, o', ξ) =
      privModel.algW A hT ε (oNode (node1 x)) (statePre r.2 (node1 x)) a *
        ((1 / 4) * if o' = o then 1 else 0) := by
    intro a o' ξ
    rw [F_node1_eq, Hobs]
    ring
  simp only [h, ← Finset.mul_sum]
  rw [← Finset.sum_mul, privModel.algW_sum, one_mul]
  simp only [Fintype.sum_bool]
  cases o <;> norm_num

/-- **Both letters marginalized**: the ε-mass of a product of a function of the root draw and the
first letter with a function of the second letter.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_lawW_mul_both (A : Alg Bool Bool Bool 2) (ε : ℝ)
    (G : Unit × Bool → Letter Bool Bool Bool → ℝ) (H : Letter Bool Bool Bool → ℝ) :
    ∑ ω, privModel.lawW A hT ε ω * (G ω.1 (ω.2 0) * H (ω.2 1)) =
      ∑ r, ∑ x, privModel.root.w r * privModel.F A hT ε r (node0 _) x * G r x *
        ∑ y, privModel.F A hT ε r (node1 x) y * H y := by
  rw [sum_pworld_two]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun x _ => ?_
  simp only [lawW_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **The ε-mass of the time-`1` atom** as a sum over the root draw and the first letter.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_atom1 (A : Alg Bool Bool Bool 2) (ε : ℝ) (ω' : PWorld Bool Bool Bool Unit 2) :
    mass (privModel.lawW A hT ε) (S.atom 1 ω') =
      ∑ r, ∑ x, privModel.root.w r * privModel.F A hT ε r (node0 _) x * Gq ω' r x := by
  unfold mass
  rw [atom1_eq, Finset.sum_filter]
  have hG : ∀ ω : PWorld Bool Bool Bool Unit 2,
      (if ω.1.2 = ω'.1.2 ∧ (ω.2 0).2.1 = (ω'.2 0).2.1 ∧ (ω.2 0).2.2 = (ω'.2 0).2.2 then
        privModel.lawW A hT ε ω else 0) = privModel.lawW A hT ε ω * Gq ω' ω.1 (ω.2 0) := by
    intro ω
    by_cases hB : ω.1.2 = ω'.1.2 ∧ (ω.2 0).2.1 = (ω'.2 0).2.1 ∧ (ω.2 0).2.2 = (ω'.2 0).2.2
    · rw [if_pos hB, Gq, if_pos hB]; ring
    · rw [if_neg hB, Gq, if_neg hB]; ring
  rw [Finset.sum_congr rfl fun ω _ => hG ω, privModel.sum_lawW_mul_fst A hT ε (Gq ω')]

/-- **The ε-mass of "second observation `o` on the time-`1` atom" is half the atom's mass**, for
every algorithm and `ε`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_atom1_obs (A : Alg Bool Bool Bool 2) (ε : ℝ) (ω' : PWorld Bool Bool Bool Unit 2)
    (o : Bool) :
    mass (privModel.lawW A hT ε) (S.nextObs 1 o ∩ S.atom 1 ω') =
      (1 / 2) * ∑ r, ∑ x, privModel.root.w r * privModel.F A hT ε r (node0 _) x * Gq ω' r x := by
  unfold mass
  rw [atom1_obs_eq, Finset.sum_filter]
  have hG : ∀ ω : PWorld Bool Bool Bool Unit 2,
      (if (ω.2 1).2.1 = o ∧
          (ω.1.2 = ω'.1.2 ∧ (ω.2 0).2.1 = (ω'.2 0).2.1 ∧ (ω.2 0).2.2 = (ω'.2 0).2.2) then
        privModel.lawW A hT ε ω else 0) =
      privModel.lawW A hT ε ω * (Gq ω' ω.1 (ω.2 0) * Hobs o (ω.2 1)) := by
    intro ω
    by_cases hA : (ω.2 1).2.1 = o
    · by_cases hB : ω.1.2 = ω'.1.2 ∧ (ω.2 0).2.1 = (ω'.2 0).2.1 ∧ (ω.2 0).2.2 = (ω'.2 0).2.2
      · rw [if_pos ⟨hA, hB⟩, Gq, Hobs, if_pos hB, if_pos hA]; ring
      · rw [if_neg (fun h => hB h.2), Gq, if_neg hB]; ring
    · rw [if_neg (fun h => hA h.1), Hobs, if_neg hA]; ring
  rw [Finset.sum_congr rfl fun ω _ => hG ω, sum_lawW_mul_both]
  simp only [F_node1_sum_obs]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **`ℙ^ε_{h₁}(o₁ = o) = 1/2`** along the ε-family of every algorithm, wherever the time-`1` atom
has non-zero ε-mass.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pr_one_eq (A : Alg Bool Bool Bool 2) (ε : ℝ) (ω' : PWorld Bool Bool Bool Unit 2) (o : Bool)
    (hne : mass (privModel.lawW A hT ε) (S.atom 1 ω') ≠ 0) :
    S.pr (privModel.lawW A hT ε) 1 (S.nextObs 1 o) ω' = 1 / 2 := by
  unfold PlaySpace.pr condProbJunk
  rw [if_neg hne, mass_atom1_obs]
  rw [mass_atom1] at hne ⊢
  rw [mul_div_assoc, div_self hne, mul_one]

/-- **The time-`1` influence of every algorithm on the probability of the second observation is `0`**
at every world: the second observation is a fair coin that ε-play does not touch.
Source: none: infrastructure (the `IP` clause of `A5Lit` at `n = 1`)
Kind: P
Fidelity: exact
Hyps: none -/
theorem IP_one_eq_zero (A : Alg Bool Bool Bool 2) (ω' : PWorld Bool Bool Bool Unit 2) (o : Bool) :
    S.IP 1 A hT o ω' = 0 := by
  unfold PlaySpace.IP
  have hpos : 0 < mass S.ℙ.w (S.atom 1 ω') :=
    mass_pos_of_mem privModel.baseW_nonneg (S.self_mem_atom 1 ω') (baseW_pos ω')
  have hev := S.eventually_mass_pos privModel.smoothLaw A hT hpos
  have heq : (fun ε => S.pr (S.law A hT ε) 1 (S.nextObs 1 o) ω') =ᶠ[nhds 0] fun _ => (1 / 2 : ℝ) := by
    filter_upwards [hev] with ε hε
    exact pr_one_eq A ε ω' o hε.ne'
  rw [heq.deriv_eq, deriv_const]

/-- **The time-`1` influence of every algorithm on conditional expected utility is `0`** at every
world and observation: the payoff is fixed by the time-`1` state.
Source: none: infrastructure (the `IEo` clause of `A5Lit` at `n = 1`)
Kind: P
Fidelity: exact
Hyps: none -/
theorem IEo_one_eq_zero (A : Alg Bool Bool Bool 2) (ω' : PWorld Bool Bool Bool Unit 2) (o : Bool) :
    S.IEo 1 A hT o ω' = 0 := by
  unfold PlaySpace.IEo
  have hpos : 0 < mass S.ℙ.w (S.atom 1 ω' ∩ S.nextObs 1 o) :=
    hall 1 (by norm_num) ω' (baseW_pos ω') o
  have hconst : ∀ ω'' ∈ S.atom 1 ω' ∩ S.nextObs 1 o, S.U ω'' = S.U ω' := fun ω'' h =>
    U_eq_of_mem_atom1 (Finset.mem_inter.1 h).1
  have hev := S.eventually_mass_pos privModel.smoothLaw A hT hpos
  have heq : (fun ε => S.cexp (S.law A hT ε) 1 (S.nextObs 1 o) S.U ω') =ᶠ[nhds 0]
      fun _ => S.U ω' := by
    filter_upwards [hev] with ε hε
    exact condExpJunk_const_on hconst hε
  rw [heq.deriv_eq, deriv_const]

/-- **Post 8's Assumption 5, as the post states it, holds in the private-signal model** (`A5Lit hT`):
at time `0` by `A5Lit_at_zero`, at time `1` because every influence of every algorithm vanishes.
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 (udt-rep-081); audit r2 (fidelity) B1
Kind: P
Fidelity: exact
Hyps: none -/
theorem A5Lit_priv : S.A5Lit hT := by
  intro n hn μ ω _ _ o
  have hn' : n ≤ 1 := hn
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hn' with rfl | rfl
  · exact A5Lit_at_zero μ ω o
  · simp only [IP_one_eq_zero, IEo_one_eq_zero, mul_zero, Finset.sum_const_zero, and_self]

/-- **The counterexample to Post 8's Theorem 1, packaged**: the private-signal model satisfies every
hypothesis of `theorem1` except the precommitment-form `A5` — smoothness, full support of the next
observation, reachability of `hT`, Assumptions 3 and 4 — and Post 8's Assumption 5 *as stated*
(`A5Lit`), yet the precommitment form fails and so does Theorem 1's conclusion at `(0, ω₀)`. Post 8's
proof uses Assumption 5 for `Ā_{h,n}` (a time-`n` precommitment), which its statement does not cover;
the gap is real, not a matter of interpretation.
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 and Assumption 5 (udt-rep-081, 082); [[udt-influence-101-findings]] F4
Kind: N+
Fidelity: exact (the hypotheses are the Lean predicates of record; `A5Lit` is Post 8's literal
Assumption 5 over the epistemic states along `hT`)
Hyps: none -/
theorem post8_theorem1_counterexample :
    S.SmoothLaw ∧ S.AllPosObs ∧ S.ReachPos hT ∧ S.A3 hT ∧ S.A4 hT ∧ S.A5Lit hT ∧ ¬ S.A5 hT ∧
      S.IE 0 privA hT ω₀ ≠
        S.cexp S.ℙ.w 0 (S.reach hT) (fun ω' => S.fS hT (S.play privA hT ω') 0 ω') ω₀ :=
  ⟨privModel.smoothLaw, hall, hRP, A3_priv, A4_priv, A5Lit_priv, not_A5, theorem1_fails⟩

end

end Priv

end Cleanroom.Udt.UdtInfluence101
