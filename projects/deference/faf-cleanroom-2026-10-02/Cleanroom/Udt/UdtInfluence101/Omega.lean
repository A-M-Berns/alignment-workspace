import Cleanroom.Udt.UdtInfluence101.Two
import Cleanroom.Udt.UdtInfluence101.Witnesses

/-!
# The Omega instance: Conservation of Expected Influence fails

Instance (II) of the mandate (T6(b), load-bearing item 4), built in repair round 1 (2026-10-02).

**The model** (`aspModel`): `O = Act = Ξ = W = Bool`, horizon `2`. The latent world `w` is Omega's
type (`true` = smart), uniform; the root state `ξ₀` is `false` (no information at time `0`). The
root node reads the agent's profile at the full-box node `hT = ⟨1, ![true]⟩` (`pn root = hT`): a
smart Omega fills the box (`o₀ = true`) iff it predicts one-boxing (`eA = δ a'`), a dumb one flips
a coin. The state `ξ₁` is a noisy report of Omega's type (`ℙ(ξ₁ = true | w) = 3/4` if smart,
`1/4` if dumb), and the agent is paid iff the report says smart: `U = [ξ₁ = true]`. Baseline and
prior belief are fair coins; the second observation is a fair coin.

**The failure** (`not_CEI`): for the always-one-box algorithm `ofAct true` at `hT`, at the witness
world `ω₀`, `𝕀^𝔼_∅(A, hT, full) = 1/8` (`IEo_eq`) while `𝔼_∅[𝕀^𝔼_{h₁}(A, hT) | full] = 0`
(`rhs_eq_zero`). The mechanism is the one Post 7 §2.1 and the mandate describe: ε-playing one-boxing
raises the predicted one-boxing rate, a smart Omega then fills the box more often, so the posterior
over Omega's type given a full box shifts toward smart, and the report `ξ₁` (hence `U`) is
correlated with the type. The action at `hT` is payoff-irrelevant, so the time-`1` influences
vanish and the failure is the shift term alone, isolated.

**Scope** (the mandate's trap): `A1` (`smoothLaw`), `A3` (`ProfileModel.A3`) and `A4` (`A4_asp`,
from the positive atoms) hold here; `AllPosObs` and `ReachPos hT` hold (`hall`, `hRP`). `A5` is
true (the root factor is affine in the profile, the action factor affine in the action, and a
time-`0` precommitment fixes both since the time-`0` atom is the whole support — which is why it
holds: with a fair private root state the precommitment form fails, `Priv.not_A5`) but `OneEps hT`
fails — the root profile read and the action at `hT` are two ε-sensitive steps on every world
reaching `hT` — so `A5_model` does not apply; it is proved by the direct two-factor computation in
`OmegaA5.lean` (`A5_asp`, repair round 2; OPEN in repair round 1).

**Finding** (F14 in [[udt-influence-101-findings]]): with the transparent-Newcomb payoffs alone
(`U = 1000·[full] + [two-box]`) and a type-blind baseline, CEI *holds* in this model — the time-`1`
expected utility is the same on the smart and dumb atoms, so the shift term is `Σ_α (d/dε ℙ(α|full))·c
= 0`. The failure needs a payoff or baseline behaviour that depends on Omega's type given the box;
`U = [ξ₁ = true]` is the minimal such payoff.
-/

namespace Cleanroom.Udt.UdtInfluence101

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree
open Home (fair fair_w coin coin_w hT hH root root_ne_hT root_ne_hH hT_ne_hH leafExt_hT_iff)
open ProfileModel

namespace Omega

noncomputable section

/-- The root draw: Omega's type uniform, the root state `false`.
Source: mandate T7 (II) (`W = {smart, dumb}`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def rootDist : FinDist (Bool × Bool) where
  w := fun r => if r.2 then 0 else 1 / 2
  nonneg := fun r => by split_ifs <;> norm_num
  sum_one := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num

/-- **The Omega model** (instance (II) of record): see the module docstring.
Source: mandate T6(b), T7 (II) (Agent-Simulates-Predictor / transparent Newcomb)
Kind: D
Fidelity: variant: the payoff is `[ξ₁ = true]` (paid iff the report says Omega is smart), not the
transparent-Newcomb payoffs, for the reason in the module docstring (F14); the report `ξ₁` is a
noisy signal of the type rather than the type itself (full support on `ξ₀ = false`). `pn` sends
`hT` and `hH` to `root` as well, so the depth-one nodes formally read the root's profile; `eA` at
step `1` is fair, so that read is vacuous
Hyps: n/a -/
def aspModel : ProfileModel Bool Bool Bool Bool 2 where
  root := rootDist
  κ := fun w _ _ _ _ _ => coin (if w then 3 / 4 else 1 / 4) (by split_ifs <;> norm_num)
    (by split_ifs <;> norm_num)
  eA := fun w k _ _ _ a' => if k.val = 0 then (if w then FinDist.delta a' else fair) else fair
  pn := fun m => if m = root then hT else root
  B := fun _ _ => fair
  π₀ := fun _ => fair
  U := fun ω => if (ω.2 0).2.2 then 1 else 0

/-- The play space of the Omega model.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
abbrev S : PlaySpace Bool Bool Bool 2 (PWorld Bool Bool Bool Bool 2) := aspModel.toPlaySpace

/-! ### Positivity: a world is positive iff its root state is `false` -/

/-- Supporting lemma `rootDist_w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem rootDist_w (r : Bool × Bool) : rootDist.w r = if r.2 then 0 else 1 / 2 := rfl

/-- Supporting lemma `root_w`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem root_w (r : Bool × Bool) : aspModel.root.w r = if r.2 then 0 else 1 / 2 := rfl

/-- Supporting lemma `obsFactor_eq` (the baseline observation factor is `1/2` at every step).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem obsFactor_eq (m' : Node Bool 2) (w : Bool) (k : Fin 2) (obs : Fin k.val → Bool)
    (acts : Fin k.val → Bool) (a o : Bool) :
    ∑ a', (aspModel.π₀ m').w a' * (aspModel.eA w k obs acts a a').w o = 1 / 2 := by
  simp only [aspModel, fair_w, Fintype.sum_bool]
  split_ifs <;> cases o <;> simp <;> norm_num

/-- Supporting lemma `κ_w_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem κ_w_pos (w : Bool) (k : Fin 2) (obs : Fin k.val → Bool) (s : Fin (k.val + 1) → Bool)
    (a o ξ : Bool) : 0 < (aspModel.κ w k obs s a o).w ξ := by
  simp only [aspModel, coin_w]
  cases w <;> cases ξ <;> norm_num

/-- Supporting lemma `baseF_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseF_pos (r : Bool × Bool) (m : Node (Letter Bool Bool Bool) 2) (ℓ : Letter Bool Bool Bool) :
    0 < aspModel.baseF r m ℓ := by
  unfold ProfileModel.baseF
  rw [obsFactor_eq]
  have h1 : (0 : ℝ) < (aspModel.B (oNode m) (statePre r.2 m)).w ℓ.1 := by simp [aspModel]
  have h3 := κ_w_pos r.1 m.1 (obsPre m) (statePre r.2 m) ℓ.1 ℓ.2.1 ℓ.2.2
  positivity

/-- **Positive worlds**: a world has positive baseline weight iff its root state is `false`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem baseW_pos_iff (ω : PWorld Bool Bool Bool Bool 2) : 0 < aspModel.baseW ω ↔ ω.1.2 = false := by
  unfold ProfileModel.baseW
  have hpath : 0 < pathLaw (aspModel.baseF ω.1) ω.2 := Finset.prod_pos fun k _ => baseF_pos _ _ _
  have hroot : aspModel.root.w ω.1 = if ω.1.2 then 0 else 1 / 2 := rfl
  rw [hroot]
  cases h : ω.1.2 <;> simp [hpath]

/-! ### Editing one observation of a world (as in the homework instance) -/

/-- The world `ω` with the observation at step `k` replaced by `o`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def setObs (ω : PWorld Bool Bool Bool Bool 2) (k : Fin 2) (o : Bool) : PWorld Bool Bool Bool Bool 2 :=
  (ω.1, Function.update ω.2 k ((ω.2 k).1, o, (ω.2 k).2.2))

/-- Supporting lemma `setObs_obs_self`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem setObs_obs_self (ω : PWorld Bool Bool Bool Bool 2) (k : Fin 2) (o : Bool) :
    pObs (setObs ω k o) k = o := by
  simp [pObs, setObs]

/-- Supporting lemma `setObs_obs_ne`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem setObs_obs_ne (ω : PWorld Bool Bool Bool Bool 2) {k j : Fin 2} (hjk : j ≠ k) (o : Bool) :
    pObs (setObs ω k o) j = pObs ω j := by
  simp [pObs, setObs, Function.update_of_ne hjk]

/-- Supporting lemma `setObs_states`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem setObs_states (ω : PWorld Bool Bool Bool Bool 2) (k : Fin 2) (o : Bool) :
    pStates (setObs ω k o) = pStates ω := by
  funext i
  unfold pStates
  refine Fin.cases rfl (fun j => ?_) i
  simp only [Fin.cases_succ, setObs]
  by_cases hjk : j = k
  · subst hjk; simp
  · simp [Function.update_of_ne hjk]

/-- Supporting lemma `atomEq_setObs`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atomEq_setObs (ω : PWorld Bool Bool Bool Bool 2) {n : ℕ} {k : Fin 2} (hnk : n ≤ k.val) (o : Bool) :
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
theorem baseW_setObs_pos {ω : PWorld Bool Bool Bool Bool 2} (hω : 0 < aspModel.baseW ω) (k : Fin 2)
    (o : Bool) : 0 < aspModel.baseW (setObs ω k o) := by
  rw [baseW_pos_iff] at hω ⊢
  exact hω

/-- Supporting lemma `mem_pReach_hT`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_pReach_hT (ω : PWorld Bool Bool Bool Bool 2) : ω ∈ pReach hT ↔ pObs ω 0 = true := by
  show ω ∈ event (fun ω => LeafExt hT (pObs ω)) ↔ _
  rw [mem_event, leafExt_hT_iff]

/-- Supporting lemma `pos_of_atomEq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pos_of_atomEq {n : ℕ} {ω ω' : PWorld Bool Bool Bool Bool 2} (hω : 0 < aspModel.baseW ω)
    (h : S.AtomEq n ω ω') : 0 < aspModel.baseW ω' := by
  rw [baseW_pos_iff] at hω ⊢
  have := h.2 0 (Nat.zero_le n)
  simpa [PlaySpace.states, ProfileModel.toPlaySpace, pStates] using this.symm.trans hω

/-! ### Regularity -/

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

/-- **Every positive atom along `hT` can still reach `hT`** (`ReachPos hT`).
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
      exact hal 0 hi
    · show pStates ω i = pStates (setObs ω 0 true) i
      rw [setObs_states]
  · show setObs ω 0 true ∈ pReach hT
    rw [mem_pReach_hT, setObs_obs_self]

/-- **Positive time-`(n+1)` atoms below `h_{n+1}`** (the hypothesis of the model's `A4`).
Source: mandate T7 (regularity of the instance)
Kind: L
Fidelity: exact
Hyps: none -/
theorem hatoms : ∀ (n : ℕ) (hn : n < hT.1.val) (ω : PWorld Bool Bool Bool Bool 2),
    0 < aspModel.baseW ω → ω ∈ pReach hT →
    ∀ ω' ∈ S.atom n ω ∩ S.nextObs n (hT.2 ⟨n, hn⟩), 0 < mass aspModel.baseW (S.atom (n + 1) ω') := by
  intro n hn ω hω _ ω' hω'
  have hpos : 0 < aspModel.baseW ω' := pos_of_atomEq hω (S.mem_atom.1 (Finset.mem_inter.1 hω').1)
  exact mass_pos_of_mem aspModel.baseW_nonneg (S.self_mem_atom (n + 1) ω') hpos

/-- **Assumption 4 holds in the Omega model** (CEG derived).
Source: `references/udt101/07-conservation-of-expected-gain.md` Assumption 4; mandate T6(a), T7
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem A4_asp : S.A4 hT := aspModel.A4 hT hatoms

/-- **Assumption 3 holds in the Omega model.**
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 3; mandate T7
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem A3_asp : S.A3 hT := aspModel.A3 hT

/-! ### The witness world and the profile of the one-boxer -/

/-- The witness world: smart Omega, root state `false`, both letters `(true, true, true)` — the box
is full and the report says smart.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ω₀ : PWorld Bool Bool Bool Bool 2 := ((true, false), fun _ => (true, true, true))

/-- Supporting lemma `ω₀_pos`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ω₀_pos : 0 < aspModel.baseW ω₀ := (baseW_pos_iff ω₀).2 rfl

/-- Supporting lemma `ω₀_reach`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem ω₀_reach : ω₀ ∈ pReach hT := (mem_pReach_hT ω₀).2 rfl

/-- Supporting lemma `hreach` (the full-box node is reached with positive probability).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hreach : 0 < mass aspModel.baseW (pReach hT) :=
  mass_pos_of_mem aspModel.baseW_nonneg ω₀_reach ω₀_pos

/-- Supporting lemma `prof_oneBox` (the profile of the always-one-box algorithm is the point mass on
one-boxing).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prof_oneBox : aspModel.prof (ofAct true) hT = FinDist.delta true := aspModel.prof_ofAct hreach true

/-- **The root step factor under ε-play of one-boxing at `hT`**, as an explicit function of the
coordinates: baseline action `1/2`; a smart Omega fills the box with probability
`(1−ε)/2 + ε` (the ε-mixed predicted one-boxing rate), a dumb one with `1/2`; the report `ξ₁` has
law `3/4`/`1/4`.
Source: mandate T6(b) ("the two sides computed as exact rationals")
Kind: L
Fidelity: exact
Hyps: none -/
theorem F_node0_eq (ε : ℝ) (w ξ₀ a₀ o₀ ξ₁ : Bool) :
    aspModel.F (ofAct true) hT ε (w, ξ₀) (node0 _) (a₀, o₀, ξ₁) =
      (1 / 2) * (if w then ((1 - ε) / 2 + ε * (if o₀ then 1 else 0)) else 1 / 2) *
        (if ξ₁ then (if w then 3 / 4 else 1 / 4) else (1 - (if w then 3 / 4 else 1 / 4))) := by
  have h0 : oNode (node0 (Letter Bool Bool Bool)) = root := oNode_node0
  have hpn : aspModel.pn root = hT := by
    show (if root = root then hT else root) = hT
    rw [if_pos rfl]
  have hB : ∀ (m : Node Bool 2) (s : Fin (m.1.val + 1) → Bool) (a : Bool),
      (aspModel.B m s).w a = 1 / 2 := fun _ _ a => fair_w a
  have hπ : ∀ (m : Node Bool 2) (a : Bool), (aspModel.π₀ m).w a = 1 / 2 := fun _ a => fair_w a
  have heA : ∀ (obs : Fin (node0 (Letter Bool Bool Bool)).1.val → Bool)
      (acts : Fin (node0 (Letter Bool Bool Bool)).1.val → Bool) (a a' : Bool),
      aspModel.eA w (node0 (Letter Bool Bool Bool)).1 obs acts a a' =
        if w then FinDist.delta a' else fair := fun obs acts a a' => by
    show (if ((node0 (Letter Bool Bool Bool)).1).val = 0 then (if w then FinDist.delta a' else fair)
      else fair) = _
    exact if_pos rfl
  have hκ : ∀ (k : Fin 2) (obs : Fin k.val → Bool) (s : Fin (k.val + 1) → Bool) (a o ξ : Bool),
      (aspModel.κ w k obs s a o).w ξ =
        if ξ then (if w then 3 / 4 else 1 / 4) else (1 - (if w then 3 / 4 else 1 / 4)) :=
    fun _ _ _ _ _ ξ => by simp only [aspModel, coin_w]
  simp only [ProfileModel.F, ProfileModel.algW, ProfileModel.profW, h0, if_neg root_ne_hT, hpn,
    eq_self_iff_true, if_true, prof_oneBox, FinDist.delta_w, hB, hπ, heA, hκ, Fintype.sum_bool,
    fair_w]
  cases w <;> cases o₀ <;> cases ξ₁ <;> norm_num <;> ring_nf

/-! ### The conditional expected utility given a full box, along the ε-family -/

/-- Supporting lemma `mem_nextObs0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_nextObs0 (ω : PWorld Bool Bool Bool Bool 2) (o : Bool) :
    ω ∈ S.nextObs 0 o ↔ (ω.2 0).2.1 = o := by
  rw [S.mem_nextObs (show (0 : ℕ) < 2 by norm_num)]
  rfl

/-- Supporting lemma `mem_E_iff` (the event "time-`0` atom of `ω₀` and a full box").
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mem_E_iff (ω : PWorld Bool Bool Bool Bool 2) :
    ω ∈ S.atom 0 ω₀ ∩ S.nextObs 0 true ↔ ω.1.2 = false ∧ (ω.2 0).2.1 = true := by
  rw [Finset.mem_inter, S.mem_atom, mem_nextObs0]
  constructor
  · rintro ⟨hat, hob⟩
    refine ⟨?_, hob⟩
    have := hat.2 0 le_rfl
    exact this.symm
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i hi => absurd hi (Nat.not_lt_zero _), fun i hi => ?_⟩, h2⟩
    have hi0 : i = 0 := Fin.ext (Nat.le_zero.1 hi)
    subst hi0
    exact h1.symm

/-- Supporting lemma `E_eq`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem E_eq : S.atom 0 ω₀ ∩ S.nextObs 0 true =
    univ.filter (fun ω : PWorld Bool Bool Bool Bool 2 => ω.1.2 = false ∧ (ω.2 0).2.1 = true) := by
  ext ω
  rw [Finset.mem_filter, mem_E_iff]
  simp only [Finset.mem_univ, true_and]

/-- The summand of the numerator as a function of the root draw and the first letter.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def G₁ (r : Bool × Bool) (x : Letter Bool Bool Bool) : ℝ :=
  if r.2 = false ∧ x.2.1 = true then (if x.2.2 then 1 else 0) else 0

/-- The summand of the denominator as a function of the root draw and the first letter.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def G₂ (r : Bool × Bool) (x : Letter Bool Bool Bool) : ℝ :=
  if r.2 = false ∧ x.2.1 = true then 1 else 0

/-- **The ε-mass of "full box and the report says smart"**: `1/4 + 3ε/16`.
Source: mandate T6(b) ("exact rationals")
Kind: L
Fidelity: exact
Hyps: none -/
theorem num_eq (ε : ℝ) :
    ∑ ω ∈ S.atom 0 ω₀ ∩ S.nextObs 0 true, aspModel.lawW (ofAct true) hT ε ω * aspModel.U ω =
      1 / 4 + 3 * ε / 16 := by
  rw [E_eq, Finset.sum_filter]
  have hG : ∀ ω : PWorld Bool Bool Bool Bool 2,
      (if ω.1.2 = false ∧ (ω.2 0).2.1 = true then aspModel.lawW (ofAct true) hT ε ω * aspModel.U ω
        else 0) = aspModel.lawW (ofAct true) hT ε ω * G₁ ω.1 (ω.2 0) := by
    intro ω
    simp only [G₁, aspModel]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun ω _ => hG ω, aspModel.sum_lawW_mul_fst (ofAct true) hT ε G₁]
  simp only [G₁, Fintype.sum_prod_type, Fintype.sum_bool, F_node0_eq, root_w]
  norm_num
  ring

/-- **The ε-mass of "full box"**: `1/2 + ε/4`.
Source: mandate T6(b) ("exact rationals")
Kind: L
Fidelity: exact
Hyps: none -/
theorem den_eq (ε : ℝ) :
    mass (aspModel.lawW (ofAct true) hT ε) (S.atom 0 ω₀ ∩ S.nextObs 0 true) = 1 / 2 + ε / 4 := by
  unfold mass
  rw [E_eq, Finset.sum_filter]
  have hG : ∀ ω : PWorld Bool Bool Bool Bool 2,
      (if ω.1.2 = false ∧ (ω.2 0).2.1 = true then aspModel.lawW (ofAct true) hT ε ω else 0) =
      aspModel.lawW (ofAct true) hT ε ω * G₂ ω.1 (ω.2 0) := by
    intro ω
    simp only [G₂]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun ω _ => hG ω, aspModel.sum_lawW_mul_fst (ofAct true) hT ε G₂]
  simp only [G₂, Fintype.sum_prod_type, Fintype.sum_bool, F_node0_eq, root_w]
  norm_num
  ring

/-- Supporting lemma `cexp_full_eq` (the conditional expected utility given a full box along the
ε-family, with its junk point).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_full_eq (ε : ℝ) :
    S.cexp (aspModel.lawW (ofAct true) hT ε) 0 (S.nextObs 0 true) aspModel.U ω₀ =
      if (1 / 2 + ε / 4 : ℝ) = 0 then 0 else (1 / 4 + 3 * ε / 16) / (1 / 2 + ε / 4) := by
  unfold PlaySpace.cexp condExpJunk
  rw [den_eq, num_eq]

/-- **The influence of one-boxing on the expected utility given a full box is `1/8`.**
Source: mandate T6(b); `references/udt101/07-conservation-of-expected-gain.md` §2.1
Kind: P
Fidelity: exact
Hyps: none -/
theorem IEo_eq : S.IEo 0 (ofAct true) hT true ω₀ = 1 / 8 := by
  unfold PlaySpace.IEo
  have hev : ∀ᶠ ε in nhds (0 : ℝ), (1 / 2 + ε / 4 : ℝ) ≠ 0 :=
    ContinuousAt.eventually_ne (by fun_prop) (by norm_num)
  have heq : (fun ε => S.cexp (S.law (ofAct true) hT ε) 0 (S.nextObs 0 true) S.U ω₀) =ᶠ[nhds 0]
      fun ε => (1 / 4 + 3 * ε / 16) / (1 / 2 + ε / 4) := by
    filter_upwards [hev] with ε hε
    show S.cexp (aspModel.lawW (ofAct true) hT ε) 0 (S.nextObs 0 true) aspModel.U ω₀ = _
    rw [cexp_full_eq, if_neg hε]
  rw [heq.deriv_eq]
  have hN : HasDerivAt (fun ε : ℝ => 1 / 4 + 3 * ε / 16) (3 * 1 / 16) 0 :=
    (((hasDerivAt_id' (x := (0 : ℝ))).const_mul 3).div_const 16).const_add (1 / 4)
  have hD : HasDerivAt (fun ε : ℝ => 1 / 2 + ε / 4) (1 / 4) 0 :=
    ((hasDerivAt_id' (x := (0 : ℝ))).div_const 4).const_add (1 / 2)
  have hq : HasDerivAt (fun ε : ℝ => (1 / 4 + 3 * ε / 16) / (1 / 2 + ε / 4))
      ((3 * 1 / 16 * (1 / 2 + (0 : ℝ) / 4) - (1 / 4 + 3 * (0 : ℝ) / 16) * (1 / 4)) /
        (1 / 2 + (0 : ℝ) / 4) ^ 2) 0 :=
    hN.div hD (by norm_num)
  rw [hq.deriv]
  norm_num

/-! ### The time-`1` influences vanish: the payoff is fixed by the time-`1` epistemic state -/

/-- Supporting lemma `condExpJunk_zero_of_pos` (a function vanishing on the positive worlds of `E`
has conditional expectation `0`, junk included).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem _root_.Cleanroom.Udt.UdtPolicyCalc.condExpJunk_zero_of_pos {X : Type} {w f : X → ℝ}
    (hw : ∀ x, 0 ≤ w x) {E : Finset X} (hf : ∀ x ∈ E, 0 < w x → f x = 0) :
    condExpJunk w f E 0 = 0 := by
  unfold condExpJunk
  split_ifs with h
  · rfl
  · rw [div_eq_zero_iff]
    left
    refine Finset.sum_eq_zero fun x hx => ?_
    rcases (hw x).lt_or_eq with hpos | hzero
    · rw [hf x hx hpos, mul_zero]
    · rw [← hzero, zero_mul]

/-- **The time-`1` influence of one-boxing is zero at every positive world**: the payoff `[ξ₁ = true]`
is constant on every time-`1` atom.
Source: mandate T6(b)
Kind: P
Fidelity: exact
Hyps: none -/
theorem IE_one_eq_zero {ω' : PWorld Bool Bool Bool Bool 2} (hω' : 0 < aspModel.baseW ω') :
    S.IE 1 (ofAct true) hT ω' = 0 := by
  unfold PlaySpace.IE
  have hpos : 0 < mass S.ℙ.w (S.atom 1 ω' ∩ univ) := by
    rw [Finset.inter_univ]
    exact mass_pos_of_mem aspModel.baseW_nonneg (S.self_mem_atom 1 ω') hω'
  have hconst : ∀ ω'' ∈ S.atom 1 ω' ∩ univ, S.U ω'' = S.U ω' := by
    intro ω'' h
    have hat := S.mem_atom.1 (Finset.mem_inter.1 h).1
    have hs : (ω''.2 0).2.2 = (ω'.2 0).2.2 := (hat.2 1 le_rfl).symm
    show (if (ω''.2 0).2.2 then (1 : ℝ) else 0) = if (ω'.2 0).2.2 then 1 else 0
    rw [hs]
  have hev := S.eventually_mass_pos aspModel.smoothLaw (ofAct true) hT hpos
  have heq : (fun ε => S.cexp (S.law (ofAct true) hT ε) 1 univ S.U ω') =ᶠ[nhds 0] fun _ => S.U ω' := by
    filter_upwards [hev] with ε hε
    exact condExpJunk_const_on hconst hε
  rw [heq.deriv_eq, deriv_const]

/-- **The right-hand side of CEI vanishes**: `𝔼_∅[𝕀^𝔼_{h₁}(one-box, hT) | full] = 0`.
Source: mandate T6(b)
Kind: P
Fidelity: exact
Hyps: none -/
theorem rhs_eq_zero :
    S.cexp S.ℙ.w 0 (S.nextObs 0 true) (fun ω' => S.IE 1 (ofAct true) hT ω') ω₀ = 0 := by
  unfold PlaySpace.cexp
  exact condExpJunk_zero_of_pos aspModel.baseW_nonneg fun ω' _ hpos => IE_one_eq_zero hpos

/-- **Conservation of Expected Influence fails** in the Omega model, for the always-one-box
algorithm at the full-box node: the left side is `1/8`, the right side `0`. The gap is the shift
term of `IEo_decomp`: ε-playing one-boxing raises a smart Omega's box-filling rate, so a full box
becomes better evidence of a smart Omega, and the payoff tracks the report of Omega's type.
Source: `references/udt101/07-conservation-of-expected-gain.md` §2.1 (udt-rep-085); mandate T6(b) (load-bearing 4)
Kind: N+
Fidelity: exact (Post 7's CEI at `n = 0`, `o = h₁`, refuted on a model satisfying `A1`, `A3`, `A4`,
`AllPosObs`, `ReachPos hT`; `A5` proved there too, `A5_asp` in `OmegaA5.lean`)
Hyps: none -/
theorem not_CEI : ¬ S.CEI 0 (ofAct true) hT ω₀ := by
  intro hc
  have h := hc (show 0 < hT.1.val by decide)
  change S.IEo 0 (ofAct true) hT true ω₀ =
    S.cexp S.ℙ.w 0 (S.nextObs 0 true) (fun ω' => S.IE 1 (ofAct true) hT ω') ω₀ at h
  rw [IEo_eq, rhs_eq_zero] at h
  norm_num at h

/-- **Assumption 1 holds in the Omega model.**
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 1
Kind: C
Fidelity: exact
Hyps: (a) all -/
theorem A1_asp : S.A1 := aspModel.A1

end

end Omega

end Cleanroom.Udt.UdtInfluence101
