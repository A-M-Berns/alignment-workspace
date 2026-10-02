import Cleanroom.Fixpoint.FixOraclesCorresp.OracleExists
import EconCSLib.GameTheory.StrategicGame.MixedStrategy
import SafeParetoImprovements.Game
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# `Cleanroom.Fixpoint.FixOraclesCorresp.NashReflective`: Theorem 4.1 — Nash ⟺ reflectivity

Targets 12–13 (fixpoint-lit-2-005/006), over EconCSLib's mixed Nash equilibrium `IsMixedNashEq`.

A finite **two-action game** is `twoActionGame u : StrategicGame N ℝ` (every player's strategy type is
`Fin 2`, payoff `u`); the FAF-form definition of record `twoActionFAF u : SafeParetoImprovements.Game N
(fun _ => Fin 2)` with `S i = univ` is stated alongside (the bridge to its `toStrategic` form is the
`L` lemma `isMixedNashEq_twoActionFAF_iff` in `GameBridge.lean`). A mixed profile `σ` is read as the
answer vector `toCube σ i = (σ i).val 1` (the probability of action `1`); `ofCube` goes back.

`gain u i x` is the expected-payoff *difference* of action `1` over action `0` for player `i` against
the independent mixture `x` of the others (it does not depend on `x i`: `gain_update`), and
`evOf u i x = (gain u i x + 1) / 2` is FTC §3's machine `Eᵢ` (Theorem 3.1's sign identity is
`reflective_cdt_iff`, target 12). **Headline** (`isMixedNashEq_iff_reflective`):
`IsMixedNashEq (twoActionGame u) σ ↔ Reflective (evOf u) (fun _ => 1/2) (toCube σ)`. Corollaries:
every finite two-action game has a mixed Nash equilibrium (`exists_isMixedNashEq`, from
`exists_reflective`, grade (a)); every Nash profile is induced by a reflective answer vector.

**Disclosure**: the paper's game is played by oracle machines calling `O(Eᵢ, ½)`; here the players'
randomization *is* the answer vector, so `Fidelity: variant: abstract, two actions`. The paper's
multi-action reduction (§3, "compare action 0 to action 1, then …") is out of scope; the paper's
direction (b) uses Theorem 2.1(ii) to fix answers off `R`, which the abstract carrier has no room for.
The notes' "fixed points = correlated equilibria" is **not** what this theorem says: the equilibria are
Nash, with *independent* randomization across players (finding F5).
-/

namespace Cleanroom.Fixpoint.FixOraclesCorresp

open Set StrategicGame

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- **A finite two-action game, direct form**: every player's strategies are `Fin 2` and the payoff at
the pure profile `τ` is `u τ`.
Source: FTC 2015 Theorem 4.1 ("the n-player normal-form game … two pure strategies");
[[fixpoint-lit-2-inventory]] 006
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev twoActionGame (u : (N → Fin 2) → N → ℝ) : StrategicGame N ℝ where
  strategy _ := Fin 2
  payoff := u

/-- **The same game as FAF's `SafeParetoImprovements.Game`** over the action universe `fun _ => Fin 2`
with every action set `S i = univ` (definition of record; the `udt-policy-calc` pattern).
Source: FAF `SafeParetoImprovements/Game.lean:43`; mandate target 13
Kind: D
Fidelity: exact
Hyps: n/a -/
def twoActionFAF (u : (N → Fin 2) → N → ℝ) : SafeParetoImprovements.Game N (fun _ => Fin 2) where
  S _ := Finset.univ
  nonempty _ := Finset.univ_nonempty
  u := u

/-- The mixed strategy on `Fin 2` with probability `t` of action `1`: `![1 - t, t]`.
Source: none: infrastructure (cf. `fix-kakutani`'s `WitnessSimplex.ofProb`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def wt (t : ℝ) : Fin 2 → ℝ := ![1 - t, t]

/-- `wt t ∈ Δ(Fin 2)` for `t ∈ [0, 1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wt_mem_stdSimplex {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : wt t ∈ stdSimplex ℝ (Fin 2) := by
  refine ⟨fun i => ?_, ?_⟩
  · fin_cases i <;> simp [wt] <;> linarith [ht.1, ht.2]
  · simp [wt, Fin.sum_univ_two]

/-- `∑ s, wt t s = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_wt (t : ℝ) : ∑ s, wt t s = 1 := by simp [wt, Fin.sum_univ_two]

/-- The pure strategy `s` as a weight vector: `pureWt s t = if t = s then 1 else 0` (the `.val` of
EconCSLib's `pureToMixed s`).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def pureWt (s : Fin 2) : Fin 2 → ℝ := fun t => if t = s then 1 else 0

/-- `∑ t, pureWt s t = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_pureWt (s : Fin 2) : ∑ t, pureWt s t = 1 := by
  simp [pureWt, Finset.sum_ite_eq']

/-- `wt` is continuous in `t` for each coordinate.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem continuous_wt (s : Fin 2) : Continuous fun t : ℝ => wt t s := by
  fin_cases s <;> simp [wt] <;> fun_prop

/-- **The answer vector of a mixed profile**: `toCube σ i = (σ i).val 1`, player `i`'s probability of
action `1` (the paper's `sᵢ := P(Aᵢ^O() = 1)`).
Source: FTC 2015 Theorem 4.1 ("the mixed strategy profile given by `sᵢ := P(Aᵢ^O() = 1)`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def toCube {u : (N → Fin 2) → N → ℝ} (σ : MixedProfile (twoActionGame u)) : N → ℝ :=
  fun i => (σ i).val 1

omit [Fintype N] [DecidableEq N] in
/-- `toCube σ ∈ [0, 1]^N`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem toCube_mem_cube {u : (N → Fin 2) → N → ℝ} (σ : MixedProfile (twoActionGame u)) :
    toCube σ ∈ cube N := by
  intro i _
  have h := (σ i).2
  have h0 := h.1 0
  have h1 := h.1 1
  have hs := h.2
  simp only [Fin.sum_univ_two] at hs
  exact ⟨h1, by simp only [toCube]; linarith⟩

/-- **The mixed profile of an answer vector** in the cube.
Source: FTC 2015 §5 (`O_x`); mandate target 13 (`ofCube`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def ofCube (u : (N → Fin 2) → N → ℝ) (x : N → ℝ) (hx : x ∈ cube N) :
    MixedProfile (twoActionGame u) :=
  fun i => ⟨wt (x i), wt_mem_stdSimplex (hx i (mem_univ _))⟩

omit [Fintype N] [DecidableEq N] in
/-- `toCube (ofCube x) = x`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem toCube_ofCube (u : (N → Fin 2) → N → ℝ) {x : N → ℝ} (hx : x ∈ cube N) :
    toCube (ofCube u x hx) = x := by
  ext i; simp [toCube, ofCube, wt]

omit [Fintype N] [DecidableEq N] in
/-- A mixed strategy on `Fin 2` is `wt` of its probability of `1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem wt_toCube {u : (N → Fin 2) → N → ℝ} (σ : MixedProfile (twoActionGame u)) (i : N) :
    wt (toCube σ i) = (σ i).val := by
  have hs := (σ i).2.2
  simp only [Fin.sum_univ_two] at hs
  ext j
  fin_cases j <;> simp [wt, toCube]
  all_goals linarith

/-! ### Expected payoff on raw weight vectors -/

/-- Expected payoff of player `j` at a family of weight vectors `ρ : N → Fin 2 → ℝ` (not required to
be probabilities): `∑ τ, (∏ i, ρ i (τ i)) * u τ j`. On mixed profiles it *is* EconCSLib's
`expectedPayoff` (`expectedPayoff_eq_rawEP`).
Source: none: infrastructure (EconCSLib `MixedStrategy.lean:150` `expectedPayoff`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def rawEP (u : (N → Fin 2) → N → ℝ) (ρ : N → Fin 2 → ℝ) (j : N) : ℝ :=
  ∑ τ : N → Fin 2, (∏ i, ρ i (τ i)) * u τ j

/-- EconCSLib's `expectedPayoff` on the two-action game is `rawEP` of the profile's weight vectors.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem expectedPayoff_eq_rawEP (u : (N → Fin 2) → N → ℝ) (σ : MixedProfile (twoActionGame u))
    (j : N) : expectedPayoff (twoActionGame u) σ j = rawEP u (fun i => (σ i).val) j := rfl

/-- The expected payoff of player `i` when deviating to the pure action `s` (EconCSLib's
`expectedPayoff G (deviateMixed G σ i s) i`, named so that the case analyses below can refer to it).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
noncomputable def devEP (u : (N → Fin 2) → N → ℝ) (σ : MixedProfile (twoActionGame u)) (i : N) (s : Fin 2) : ℝ :=
  expectedPayoff (twoActionGame u) (deviateMixed (twoActionGame u) σ i s) i

/-- `IsMixedNashEq` in terms of `devEP`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem isMixedNashEq_iff_devEP (u : (N → Fin 2) → N → ℝ) (σ : MixedProfile (twoActionGame u)) :
    IsMixedNashEq (twoActionGame u) σ ↔
      ∀ (i : N) (s : Fin 2), devEP u σ i s ≤ expectedPayoff (twoActionGame u) σ i := Iff.rfl

omit [Fintype N] in
/-- The weight vectors of a deviation are the `update` of the weight vectors.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem val_deviateMixed (u : (N → Fin 2) → N → ℝ) (σ : MixedProfile (twoActionGame u)) (i : N)
    (s : Fin 2) :
    (fun j => (deviateMixed (twoActionGame u) σ i s j).val) =
      Function.update (fun j => (σ j).val) i (pureWt s) := by
  funext j
  by_cases h : j = i
  · subst h
    simp only [deviateMixed, Function.update_self]
    rfl
  · simp [deviateMixed, Function.update_of_ne h]

/-- `devEP` as an explicit sum with player `i`'s factor pulled out.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem devEP_eq (u : (N → Fin 2) → N → ℝ) (σ : MixedProfile (twoActionGame u)) (i : N)
    (s : Fin 2) :
    devEP u σ i s =
      ∑ τ : N → Fin 2, (pureWt s (τ i) * ∏ j ∈ Finset.univ.erase i, (σ j).val (τ j)) * u τ i := by
  unfold devEP
  rw [expectedPayoff_eq_rawEP, val_deviateMixed]
  unfold rawEP
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- The expected payoff as an explicit sum with player `i`'s factor pulled out.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem expectedPayoff_eq_split (u : (N → Fin 2) → N → ℝ) (σ : MixedProfile (twoActionGame u))
    (i : N) :
    expectedPayoff (twoActionGame u) σ i =
      ∑ τ : N → Fin 2, ((σ i).val (τ i) * ∏ j ∈ Finset.univ.erase i, (σ j).val (τ j)) * u τ i := by
  rw [expectedPayoff_eq_rawEP]
  unfold rawEP
  refine Finset.sum_congr rfl fun τ _ => ?_
  congr 1
  exact (Finset.mul_prod_erase Finset.univ (fun j => (σ j).val (τ j)) (Finset.mem_univ i)).symm

/-- **Linearity of the expected payoff in one player's strategy**: player `i`'s expected payoff is the
`σ i`-average of the expected payoffs of `i`'s pure deviations. This is the one general fact about
`IsMixedNashEq` the package needs (the paper's "a pure strategy `aᵢ` can only be assigned positive
probability if it maximizes …").
Source: FTC 2015 Theorem 4.1 (proof); EconCSLib `MixedStrategy.lean` ("by linearity of expected
payoff in each player's mixed strategy"); MSZ 5.5
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem expectedPayoff_eq_sum_deviate (u : (N → Fin 2) → N → ℝ)
    (σ : MixedProfile (twoActionGame u)) (i : N) :
    expectedPayoff (twoActionGame u) σ i = ∑ s, (σ i).val s * devEP u σ i s := by
  simp only [devEP_eq, expectedPayoff_eq_split, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp only [pureWt]
  rw [Finset.sum_eq_single (τ i)]
  · rw [if_pos rfl]; ring
  · intro s _ hs
    rw [if_neg (Ne.symm hs)]; ring
  · intro h; exact absurd (Finset.mem_univ _) h

/-! ### The gain and the evaluation maps -/

/-- **The gain of action `1` over action `0`** for player `i` against the answer vector `x`: the
expected payoff of deviating to `1` minus that of deviating to `0`, the other players mixing
independently with probabilities `x j` of action `1`. Does not depend on `x i` (`gain_update`).
Source: FTC 2015 §3 (`E[u(W_A(1))] − E[u(W_A(0))]`), §4 (`Wᵢ(aᵢ) := F(aᵢ, A₋ᵢ)`);
[[fixpoint-lit-2-inventory]] 006 (`Δᵢ(s₋ᵢ)`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def gain (u : (N → Fin 2) → N → ℝ) (i : N) (x : N → ℝ) : ℝ :=
  rawEP u (Function.update (fun j => wt (x j)) i (pureWt 1)) i -
    rawEP u (Function.update (fun j => wt (x j)) i (pureWt 0)) i

/-- `gain u i` does not depend on the `i`-th coordinate of `x`.
Source: mandate target 13 ("independent of `σ i` (prove)")
Kind: L
Fidelity: n/a
Hyps: none -/
theorem gain_update (u : (N → Fin 2) → N → ℝ) (i : N) (x : N → ℝ) (t : ℝ) :
    gain u i (Function.update x i t) = gain u i x := by
  have : ∀ s, Function.update (fun j => wt (Function.update x i t j)) i (pureWt s) =
      Function.update (fun j => wt (x j)) i (pureWt s) := by
    intro s; funext j
    by_cases h : j = i
    · subst h; simp
    · simp [Function.update_of_ne h]
  simp only [gain, this]

/-- The gain at a profile's answer vector is the difference of the two deviation payoffs.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem gain_toCube (u : (N → Fin 2) → N → ℝ) (σ : MixedProfile (twoActionGame u)) (i : N) :
    gain u i (toCube σ) = devEP u σ i 1 - devEP u σ i 0 := by
  simp only [gain, devEP, expectedPayoff_eq_rawEP, val_deviateMixed]
  have : (fun j => wt (toCube σ j)) = fun j => (σ j).val := funext (wt_toCube σ)
  rw [this]

/-- **The evaluation maps of a two-action game** (FTC §3's machine `Eᵢ`, output probability
`(u(W(1)) − u(W(0)) + 1)/2` with the utilities' difference replaced by the gain):
`evOf u i x = (gain u i x + 1) / 2`.
Source: FTC 2015 §3 (`E^O() := flip((u(W_A(1)) − u(W_A(0)) + 1)/2)`), §4 (`Eᵢ`)
Kind: D
Fidelity: variant: abstract (the machine's output probability as a function of the answer vector)
Hyps: n/a -/
noncomputable def evOf (u : (N → Fin 2) → N → ℝ) (i : N) (x : N → ℝ) : ℝ := (gain u i x + 1) / 2

/-- `gain u i` is continuous (a polynomial in `x`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem continuous_gain (u : (N → Fin 2) → N → ℝ) (i : N) : Continuous (gain u i) := by
  have key : ∀ s : Fin 2, Continuous fun x : N → ℝ =>
      rawEP u (Function.update (fun j => wt (x j)) i (pureWt s)) i := by
    intro s
    unfold rawEP
    refine continuous_finsetSum _ fun τ _ => Continuous.mul ?_ continuous_const
    refine continuous_finsetProd _ fun j _ => ?_
    by_cases h : j = i
    · subst h; simp only [Function.update_self]; exact continuous_const
    · simp only [Function.update_of_ne h]
      exact (continuous_wt (τ j)).comp (continuous_apply j)
  exact (key 1).sub (key 0)

/-- `evOf u i` is continuous, in particular on the cube.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem continuousOn_evOf (u : (N → Fin 2) → N → ℝ) (i : N) : ContinuousOn (evOf u i) (cube N) :=
  (((continuous_gain u i).add continuous_const).div_const 2).continuousOn

/-! ### Target 12: Theorem 3.1, the CDT agent as a query (a sign identity) -/

/-- **Theorem 3.1, abstract**: reflectivity at threshold `1/2` for the evaluation map
`(u₁ x − u₀ x + 1)/2` says exactly "answer `1` if `u₁ > u₀`, `0` if `u₁ < u₀`, ties free" — the agent
`A^O() := O(E, ½)` returns a utility-maximizing action. A sign identity (near-squeeze, as the
inventory flags); it is the bridge the headline uses.
Source: FTC 2015 Theorem 3.1; [[fixpoint-lit-2-inventory]] 005
Kind: L
Fidelity: variant: abstract (utilities as functions of the answer vector)
Hyps: none -/
theorem reflective_cdt_iff {I : Type*} [Fintype I] (u₁ u₀ : I → (I → ℝ) → ℝ) (x : I → ℝ) :
    Reflective (fun i x => (u₁ i x - u₀ i x + 1) / 2) (fun _ => 1 / 2) x ↔
      ∀ i, (u₀ i x < u₁ i x → x i = 1) ∧ (u₁ i x < u₀ i x → x i = 0) := by
  unfold Reflective
  refine forall_congr' fun i => ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (by linarith), fun h => h2 (by linarith)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun h => h1 (by linarith), fun h => h2 (by linarith)⟩

/-! ### Target 13: Theorem 4.1 -/

/-- At a mixed Nash equilibrium of a two-action game, if action `1` is strictly better than action
`0` for player `i` then `i` plays `1` with probability `1` (and symmetrically). From
`expectedPayoff_eq_sum_deviate`.
Source: FTC 2015 Theorem 4.1 (proof: "a pure strategy `aᵢ` can only be assigned positive probability
if it maximizes …")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem isMixedNashEq_support (u : (N → Fin 2) → N → ℝ) {σ : MixedProfile (twoActionGame u)}
    (h : IsMixedNashEq (twoActionGame u) σ) (i : N) :
    (devEP u σ i 0 < devEP u σ i 1 → (σ i).val 1 = 1) ∧
    (devEP u σ i 1 < devEP u σ i 0 → (σ i).val 1 = 0) := by
  have hlin := expectedPayoff_eq_sum_deviate u σ i
  simp only [Fin.sum_univ_two] at hlin
  have hsum := (σ i).2.2
  simp only [Fin.sum_univ_two] at hsum
  have h0 := (σ i).2.1 0
  have h1 := (σ i).2.1 1
  have hn1 : devEP u σ i 1 ≤ expectedPayoff (twoActionGame u) σ i := h i 1
  have hn0 : devEP u σ i 0 ≤ expectedPayoff (twoActionGame u) σ i := h i 0
  constructor
  · intro hlt
    by_contra hne
    have hpos : 0 < (σ i).val 0 := by
      rcases lt_or_eq_of_le h0 with h' | h'
      · exact h'
      · exact absurd (by linarith : (σ i).val 1 = 1) hne
    have : 0 < (σ i).val 0 * (devEP u σ i 1 - devEP u σ i 0) := mul_pos hpos (by linarith)
    rw [show (σ i).val 1 = 1 - (σ i).val 0 by linarith] at hlin
    nlinarith
  · intro hlt
    by_contra hne
    have hpos : 0 < (σ i).val 1 := lt_of_le_of_ne h1 (Ne.symm hne)
    have : 0 < (σ i).val 1 * (devEP u σ i 0 - devEP u σ i 1) := mul_pos hpos (by linarith)
    rw [show (σ i).val 0 = 1 - (σ i).val 1 by linarith] at hlin
    nlinarith

/-- **Target 13, Theorem 4.1 (abstract, two actions): Nash ⟺ reflectivity.** A mixed profile `σ` of
the two-action game `u` is a mixed Nash equilibrium (EconCSLib's `IsMixedNashEq`) iff its answer
vector `toCube σ` is reflective for the evaluation maps `evOf u` at thresholds `1/2`.
⟹: `isMixedNashEq_support`. ⟸: for each deviation, case on the sign of the gain and use
`expectedPayoff_eq_sum_deviate`.
Source: FTC 2015 Theorem 4.1; [[fixpoint-lit-2-inventory]] 006
Kind: P
Fidelity: variant: abstract, two actions (the players' randomization is the answer vector; the
paper's multi-action reduction is out of scope; see the module docstring); stronger: real payoffs
with no range condition (the paper takes utilities in `[0, 1]` so that `E_i`'s flip probability is a
probability; `evOf u` needs no such bound)
Hyps: (a) none; (c) evaluation maps in place of oracle machines -/
theorem isMixedNashEq_iff_reflective (u : (N → Fin 2) → N → ℝ)
    (σ : MixedProfile (twoActionGame u)) :
    IsMixedNashEq (twoActionGame u) σ ↔ Reflective (evOf u) (fun _ => 1 / 2) (toCube σ) := by
  have hev : Reflective (evOf u) (fun _ => 1 / 2) (toCube σ) ↔
      ∀ i, (devEP u σ i 0 < devEP u σ i 1 → (σ i).val 1 = 1) ∧
        (devEP u σ i 1 < devEP u σ i 0 → (σ i).val 1 = 0) := by
    unfold Reflective
    refine forall_congr' fun i => ?_
    simp only [evOf, gain_toCube, toCube]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by linarith), fun h => h2 (by linarith)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 (by linarith), fun h => h2 (by linarith)⟩
  rw [hev]
  constructor
  · exact fun h i => isMixedNashEq_support u h i
  · intro h
    rw [isMixedNashEq_iff_devEP]
    intro who s'
    have hlin := expectedPayoff_eq_sum_deviate u σ who
    simp only [Fin.sum_univ_two] at hlin
    have hsum := (σ who).2.2
    simp only [Fin.sum_univ_two] at hsum
    have h0 := (σ who).2.1 0
    have h1 := (σ who).2.1 1
    obtain ⟨hA, hB⟩ := h who
    rw [hlin]
    rcases lt_trichotomy (devEP u σ who 0) (devEP u σ who 1) with hlt | heq | hgt
    · have hv1 := hA hlt
      have hv0 : (σ who).val 0 = 0 := by linarith
      rw [hv0, hv1]
      fin_cases s' <;> simp
      all_goals linarith
    · rw [heq, ← add_mul, hsum, one_mul]
      fin_cases s' <;> simp [heq]
    · have hv1 := hB hgt
      have hv0 : (σ who).val 0 = 1 := by linarith
      rw [hv0, hv1]
      fin_cases s' <;> simp
      all_goals linarith

/-- **Corollary (a): every finite two-action game has a mixed Nash equilibrium**, from
`exists_reflective` (Kakutani, grade (a) via `fix-kakutani`) and the headline.
Source: FTC 2015 §4 ("every reflective oracle (which exists by Theorem 2.1) gives rise to a Nash
equilibrium"); [[fixpoint-lit-2-inventory]] 006 (a)
Kind: C
Fidelity: variant: abstract, two actions
Hyps: (a) all; (c) evaluation maps in place of oracle machines -/
theorem exists_isMixedNashEq (u : (N → Fin 2) → N → ℝ) :
    ∃ σ : MixedProfile (twoActionGame u), IsMixedNashEq (twoActionGame u) σ := by
  obtain ⟨x, hx, hrefl⟩ := exists_reflective (evOf u) (continuousOn_evOf u) (fun _ => 1 / 2)
  refine ⟨ofCube u x hx, ?_⟩
  rw [isMixedNashEq_iff_reflective, toCube_ofCube]
  exact hrefl

/-- **Corollary (b): every Nash profile is induced by a reflective answer vector** (its own
`toCube σ`). The paper's version also prescribes the oracle's answers off `R` via Theorem 2.1(ii),
which the abstract carrier has no room for.
Source: FTC 2015 §4 ("for any Nash equilibrium … there is a reflective oracle such that
`P(Aᵢ^O() = 1) = sᵢ`"); [[fixpoint-lit-2-inventory]] 006 (b)
Kind: L
Fidelity: variant: abstract, two actions; weaker: no off-`R` clause
Hyps: none; (c) evaluation maps in place of oracle machines -/
theorem exists_reflective_of_isMixedNashEq (u : (N → Fin 2) → N → ℝ)
    {σ : MixedProfile (twoActionGame u)} (h : IsMixedNashEq (twoActionGame u) σ) :
    ∃ x ∈ cube N, Reflective (evOf u) (fun _ => 1 / 2) x ∧ toCube σ = x :=
  ⟨toCube σ, toCube_mem_cube σ, (isMixedNashEq_iff_reflective u σ).1 h, rfl⟩

/-! ### Witness: matching pennies as a two-action game -/

/-- Expected payoff of a two-player two-action game as an explicit double sum.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem rawEP_two (u : (Fin 2 → Fin 2) → Fin 2 → ℝ) (ρ : Fin 2 → Fin 2 → ℝ) (j : Fin 2) :
    rawEP u ρ j = ∑ a : Fin 2, ∑ b : Fin 2, ρ 0 a * ρ 1 b * u ![a, b] j := by
  unfold rawEP
  rw [← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (finTwoArrowEquiv (Fin 2)) _ _ fun τ => ?_
  have hτ : ![τ 0, τ 1] = τ := by ext i; fin_cases i <;> rfl
  show (∏ i, ρ i (τ i)) * u τ j = ρ 0 (τ 0) * ρ 1 (τ 1) * u ![τ 0, τ 1] j
  rw [hτ, Fin.prod_univ_two]

/-- **Matching pennies as a two-action game**: player `0` (row) gets `1` iff the actions match,
player `1` (column) gets `1` iff they differ.
Source: [[fixpoint-lit-2-inventory]] 010 (matching pennies instance); `fix-kakutani` `Witness.lean`
(`rowPayoff`/`colPayoff`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def mpU : (Fin 2 → Fin 2) → Fin 2 → ℝ :=
  fun τ j => if j = 0 then (if τ 0 = τ 1 then 1 else 0) else (if τ 0 = τ 1 then 0 else 1)

/-- The evaluation maps of matching pennies are `mpEv` (`x ↦ x 1` and `x ↦ 1 − x 0`).
Source: [[fixpoint-lit-2-inventory]] 010
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem evOf_mpU : evOf mpU = mpEv := by
  funext i x
  fin_cases i <;>
    simp [evOf, gain, rawEP_two, mpU, mpEv, wt, pureWt, Fin.sum_univ_two, Function.update_self,
      Function.update_of_ne] <;> ring

/-- **N+ witness of target 13**: the mixed Nash equilibria of matching pennies are exactly the
profiles whose answer vector is `![1/2, 1/2]`, i.e. the uniform profile (reduces to
`reflective_mp_iff`).
Source: [[fixpoint-lit-2-inventory]] 010; mandate target 13 (N+)
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem isMixedNashEq_mp_iff (σ : MixedProfile (twoActionGame mpU)) :
    IsMixedNashEq (twoActionGame mpU) σ ↔ ∀ i, (σ i).val = ![1 / 2, 1 / 2] := by
  rw [isMixedNashEq_iff_reflective, evOf_mpU, reflective_mp_iff (toCube_mem_cube σ)]
  constructor
  · intro h i
    rw [← wt_toCube σ i, h]
    fin_cases i <;> ext j <;> fin_cases j <;> norm_num [wt]
  · intro h
    ext i
    fin_cases i <;> simp [toCube, h]

end Cleanroom.Fixpoint.FixOraclesCorresp
