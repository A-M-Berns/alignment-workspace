import Cleanroom.Bli.UdtBliLearning.Defs

/-!
# `udt-bli-learning` · Conventions: utility conventions on the iterated mugging — averaged and
discounted weights, and the "`U_{>n}` reintroduces dynamic instability" claim tested (T10)

**Scope: single coin, additive stakes, finite horizon `K`.**

PDF 07 ("A naive proposal", "Utility") considers two conventions for the utility of an infinite
sequence of decision problems — the average of the per-round rewards and a discounted sum — and
suggests that using at each node the utility of the remaining rounds `U_{>n}` "reintroduces
dynamic instability". On `udt-bli-tiling`'s `SingleCoin` model:

* `avgParams p` (`γ_k = 1/K`) and `discParams p δ` (`γ_k = δ^k`) are `Params` instances (D); the
  one-step verdict at every `Ask_j` depends on `γ` only through its sign
  (`isOneStepChoice_askT_iff`: `pay` is one-step iff `0 ≤ γ_j · gain`), so both conventions give
  the same verdict as any positive weights (`oneStep_sign_gamma_free`).
* `truncParams p n` (`γ'_k = γ_k` for `k > n`, `0` otherwise) is the `U_{>n}` convention: **on
  this model, dropping the past rounds changes no one-step choice at any round `k > n`**
  (`trunc_oneStep_iff`, **L**: two rewrites of `isOneStepChoice_askT_iff`) — the N− of the claim
  *on the single-coin model*. At the dropped rounds every action is tied (`trunc_tied`). This does
  not refute PDF 07's remark for additive utility in general: for any `FiniteBLIPrior` with
  `U = U_{≤n} + U_{>n}`, the node-`n` verdict at `T` differs from the node-`0` verdict by
  `𝔼[U_{≤n} | pp·T = a]`, which is action-blind here for two structural reasons that are not
  "additive utility" — every round's payoff reads only that round's own `Ask` point (`scU`), and
  the points are independent (`structure_facts`). An additive tree whose round-`j` payoff (`j ≤ n`)
  depends on the point at a later `Ask_k` (a Parfit's-hitchhiker shape) would have the dropped past
  correlated with the action at `Ask_k`, and `U_{>n}` flips the verdict there: the claim's
  mechanism is absent from the single-coin model by construction, so that model can neither confirm
  nor refute it. Non-additive utility (the log-wealth agent of `LogWealth.lean`) is *one* reading
  under which the claim holds; additive utility with a cross-round payoff is another, **and it is
  built below**: `hhU`/`hhPrior` (the same base, tables and policy law with a hitchhiker utility —
  round `j` rewards paying at the later `Ask_k`), `hitchhiker_instability` (**N+** for the claim):
  under `γ_k c < γ_j R` the node-`0` agent uniquely pays at `Ask_k` and the node-`n` agent
  (`j ≤ n < k`) with `U_{>n}` — the same `truncParams` convention — uniquely refuses.

Sources: bli-soto-a-060 ([[Soto 2023 - 07 A naive proposal.pdf]] "Utility", pp. 5–6); mandate T10.
-/

set_option autoImplicit false

namespace Cleanroom.Bli.UdtBliLearning

open Cleanroom.Bli.BliFinite Cleanroom.Bli.UdtBliCore Cleanroom.Bli.UdtBliSist
  Cleanroom.Bli.UdtBliTiling Finset
open Cleanroom.Bli.UdtBliSist.Iter
open Cleanroom.Bli.UdtBliTiling.SingleCoin

variable {K : ℕ} (p : Params K)

/-- **The one-step verdict at `Ask_j` is the sign of `γ_j · gain`**: `pay` is a one-step choice iff
`0 ≤ γ_j · gain`, `refuse` iff `γ_j · gain ≤ 0`.
Source: bli-soto-a-060; `udt-bli-tiling`'s `EU_diff`; mandate T10
Kind: L
Fidelity: exact -/
theorem isOneStepChoice_askT_iff (j : Fin K) (a : Bool) :
    (scPrior p).IsOneStepChoice (askT K j) a ↔
      (if a then 0 ≤ p.γ j * gain p else p.γ j * gain p ≤ 0) := by
  have hd := EU_diff p j
  unfold FiniteBLIPrior.IsOneStepChoice
  cases a
  · simp only [Bool.false_eq_true, ↓reduceIte]
    constructor
    · intro h; have := h true; linarith
    · intro h b; cases b
      · exact le_rfl
      · linarith
  · simp only [↓reduceIte]
    constructor
    · intro h; have := h false; linarith
    · intro h b; cases b
      · linarith
      · exact le_rfl

/-! ## Averaged and discounted weights -/

/-- **The averaged convention** `γ_k = 1/K`.
Source: bli-soto-a-060 (PDF 07 "Utility": the average of the rewards)
Kind: D
Fidelity: exact (finite horizon) -/
def avgParams : Params K := { p with γ := fun _ => 1 / (K : ℚ) }

/-- **The discounted convention** `γ_k = δ^k`.
Source: bli-soto-a-060 (PDF 07 "Utility": a discounted sum)
Kind: D
Fidelity: exact (finite horizon) -/
def discParams (δ : ℚ) : Params K := { p with γ := fun k => δ ^ k.val }

/-- The gain does not depend on the weights.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gain_avgParams : gain (avgParams p) = gain p := rfl

/-- The gain does not depend on the weights.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gain_discParams (δ : ℚ) : gain (discParams p δ) = gain p := rfl

/-- **The one-step verdict is convention-free**: under the averaged weights (`0 < K`) and under
positive discounting (`0 < δ`), `pay` is the one-step choice at every `Ask_j` iff it is under any
positive weights, iff `0 ≤ gain`.
Source: bli-soto-a-060; mandate T10 ("the sign of the one-step choice is `γ`-free")
Kind: L (`isOneStepChoice_askT_iff` with a positive factor)
Fidelity: exact
Hyps: (a) `0 < K`, `0 < δ` -/
theorem oneStep_sign_gamma_free (hK : 0 < K) (δ : ℚ) (hδ : 0 < δ) (j : Fin K) :
    ((scPrior (avgParams p)).IsOneStepChoice (askT K j) true ↔ 0 ≤ gain p) ∧
    ((scPrior (discParams p δ)).IsOneStepChoice (askT K j) true ↔ 0 ≤ gain p) := by
  have hK' : (0 : ℚ) < 1 / (K : ℚ) := by positivity
  have hδ' : 0 < δ ^ j.val := pow_pos hδ _
  constructor
  · rw [isOneStepChoice_askT_iff, gain_avgParams]
    simp only [↓reduceIte]
    change 0 ≤ 1 / (K : ℚ) * gain p ↔ _
    constructor
    · intro h; nlinarith
    · intro h; exact mul_nonneg hK'.le h
  · rw [isOneStepChoice_askT_iff, gain_discParams]
    simp only [↓reduceIte]
    change 0 ≤ δ ^ j.val * gain p ↔ _
    constructor
    · intro h; nlinarith
    · intro h; exact mul_nonneg hδ'.le h

/-! ## The `U_{>n}` convention -/

/-- **The `U_{>n}` convention**: the weights of the rounds up to `n` set to `0`, the later rounds
unchanged — the utility of the remaining rounds, used at node `n`.
Source: bli-soto-a-060 (PDF 07: "`U_{>n}` at each node")
Kind: D
Fidelity: exact (finite horizon) -/
def truncParams (n : ℕ) : Params K := { p with γ := fun k => if n < k.val then p.γ k else 0 }

/-- The gain does not depend on the weights.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma gain_truncParams (n : ℕ) : gain (truncParams p n) = gain p := rfl

/-- **Dropping the past rounds changes no one-step choice at the remaining rounds, on this
model**: for every `k > n` and every action, `a` is a one-step choice at `Ask_k` under `U_{>n}` iff
it is under the full utility — because the verdict at `Ask_k` is the sign of `γ_k · gain`
(`isOneStepChoice_askT_iff`) and `γ_k` is unchanged. The claim "`U_{>n}` reintroduces dynamic
instability" has no instance *on the single-coin model*, whose payoffs are round-local and whose
points are independent; it is not refuted for additive utility in general (see the module
docstring: a cross-round payoff shape would instantiate it).
Source: bli-soto-a-060 (PDF 07: "reintroduces dynamic instability"); mandate T10 ("test the
claim"); audit r1 fidelity B1
Kind: L
Fidelity: weaker: N− of the claim on this model only
Hyps: (a) `n < k`; does not use faith -/
theorem trunc_oneStep_iff (n : ℕ) (k : Fin K) (hk : n < k.val) (a : Bool) :
    (scPrior (truncParams p n)).IsOneStepChoice (askT K k) a ↔
      (scPrior p).IsOneStepChoice (askT K k) a := by
  rw [isOneStepChoice_askT_iff, isOneStepChoice_askT_iff, gain_truncParams]
  have : (truncParams p n).γ k = p.γ k := by simp [truncParams, hk]
  rw [this]

/-- At the dropped rounds `k ≤ n` every action is a one-step choice under `U_{>n}` (ties).
Source: mandate T10
Kind: L
Fidelity: exact -/
theorem trunc_tied (n : ℕ) (k : Fin K) (hk : k.val ≤ n) (a : Bool) :
    (scPrior (truncParams p n)).IsOneStepChoice (askT K k) a := by
  rw [isOneStepChoice_askT_iff, gain_truncParams]
  have : (truncParams p n).γ k = 0 := by simp [truncParams, not_lt.mpr hk]
  rw [this]; cases a <;> simp

/-! ## An instance *for* the claim: an additive utility with a cross-round payoff

The single-coin utility is round-local (round `j`'s summand reads `π Ask_j` only) and the points
are independent, which is why `U_{>n}` changes nothing there. Here the same base, tables and
product-uniform policy law carry a different additive utility: round `j` pays a reward `R` iff the
policy pays at a *later* round `k` (Parfit's hitchhiker: rewarded now for being the kind of agent
who pays later), and round `k` costs `c` for paying. The node-`0` agent's one-step verdict at
`Ask_k` weighs `γ_j R` against `γ_k c`; the node-`n` agent (`j ≤ n < k`) using `U_{>n}` has dropped
the reward and refuses. That is the instability PDF 07 names, with additive stakes. -/

/-- **The hitchhiker utility** on the single-coin base: `γ_j · R · [π Ask_k] + γ_k · (−c) · [π Ask_k]`
— round `j`'s reward depends on the point at the later `Ask_k`, round `k`'s cost is for paying
there; additive over rounds with the weights `γ`, every other round `0`; the coin is unused.
Source: bli-soto-a-060 (PDF 07: "`U_{>n}` … reintroduces dynamic instability"); audit r1
fidelity B1 (the Parfit's-hitchhiker shape)
Kind: D
Fidelity: variant: two rounds of the `K`-round tree carry the stakes -/
def hhU (j k : Fin K) (R : ℚ) (_ω : Base K) (π : Policy (iterTables K) Bool) : ℚ :=
  p.γ j * (R * ind (π (askT K k))) + p.γ k * (-p.c * ind (π (askT K k)))

/-- The single-coin data with the hitchhiker utility in place of `scU`: same base, same tables,
same product-uniform policy law.
Source: audit r1 fidelity B1
Kind: D
Fidelity: variant: as `hhU` -/
def hhData (j k : Fin K) (R : ℚ) : IndepData (iterIndex K) 1 (iterTables K) Bool :=
  { scData p with U₀ := hhU p j k R }

/-- The hitchhiker prior.
Source: audit r1 fidelity B1
Kind: D
Fidelity: variant: as `hhU` -/
def hhPrior (j k : Fin K) (R : ℚ) : FiniteBLIPrior (iterIndex K) 1 (iterTables K) Bool :=
  (hhData p j k R).toPrior

/-- **The one-step value at `Ask_k` under the hitchhiker utility**: `EU Ask_k a = (γ_j R − γ_k c) · [a]`
— the utility reads one point, so its one-step value is the full base expectation.
Source: none: infrastructure (`IndepData.EU_single`)
Kind: L
Fidelity: n/a -/
lemma hhPrior_EU (j k : Fin K) (R : ℚ) (a : Bool) :
    (hhPrior p j k R).EU (askT K k) a = (p.γ j * R - p.γ k * p.c) * ind a := by
  unfold hhPrior
  rw [(hhData p j k R).EU_single (half K) (half_sum K) rfl (askT K k)
    (fun _ b => (p.γ j * R - p.γ k * p.c) * ind b)
    (fun _ π => by simp only [hhData, hhU]; ring) a (by norm_num [half])]
  rw [← Finset.sum_mul]
  change (∑ ω : Base K, baseMass p ω) * _ = _
  rw [baseMass_sum p, one_mul]

/-- **PDF 07's "dynamic instability" has an instance with additive utility** (N+ *for* the
claim): on the hitchhiker utility with `γ_k c < γ_j R` (`c > 0`, `γ_k > 0`), the node-`0` agent's
unique one-step choice at `Ask_k` is `pay` (the round-`j` reward for being a payer outweighs the
round-`k` cost), while the node-`n` agent (`j ≤ n < k`) evaluating with `U_{>n}` — the same
`truncParams` convention as `trunc_oneStep_iff` — has dropped the reward and uniquely refuses.
The verdict at `Ask_k` flips with the node, with additive stakes: what the single-coin model
cannot show (`trunc_oneStep_iff`) because its payoffs are round-local.
Source: bli-soto-a-060 (PDF 07 "Utility": "reintroduces dynamic instability"); audit r1 fidelity
B1 ("an additive tree with a Parfit's-hitchhiker shape … exactly the 'dynamic instability' PDF 07
names")
Kind: N+
Fidelity: exact (one instance; the claim is a remark, so an instance is what it asks for)
Hyps: (a) `j ≤ n < k`, `0 < c`, `0 < γ_k`, `γ_k c < γ_j R`; does not use faith -/
theorem hitchhiker_instability (j k : Fin K) (n : ℕ) (hj : j.val ≤ n) (hk : n < k.val)
    (R : ℚ) (hc : 0 < p.c) (hγk : 0 < p.γ k) (hR : p.γ k * p.c < p.γ j * R) :
    ((hhPrior p j k R).IsOneStepChoice (askT K k) true ∧
      ¬ (hhPrior p j k R).IsOneStepChoice (askT K k) false) ∧
    ((hhPrior (truncParams p n) j k R).IsOneStepChoice (askT K k) false ∧
      ¬ (hhPrior (truncParams p n) j k R).IsOneStepChoice (askT K k) true) := by
  have hj' : (truncParams p n).γ j = 0 := by simp [truncParams, not_lt.mpr hj]
  have hk' : (truncParams p n).γ k = p.γ k := by simp [truncParams, hk]
  have hc' : (truncParams p n).c = p.c := rfl
  have hpos : 0 < p.γ j * R - p.γ k * p.c := by linarith
  have hneg : 0 * R - p.γ k * p.c < 0 := by nlinarith
  unfold FiniteBLIPrior.IsOneStepChoice
  simp only [hhPrior_EU, hj', hk', hc']
  refine ⟨⟨fun b => ?_, fun h => ?_⟩, ⟨fun b => ?_, fun h => ?_⟩⟩
  · cases b <;> simp [ind] <;> linarith
  · have := h true; simp [ind] at this; linarith
  · cases b <;> simp [ind] <;> linarith
  · have := h false; simp [ind] at this; linarith

end Cleanroom.Bli.UdtBliLearning
