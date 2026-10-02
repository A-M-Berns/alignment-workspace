import Cleanroom.Decision.DpCalibration.Theories
import Cleanroom.Decision.DpCalibration.Bridge
import Cleanroom.Found.DpCoreTree.Catalogue
import Cleanroom.Found.DpCoreTree.Witnesses
import Cleanroom.Found.DpCoreTree.ScreeningWitness

/-!
# Local witness trees and the T5 witnesses

* `splitWorld` — the refutation of Remark 3.10's converse (T7/T20): a chance root, both
  branches ending in the one world `()` with payoff `0`, a `p2`-node on one branch only. The
  symmetric difference `occ(p2) △ {λ ⊨ O}` has mass `½`, yet for every state and every procedure
  per-run SSC at `p2` ⟺ strict OC at `p2` (`splitWorld_senses_agree`). **Graded N−** (repair
  round 1): on a one-world carrier clause 1 of every sense is a tautology.
* `splitWorld2` — the same refutation on a **two-world carrier** (N+): a fair chance root, branch
  `0` queries `p1`, branch `1` queries `p2`, below each decision a fair coin picks the world
  (`false`/`true`) with payoff `1` on `true`, `O = ⊤`. `μ({λ ⊨ O} ∖ occ(p2)) = ½`, both senses
  pin `P(true) = ½` (`splitWorld2_pins_half`), and per-run SSC at `p2` ⟺ strict OC at `p2` for
  every state and procedure (`splitWorld2_senses_agree`), because the world and payoff marginals
  of the unconsulted branch coincide with those of `occ(p2)`.
* `a1Node` — adversary-repair A.1's node (T10, limit ⇏ per-run off "realized"): one point,
  `O_d = {coin = T}`, both leaves have `coin = H`, `a → 0`, `b → 1`. Limit calibration is vacuous
  for every procedure (`nuPoly O_d = 0`); per-run SSC is violated by the `½/½` state under `δ_a`
  and under `δ_b`.
* `fiveTen` — the one-point five-and-ten tree (`a → 5`, `b → 10`, `O = ⊤`), used by
  `Miniature.lean` for Remark 3.12's instance.
* T5's witnesses on `coinQuery` (Proposition 7's hypothesis package inhabited with `C = C'`; the
  contrapositive: procedures differing at `d` have different strict states) and on
  `routingRoot` (necessity of recording: every procedure with `ν(O) > 0` has the *same* strict
  state while `C d ≠ C' d`; the routing root is not recorded).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Decision.DpCalibration

open Cleanroom.Found.DpCoreTree
open Cleanroom.Found.DpCoreTree.Tree
open Cleanroom.Found.DpCoreTree.Catalogue
open Finset

/-! ## Generic helpers -/

/-- `μ(S)` as an indicator sum over all leaves. Source: none: infrastructure. Kind: L -/
theorem mass_eq_sum_ite {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
    (C : Proc ι acts K) (B : Tree Ω ι acts K) (S : Finset B.Leaves) :
    mass C B S = ∑ ℓ, if ℓ ∈ S then leafLaw C B ℓ else 0 := by
  unfold mass; rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- A payoff sum over a leaf set as an indicator sum. Source: none: infrastructure. Kind: L -/
theorem paySumLeaves_eq_sum_ite {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Ω ι : Type} {acts : ι → Type} [∀ d, Fintype (acts d)] [∀ d, DecidableEq (acts d)]
    (C : Proc ι acts K) (B : Tree Ω ι acts K) (S : Finset B.Leaves) :
    (∑ ℓ ∈ S, leafLaw C B ℓ * payoff B ℓ) =
      ∑ ℓ, if ℓ ∈ S then leafLaw C B ℓ * payoff B ℓ else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- Sums over `Pt2`. Source: none: infrastructure. Kind: L -/
theorem Pt2.sum_univ {M : Type} [AddCommMonoid M] (f : Pt2 → M) : ∑ x, f x = f .p1 + f .p2 := by
  have : (Finset.univ : Finset Pt2) = {.p1, .p2} := by ext x; cases x <;> simp
  rw [this, Finset.sum_pair (by decide)]

/-- Sums over `Box`. Source: none: infrastructure. Kind: L -/
theorem Box.sum_univ {M : Type} [AddCommMonoid M] (f : Box → M) :
    ∑ x, f x = f .large + f .both := by
  have : (Finset.univ : Finset Box) = {.large, .both} := by ext x; cases x <;> simp
  rw [this, Finset.sum_pair (by decide)]

/-- Sums over `Five10`. Source: none: infrastructure. Kind: L -/
theorem Five10.sum_univ {M : Type} [AddCommMonoid M] (f : Five10 → M) :
    ∑ x, f x = f .five + f .ten := by
  have : (Finset.univ : Finset Five10) = {.five, .ten} := by ext x; cases x <;> simp
  rw [this, Finset.sum_pair (by decide)]

/-! ## `splitWorld`: the refutation of Remark 3.10's converse -/

/-- **The split-world tree**: a fair chance root; branch `0` queries `p1`, branch `1` queries
`p2`; every leaf has the single world `()` and payoff `0`. `occ(p2)` is branch `1` (mass `½`),
`{λ ⊨ O_{p2}}` with `O_{p2} = ⊤` is every run: the symmetric difference has mass `½`, but the
two conditionals on worlds coincide (`δ_{()}`), as do the conditional payoffs (`0`).
Source: none in the corpus (this run's construction, refuting the state-level reading of
[[decision-problems-v2]] Remark 3.10's "exactly"; findings F-3.10)
Kind: D -/
def splitWorld : Tree Unit Pt2 (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => .decision (if i = 0 then .p1 else .p2) fun _ => .leaf () 0

/-- Observations on `splitWorld`: `⊤` everywhere. Source: none in the corpus. Kind: D -/
def swObs : Pt2 → Finset Unit := fun _ => Finset.univ

/-- A sum over the leaves of `splitWorld` as four terms. Source: none: infrastructure. Kind: L -/
theorem splitWorld_sum (f : splitWorld.Leaves → ℚ) :
    ∑ ℓ, f ℓ = f ⟨0, .a, ()⟩ + f ⟨0, .b, ()⟩ + f ⟨1, .a, ()⟩ + f ⟨1, .b, ()⟩ := by
  unfold splitWorld at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_two, sum_leaves_decision, sum_leaves_decision,
    Act2.sum_univ, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]
  ring

/-- The mass of `occ(p2)` on `splitWorld` is `½` for every procedure.
Source: none in the corpus. Kind: L -/
theorem splitWorld_mass_occ (C : Proc Pt2 (fun _ => Act2) ℚ) :
    mass C splitWorld (occ .p2 splitWorld) = 1 / 2 := by
  rw [mass_eq_sum_ite, splitWorld_sum]
  simp only [mem_occ]
  unfold splitWorld
  simp [count_decision, leafLaw_chance, leafLaw_decision, leafLaw_leaf, FinDistr.fair,
    FinDistr.coin]
  have := (C .p2).sum_one
  rw [Act2.sum_univ] at this
  linarith

/-- `μ({λ ⊨ X} ∩ occ(p2))` on `splitWorld`: `½` if `() ∈ X`, else `0`.
Source: none in the corpus. Kind: L -/
theorem splitWorld_mass_worldEv_occ (C : Proc Pt2 (fun _ => Act2) ℚ) (X : Finset Unit) :
    mass C splitWorld (worldEv splitWorld X ∩ occ .p2 splitWorld) =
      if () ∈ X then 1 / 2 else 0 := by
  rw [mass_eq_sum_ite, splitWorld_sum]
  simp only [Finset.mem_inter, mem_occ, worldEv, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold splitWorld
  simp [count_decision, leafLaw_chance, leafLaw_decision, leafLaw_leaf, world_chance,
    world_decision, world_leaf, FinDistr.fair, FinDistr.coin]
  have := (C .p2).sum_one
  rw [Act2.sum_univ] at this
  split_ifs <;> linarith

/-- Every payoff on `splitWorld` is `0`. Source: none in the corpus. Kind: L -/
theorem splitWorld_payoff (ℓ : splitWorld.Leaves) : payoff splitWorld ℓ = 0 := by
  unfold splitWorld at ℓ ⊢
  rcases ℓ with ⟨i, act, _⟩
  rfl

/-- `ν(X)` on `splitWorld`: `1` if `() ∈ X`, else `0`. Source: none in the corpus. Kind: L -/
theorem splitWorld_nu (C : Proc Pt2 (fun _ => Act2) ℚ) (X : Finset Unit) :
    nu C splitWorld X = if () ∈ X then 1 else 0 := by
  rw [nu_eq_sum, splitWorld_sum]
  unfold splitWorld
  simp [leafLaw_chance, leafLaw_decision, leafLaw_leaf, world_chance, world_decision, world_leaf,
    FinDistr.fair, FinDistr.coin]
  have h1 := (C .p1).sum_one
  have h2 := (C .p2).sum_one
  rw [Act2.sum_univ] at h1 h2
  split_ifs <;> linarith

/-- **The symmetric difference has mass `½`** on `splitWorld`: `{λ ⊨ O_{p2}} ∖ occ(p2)` is branch
`0`.
Source: none in the corpus (findings F-3.10)
Kind: N− (one-world carrier; the two-world version is `splitWorld2_occ_diff`) -/
theorem splitWorld_occ_diff (C : Proc Pt2 (fun _ => Act2) ℚ) :
    mass C splitWorld (worldEv splitWorld (swObs .p2) \ occ .p2 splitWorld) = 1 / 2 := by
  rw [mass_eq_sum_ite, splitWorld_sum]
  simp only [Finset.mem_sdiff, mem_occ, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
    swObs]
  unfold splitWorld
  simp [count_decision, leafLaw_chance, leafLaw_decision, leafLaw_leaf, FinDistr.fair,
    FinDistr.coin]
  have := (C .p1).sum_one
  rw [Act2.sum_univ] at this
  linarith

/-- **Remark 3.10's converse refuted (one-world carrier)**: on `splitWorld`, for every state
assignment and every procedure, per-run SSC at `p2` holds iff strict OC at `p2` holds — although
`μ(occ(p2) △ {λ ⊨ O_{p2}}) = ½ > 0` (`splitWorld_occ_diff`) and both positivities hold. The two
conditionals coincide because both branches end in the same world with the same payoff. **N−**:
with `Ω = Unit` every state has `P = δ_()`, so clause 1 of both senses holds for every state and
the `V`-clauses reduce to `V(⊤) · m = 0` on both sides; the refutation is logically valid (the
refuted claim quantifies over all trees) but degenerate. The non-degenerate witness is
`splitWorld2_senses_agree`.
Source: [[decision-problems-v2]] §3.1 Remark 3.10 ("the divergence … is exactly the symmetric
difference") — the state-level reading, ATTRIBUTION-UNVETTED; refuted
Kind: N− (regraded in repair round 1)
Fidelity: exact (the refuted claim is the "⇒" half of T20's exact-class statement) -/
theorem splitWorld_senses_agree (s : Pt2 → State Unit ℚ) (C : Proc Pt2 (fun _ => Act2) ℚ) :
    PerRunSSCAt s C splitWorld .p2 ↔ StrictOCAt s swObs C splitWorld .p2 := by
  have hpay : ∀ S : Finset splitWorld.Leaves,
      (∑ ℓ ∈ S, leafLaw C splitWorld ℓ * payoff splitWorld ℓ) = 0 :=
    fun S => Finset.sum_eq_zero fun ℓ _ => by rw [splitWorld_payoff, mul_zero]
  have hpay' : ∀ X : Finset Unit, paySum C splitWorld X = 0 := fun X => hpay _
  unfold PerRunSSCAt StrictOCAt PerRunClausesAt StrictClausesAt PerRunClause1At PerRunClause2At
    StrictClause1At StrictClause2At
  simp only [splitWorld_mass_occ, splitWorld_mass_worldEv_occ, splitWorld_nu, hpay, hpay', swObs,
    Finset.inter_univ, Finset.mem_univ, if_true]
  constructor
  · rintro h
    obtain ⟨h1, h2⟩ := h (by norm_num)
    refine fun _ => ⟨fun X => ?_, fun X hX hX' => ?_⟩
    · have := h1 X
      split_ifs at this ⊢ <;> linarith
    · have hmem : () ∈ X := by by_contra hc; simp [hc] at hX'
      have := h2 X hX (by simp [hmem])
      simp [hmem] at this ⊢
      linarith
  · rintro h
    obtain ⟨h1, h2⟩ := h (by norm_num)
    refine fun _ => ⟨fun X => ?_, fun X hX hX' => ?_⟩
    · have := h1 X
      split_ifs at this ⊢ <;> linarith
    · have hmem : () ∈ X := by by_contra hc; simp [hc] at hX'
      have := h2 X hX (by simp [hmem])
      simp [hmem] at this ⊢
      linarith

/-! ## `splitWorld2`: the same refutation on a two-world carrier (N+) -/

/-- **The two-world split tree**: a fair chance root; branch `0` queries `p1`, branch `1` queries
`p2`; below each decision a fair coin picks the world (`false`/`true`), payoff `1` on `true`.
`occ(p2)` is branch `1` (mass `½`); with `O_{p2} = ⊤` the symmetric difference is branch `0`
(mass `½`), while the world marginal (`½/½`) and the conditional payoff (`½`) of the unconsulted
branch coincide with those of `occ(p2)`.
Source: none in the corpus (this run's construction; audit round 1 fidelity probe, refuting the
state-level reading of [[decision-problems-v2]] Remark 3.10 non-degenerately; findings F7)
Kind: D -/
def splitWorld2 : Tree Bool Pt2 (fun _ => Act2) ℚ :=
  .chance 2 FinDistr.fair fun i => .decision (if i = 0 then .p1 else .p2) fun _ =>
    .chance 2 FinDistr.fair fun j => .leaf (decide (j = 1)) (if j = 1 then 1 else 0)

/-- `O = ⊤` at both points of `splitWorld2`. Source: none in the corpus. Kind: D -/
def sw2Obs : Pt2 → Finset Bool := fun _ => Finset.univ

/-- A sum over the leaves of `splitWorld2` as eight terms. Source: none: infrastructure. Kind: L -/
theorem splitWorld2_sum (f : splitWorld2.Leaves → ℚ) :
    ∑ ℓ, f ℓ = f ⟨0, .a, 0, ()⟩ + f ⟨0, .a, 1, ()⟩ + f ⟨0, .b, 0, ()⟩ + f ⟨0, .b, 1, ()⟩ +
      f ⟨1, .a, 0, ()⟩ + f ⟨1, .a, 1, ()⟩ + f ⟨1, .b, 0, ()⟩ + f ⟨1, .b, 1, ()⟩ := by
  unfold splitWorld2 at f ⊢
  rw [sum_leaves_chance, Fin.sum_univ_two, sum_leaves_decision, sum_leaves_decision,
    Act2.sum_univ, Act2.sum_univ]
  simp only [sum_leaves_chance, Fin.sum_univ_two, Tree.sum_leaves_leaf]
  ring

/-- `μ(occ(p2)) = ½` on `splitWorld2` for every procedure. Source: none: infrastructure. Kind: L -/
theorem splitWorld2_mass_occ (C : Proc Pt2 (fun _ => Act2) ℚ) :
    mass C splitWorld2 (occ .p2 splitWorld2) = 1 / 2 := by
  rw [mass_eq_sum_ite, splitWorld2_sum]
  simp only [mem_occ]
  unfold splitWorld2
  simp [count_chance, count_decision, count_leaf, leafLaw_chance, leafLaw_decision, leafLaw_leaf,
    FinDistr.fair, FinDistr.coin]
  have := (C .p2).sum_one
  rw [Act2.sum_univ] at this
  linarith

/-- `μ({λ ⊨ X} ∩ occ(p2))` on `splitWorld2`: `¼` per world in `X`.
Source: none: infrastructure. Kind: L -/
theorem splitWorld2_mass_worldEv_occ (C : Proc Pt2 (fun _ => Act2) ℚ) (X : Finset Bool) :
    mass C splitWorld2 (worldEv splitWorld2 X ∩ occ .p2 splitWorld2) =
      (if false ∈ X then 1 / 4 else 0) + (if true ∈ X then 1 / 4 else 0) := by
  rw [mass_eq_sum_ite, splitWorld2_sum]
  simp only [Finset.mem_inter, mem_occ, worldEv, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold splitWorld2
  simp [count_chance, count_decision, count_leaf, leafLaw_chance, leafLaw_decision, leafLaw_leaf,
    world_chance, world_decision, world_leaf, FinDistr.fair, FinDistr.coin]
  have := (C .p2).sum_one
  rw [Act2.sum_univ] at this
  split_ifs <;> linarith

/-- The payoff mass on `{λ ⊨ X} ∩ occ(p2)`: `¼` if `true ∈ X`. Source: none: infrastructure.
Kind: L -/
theorem splitWorld2_payOcc (C : Proc Pt2 (fun _ => Act2) ℚ) (X : Finset Bool) :
    (∑ ℓ ∈ worldEv splitWorld2 X ∩ occ .p2 splitWorld2,
      leafLaw C splitWorld2 ℓ * payoff splitWorld2 ℓ) = if true ∈ X then 1 / 4 else 0 := by
  rw [paySumLeaves_eq_sum_ite, splitWorld2_sum]
  simp only [Finset.mem_inter, mem_occ, worldEv, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold splitWorld2
  simp [count_chance, count_decision, count_leaf, leafLaw_chance, leafLaw_decision, leafLaw_leaf,
    world_chance, world_decision, world_leaf, payoff_chance, payoff_decision, payoff_leaf,
    FinDistr.fair, FinDistr.coin]
  have := (C .p2).sum_one
  rw [Act2.sum_univ] at this
  split_ifs <;> linarith

/-- `ν(X)` on `splitWorld2`: `½` per world in `X`. Source: none: infrastructure. Kind: L -/
theorem splitWorld2_nu (C : Proc Pt2 (fun _ => Act2) ℚ) (X : Finset Bool) :
    nu C splitWorld2 X = (if false ∈ X then 1 / 2 else 0) + (if true ∈ X then 1 / 2 else 0) := by
  rw [nu_eq_sum, splitWorld2_sum]
  unfold splitWorld2
  simp [leafLaw_chance, leafLaw_decision, leafLaw_leaf, world_chance, world_decision, world_leaf,
    FinDistr.fair, FinDistr.coin]
  have h1 := (C .p1).sum_one
  have h2 := (C .p2).sum_one
  rw [Act2.sum_univ] at h1 h2
  split_ifs <;> linarith

/-- `paySum X` on `splitWorld2`: `½` if `true ∈ X`. Source: none: infrastructure. Kind: L -/
theorem splitWorld2_paySum (C : Proc Pt2 (fun _ => Act2) ℚ) (X : Finset Bool) :
    paySum C splitWorld2 X = if true ∈ X then 1 / 2 else 0 := by
  rw [paySum_eq_sum_ite, splitWorld2_sum]
  unfold splitWorld2
  simp [leafLaw_chance, leafLaw_decision, leafLaw_leaf, world_chance, world_decision, world_leaf,
    payoff_chance, payoff_decision, payoff_leaf, FinDistr.fair, FinDistr.coin]
  have h1 := (C .p1).sum_one
  have h2 := (C .p2).sum_one
  rw [Act2.sum_univ] at h1 h2
  split_ifs <;> linarith

/-- **`μ({λ ⊨ O_{p2}} ∖ occ(p2)) = ½`** on `splitWorld2`: the unconsulted branch.
Source: none in the corpus (findings F7)
Kind: N+ -/
theorem splitWorld2_occ_diff (C : Proc Pt2 (fun _ => Act2) ℚ) :
    mass C splitWorld2 (worldEv splitWorld2 (sw2Obs .p2) \ occ .p2 splitWorld2) = 1 / 2 := by
  rw [mass_eq_sum_ite, splitWorld2_sum]
  simp only [Finset.mem_sdiff, mem_occ, worldEv, Finset.mem_filter, Finset.mem_univ, true_and,
    sw2Obs]
  unfold splitWorld2
  simp [count_chance, count_decision, count_leaf, leafLaw_chance, leafLaw_decision, leafLaw_leaf,
    FinDistr.fair, FinDistr.coin]
  have := (C .p1).sum_one
  rw [Act2.sum_univ] at this
  linarith

/-- **Remark 3.10's state-level converse refuted on a two-world carrier**: for every state and
every procedure, per-run SSC at `p2` ⟺ strict OC at `p2`, although `μ(O ∖ occ) = ½` and both
positivities hold (`μ(occ) = ½`, `ν(⊤) = 1`); clause 1 is not a tautology here (both senses pin
`P(true) = ½`, `splitWorld2_pins_half`) and the `V`-clause has content (conditional payoff `½`).
Source: [[decision-problems-v2]] §3.1 Remark 3.10 ("the divergence … is exactly the symmetric
difference") — the state-level reading, ATTRIBUTION-UNVETTED; refuted
Kind: N+
Fidelity: exact (the refuted claim is the "⇒" half of T20's exact-class statement) -/
theorem splitWorld2_senses_agree (s : Pt2 → State Bool ℚ) (C : Proc Pt2 (fun _ => Act2) ℚ) :
    PerRunSSCAt s C splitWorld2 .p2 ↔ StrictOCAt s sw2Obs C splitWorld2 .p2 := by
  unfold PerRunSSCAt StrictOCAt PerRunClausesAt StrictClausesAt PerRunClause1At PerRunClause2At
    StrictClause1At StrictClause2At
  simp only [splitWorld2_mass_occ, splitWorld2_mass_worldEv_occ, splitWorld2_payOcc,
    splitWorld2_nu, splitWorld2_paySum, sw2Obs, Finset.inter_univ, Finset.mem_univ, if_true,
    add_halves, mul_one]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h (by norm_num)
    refine fun _ => ⟨fun X => ?_, fun X hX hX' => ?_⟩
    · have := h1 X
      split_ifs at this ⊢ <;> linarith
    · have := h2 X hX (by split_ifs at hX' ⊢ <;> linarith)
      split_ifs at this ⊢ <;> linarith
  · intro h
    obtain ⟨h1, h2⟩ := h (by norm_num)
    refine fun _ => ⟨fun X => ?_, fun X hX hX' => ?_⟩
    · have := h1 X
      split_ifs at this ⊢ <;> linarith
    · have := h2 X hX (by split_ifs at hX' ⊢ <;> linarith)
      split_ifs at this ⊢ <;> linarith

/-- The senses pin `P(true) = ½` on `splitWorld2`: clause 1 has content on this carrier.
Source: none in the corpus (findings F7)
Kind: N+ -/
theorem splitWorld2_pins_half (s : Pt2 → State Bool ℚ) (C : Proc Pt2 (fun _ => Act2) ℚ)
    (h : StrictOCAt s sw2Obs C splitWorld2 .p2) : (s .p2).pr {true} = 1 / 2 := by
  have := (h (by rw [splitWorld2_nu]; simp [sw2Obs])).1 {true}
  rw [sw2Obs, Finset.inter_univ, splitWorld2_nu, splitWorld2_nu] at this
  simp only [Finset.mem_univ, if_true, Finset.mem_singleton, Bool.false_eq_true, if_false,
    add_halves, mul_one, zero_add] at this
  exact this

/-! ## A.1's node: limit calibration vacuous, per-run SSC violated -/

/-- A.1 worlds `(coin, act)`. Source: `zoo.md` ZO-2 ("adversary-repair A.1's node"). Kind: D -/
abbrev A1W : Type := Bool × Act2

/-- **A.1's node**: one point `d`, `O_d = {coin = T}`, both leaves have `coin = H`; `a → 0`,
`b → 1`.
Source: `cf-workflow/phase2-notes/repair/zoo.md` ZO-2 ("Witness off 'realized'")
Kind: D -/
def a1Node : Tree A1W Unit (fun _ => Act2) ℚ :=
  .decision () fun act => .leaf (false, act) (if act = .b then 1 else 0)

/-- `O_d = {coin = T}` on A.1. Source: `zoo.md` ZO-2. Kind: D -/
def a1Obs : Unit → Finset A1W := fun _ => Finset.univ.filter fun w => w.1 = true

/-- Action events on A.1. Source: `zoo.md` ZO-2. Kind: D -/
def a1ActEv (_ : Unit) (act : Act2) : Finset A1W := Finset.univ.filter fun w => w.2 = act

/-- The `½/½` state on A.1's two leaf-worlds (`V ≡ 7`, the zoo's number, never read).
Source: `zoo.md` ZO-2 (`s = ½/½`, `V(a) = 7`)
Kind: D -/
def a1State : State A1W ℚ :=
  State.ofConst (uniformOn {(false, .a), (false, .b)} (by simp)) 7

/-- No leaf-world of A.1 satisfies `O_d`, so `nuPoly O_d = 0` for every procedure: limit
calibration is vacuous at `d`.
Source: `zoo.md` ZO-2 ("limit OC vacuous (`ν_{C^ε}(O_d) ≡ 0`)")
Kind: L -/
theorem a1_nuPoly_obs_eq_zero (C : Proc Unit (fun _ => Act2) ℚ) :
    nuPoly C a1Node (a1Obs ()) = 0 := by
  by_contra h
  obtain ⟨ℓ, hℓ, -⟩ := (nuPoly_ne_zero_iff C a1Node (a1Obs ())).mp h
  unfold a1Node at ℓ hℓ
  rcases ℓ with ⟨act, _⟩
  simp [a1Obs, world_decision, world_leaf] at hℓ

/-- **Limit calibration is vacuous on A.1** for every state and every procedure.
Source: `zoo.md` ZO-2
Kind: N− (vacuous by design: the observation is unrealizable) -/
theorem a1_limitOCAt (s : Unit → State A1W ℚ) (C : Proc Unit (fun _ => Act2) ℚ) :
    LimitOCAt s a1Obs C a1Node () :=
  fun h => absurd (a1_nuPoly_obs_eq_zero C) h

/-- `μ(occ(d)) = 1` on A.1. Source: none: infrastructure. Kind: L -/
theorem a1_mass_occ (C : Proc Unit (fun _ => Act2) ℚ) : mass C a1Node (occ () a1Node) = 1 := by
  rw [mass_eq_sum_ite]
  unfold a1Node
  rw [sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf, mem_occ, count_decision, count_leaf, leafLaw_decision,
    leafLaw_leaf]
  have := (C ()).sum_one
  rw [Act2.sum_univ] at this
  simp; linarith

/-- `μ({λ ⊨ {(H,a)}} ∩ occ(d)) = C(d)(a)` on A.1. Source: none: infrastructure. Kind: L -/
theorem a1_mass_worldEv_a (C : Proc Unit (fun _ => Act2) ℚ) :
    mass C a1Node (worldEv a1Node {(false, .a)} ∩ occ () a1Node) = (C ()).w .a := by
  rw [mass_eq_sum_ite]
  unfold a1Node
  rw [sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]
  simp [worldEv, count_decision, leafLaw_decision, world_decision]

/-- **Per-run SSC is violated on A.1** by the `½/½` state under `δ_a` and under `δ_b`
(`μ(· | occ(d))` is a point mass, the state is not).
Source: `zoo.md` ZO-2 ("per-run and per-occurrence SSC violated for `δ_a` … and for `δ_b`")
Kind: N+ -/
theorem a1_not_perRunSSCAt :
    ¬ PerRunSSCAt (fun _ => a1State) (Proc.ofFun fun _ => Act2.a) a1Node () ∧
    ¬ PerRunSSCAt (fun _ => a1State) (Proc.ofFun fun _ => Act2.b) a1Node () := by
  have hpr : a1State.pr {(false, .a)} = 1 / 2 := by
    simp [a1State, State.pr, State.ofConst, probOf_singleton, uniformOn_w]
  constructor
  · intro h
    have := (h (by rw [a1_mass_occ]; exact one_pos)).1 {(false, .a)}
    rw [a1_mass_occ, a1_mass_worldEv_a, hpr] at this
    simp at this
  · intro h
    have := (h (by rw [a1_mass_occ]; exact one_pos)).1 {(false, .a)}
    rw [a1_mass_occ, a1_mass_worldEv_a, hpr] at this
    simp at this

/-! ## The five-and-ten tree -/

/-- Five-and-ten worlds: the act taken. Source: [[decision-problems-v2]] Remark 3.12. Kind: D -/
abbrev FiveTenW : Type := Act2

/-- **The five-and-ten tree**: one point, `a → 5`, `b → 10`, world = the act, `O = ⊤`.
Source: [[decision-problems-v2]] §3.2 Remark 3.12 ("one point, leaf payoffs `5` and `10`")
Kind: D -/
def fiveTen : Tree FiveTenW Unit (fun _ => Act2) ℚ :=
  .decision () fun act => .leaf act (if act = .a then 5 else 10)

/-- `O = ⊤` on five-and-ten. Source: [[decision-problems-v2]] Remark 3.12. Kind: D -/
def ftObs : Unit → Finset FiveTenW := fun _ => Finset.univ

/-- Action events on five-and-ten: `{act = ·}`. Source: [[decision-problems-v2]] Remark 3.12.
Kind: D -/
def ftActEv (_ : Unit) (act : Act2) : Finset FiveTenW := {act}

/-! ## T5 witnesses: coinQuery and the routing root -/

section coinQuery

/-- `ν(O) = 1` on `coinQuery` (`O = ⊤`). Source: none: infrastructure. Kind: L -/
theorem coinQuery_nu_obs (C : Proc Unit (fun _ => Act2) ℚ) : nu C coinQuery (cqObs ()) = 1 := by
  unfold cqObs; exact nu_univ C coinQuery

/-- The strict state of `procQ q` on `coinQuery`. Source: none: infrastructure. Kind: D -/
noncomputable def cqStrictState (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) : State CoinQueryW ℚ :=
  calibratedState (procQ q h0 h1) coinQuery (cqObs ()) (by rw [coinQuery_nu_obs]; exact one_pos)

/-- **Proposition 7's hypothesis package is inhabited on `coinQuery`** (N−): for `C = C' = procQ q`,
recording for both (`dp-core-tree`'s `coinQuery_recordsFor`), `ν(O) = 1 > 0` for both, and strict
OC at `d` for both with the strict state of `procQ q`; the conclusion `C d = C' d` holds.
Degenerate because `C = C'`: the conclusion is `rfl`. The N+ instances (`C ≠ C'`) are
`prop7_nondegenerate_instance` (deterministic at `d`) and `prop7_mixed_instance` (properly
mixed at `d`) in `HypWitnesses.lean` (regraded in repair round 1, adversarial B4).
Source: mandate T5 ("N+ positive instance on `coinQuery`" — the mandate's grade; N− as shipped)
Kind: N− -/
theorem coinQuery_prop7_instance (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    RecordsFor cqObs cqActEv (procQ q h0 h1) coinQuery () ∧
    0 < nu (procQ q h0 h1) coinQuery (cqObs ()) ∧
    StrictOCAt (fun _ => cqStrictState q h0 h1) cqObs (procQ q h0 h1) coinQuery () := by
  refine ⟨coinQuery_recordsFor _, by rw [coinQuery_nu_obs]; exact one_pos, ?_⟩
  exact strictOCAt_calibratedState cqObs (procQ q h0 h1) coinQuery _ () _ rfl

/-- **The contrapositive of Proposition 7 on `coinQuery`**: two procedures differing at `d`
(`q ≠ q'`) have strict states that do not agree (`P(a) = q` versus `q'`, by self-transparency).
Source: mandate T5 ("the contrapositive instance")
Kind: N+ -/
theorem coinQuery_strict_states_differ (q q' : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (h0' : 0 ≤ q')
    (h1' : q' ≤ 1) (hne : q ≠ q') :
    ¬ State.Agree (cqStrictState q h0 h1) (cqStrictState q' h0' h1') := by
  intro hag
  have key : ∀ (r : ℚ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1),
      (cqStrictState r hr0 hr1).pr (cqActEv () .a) = r := by
    intro r hr0 hr1
    have := selfTransparent_of_recordsFor_strict cqObs cqActEv (procQ r hr0 hr1) coinQuery
      (fun _ => cqStrictState r hr0 hr1) (coinQuery_recordsFor _)
      (by rw [coinQuery_nu_obs]; exact one_pos)
      (strictOCAt_calibratedState cqObs (procQ r hr0 hr1) coinQuery _ () _ rfl) .a
    simpa [procQ] using this
  have h := key q h0 h1
  have h' := key q' h0' h1'
  rw [State.pr, hag.1] at h
  rw [State.pr] at h'
  exact hne (h.symm.trans h')

end coinQuery

section routingRoot

/-- `ν` on the routing root: `q·[inO ∈ X] + (1−q)·[outO ∈ X]`.
Source: none: infrastructure. Kind: L -/
theorem routingRoot_nu (q : ℚ) (h0 : 0 ≤ q) (h1 : q ≤ 1) (X : Finset RouteW) :
    nu (procQ q h0 h1) routingRoot X =
      (if RouteW.inO ∈ X then q else 0) + (if RouteW.outO ∈ X then 1 - q else 0) := by
  rw [nu_eq_sum]
  unfold routingRoot
  rw [sum_leaves_decision, Act2.sum_univ]
  simp only [Tree.sum_leaves_leaf]
  simp [leafLaw_decision, world_decision, procQ]

/-- Every payoff on the routing root is `0`. Source: none: infrastructure. Kind: L -/
theorem routingRoot_payoff (ℓ : routingRoot.Leaves) : payoff routingRoot ℓ = 0 := by
  unfold routingRoot at ℓ ⊢
  rcases ℓ with ⟨act, _⟩
  cases act <;> rfl

/-- The strict state of `procQ q` at the routing root (`q > 0`).
Source: none: infrastructure. Kind: D -/
noncomputable def rrStrictState (q : ℚ) (h0 : 0 < q) (h1 : q ≤ 1) : State RouteW ℚ :=
  calibratedState (procQ q h0.le h1) routingRoot (routeObs ())
    (by rw [routingRoot_nu_obs]; exact h0)

/-- **Necessity of recording in Proposition 7**: on the routing root (a selection node), the
strict state of *any* `q > 0` is strictly calibrated for *every* `q' > 0` — every procedure with
`ν(O) > 0` has the same strict state at `d` — while `procQ q () ≠ procQ q' ()` for `q ≠ q'`. All
of Proposition 7's hypotheses except recording hold, and its conclusion fails.
Source: mandate T5 ("on `routingRoot` … every procedure with `0 < ν(O)` has the *same* strict
state at `d` while `C d ≠ C' d` — Proposition 7 fails without recording"); v2 Remark 3.7
Kind: N+ -/
theorem routingRoot_prop7_needs_recording (q q' : ℚ) (h0 : 0 < q) (h1 : q ≤ 1) (h0' : 0 < q')
    (h1' : q' ≤ 1) (hne : q ≠ q') :
    StrictOCAt (fun _ => rrStrictState q h0 h1) routeObs (procQ q h0.le h1) routingRoot () ∧
    StrictOCAt (fun _ => rrStrictState q h0 h1) routeObs (procQ q' h0'.le h1') routingRoot () ∧
    0 < nu (procQ q h0.le h1) routingRoot (routeObs ()) ∧
    0 < nu (procQ q' h0'.le h1') routingRoot (routeObs ()) ∧
    procQ q h0.le h1 () ≠ procQ q' h0'.le h1' () := by
  have hpay : ∀ (C : Proc Unit (fun _ => Act2) ℚ) (X : Finset RouteW), paySum C routingRoot X = 0 :=
    fun C X => Finset.sum_eq_zero fun ℓ _ => by rw [routingRoot_payoff, mul_zero]
  have hpr : ∀ X, (rrStrictState q h0 h1).pr X = if RouteW.inO ∈ X then 1 else 0 := by
    intro X
    rw [rrStrictState, calibratedState_pr, routingRoot_nu, routingRoot_nu]
    simp only [routeObs, Finset.mem_inter, Finset.mem_singleton]
    by_cases hX : RouteW.inO ∈ X <;> simp [hX, h0.ne']
  refine ⟨strictOCAt_calibratedState routeObs _ routingRoot _ () _ rfl, ?_,
    by rw [routingRoot_nu_obs]; exact h0, by rw [routingRoot_nu_obs]; exact h0', ?_⟩
  · intro _
    refine ⟨fun X => ?_, fun X _ _ => ?_⟩
    · rw [hpr, routingRoot_nu, routingRoot_nu]
      simp only [routeObs, Finset.mem_inter, Finset.mem_singleton]
      split_ifs <;> simp_all
    · rw [hpay, rrStrictState, calibratedState_V, hpay]; simp
  · intro h
    have := congrArg (fun p => p.w Act2.a) h
    simp [procQ] at this
    exact hne this

/-- The routing root is **not** recorded at `d` for any `q > 0`: the root is not
subtree-veridical (its `b`-leaf has world `outO ∉ O`).
Source: [[decision-problems-v2]] Remark 3.4 ("a selection node")
Kind: N+ -/
theorem routingRoot_not_recordsFor (q : ℚ) (h0 : 0 < q) (h1 : q ≤ 1) :
    ¬ RecordsFor routeObs routeActEv (procQ q h0.le h1) routingRoot () := by
  intro h
  have hpos : 0 < leafLaw (procQ q h0.le h1) routingRoot ⟨.a, ()⟩ := by
    unfold routingRoot; simp [procQ, h0]
  have hobs : world routingRoot ⟨.a, ()⟩ ∈ routeObs () := by
    unfold routingRoot; simp [routeObs]
  have hsv := ((h ⟨.a, ()⟩ hpos hobs).2 none rfl .a rfl).1
  have := hsv ⟨.b, ()⟩ (by unfold routingRoot; simp [leavesBelow])
  unfold routingRoot at this
  simp [routeObs] at this

end routingRoot

end Cleanroom.Decision.DpCalibration
