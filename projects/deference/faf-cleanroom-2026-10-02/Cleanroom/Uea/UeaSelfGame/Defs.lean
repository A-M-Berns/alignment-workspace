import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The finite updateless self-game: definitions of record

The finite formalism of [[updateless-self-game]] §1 (executable specs `updateless_self_game.py`:
`conditionals`, `realized_policies`, `fixed_points`; `updateless_existence.py`: `F_ext`, `F_herr`,
`is_fixed_point`, `floored_allowed`): finite situations `S`, actions `A`, policies `S → A`, utility
`U : (S → A) → [0,1]`, a chosen optimum `piStar`, an "other" distribution `Po ∈ Δ(A^S)` and `δ ∈ [0,1)`.
A UDT1.0 agent with a belief `μ` over policies plays at `s` an argmax of the pointwise EDT conditional
`E_μ[U(π') | π'(s) = a]` — no history, no updating. Conventions of record:

* **Herrmann's convention** for the pure conditional: an action of `μ`-probability zero at `s` is
  *unavailable* (`avail`), and the argmax `IsArgmaxH` ranges over available actions only. `cond` returns
  the junk value `0` at an unavailable action (Lean's `x / 0 = 0`); this is harmless only because every
  consumer (`IsArgmaxH`, `Realizes`, `TB`) requires availability — keep it that way.
* **Static belief** `mu := (1-δ) δ_{piStar} + δ Po` (the proposed theorem's object; Theorems A, B, E) and
  **self-consistent belief** `muSelf π := (1-δ) δ_π + δ Po` (Theorems C, D); `mu = muSelf piStar`.
* **Mixed policies** `σ : S → A → ℝ` with each `σ s ∈ Δ(A)`, product self-hypothesis `prodW σ`, value
  `Umix`, and the **continuous extension** `Fext` of the conditional (`F_ext`): at an action with
  `(1-δ) σ s a + δ pa s a = 0` the value is the fixed-coordinate value `Ucoord σ s a`, the limit as
  `σ s a ↓ 0`. The Herrmann mixed fixed point (`IsFPherr`) ranges over available actions only
  (`F_herr`); the extension fixed point (`IsFPext`) over all actions.
* **Floored fixed points** by the sign of the residual `max_a Fext − (1-δ) Ustar` (`floored_allowed`
  verbatim; the equality branch is the convex-hull rule).

Scope: finite updateless self-game — pointwise EDT conditional on one's own action, static or
self-consistent belief, product self-hypothesis for mixed policies, continuous extension at null actions
(`Fext`); not rOSI, not the sequential model of `uea-cole-shadow` (a separate finite formalism by design,
[[plan]] §0.4 rule 10 — no bridge is planned).

Package: `Cleanroom.Uea.UeaSelfGame` (faf-cleanroom run, 2026-09-30).
-/

namespace Cleanroom.Uea.UeaSelfGame

open Finset

/-! ### Objects that depend on the belief alone -/

section BeliefOnly

variable {S A : Type*} [Fintype A]

/-- **Mixed policy**: a simplex element at every situation.
Source: [[updateless-self-game]] §1 ("A mixed policy `σ = (σ_s)`")
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsMixed (σ : S → A → ℝ) : Prop := ∀ s, σ s ∈ stdSimplex ℝ A
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem IsMixed.nonneg {σ : S → A → ℝ} (h : IsMixed σ) (s : S) (a : A) : 0 ≤ σ s a := (h s).1 a
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem IsMixed.sum {σ : S → A → ℝ} (h : IsMixed σ) (s : S) : ∑ a, σ s a = 1 := (h s).2
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem IsMixed.le_one {σ : S → A → ℝ} (h : IsMixed σ) (s : S) (a : A) : σ s a ≤ 1 := by
  have := h.sum s
  have := Finset.single_le_sum (fun b _ => h.nonneg s b) (Finset.mem_univ a)
  linarith

variable [DecidableEq A]

/-- The pure policy `π` as a mixed policy (`δ_{π s}` at every `s`).
Source: [[updateless-self-game]] §1; `pure_sigma`
Kind: D
Fidelity: exact
Hyps: n/a -/
def pureMix (π : S → A) : S → A → ℝ := fun s a => if a = π s then 1 else 0
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem isMixed_pureMix (π : S → A) : IsMixed (pureMix π) := fun s =>
  ⟨fun a => by unfold pureMix; split_ifs <;> norm_num, by simp [pureMix]⟩

variable [Fintype S]

/-- **Product self-hypothesis** `σ^⊗(π') := ∏_s σ_s(π'(s))`.
Source: [[updateless-self-game]] §1; `product_weight`
Kind: D
Fidelity: exact
Hyps: n/a -/
def prodW (σ : S → A → ℝ) (π' : S → A) : ℝ := ∏ s, σ s (π' s)

omit [DecidableEq A] in
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem prodW_nonneg {σ : S → A → ℝ} (h : IsMixed σ) (π' : S → A) : 0 ≤ prodW σ π' :=
  Finset.prod_nonneg fun s _ => h.nonneg s (π' s)

omit [Fintype A] in
/-- `σ^⊗` at the pure policy `π` is the point mass at `π`.
Source: [[updateless-self-game]] §1; `pure_sigma`
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem prodW_pureMix (π π' : S → A) : prodW (pureMix π) π' = if π' = π then 1 else 0 := by
  unfold prodW pureMix
  by_cases h : π' = π
  · subst h; simp
  · rw [if_neg h]
    obtain ⟨s, hs⟩ : ∃ s, π' s ≠ π s := by
      by_contra hall
      push Not at hall
      exact h (funext hall)
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs])

variable [DecidableEq S]

/-- Denominator `μ(π'(s) = a)` of the conditional: the belief's mass on policies playing `a` at `s`.
Source: [[updateless-self-game]] §1; `conditionals` (`den`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def condDen (μ : (S → A) → ℝ) (s : S) (a : A) : ℝ :=
  ∑ π', if π' s = a then μ π' else 0

/-- **Availability** (Herrmann's convention): `a` is available at `s` iff `μ(π'(s) = a) > 0`.
Source: [[updateless-self-game]] §1 ("Zero-probability actions … unavailable"); `conditionals` (`None`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def avail (μ : (S → A) → ℝ) (s : S) (a : A) : Prop := 0 < condDen μ s a
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_nonneg {μ : (S → A) → ℝ} (hμ : ∀ π', 0 ≤ μ π') (s : S) (a : A) :
    0 ≤ condDen μ s a := by
  unfold condDen
  exact Finset.sum_nonneg fun π' _ => by split_ifs <;> simp [hμ π']

/-- The denominator is zero or positive (for a nonnegative belief): there is no third case.
Source: [[updateless-self-game]] §1 (availability dichotomy)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_eq_zero_or_pos {μ : (S → A) → ℝ} (hμ : ∀ π', 0 ≤ μ π') (s : S) (a : A) :
    condDen μ s a = 0 ∨ 0 < condDen μ s a :=
  (condDen_nonneg hμ s a).eq_or_lt.imp Eq.symm id

/-- The denominators over `a` sum to the total mass `∑ μ`.
Source: [[updateless-self-game]] §1
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sum_condDen (μ : (S → A) → ℝ) (s : S) : ∑ a, condDen μ s a = ∑ π', μ π' := by
  unfold condDen
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π' _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (π' s) (fun _ => μ π'), if_pos (Finset.mem_univ _)]

omit [Fintype A] [DecidableEq A] in
/-- `σ^⊗(π') = σ_s(π'(s)) · ∏_{t ≠ s} σ_t(π'(t))`: one coordinate split off the product.
Source: [[updateless-self-game]] §5 (Theorem C′ proof, "a product measure conditioned on one coordinate")
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem prodW_eq_mul_prod_erase (σ : S → A → ℝ) (π' : S → A) (s : S) :
    prodW σ π' = σ s (π' s) * ∏ t ∈ Finset.univ.erase s, σ t (π' t) :=
  (Finset.mul_prod_erase Finset.univ (fun t => σ t (π' t)) (Finset.mem_univ s)).symm

/-- **The `(−s)`-marginal of a product measure is a probability**: the policies playing `a` at `s`, weighted
by the product over the other coordinates, have total weight `1`. (Proof: the restricted product is the
full product of the kernel `τ_t := σ_t` for `t ≠ s`, `τ_s := δ_a`, and `∑_{π'} ∏_t τ_t(π'(t)) = ∏_t ∑_b τ_t(b)`.)
Source: [[updateless-self-game]] §5 (Theorem C′ proof)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem sum_prod_erase_eq_one {σ : S → A → ℝ} (h : IsMixed σ) (s : S) (a : A) :
    (∑ π' : S → A, if π' s = a then ∏ t ∈ Finset.univ.erase s, σ t (π' t) else 0) = 1 := by
  classical
  let τ : S → A → ℝ := fun t b => if t = s then (if b = a then 1 else 0) else σ t b
  have hterm : ∀ π' : S → A,
      (if π' s = a then ∏ t ∈ Finset.univ.erase s, σ t (π' t) else 0) = ∏ t, τ t (π' t) := by
    intro π'
    rw [← Finset.mul_prod_erase Finset.univ (fun t => τ t (π' t)) (Finset.mem_univ s)]
    have h1 : τ s (π' s) = if π' s = a then 1 else 0 := by simp [τ]
    have h2 : ∏ t ∈ Finset.univ.erase s, τ t (π' t) = ∏ t ∈ Finset.univ.erase s, σ t (π' t) := by
      refine Finset.prod_congr rfl fun t ht => ?_
      have : t ≠ s := Finset.ne_of_mem_erase ht
      simp [τ, this]
    rw [h1, h2]
    split_ifs <;> simp
  simp_rw [hterm]
  have hps : ∑ π' : S → A, ∏ t, τ t (π' t) = ∏ t, ∑ b, τ t b := by
    rw [Finset.prod_univ_sum]
    simp [Fintype.piFinset_univ]
  rw [hps]
  refine Finset.prod_eq_one fun t _ => ?_
  by_cases hts : t = s
  · subst hts; simp [τ]
  · simp [τ, hts, h.sum t]

omit [DecidableEq A] in
/-- The product self-hypothesis is a probability on policies.
Source: [[updateless-self-game]] §1
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem sum_prodW {σ : S → A → ℝ} (h : IsMixed σ) : ∑ π', prodW σ π' = 1 := by
  classical
  unfold prodW
  have hps : ∑ π' : S → A, ∏ t, σ t (π' t) = ∏ t, ∑ b, σ t b := by
    rw [Finset.prod_univ_sum]
    simp [Fintype.piFinset_univ]
  rw [hps]
  exact Finset.prod_eq_one fun t _ => h.sum t

end BeliefOnly

/-- **The finite updateless self-game**: utility `U ∈ [0,1]` on policies `S → A`, a chosen maximizer
`piStar` (the note's `π*`; theorems are stated for this chosen one, and `Ustar := U piStar` is the value of
*every* maximizer), an "other" distribution `Po ∈ Δ(A^S)`, and `δ ∈ [0,1)` (`δ = 0` is allowed so that
Theorem C's certain corner is inside the structure; `0 < δ` is a hypothesis where a theorem needs it).
Source: [[updateless-self-game]] §1 ("Decision problem", "`(1-δ)`-believes it is UDT1.1")
Kind: D
Fidelity: exact (`U*` kept as a variable `≤ 1`, not normalised to `1`)
Hyps: n/a -/
structure Game (S A : Type*) [Fintype S] [DecidableEq S] [Fintype A] where
  /-- the utility of a policy -/
  U : (S → A) → ℝ
  U_nonneg : ∀ π, 0 ≤ U π
  U_le_one : ∀ π, U π ≤ 1
  /-- a chosen optimal policy -/
  piStar : S → A
  piStar_max : ∀ π, U π ≤ U piStar
  /-- the "other" hypothesis about the policy -/
  Po : (S → A) → ℝ
  Po_mem : Po ∈ stdSimplex ℝ (S → A)
  /-- the prior on "other" -/
  δ : ℝ
  δ_nonneg : 0 ≤ δ
  δ_lt_one : δ < 1

namespace Game

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] (G : Game S A)

/-- `U* := U piStar`, the optimal value.
Source: [[updateless-self-game]] §1
Kind: D
Fidelity: exact
Hyps: n/a -/
def Ustar : ℝ := G.U G.piStar

/-- The trust-bound threshold `(1-δ) U*`.
Source: [[updateless-self-game]] §1 (`TB_s`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def thr : ℝ := (1 - G.δ) * G.Ustar
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Ustar_nonneg : 0 ≤ G.Ustar := G.U_nonneg _
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Ustar_le_one : G.Ustar ≤ 1 := G.U_le_one _
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem U_le_Ustar (π : S → A) : G.U π ≤ G.Ustar := G.piStar_max π
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem one_sub_δ_pos : 0 < 1 - G.δ := by linarith [G.δ_lt_one]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem thr_nonneg : 0 ≤ G.thr := mul_nonneg G.one_sub_δ_pos.le G.Ustar_nonneg
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Po_nonneg (π : S → A) : 0 ≤ G.Po π := G.Po_mem.1 π
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Po_sum : ∑ π, G.Po π = 1 := G.Po_mem.2
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Po_le_one (π : S → A) : G.Po π ≤ 1 := by
  have := G.Po_sum
  have h := Finset.single_le_sum (fun π' _ => G.Po_nonneg π') (Finset.mem_univ π)
  linarith

/-! ### Beliefs over policies -/

variable [DecidableEq A]

/-- **Self-consistent belief** `μ_π := (1-δ) δ_π + δ Po`: the agent whose own policy is `π` and who
assigns prior `1-δ` to that fact. With `π := piStar` it is the static belief `mu`.
Source: [[updateless-self-game]] §1 ("Self-consistent belief / fixed point"); `mixture`
Kind: D
Fidelity: exact
Hyps: n/a -/
def muSelf (π : S → A) : (S → A) → ℝ :=
  fun π' => (1 - G.δ) * (if π' = π then 1 else 0) + G.δ * G.Po π'

/-- **Static belief** `μ := (1-δ) δ_{piStar} + δ Po` — "`(1-δ)`-believes it is UDT1.1", the proposed
theorem's object (Theorems A, B).
Source: [[updateless-self-game]] §1; [[00-founding-sketches]] §3
Kind: D
Fidelity: exact
Hyps: n/a -/
def mu : (S → A) → ℝ := G.muSelf G.piStar
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem muSelf_nonneg (π π' : S → A) : 0 ≤ G.muSelf π π' := by
  unfold muSelf
  have := G.δ_nonneg; have := G.one_sub_δ_pos; have := G.Po_nonneg π'
  split_ifs <;> nlinarith
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem muSelf_sum (π : S → A) : ∑ π', G.muSelf π π' = 1 := by
  unfold muSelf
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_ite_eq' Finset.univ π,
    if_pos (Finset.mem_univ π), G.Po_sum]
  ring
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem muSelf_self (π : S → A) : G.muSelf π π = (1 - G.δ) + G.δ * G.Po π := by
  simp [muSelf]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem muSelf_ne (π π' : S → A) (h : π' ≠ π) : G.muSelf π π' = G.δ * G.Po π' := by
  simp [muSelf, h]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem mu_nonneg (π' : S → A) : 0 ≤ G.mu π' := G.muSelf_nonneg _ _
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem mu_sum : ∑ π', G.mu π' = 1 := G.muSelf_sum _

/-! ### The pointwise EDT conditional (pure) -/

/-- Numerator `∑_{π' : π'(s) = a} μ(π') U(π')` of the conditional.
Source: [[updateless-self-game]] §1; `conditionals` (`num`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def condNum (μ : (S → A) → ℝ) (s : S) (a : A) : ℝ :=
  ∑ π', if π' s = a then μ π' * G.U π' else 0

/-- **The pointwise EDT conditional** `E_μ[U(π') | π'(s) = a] := condNum / condDen`. Junk value `0` when
`condDen μ s a = 0` (Lean's division); harmless only because `IsArgmaxH`, `Realizes` and `TB` all require
`avail` — never consume `cond` at an unavailable action.
Source: [[updateless-self-game]] §1 ("UDT1.0 with a belief"); `conditionals`
Kind: D
Fidelity: exact at available actions; junk `0` elsewhere (see the docstring)
Hyps: n/a -/
noncomputable def cond (μ : (S → A) → ℝ) (s : S) (a : A) : ℝ :=
  G.condNum μ s a / condDen μ s a

/-- **Argmax under Herrmann's convention**: `a` is available and no available `b` has a larger conditional.
Source: [[updateless-self-game]] §1; `argmax_set`
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsArgmaxH (μ : (S → A) → ℝ) (s : S) (a : A) : Prop :=
  avail μ s a ∧ ∀ b, avail μ s b → G.cond μ s b ≤ G.cond μ s a

/-- **Realized policy**: `π` is realized by the belief `μ` iff `π s` is a Herrmann argmax at every `s`
(any element of the product of argmax sets).
Source: [[updateless-self-game]] §1 ("Ties", "realized policy"); `realized_policies`
Kind: D
Fidelity: exact
Hyps: n/a -/
def Realizes (μ : (S → A) → ℝ) (π : S → A) : Prop := ∀ s, G.IsArgmaxH μ s (π s)

/-- **Strict argmax everywhere**: every argmax set is a singleton.
Source: [[updateless-self-game]] §1 ("strict")
Kind: D
Fidelity: exact
Hyps: n/a -/
def StrictArgmax (μ : (S → A) → ℝ) : Prop := ∀ s, ∃! a, G.IsArgmaxH μ s a

/-- **Trust bound at `s`** (`TB_s`): some available action has conditional `≥ (1-δ) U*` (equivalently the
max over available actions is `≥ (1-δ) U*`).
Source: [[updateless-self-game]] §1 ("Trust bound at `s`"); `trust_bound_ok`
Kind: D
Fidelity: exact
Hyps: n/a -/
def TB (μ : (S → A) → ℝ) (s : S) : Prop := ∃ a, avail μ s a ∧ G.thr ≤ G.cond μ s a

/-- **Pure fixed point** of the self-consistent agent: `π s` is a Herrmann argmax under `μ_π` at every `s`.
Source: [[updateless-self-game]] §1 ("pure fixed point"); `fixed_points`
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsPureFP (π : S → A) : Prop := ∀ s, G.IsArgmaxH (G.muSelf π) s (π s)

/-- **Pure floored fixed point** (Herrmann availability), by the three branches of `floored_allowed` written
with explicit quantifiers over available actions: if every available conditional is `< (1-δ) U*` then
`π s = piStar s`; if some available conditional is `> (1-δ) U*` then `π s` is an argmax; if the available
maximum equals `(1-δ) U*` then `π s` is an argmax or `π s = piStar s`.
Source: [[updateless-self-game]] §1 ("Floored agent"); `floored_allowed`, `is_floored_fixed_point`
Kind: D
Fidelity: exact (the three branches are exhaustive because `π s` itself is always available under `μ_π`)
Hyps: n/a -/
def IsPureFPfloored (π : S → A) : Prop := ∀ s,
  ((∀ a, avail (G.muSelf π) s a → G.cond (G.muSelf π) s a < G.thr) → π s = G.piStar s) ∧
  ((∃ a, avail (G.muSelf π) s a ∧ G.thr < G.cond (G.muSelf π) s a) →
    G.IsArgmaxH (G.muSelf π) s (π s)) ∧
  ((∀ a, avail (G.muSelf π) s a → G.cond (G.muSelf π) s a ≤ G.thr) →
    (∃ a, avail (G.muSelf π) s a ∧ G.cond (G.muSelf π) s a = G.thr) →
    G.IsArgmaxH (G.muSelf π) s (π s) ∨ π s = G.piStar s)

/-! ### Basic facts about the pure conditional -/

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condNum_nonneg {μ : (S → A) → ℝ} (hμ : ∀ π', 0 ≤ μ π') (s : S) (a : A) :
    0 ≤ G.condNum μ s a := by
  unfold condNum
  exact Finset.sum_nonneg fun π' _ => by
    split_ifs
    · exact mul_nonneg (hμ π') (G.U_nonneg π')
    · exact le_rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_le_condDen {μ : (S → A) → ℝ} (hμ : ∀ π', 0 ≤ μ π') (s : S) (a : A) :
    G.condNum μ s a ≤ condDen μ s a := by
  unfold condNum condDen
  refine Finset.sum_le_sum fun π' _ => ?_
  split_ifs
  · have := G.U_le_one π'; have := hμ π'; nlinarith
  · exact le_rfl

/-- The conditional lies in `[0,1]` at every available action.
Source: [[updateless-self-game]] §1 (`U ∈ [0,1]`)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem cond_mem_Icc {μ : (S → A) → ℝ} (hμ : ∀ π', 0 ≤ μ π') {s : S} {a : A} (h : avail μ s a) :
    0 ≤ G.cond μ s a ∧ G.cond μ s a ≤ 1 := by
  unfold cond
  have hd : 0 < condDen μ s a := h
  constructor
  · exact div_nonneg (G.condNum_nonneg hμ s a) hd.le
  · rw [div_le_one hd]; exact G.condNum_le_condDen hμ s a
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_nonneg {μ : (S → A) → ℝ} (hμ : ∀ π', 0 ≤ μ π') {s : S} {a : A} (h : avail μ s a) :
    0 ≤ G.cond μ s a := (G.cond_mem_Icc hμ h).1
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem cond_le_one {μ : (S → A) → ℝ} (hμ : ∀ π', 0 ≤ μ π') {s : S} {a : A} (h : avail μ s a) :
    G.cond μ s a ≤ 1 := (G.cond_mem_Icc hμ h).2
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_mul_cond {μ : (S → A) → ℝ} {s : S} {a : A} (h : avail μ s a) :
    condDen μ s a * G.cond μ s a = G.condNum μ s a := by
  unfold cond; have hd : condDen μ s a ≠ 0 := ne_of_gt h
  field_simp
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem sum_condNum (μ : (S → A) → ℝ) (s : S) : ∑ a, G.condNum μ s a = ∑ π', μ π' * G.U π' := by
  unfold condNum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π' _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (π' s) (fun _ => μ π' * G.U π'), if_pos (Finset.mem_univ _)]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_eq_zero_of_condDen_eq_zero {μ : (S → A) → ℝ} (hμ : ∀ π', 0 ≤ μ π') {s : S} {a : A}
    (h : condDen μ s a = 0) : G.condNum μ s a = 0 := by
  have h0 := G.condNum_nonneg hμ s a
  have h1 := G.condNum_le_condDen hμ s a
  linarith

/-- **The unconditional value is the `condDen`-weighted combination of the conditionals**:
`E_μ U = ∑_a condDen μ s a · cond μ s a` (unavailable actions contribute `0`).
Source: [[updateless-self-game]] §1 ("`E_μ[U]` is a convex combination of the available conditionals")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem sum_condDen_mul_cond {μ : (S → A) → ℝ} (hμ : ∀ π', 0 ≤ μ π') (s : S) :
    ∑ a, condDen μ s a * G.cond μ s a = ∑ π', μ π' * G.U π' := by
  rw [← G.sum_condNum μ s]
  refine Finset.sum_congr rfl fun a _ => ?_
  rcases condDen_eq_zero_or_pos hμ s a with h | h
  · rw [h, zero_mul, G.condNum_eq_zero_of_condDen_eq_zero hμ h]
  · exact G.condDen_mul_cond h

/-- **A zero-probability action is never a strict argmax under the "unconditional" convention**: for a
probability `μ`, some available action's conditional is at least the unconditional value `E_μ U` (the
value the convention assigns to unavailable actions). Under the "zero" convention the same follows from
`cond_nonneg`. So the three conventions differ only in tie-breaking.
Source: [[updateless-self-game]] §1 ("Under all three, a zero-probability action is never a strict argmax")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem exists_avail_uncond_le_cond {μ : (S → A) → ℝ} (hμ : ∀ π', 0 ≤ μ π') (hsum : ∑ π', μ π' = 1)
    (s : S) : ∃ a, avail μ s a ∧ ∑ π', μ π' * G.U π' ≤ G.cond μ s a := by
  by_contra hcon
  push Not at hcon
  have hlt : ∑ a, condDen μ s a * G.cond μ s a < ∑ a, condDen μ s a * (∑ π', μ π' * G.U π') := by
    have hex : ∃ a, 0 < condDen μ s a := by
      by_contra hall
      push Not at hall
      have : ∑ a, condDen μ s a = 0 :=
        Finset.sum_eq_zero fun a _ => le_antisymm (hall a) (condDen_nonneg hμ s a)
      rw [sum_condDen, hsum] at this
      exact one_ne_zero this
    obtain ⟨a₀, ha₀⟩ := hex
    refine Finset.sum_lt_sum (fun a _ => ?_) ⟨a₀, Finset.mem_univ _, ?_⟩
    · rcases condDen_eq_zero_or_pos hμ s a with h | h
      · simp [h]
      · exact mul_le_mul_of_nonneg_left (hcon a h).le h.le
    · exact mul_lt_mul_of_pos_left (hcon a₀ ha₀) ha₀
  rw [G.sum_condDen_mul_cond hμ, ← Finset.sum_mul, sum_condDen, hsum, one_mul] at hlt
  exact lt_irrefl _ hlt

/-! ### Mixed policies: the continuous extension of the conditional -/

/-- `p_a := Po(π'(s) = a)`, the "other" mass on policies playing `a` at `s` (`condDen` of `Po`).
Source: [[updateless-self-game]] §2 (self-evidence), §5 (`p_a`); `po_stats`
Kind: D
Fidelity: exact
Hyps: n/a -/
def pa (s : S) (a : A) : ℝ := condDen G.Po s a

/-- `p_a V_a := ∑_{ρ : ρ(s) = a} Po(ρ) U(ρ)` (`condNum` of `Po`); `V_a = pva / pa` when `pa > 0`.
Source: [[updateless-self-game]] §2, §5; `po_stats`
Kind: D
Fidelity: exact
Hyps: n/a -/
def pva (s : S) (a : A) : ℝ := G.condNum G.Po s a

/-- **Value of a mixed policy** `U(σ) := E_{σ^⊗}[U]`.
Source: [[updateless-self-game]] §1; `value_mixed`
Kind: D
Fidelity: exact
Hyps: n/a -/
def Umix (σ : S → A → ℝ) : ℝ := ∑ π', prodW σ π' * G.U π'

/-- **Fixed-coordinate value** `U_a(σ) := E_{σ_{-s}^⊗}[U(a, ·)]`, the product over the other coordinates
with coordinate `s` fixed to `a` (a theorem, `cond_prodW`, identifies it with the `σ^⊗`-conditional given
`π'(s) = a` when `σ s a > 0`).
Source: [[updateless-self-game]] §5 (Theorem C′ proof); `U_cond_self`
Kind: D
Fidelity: exact
Hyps: n/a -/
def Ucoord (σ : S → A → ℝ) (s : S) (a : A) : ℝ :=
  ∑ π' : S → A, if π' s = a then (∏ t ∈ Finset.univ.erase s, σ t (π' t)) * G.U π' else 0

/-- The mixed denominator `(1-δ) σ_s(a) + δ p_a` — the belief `μ_σ`'s mass on `π'(s) = a`.
Source: [[updateless-self-game]] §5; `F_ext` (`den`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def denMix (σ : S → A → ℝ) (s : S) (a : A) : ℝ := (1 - G.δ) * σ s a + G.δ * G.pa s a

/-- **The extended conditional of record** (`F_ext`): `[(1-δ) σ_s(a) U_a(σ) + δ p_a V_a] / [(1-δ) σ_s(a) + δ p_a]`,
and `U_a(σ)` when the denominator vanishes (the limit as `σ_s(a) ↓ 0`; `Fext_eq_Ucoord_of_pa_eq_zero`).
Source: [[updateless-self-game]] §6 ("the continuous extension"); `F_ext`
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def Fext (σ : S → A → ℝ) (s : S) (a : A) : ℝ :=
  if G.denMix σ s a = 0 then G.Ucoord σ s a
  else ((1 - G.δ) * σ s a * G.Ucoord σ s a + G.δ * G.pva s a) / G.denMix σ s a

/-- **Mixed availability** (Herrmann): `(1-δ) σ_s(a) + δ p_a > 0`.
Source: [[updateless-self-game]] §6; `F_herr` (`None`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def availMix (σ : S → A → ℝ) (s : S) (a : A) : Prop := 0 < G.denMix σ s a

/-- **Mixed fixed point under the continuous extension**: `σ` is a mixed policy and every supported action
at `s` maximises `Fext σ s ·` over *all* actions.
Source: [[updateless-self-game]] §1, §6; `is_fixed_point` (`convention='ext'`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsFPext (σ : S → A → ℝ) : Prop :=
  IsMixed σ ∧ ∀ s a, 0 < σ s a → ∀ b, G.Fext σ s b ≤ G.Fext σ s a

/-- **Mixed fixed point under Herrmann's convention**: every supported action maximises `Fext σ s ·` over
the *available* actions.
Source: [[updateless-self-game]] §1, §6; `is_fixed_point` (`convention='herr'`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsFPherr (σ : S → A → ℝ) : Prop :=
  IsMixed σ ∧ ∀ s a, 0 < σ s a → ∀ b, G.availMix σ s b → G.Fext σ s b ≤ G.Fext σ s a

/-- **Trust bound at `s` for a mixed policy** under the extension: some action has `Fext ≥ (1-δ) U*`.
Source: [[updateless-self-game]] §1 (`TB_s`), §5 (Theorem C′); `trust_bound_holds`
Kind: D
Fidelity: exact
Hyps: n/a -/
def TBext (σ : S → A → ℝ) (s : S) : Prop := ∃ a, G.thr ≤ G.Fext σ s a

/-- **Trust bound at `s` for a mixed policy** under Herrmann's convention: some *available* action has
`Fext ≥ (1-δ) U*`.
Source: [[updateless-self-game]] §1 (`TB_s`); `trust_bound_holds` (`convention='herr'`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def TBherr (σ : S → A → ℝ) (s : S) : Prop := ∃ a, G.availMix σ s a ∧ G.thr ≤ G.Fext σ s a

section Floored

variable [Nonempty A]

/-- `max_a Fext σ s a` (the extension convention; `A` is nonempty).
Source: [[updateless-self-game]] §1 ("Floored agent"); `floored_allowed` (`m`)
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def maxF (σ : S → A → ℝ) (s : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a => G.Fext σ s a)

/-- The residual `max_a Fext σ s a − (1-δ) U*` whose sign selects the floored agent's branch.
Source: [[updateless-self-game]] §1 ("Floored agent"); `floored_allowed`
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def resid (σ : S → A → ℝ) (s : S) : ℝ := G.maxF σ s - G.thr

/-- **Floored mixed fixed point** (extension convention), `floored_allowed` verbatim: `resid < 0 ⇒ supp σ_s =
{piStar s}`; `resid > 0 ⇒ supp ⊆ argmax`; `resid = 0 ⇒ supp ⊆ argmax ∪ {piStar s}`.
Source: [[updateless-self-game]] §1 ("Floored agent"); `is_floored_fixed_point`
Kind: D
Fidelity: exact
Hyps: n/a -/
def IsFlooredFPext (σ : S → A → ℝ) : Prop :=
  IsMixed σ ∧ ∀ s,
    (G.resid σ s < 0 → ∀ a, 0 < σ s a → a = G.piStar s) ∧
    (0 < G.resid σ s → ∀ a, 0 < σ s a → G.Fext σ s a = G.maxF σ s) ∧
    (G.resid σ s = 0 → ∀ a, 0 < σ s a → G.Fext σ s a = G.maxF σ s ∨ a = G.piStar s)
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Fext_le_maxF (σ : S → A → ℝ) (s : S) (a : A) : G.Fext σ s a ≤ G.maxF σ s :=
  Finset.le_sup' (fun a => G.Fext σ s a) (Finset.mem_univ a)
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem exists_Fext_eq_maxF (σ : S → A → ℝ) (s : S) : ∃ a, G.Fext σ s a = G.maxF σ s := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun a => G.Fext σ s a)
  exact ⟨a, ha.symm⟩

end Floored

/-! ### Facts about `pa`, `pva`, `Ucoord`, `Umix` -/

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem pa_nonneg (s : S) (a : A) : 0 ≤ G.pa s a := condDen_nonneg G.Po_nonneg s a
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem pva_nonneg (s : S) (a : A) : 0 ≤ G.pva s a := G.condNum_nonneg G.Po_nonneg s a
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem pva_le_pa (s : S) (a : A) : G.pva s a ≤ G.pa s a := G.condNum_le_condDen G.Po_nonneg s a
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem sum_pa (s : S) : ∑ a, G.pa s a = 1 := by
  unfold pa; rw [sum_condDen, G.Po_sum]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem pa_le_one (s : S) (a : A) : G.pa s a ≤ 1 := by
  have := G.sum_pa s
  have := Finset.single_le_sum (fun b _ => G.pa_nonneg s b) (Finset.mem_univ a)
  linarith
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem denMix_nonneg {σ : S → A → ℝ} (h : IsMixed σ) (s : S) (a : A) : 0 ≤ G.denMix σ s a := by
  unfold denMix
  have := G.one_sub_δ_pos; have := G.δ_nonneg; have := h.nonneg s a; have := G.pa_nonneg s a
  positivity

/-- A supported action is available: `denMix ≥ (1-δ) σ_s(a) > 0`.
Source: [[updateless-self-game]] §6 (`FP_ext ⊆ FP_Herr` argument)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem availMix_of_pos {σ : S → A → ℝ} (s : S) {a : A} (ha : 0 < σ s a) : G.availMix σ s a := by
  unfold availMix denMix
  have := G.one_sub_δ_pos; have := G.δ_nonneg; have := G.pa_nonneg s a
  nlinarith
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Ucoord_nonneg {σ : S → A → ℝ} (h : IsMixed σ) (s : S) (a : A) : 0 ≤ G.Ucoord σ s a := by
  unfold Ucoord
  refine Finset.sum_nonneg fun π' _ => ?_
  split_ifs
  · exact mul_nonneg (Finset.prod_nonneg fun t _ => h.nonneg t (π' t)) (G.U_nonneg π')
  · exact le_rfl
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Ucoord_le_one {σ : S → A → ℝ} (h : IsMixed σ) (s : S) (a : A) : G.Ucoord σ s a ≤ 1 := by
  unfold Ucoord
  rw [← sum_prod_erase_eq_one h s a]
  refine Finset.sum_le_sum fun π' _ => ?_
  split_ifs
  · have h0 : 0 ≤ ∏ t ∈ Finset.univ.erase s, σ t (π' t) := Finset.prod_nonneg fun t _ => h.nonneg t (π' t)
    have := G.U_le_one π'
    nlinarith
  · exact le_rfl

/-- **Law of total expectation for the product measure**: `U(σ) = ∑_a σ_s(a) U_a(σ)` at every `s`.
Source: [[updateless-self-game]] §5 (Theorem C′ proof, "`∑_a q_a U_a = U(σ)`")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Umix_eq_sum_Ucoord (σ : S → A → ℝ) (s : S) : G.Umix σ = ∑ a, σ s a * G.Ucoord σ s a := by
  unfold Umix Ucoord
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun π' _ => ?_
  rw [prodW_eq_mul_prod_erase σ π' s]
  have : ∀ a, σ s a * (if π' s = a then (∏ t ∈ Finset.univ.erase s, σ t (π' t)) * G.U π' else 0) =
      if π' s = a then σ s (π' s) * (∏ t ∈ Finset.univ.erase s, σ t (π' t)) * G.U π' else 0 := by
    intro a; split_ifs with h
    · subst h; ring
    · simp
  simp_rw [this]
  rw [Finset.sum_ite_eq Finset.univ (π' s), if_pos (Finset.mem_univ _)]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condDen_prodW {σ : S → A → ℝ} (h : IsMixed σ) (s : S) (a : A) :
    condDen (prodW σ) s a = σ s a := by
  unfold condDen
  have : ∀ π' : S → A, (if π' s = a then prodW σ π' else 0) =
      σ s a * (if π' s = a then ∏ t ∈ Finset.univ.erase s, σ t (π' t) else 0) := by
    intro π'; split_ifs with hp
    · rw [prodW_eq_mul_prod_erase σ π' s, hp]
    · simp
  simp_rw [this]
  rw [← Finset.mul_sum, sum_prod_erase_eq_one h s a, mul_one]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_prodW (σ : S → A → ℝ) (s : S) (a : A) :
    G.condNum (prodW σ) s a = σ s a * G.Ucoord σ s a := by
  unfold condNum Ucoord
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun π' _ => ?_
  split_ifs with hp
  · rw [prodW_eq_mul_prod_erase σ π' s, hp]; ring
  · simp

/-- **`Ucoord` is the product-measure conditional**: `E_{σ^⊗}[U | π'(s) = a] = U_a(σ)` whenever
`σ_s(a) > 0` (the note's "a product measure conditioned on one coordinate is the product with that
coordinate fixed").
Source: [[updateless-self-game]] §5 (Theorem C′ proof)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem cond_prodW {σ : S → A → ℝ} (h : IsMixed σ) {s : S} {a : A} (ha : 0 < σ s a) :
    G.cond (prodW σ) s a = G.Ucoord σ s a := by
  unfold cond
  rw [G.condNum_prodW, condDen_prodW h]
  field_simp

/-- The extended conditional lies in `[0,1]` for every mixed policy and every action (available or not).
Source: [[updateless-self-game]] §6
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Fext_mem_Icc {σ : S → A → ℝ} (h : IsMixed σ) (s : S) (a : A) :
    0 ≤ G.Fext σ s a ∧ G.Fext σ s a ≤ 1 := by
  unfold Fext
  split_ifs with hd
  · exact ⟨G.Ucoord_nonneg h s a, G.Ucoord_le_one h s a⟩
  · have hpos : 0 < G.denMix σ s a := lt_of_le_of_ne (G.denMix_nonneg h s a) (Ne.symm hd)
    have h1 := G.one_sub_δ_pos; have h2 := G.δ_nonneg; have h3 := h.nonneg s a
    have h4 := G.Ucoord_nonneg h s a; have h5 := G.Ucoord_le_one h s a
    have h6 := G.pva_nonneg s a; have h7 := G.pva_le_pa s a
    constructor
    · apply div_nonneg _ hpos.le
      positivity
    · rw [div_le_one hpos]
      unfold denMix
      nlinarith [mul_nonneg h1.le h3]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Fext_nonneg {σ : S → A → ℝ} (h : IsMixed σ) (s : S) (a : A) : 0 ≤ G.Fext σ s a :=
  (G.Fext_mem_Icc h s a).1
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Fext_le_one {σ : S → A → ℝ} (h : IsMixed σ) (s : S) (a : A) : G.Fext σ s a ≤ 1 :=
  (G.Fext_mem_Icc h s a).2
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem Fext_eq_of_availMix {σ : S → A → ℝ} {s : S} {a : A} (h : G.availMix σ s a) :
    G.Fext σ s a = ((1 - G.δ) * σ s a * G.Ucoord σ s a + G.δ * G.pva s a) / G.denMix σ s a := by
  unfold Fext; rw [if_neg (ne_of_gt h)]

/-- **The extension is the limit**: when `p_a = 0`, `Fext σ s a = U_a(σ)` identically — both branches agree
(`((1-δ) q U_a)/((1-δ) q) = U_a` for `q > 0`, and the `if` gives `U_a` at `q = 0`). This is the case split
that makes `Fext` continuous on the product of simplices.
Source: [[updateless-self-game]] §6 ("with the continuous extension … the conditionals are continuous")
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Fext_eq_Ucoord_of_pa_eq_zero (σ : S → A → ℝ) {s : S} {a : A} (hpa : G.pa s a = 0) :
    G.Fext σ s a = G.Ucoord σ s a := by
  have hpva : G.pva s a = 0 := G.condNum_eq_zero_of_condDen_eq_zero G.Po_nonneg hpa
  unfold Fext denMix
  rw [hpa, hpva]
  split_ifs with hd
  · rfl
  · have hq : σ s a ≠ 0 := by
      intro h0; apply hd; rw [h0]; ring
    have h1 : (1 - G.δ) ≠ 0 := ne_of_gt G.one_sub_δ_pos
    field_simp
    ring

/-! ### The pure/mixed bridge -/

/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem condDen_muSelf (π : S → A) (s : S) (a : A) :
    condDen (G.muSelf π) s a = (1 - G.δ) * (if π s = a then 1 else 0) + G.δ * G.pa s a := by
  unfold condDen muSelf pa condDen
  have : ∀ π' : S → A, (if π' s = a then (1 - G.δ) * (if π' = π then 1 else 0) + G.δ * G.Po π' else 0) =
      (1 - G.δ) * (if π' = π then (if π s = a then 1 else 0) else 0) +
        G.δ * (if π' s = a then G.Po π' else 0) := by
    intro π'
    by_cases hp : π' = π
    · subst hp; split_ifs <;> simp_all
    · simp [hp]
  simp_rw [this]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_ite_eq' Finset.univ π, if_pos (Finset.mem_univ _)]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem condNum_muSelf (π : S → A) (s : S) (a : A) :
    G.condNum (G.muSelf π) s a = (1 - G.δ) * (if π s = a then G.U π else 0) + G.δ * G.pva s a := by
  unfold condNum muSelf pva condNum
  have : ∀ π' : S → A,
      (if π' s = a then ((1 - G.δ) * (if π' = π then 1 else 0) + G.δ * G.Po π') * G.U π' else 0) =
      (1 - G.δ) * (if π' = π then (if π s = a then G.U π else 0) else 0) +
        G.δ * (if π' s = a then G.Po π' * G.U π' else 0) := by
    intro π'
    by_cases hp : π' = π
    · subst hp; by_cases hs : π' s = a <;> (simp [hs]; try ring)
    · by_cases hs : π' s = a <;> (simp [hp, hs]; try ring)
  simp_rw [this]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_ite_eq' Finset.univ π, if_pos (Finset.mem_univ _)]

/-- The own action `π s` is always available under the self-consistent belief `μ_π`.
Source: [[updateless-self-game]] §5
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem avail_muSelf_self (π : S → A) (s : S) : avail (G.muSelf π) s (π s) := by
  unfold avail
  rw [G.condDen_muSelf, if_pos rfl]
  have := G.one_sub_δ_pos; have := G.δ_nonneg; have := G.pa_nonneg s (π s)
  nlinarith
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem denMix_pureMix (π : S → A) (s : S) (a : A) :
    G.denMix (pureMix π) s a = condDen (G.muSelf π) s a := by
  rw [G.condDen_muSelf]; unfold denMix pureMix
  by_cases h : a = π s
  · subst h; simp
  · simp [h, Ne.symm h]
/-- Supporting lemma (no headline claim; see the headline it serves).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) -/

theorem availMix_pureMix_iff (π : S → A) (s : S) (a : A) :
    G.availMix (pureMix π) s a ↔ avail (G.muSelf π) s a := by
  unfold availMix avail; rw [G.denMix_pureMix]

/-- At the pure policy `π`, the fixed-coordinate value is `U(π[s ↦ a])`.
Source: [[updateless-self-game]] §5
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem Ucoord_pureMix (π : S → A) (s : S) (a : A) :
    G.Ucoord (pureMix π) s a = G.U (Function.update π s a) := by
  unfold Ucoord pureMix
  have hprod : ∀ π' : S → A, (∏ t ∈ Finset.univ.erase s, (if π' t = π t then (1:ℝ) else 0)) =
      if ∀ t ∈ Finset.univ.erase s, π' t = π t then 1 else 0 := fun π' => by convert Finset.prod_boole
  simp_rw [hprod]
  have key : ∀ π' : S → A,
      (if π' s = a then (if ∀ t ∈ Finset.univ.erase s, π' t = π t then (1:ℝ) else 0) * G.U π' else 0) =
      if π' = Function.update π s a then G.U π' else 0 := by
    intro π'
    by_cases h1 : π' = Function.update π s a
    · subst h1
      have hall : ∀ t ∈ Finset.univ.erase s, Function.update π s a t = π t := fun t ht =>
        Function.update_of_ne (Finset.ne_of_mem_erase ht) a π
      rw [if_pos (Function.update_self s a π), if_pos hall, one_mul, if_pos rfl]
    · rw [if_neg h1]
      by_cases h2 : π' s = a
      · by_cases h3 : ∀ t ∈ Finset.univ.erase s, π' t = π t
        · exfalso; apply h1
          funext t
          by_cases hts : t = s
          · subst hts; simp [h2]
          · rw [Function.update_of_ne hts]; exact h3 t (Finset.mem_erase.2 ⟨hts, Finset.mem_univ _⟩)
        · rw [if_pos h2, if_neg h3, zero_mul]
      · simp [h2]
  simp_rw [key]
  rw [Finset.sum_ite_eq' Finset.univ, if_pos (Finset.mem_univ _)]

/-- **The pure/mixed bridge**: at the pure policy `π` and an available action, the extended conditional is
the pure conditional under `μ_π` — the mixed and pure developments are one object.
Source: [[updateless-self-game]] §1, §5–§6 (mandate target 1)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem Fext_pureMix (π : S → A) {s : S} {a : A} (h : avail (G.muSelf π) s a) :
    G.Fext (pureMix π) s a = G.cond (G.muSelf π) s a := by
  have hav : G.availMix (pureMix π) s a := (G.availMix_pureMix_iff π s a).2 h
  rw [G.Fext_eq_of_availMix hav, G.denMix_pureMix]
  unfold cond
  rw [G.condNum_muSelf, G.Ucoord_pureMix]
  congr 1
  unfold pureMix
  by_cases hp : a = π s
  · subst hp; simp
  · simp [hp, Ne.symm hp]

/-- **`FP_ext ⊆ FP_Herr`**: an extension fixed point is a Herrmann fixed point (the argmax over available
actions is weaker than the argmax over all actions).
Source: [[updateless-self-game]] §6; [[uea-inventory]] 029, [[uea-2-inventory]] 2-014
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem IsFPext.isFPherr {G : Game S A} {σ : S → A → ℝ} (h : G.IsFPext σ) : G.IsFPherr σ :=
  ⟨h.1, fun s a ha b _ => h.2 s a ha b⟩

/-- Under an extension fixed point, the extension trust bound at `s` is the Herrmann one (a supported
action attains the maximum and is available).
Source: [[updateless-self-game]] §5 (Theorem C′ proof)
Kind: L
Fidelity: n/a
Hyps: (a) -/
theorem IsFPext.tbherr_of_tbext {G : Game S A} {σ : S → A → ℝ} (h : G.IsFPext σ) {s : S} (htb : G.TBext σ s) :
    G.TBherr σ s := by
  obtain ⟨b, hb⟩ := htb
  obtain ⟨a, ha⟩ : ∃ a, 0 < σ s a := by
    by_contra hall
    push Not at hall
    have : ∑ a, σ s a = 0 := Finset.sum_eq_zero fun a _ => le_antisymm (hall a) (h.1.nonneg s a)
    rw [h.1.sum s] at this
    exact one_ne_zero this
  exact ⟨a, G.availMix_of_pos s ha, le_trans hb (h.2 s a ha b)⟩

/-- **Pure fixed points are the Herrmann mixed fixed points at pure policies**.
Source: [[updateless-self-game]] §1 (pure fixed point as the pure case of the mixed one)
Kind: P
Fidelity: exact
Hyps: (a) -/
theorem isPureFP_iff_isFPherr_pureMix (π : S → A) : G.IsPureFP π ↔ G.IsFPherr (pureMix π) := by
  constructor
  · intro h
    refine ⟨isMixed_pureMix π, fun s a ha b hb => ?_⟩
    have hav : a = π s := by
      unfold pureMix at ha; by_contra hne; simp [hne] at ha
    subst hav
    have hb' : avail (G.muSelf π) s b := (G.availMix_pureMix_iff π s b).1 hb
    rw [G.Fext_pureMix π hb', G.Fext_pureMix π (G.avail_muSelf_self π s)]
    exact (h s).2 b hb'
  · intro h s
    refine ⟨G.avail_muSelf_self π s, fun b hb => ?_⟩
    have hb' : G.availMix (pureMix π) s b := (G.availMix_pureMix_iff π s b).2 hb
    have ha : 0 < pureMix π s (π s) := by simp [pureMix]
    have := h.2 s (π s) ha b hb'
    rwa [G.Fext_pureMix π hb, G.Fext_pureMix π (G.avail_muSelf_self π s)] at this


end Game

end Cleanroom.Uea.UeaSelfGame
