import Cleanroom.Udt.UdtPolicyCalc.Games
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Post 1's policy-selection setup: T12(a), (c), (d), (e)

Diffractor's UDT1.01 Post 1 ("The Story So Far"), lines 90–118: finite observations `O`, actions
`A`, horizon `n`; the tree of histories `O^{≤ n}`; leaves `O^n`, nodes `O^{< n}`; policies
`Π = O^{<n} → A`; environments `e : Π × O^{<n} → ΔO` (**the environment reads the whole
policy**); `π ⋈ e ∈ Δ(O^n)` the induced law; `V e U π := E_{π ⋈ e}[U]`.

* `Leaf`, `Node`, `Pol`, `Env`, `prefixOf`, `pathLaw`/`runLaw` (the product of the kernel along
  the path), `V`.
* `runLaw_nonneg`, `runLaw_sum_one` (`pathLaw` of a row-stochastic kernel is a distribution on
  leaves), via the general `sum_suffixLaw` (the mass of the extensions of a prefix is one).
* T12(b) over `V`: `isNashEquilibrium_iff_isLocalOptimum_V`, `isNashEquilibrium_of_isOptimal_V`.
* T12(c) `exists_env_of_policyUtility`: every `W : Pol → [0,1]` is `V e U` for some `e, U`
  (randomized root, deterministic afterwards, `U` reads the first observation).
* T12(d) `perverse_V`: the perverse environment `e_{π₀}`.
* T12(e) `card_node`, `card_node_geom`, `card_pol`.
* `exists_nash_not_optimal_policySelection`: a non-optimal Nash equilibrium realized through (c).

Package `udt-policy-calc` (faf-cleanroom run, 2026-09-29).
-/

namespace Cleanroom.Udt.UdtPolicyCalc

noncomputable section

namespace Tree

open Finset

/-- Completed histories `O^n`.
Source: `references/udt101/01-story-so-far.md` lines 90–96 (udt-rep-2-018)
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev Leaf (O : Type) (n : ℕ) := Fin n → O

/-- Nodes `O^{<n}`: a length `k < n` and a history of that length.
Source: `references/udt101/01-story-so-far.md` lines 94–96 (udt-rep-2-018)
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev Node (O : Type) (n : ℕ) := Σ k : Fin n, (Fin k → O)

/-- Policies `Π = O^{<n} → A`.
Source: `references/udt101/01-story-so-far.md` line 98 (udt-rep-2-018)
Kind: D
Fidelity: exact (deterministic policies; the post is "sloppy" about deterministic vs probabilistic)
Hyps: n/a -/
abbrev Pol (O A : Type) (n : ℕ) := Node O n → A

/-- Environments `e : Π × O^{<n} → ΔO`: given the **whole policy** and the current node, a
distribution over the next observation.
Source: `references/udt101/01-story-so-far.md` line 100 (udt-rep-2-018)
Kind: D
Fidelity: exact
Hyps: n/a -/
abbrev Env (O A : Type) (n : ℕ) [Fintype O] := Pol O A n → Node O n → FinDist O

variable {O A : Type} {n : ℕ}

/-- The length-`m` prefix of a leaf.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def prefixOf' (l : Leaf O n) (m : ℕ) (hm : m ≤ n) : Fin m → O := fun i => l (Fin.castLE hm i)

/-- The node at depth `k` on the path to the leaf `l`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def prefixOf (l : Leaf O n) (k : Fin n) : Node O n := ⟨k, prefixOf' l k k.isLt.le⟩

/-- Supporting lemma `prefixOf'_self` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prefixOf'_self (l : Leaf O n) (hm : n ≤ n) : prefixOf' l n hm = l :=
  funext fun i => congrArg l (Fin.ext rfl)

/-- Supporting lemma `prefixOf'_succ` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prefixOf'_succ (l : Leaf O n) (m : ℕ) (hm : m + 1 ≤ n) :
    prefixOf' l (m + 1) hm = Fin.snoc (prefixOf' l m (Nat.le_of_succ_le hm)) (l ⟨m, hm⟩) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    exact congrArg l (Fin.ext rfl)
  · rw [Fin.snoc_castSucc]
    exact congrArg l (Fin.ext rfl)

/-- Supporting lemma `snoc_eq_snoc_iff` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem snoc_eq_snoc_iff {m : ℕ} {a p : Fin m → O} {b o : O} :
    (Fin.snoc a b : Fin (m + 1) → O) = Fin.snoc p o ↔ a = p ∧ b = o := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := congrArg (Fin.init (α := fun _ => O)) h
      simpa [Fin.init_snoc] using this
    · have := congrFun h (Fin.last m)
      simpa [Fin.snoc_last] using this
  · rintro ⟨rfl, rfl⟩
    rfl

section Kernel

/-- The mass a kernel `F : Node → O → ℝ` gives to a leaf: the product of `F` along the path.
Source: `references/udt101/01-story-so-far.md` line 104 (`π ⋈ e`) (udt-rep-2-018)
Kind: D
Fidelity: exact (closed product form)
Hyps: n/a -/
def pathLaw (F : Node O n → O → ℝ) (l : Leaf O n) : ℝ := ∏ k, F (prefixOf l k) (l k)

/-- The product along the path from depth `m` on.
Source: none: infrastructure (Post 4's `π' ⋈ (e|h)`)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def suffixLaw (F : Node O n → O → ℝ) (m : ℕ) (l : Leaf O n) : ℝ :=
  ∏ k ∈ univ.filter (fun k : Fin n => m ≤ k.val), F (prefixOf l k) (l k)

/-- A kernel is **row-stochastic**: non-negative rows summing to one.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def RowStochastic [Fintype O] (F : Node O n → O → ℝ) : Prop := (∀ h o, 0 ≤ F h o) ∧ ∀ h, ∑ o, F h o = 1

/-- Supporting lemma `suffixLaw_zero` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem suffixLaw_zero (F : Node O n → O → ℝ) (l : Leaf O n) : suffixLaw F 0 l = pathLaw F l := by
  simp [suffixLaw, pathLaw]

/-- Supporting lemma `suffixLaw_succ` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem suffixLaw_succ (F : Node O n → O → ℝ) (m : ℕ) (hm : m + 1 ≤ n) (l : Leaf O n) :
    suffixLaw F m l = F (prefixOf l ⟨m, hm⟩) (l ⟨m, hm⟩) * suffixLaw F (m + 1) l := by
  have hset : (univ.filter fun k : Fin n => m ≤ k.val) =
      insert ⟨m, hm⟩ (univ.filter fun k : Fin n => m + 1 ≤ k.val) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hnot : (⟨m, hm⟩ : Fin n) ∉ (univ.filter fun k : Fin n => m + 1 ≤ k.val) := by
    simp
  rw [suffixLaw, hset, Finset.prod_insert hnot]
  rfl

/-- Supporting lemma `prefixOf_eq_of_prefixOf'` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem prefixOf_eq_of_prefixOf' {l : Leaf O n} {m : ℕ} (hm : m + 1 ≤ n) {p : Fin m → O}
    (h : prefixOf' l m (Nat.le_of_succ_le hm) = p) :
    prefixOf l ⟨m, hm⟩ = ⟨⟨m, hm⟩, p⟩ := by
  rw [← h]
  rfl

/-- The fibre decomposition: leaves extending `p` with next observation `o` are the leaves
extending `snoc p o`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem filter_prefix_succ [Fintype O] [DecidableEq O] (m : ℕ) (hm : m + 1 ≤ n) (p : Fin m → O) (o : O) :
    ((univ.filter fun l : Leaf O n => prefixOf' l m (Nat.le_of_succ_le hm) = p).filter
        fun l => l ⟨m, hm⟩ = o) =
      univ.filter fun l : Leaf O n => prefixOf' l (m + 1) hm = Fin.snoc p o := by
  ext l
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, prefixOf'_succ l m hm,
    snoc_eq_snoc_iff]

/-- **The mass of the extensions of a prefix is one** (row-stochastic kernel): for every `m ≤ n`
and prefix `p ∈ O^m`, `∑_{l ⊇ p} ∏_{k ≥ m} F (prefix l k) (l k) = 1`. Downward induction on `m`.
Source: `references/udt101/01-story-so-far.md` line 104 (`π ⋈ e ∈ Δ(O^n)`) (udt-rep-2-018)
Kind: P
Fidelity: exact
Hyps: (a) none beyond `RowStochastic F` -/
theorem sum_suffixLaw [Fintype O] [DecidableEq O] {F : Node O n → O → ℝ} (hF : RowStochastic F) :
    ∀ (d m : ℕ) (hd : m + d = n) (p : Fin m → O),
      ∑ l ∈ univ.filter (fun l : Leaf O n => prefixOf' l m (by omega) = p), suffixLaw F m l = 1 := by
  intro d
  induction d with
  | zero =>
    intro m hd p
    have hmn : m = n := by omega
    subst hmn
    have hfilt : (univ.filter fun l : Leaf O m => prefixOf' l m (by omega) = p) = {p} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      rw [prefixOf'_self]
    rw [hfilt, Finset.sum_singleton, suffixLaw]
    apply Finset.prod_eq_one
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
    exact absurd hk (by omega)
  | succ d ih =>
    intro m hd p
    have hm : m + 1 ≤ n := by omega
    calc ∑ l ∈ univ.filter (fun l : Leaf O n => prefixOf' l m (by omega) = p), suffixLaw F m l
        = ∑ l ∈ univ.filter (fun l : Leaf O n => prefixOf' l m (by omega) = p),
            F ⟨⟨m, hm⟩, p⟩ (l ⟨m, hm⟩) * suffixLaw F (m + 1) l := by
          refine Finset.sum_congr rfl fun l hl => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
          rw [suffixLaw_succ F m hm l, prefixOf_eq_of_prefixOf' hm hl]
      _ = ∑ o, ∑ l ∈ (univ.filter (fun l : Leaf O n => prefixOf' l m (by omega) = p)).filter
            (fun l => l ⟨m, hm⟩ = o), F ⟨⟨m, hm⟩, p⟩ (l ⟨m, hm⟩) * suffixLaw F (m + 1) l :=
          (Finset.sum_fiberwise (univ.filter (fun l : Leaf O n => prefixOf' l m (by omega) = p))
            (fun l => l ⟨m, hm⟩)
            (fun l => F ⟨⟨m, hm⟩, p⟩ (l ⟨m, hm⟩) * suffixLaw F (m + 1) l)).symm
      _ = ∑ o, F ⟨⟨m, hm⟩, p⟩ o *
            ∑ l ∈ univ.filter (fun l : Leaf O n => prefixOf' l (m + 1) hm = Fin.snoc p o),
              suffixLaw F (m + 1) l := by
          refine Finset.sum_congr rfl fun o _ => ?_
          rw [Finset.mul_sum, ← filter_prefix_succ m hm p o]
          refine Finset.sum_congr rfl fun l hl => ?_
          simp only [Finset.mem_filter] at hl
          rw [hl.2]
      _ = ∑ o, F ⟨⟨m, hm⟩, p⟩ o * 1 := by
          refine Finset.sum_congr rfl fun o _ => ?_
          rw [ih (m + 1) (by omega) (Fin.snoc p o)]
      _ = 1 := by
          simp only [mul_one]
          exact hF.2 _

/-- The path law of a row-stochastic kernel is non-negative.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem pathLaw_nonneg [Fintype O] {F : Node O n → O → ℝ} (hF : RowStochastic F) (l : Leaf O n) :
    0 ≤ pathLaw F l :=
  Finset.prod_nonneg fun k _ => hF.1 _ _

/-- **The path law of a row-stochastic kernel is a distribution on leaves.**
Source: `references/udt101/01-story-so-far.md` line 104 (udt-rep-2-018)
Kind: P
Fidelity: exact
Hyps: (a) none beyond `RowStochastic F` -/
theorem pathLaw_sum_one [Fintype O] {F : Node O n → O → ℝ} (hF : RowStochastic F) : ∑ l, pathLaw F l = 1 := by
  classical
  have := sum_suffixLaw hF n 0 (by omega) (Fin.elim0)
  rw [Finset.filter_true_of_mem (fun l _ => Subsingleton.elim _ _)] at this
  simpa [suffixLaw_zero] using this

end Kernel

section Run

variable [Fintype O]

/-- The kernel induced by an environment and a policy: `(e π h).w o`.
Source: `references/udt101/01-story-so-far.md` line 104 (udt-rep-2-018)
Kind: D
Fidelity: exact
Hyps: n/a -/
def envKernel (e : Env O A n) (π : Pol O A n) : Node O n → O → ℝ := fun h o => (e π h).w o

/-- Supporting lemma `envKernel_rowStochastic` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem envKernel_rowStochastic (e : Env O A n) (π : Pol O A n) : RowStochastic (envKernel e π) :=
  ⟨fun h o => (e π h).nonneg o, fun h => (e π h).sum_one⟩

/-- **`π ⋈ e`**: the law on completed histories induced by `π` interacting with `e`, as the
product of `e π` along the path.
Source: `references/udt101/01-story-so-far.md` line 104 (udt-rep-2-018)
Kind: D
Fidelity: exact
Hyps: n/a -/
def runLaw (e : Env O A n) (π : Pol O A n) : Leaf O n → ℝ := pathLaw (envKernel e π)

/-- Supporting lemma `runLaw_nonneg` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem runLaw_nonneg (e : Env O A n) (π : Pol O A n) (l : Leaf O n) : 0 ≤ runLaw e π l :=
  pathLaw_nonneg (envKernel_rowStochastic e π) l

/-- **`π ⋈ e` is a distribution** on `O^n`.
Source: `references/udt101/01-story-so-far.md` line 104 (udt-rep-2-018)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem runLaw_sum_one (e : Env O A n) (π : Pol O A n) : ∑ l, runLaw e π l = 1 :=
  pathLaw_sum_one (envKernel_rowStochastic e π)

/-- `π ⋈ e` as a `FinDist`.
Source: `references/udt101/01-story-so-far.md` line 104
Kind: D
Fidelity: exact
Hyps: n/a -/
def runDist (e : Env O A n) (π : Pol O A n) : FinDist (Leaf O n) :=
  ⟨runLaw e π, runLaw_nonneg e π, runLaw_sum_one e π⟩

/-- **The policy value** `V e U π := E_{π ⋈ e}[U]`. Post 1 has `U : O^n → [0,1]`; here `U : Leaf → ℝ`,
with the bound a hypothesis where a target needs it.
Source: `references/udt101/01-story-so-far.md` lines 106–110 (udt-rep-2-018)
Kind: D
Fidelity: exact (`ℝ`-valued `U`)
Hyps: n/a -/
def V (e : Env O A n) (U : Leaf O n → ℝ) (π : Pol O A n) : ℝ := ∑ l, runLaw e π l * U l

/-- Supporting lemma `V_eq_exp` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem V_eq_exp (e : Env O A n) (U : Leaf O n → ℝ) (π : Pol O A n) :
    V e U π = (runDist e π).exp U := rfl

variable [DecidableEq O] [Fintype A] [Nonempty A]

/-- **T12(b) over the environment model.** A policy is a UDT1.0 fixed point of `V e U` (a local
optimum) iff it is a pure Nash equilibrium of the common-payoff instance game (FAF form).
Source: `references/udt101/01-story-so-far.md` lines 65–77 (udt-rep-2-018)
Kind: P
Fidelity: exact (the content is the coercion plumbing plus T2)
Hyps: (a) none -/
theorem isNashEquilibrium_iff_isLocalOptimum_V (e : Env O A n) (U : Leaf O n → ℝ) (π : Pol O A n) :
    IsNashEquilibrium (instanceGame (V e U)).toStrategic
        ((instanceGame (V e U)).toStrategicProfile π (mem_profiles_instanceGame _ π)) ↔
      IsLocalOptimum (V e U) π :=
  isNashEquilibrium_instanceGame_iff (V e U) π

/-- **T12(b).** The UDT1.1 optimum `argmax_π V e U π` is a Nash equilibrium of the instance game.
Source: `references/udt101/01-story-so-far.md` lines 71–77, 106–110 (udt-rep-2-018)
Kind: L
Fidelity: exact
Hyps: (a) none beyond `IsOptimal (V e U) π` -/
theorem isNashEquilibrium_of_isOptimal_V {e : Env O A n} {U : Leaf O n → ℝ} {π : Pol O A n}
    (h : IsOptimal (V e U) π) :
    IsNashEquilibrium (instanceGame (V e U)).toStrategic
      ((instanceGame (V e U)).toStrategicProfile π (mem_profiles_instanceGame _ π)) :=
  isNashEquilibrium_of_isOptimal h

end Run

/-! ### T12(c): every policy utility arises from some environment -/

section Realize

variable [Fintype O] [DecidableEq O]

/-- The environment realizing `W`: at the root, mass `W π` on `o₀` and `1 − W π` on `o₁`; every
later node deterministically `o₀`.
Source: mandate T12(c) (udt-rep-2-018's "Omega can implement any `{0,1}^4 → ℝ`")
Kind: D
Fidelity: n/a
Hyps: n/a -/
def realizeEnv (W : Pol O A n → ℝ) (hW0 : ∀ π, 0 ≤ W π) (hW1 : ∀ π, W π ≤ 1) (o₀ o₁ : O) :
    Env O A n :=
  fun π h => if h.1.val = 0 then FinDist.bern (W π) (hW0 π) (hW1 π) o₀ o₁ else FinDist.delta o₀

/-- The utility reading the first observation: `[l 0 = o₀]`.
Source: mandate T12(c)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def realizeU (hn : 0 < n) (o₀ : O) : Leaf O n → ℝ := fun l => if l ⟨0, hn⟩ = o₀ then 1 else 0

/-- Supporting lemma `runLaw_realize_eq_zero` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem runLaw_realize_eq_zero {W : Pol O A n → ℝ} {hW0 hW1} {o₀ o₁ : O} (π : Pol O A n)
    (l : Leaf O n) (k : Fin n) (hk : k.val ≠ 0) (hl : l k ≠ o₀) :
    runLaw (realizeEnv W hW0 hW1 o₀ o₁) π l = 0 := by
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  simp [envKernel, realizeEnv, prefixOf, hk, hl]

/-- Supporting lemma `runLaw_realize_const` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem runLaw_realize_const {W : Pol O A n → ℝ} {hW0 hW1} {o₀ o₁ : O} (hne : o₀ ≠ o₁)
    (hn : 0 < n) (π : Pol O A n) :
    runLaw (realizeEnv W hW0 hW1 o₀ o₁) π (fun _ => o₀) = W π := by
  unfold runLaw pathLaw
  rw [Finset.prod_eq_single ⟨0, hn⟩]
  · simp [envKernel, realizeEnv, prefixOf, hne]
  · intro k _ hk
    have hk' : k.val ≠ 0 := fun h => hk (Fin.ext h)
    simp [envKernel, realizeEnv, prefixOf, hk']
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **T12(c), the computation.** `V (realizeEnv W) (realizeU) π = W π`: only the constant-`o₀` leaf
carries mass and utility.
Source: mandate T12(c) (udt-rep-2-018)
Kind: P
Fidelity: exact
Hyps: (a) `0 < n`, `o₀ ≠ o₁`, `0 ≤ W ≤ 1` (all explicit) -/
theorem V_realize {W : Pol O A n → ℝ} {hW0 : ∀ π, 0 ≤ W π} {hW1 : ∀ π, W π ≤ 1} {o₀ o₁ : O}
    (hne : o₀ ≠ o₁) (hn : 0 < n) (π : Pol O A n) :
    V (realizeEnv W hW0 hW1 o₀ o₁) (realizeU hn o₀) π = W π := by
  unfold V
  rw [Finset.sum_eq_single (fun _ => o₀)]
  · rw [runLaw_realize_const hne hn]
    simp [realizeU]
  · intro l _ hl
    by_cases h0 : l ⟨0, hn⟩ = o₀
    · have : ∃ k : Fin n, k.val ≠ 0 ∧ l k ≠ o₀ := by
        by_contra hcon
        push Not at hcon
        apply hl
        funext k
        by_cases hk : k.val = 0
        · have : k = ⟨0, hn⟩ := Fin.ext hk
          rw [this]
          exact h0
        · exact hcon k hk
      obtain ⟨k, hk, hlk⟩ := this
      rw [runLaw_realize_eq_zero π l k hk hlk, zero_mul]
    · simp [realizeU, h0]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **T12(c), headline (udt-rep-2-018).** For `n ≥ 1`, two distinct observations, and any
`W : Pol → [0,1]`, there are an environment `e` and a utility `U` with `V e U = W`: every
policy utility with values in `[0,1]` arises from some environment. (Not by encoding `π` into a
leaf — `|Pol| = |A|^{|Node|}` exceeds `|Leaf| = |O|^n` — but by randomizing the root.) This is the
bridge from Post 1's `V e U` back to the abstract `U : (S → A) → ℝ` of `Defs`.
Source: `references/udt101/01-story-so-far.md` lines 65–69 (udt-rep-2-018; the inventory's encoding remark corrected)
Kind: P
Fidelity: exact
Hyps: (a) `0 < n`, `o₀ ≠ o₁`, `0 ≤ W ≤ 1` (all explicit) -/
theorem exists_env_of_policyUtility (hn : 0 < n) {o₀ o₁ : O} (hne : o₀ ≠ o₁) (W : Pol O A n → ℝ)
    (hW0 : ∀ π, 0 ≤ W π) (hW1 : ∀ π, W π ≤ 1) :
    ∃ (e : Env O A n) (U : Leaf O n → ℝ), ∀ π, V e U π = W π :=
  ⟨realizeEnv W hW0 hW1 o₀ o₁, realizeU hn o₀, fun π => V_realize hne hn π⟩

/-- **T12(d), the perverse environment (udt-rep-2-019(a)).** For every `π₀` there is `e_{π₀}` with
`V e_{π₀} U π = 1` if `π = π₀` and `0` otherwise: policy-selection environments read the whole
policy.
Source: `references/udt101/01-story-so-far.md` lines 108–110 ("a really perverse environment `e_π`") (udt-rep-2-019(a))
Kind: N+
Fidelity: exact
Hyps: (a) `0 < n`, `o₀ ≠ o₁` -/
theorem perverse_V [DecidableEq A] (hn : 0 < n) {o₀ o₁ : O} (hne : o₀ ≠ o₁) (π₀ : Pol O A n) :
    ∃ (e : Env O A n) (U : Leaf O n → ℝ), ∀ π, V e U π = if π = π₀ then 1 else 0 :=
  exists_env_of_policyUtility hn hne (fun π => if π = π₀ then 1 else 0)
    (fun _ => by split_ifs <;> norm_num) (fun _ => by split_ifs <;> norm_num)

end Realize

/-! ### T12(e): counts -/

section Counts

variable [Fintype O] [Fintype A]

/-- **T12(e) (udt-rep-2-019(b)).** `|O^{<n}| = ∑_{k < n} |O|^k`.
Source: `references/udt101/01-story-so-far.md` line 112 ("about `|O|^n` elements of `O^{<n}`") (udt-rep-2-019(b))
Kind: L
Fidelity: exact (the source's "about `|O|^n`" is an order-of-magnitude remark)
Hyps: none -/
theorem card_node : Fintype.card (Node O n) = ∑ k ∈ Finset.range n, Fintype.card O ^ k := by
  rw [Fintype.card_sigma, ← Fin.sum_univ_eq_sum_range (fun k => Fintype.card O ^ k) n]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Fintype.card_fun, Fintype.card_fin]

/-- **T12(e).** For `|O| ≥ 2`, `|O^{<n}| = (|O|^n − 1)/(|O| − 1)`.
Source: `references/udt101/01-story-so-far.md` line 112 (udt-rep-2-019(b))
Kind: L
Fidelity: exact
Hyps: (a) `2 ≤ |O|` -/
theorem card_node_geom (hO : 2 ≤ Fintype.card O) :
    Fintype.card (Node O n) = (Fintype.card O ^ n - 1) / (Fintype.card O - 1) := by
  rw [card_node, Nat.geomSum_eq hO]

/-- **T12(e).** `|Π| = |A|^{|O^{<n}|}`.
Source: `references/udt101/01-story-so-far.md` line 112 (udt-rep-2-019(b))
Kind: L
Fidelity: exact
Hyps: none -/
theorem card_pol [DecidableEq O] : Fintype.card (Pol O A n) = Fintype.card A ^ Fintype.card (Node O n) :=
  Fintype.card_fun

end Counts

/-! ### A non-optimal Nash equilibrium in a policy-selection environment -/

section NashWitness

/-- The two depth-one nodes of the depth-two binary tree.
Source: mandate T12(b) ("non-optimal Nash equilibria exist: T3's `U` realized through (c)")
Kind: D
Fidelity: n/a
Hyps: n/a -/
def node₀ : Node Bool 2 := ⟨1, ![false]⟩

/-- Supporting definition `node₁` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: none -/
def node₁ : Node Bool 2 := ⟨1, ![true]⟩

/-- Supporting lemma `node₀_ne_node₁` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem node₀_ne_node₁ : node₀ ≠ node₁ := by
  intro h
  have h2 := (Sigma.mk.inj_iff.mp h).2
  have h0 := congrFun (eq_of_heq h2) 0
  simp at h0

/-- Coordinated Buttons on the two depth-one nodes, scaled into `[0,1]`.
Source: mandate T12(b)
Kind: D
Fidelity: n/a
Hyps: n/a -/
def coordW : Pol Bool (Fin 2) 2 → ℝ := fun π => coordButtons ![π node₀, π node₁] / 10

/-- Supporting lemma `coordW_nonneg` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem coordW_nonneg (π : Pol Bool (Fin 2) 2) : 0 ≤ coordW π := by
  unfold coordW
  have := forall_policy2 (P := fun π => 0 ≤ coordButtons π)
  refine div_nonneg (this.mpr ⟨?_, ?_, ?_, ?_⟩ _) (by norm_num) <;>
    simp only [coordButtons, tbl_00, tbl_01, tbl_10, tbl_11] <;> norm_num

/-- Supporting lemma `coordW_le_one` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem coordW_le_one (π : Pol Bool (Fin 2) 2) : coordW π ≤ 1 := by
  unfold coordW
  have := forall_policy2 (P := fun π => coordButtons π ≤ 10)
  refine (div_le_one (by norm_num)).mpr (this.mpr ⟨?_, ?_, ?_, ?_⟩ _) <;>
    simp only [coordButtons, tbl_00, tbl_01, tbl_10, tbl_11] <;> norm_num

/-- Supporting lemma `coordW_localOptimum` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem coordW_localOptimum : IsLocalOptimum coordW (fun _ => 0) := by
  rw [isLocalOptimum_iff]
  intro m
  unfold coordW
  by_cases h0 : m = node₀
  · subst h0
    simp only [Fin.forall_fin_two, Function.update_self,
      Function.update_of_ne node₀_ne_node₁.symm, coordButtons, tbl_00, tbl_10]
    norm_num
  · by_cases h1 : m = node₁
    · subst h1
      simp only [Fin.forall_fin_two, Function.update_self,
        Function.update_of_ne node₀_ne_node₁, coordButtons, tbl_00, tbl_01]
      norm_num
    · intro a
      rw [Function.update_of_ne (Ne.symm h0), Function.update_of_ne (Ne.symm h1)]

/-- Supporting lemma `coordW_not_optimal` (infrastructure for the headlines of this file).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem coordW_not_optimal : ¬ IsOptimal coordW (fun _ => 0) := by
  intro h
  have := h (fun _ => 1)
  simp only [coordW, coordButtons, tbl_00, tbl_11] at this
  norm_num at this

/-- **T12(b), non-optimal Nash equilibria in policy-selection environments.** In the depth-two
binary tree with two actions there are an environment `e`, a utility `U` and a policy `π` that is
a Nash equilibrium of the instance game of `V e U` (a UDT1.0 fixed point) but not `V e U`-optimal:
Coordinated Buttons on the two depth-one nodes, realized through T12(c).
Source: `references/udt101/01-story-so-far.md` lines 71–77 (udt-rep-2-018, 003(a))
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem exists_nash_not_optimal_policySelection :
    ∃ (e : Env Bool (Fin 2) 2) (U : Leaf Bool 2 → ℝ) (π : Pol Bool (Fin 2) 2),
      IsNashEquilibrium (instanceGame (V e U)).toStrategic
          ((instanceGame (V e U)).toStrategicProfile π (mem_profiles_instanceGame _ π)) ∧
        ¬ IsOptimal (V e U) π := by
  obtain ⟨e, U, hV⟩ := exists_env_of_policyUtility (O := Bool) (A := Fin 2) (n := 2) (by norm_num)
    (Bool.false_ne_true) coordW coordW_nonneg coordW_le_one
  have hVW : V e U = coordW := funext hV
  refine ⟨e, U, fun _ => 0, ?_, ?_⟩
  · rw [isNashEquilibrium_iff_isLocalOptimum_V, hVW]
    exact coordW_localOptimum
  · rw [hVW]
    exact coordW_not_optimal

end NashWitness

end Tree

end

end Cleanroom.Udt.UdtPolicyCalc
