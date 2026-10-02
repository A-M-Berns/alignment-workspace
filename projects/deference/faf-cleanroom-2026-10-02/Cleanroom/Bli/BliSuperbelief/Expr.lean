import Cleanroom.Bli.BliFinite.Tent
import Cleanroom.Bli.BliFinite.Actual
import LogicalInduction.Framework.Criterion
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# `bli-superbelief` · Expr: the tent kernel's marginals as FAF `EF` terms (E2)

The property that lets `bli-transfer`'s transfer theorem turn B1 into a logical inductor: the
day-`(m+h+1)` marginal of the tent chain started at the day-`m` table is an **explicit FAF `EF`
term** in the day-`m` prices, closed, built from `add`/`mul`/`max`/`const`/`price` only (no
`safeRecip`, whose clamp at `1` makes reciprocals of numbers in `(0,1)` wrong; no `var`/`letE`),
whose leaves are exactly `price φ m` for `φ ∈ S m`, and whose token count is linear in
`|S (m+h+1)|` with an absolute constant.

The construction: the one-coordinate tent law is a mixture of three *fixed* laws,
`tent1 d x = w₀(x)·δ₀ + w_U(x)·U_d + w₁(x)·δ₁` with the piecewise-affine weights
`w₀ = max 0 (1−2x)`, `w_U = 1−|2x−1|`, `w₁ = max 0 (2x−1)` (in the clamped price), so the
`h`-step law of the coordinate is the *same* mixture of the `h`-step laws of `δ₀`, `U_d`, `δ₁`
(`chainFrom_tentW`) — three rational constants per coordinate, computed by recursion through the
day-dependent meshes (`chainFrom`), never as a power of one matrix. A coordinate that enters the
small set after day `m` contributes a constant (`coordMarg_const_of_not_mem`). The product over
the coordinates is the marginal (`lastMarg_tent_eq_prod_coordMarg`: the trajectory law's last-day
marginal factorizes coordinatewise, by `Finset.prod_univ_sum`), and `tentExpr` is the product of
the coordinate terms; `tentExpr_denoteRat` is the identity, for **every** rational history (the
clamp is carried inside the term, so no unit-cube hypothesis is needed).

Indexing: `tentExpr 𝓜 m h Q` reads a day-`(m+h+1)` table (horizon `h+1 ≥ 1`); `tentExpr₁ 𝓜 m Q`
is the one-step case `h = 0`.

Sources: [[bli-program]] §2.4 (kernel of record), §3.4 (Expressibility — this run's construction;
attributed to no corpus author); bli-slides-003 (the product form); bli-slides-049 (why the kernel
must be rational). `Kernel` has no computability field (`bli-finite`, T10 not attempted); E2's
computability content is this file.
-/

namespace Cleanroom.Bli.BliSuperbelief

open LogicalInduction Finset Cleanroom.Bli.BliFinite

/-! ## The expression algebra: negation, subtraction, min, clamp, abs, the tent weights, products -/

/-- Negation as an `EF` term: `(−1) · a`.
Source: none: infrastructure (mandate design decision 3)
Kind: D
Fidelity: n/a -/
def negE (a : EF) : EF := .mul (.const (-1)) a

/-- Subtraction as an `EF` term: `a + (−1)·b`.
Source: none: infrastructure (mandate design decision 3)
Kind: D
Fidelity: n/a -/
def subE (a b : EF) : EF := .add a (negE b)

/-- Minimum as an `EF` term: `min a b = −max (−a) (−b)`.
Source: none: infrastructure (mandate design decision 3)
Kind: D
Fidelity: n/a -/
def minE (a b : EF) : EF := negE (.max (negE a) (negE b))

/-- The clamp `max 0 (min 1 a)` as an `EF` term (so that `tent1`'s `clamp01` is carried inside the
expression and the denotation identity needs no unit-cube hypothesis).
Source: none: infrastructure (mandate E2 "carry `clamp01` in the expression")
Kind: D
Fidelity: n/a -/
def clampE (a : EF) : EF := .max (.const 0) (minE (.const 1) a)

/-- Absolute value as an `EF` term: `|a| = max a (−a)`.
Source: none: infrastructure (mandate design decision 3: `|2t−1| = max (2t−1) (1−2t)`)
Kind: D
Fidelity: n/a -/
def absE (a : EF) : EF := .max a (negE a)

/-- The tent weight on `δ₀`: `max 0 (1 − 2·clamp x)`.
Source: [[bli-program]] §2.4 (tent kernel weights)
Kind: D
Fidelity: exact -/
def w0E (x : EF) : EF := .max (.const 0) (subE (.const 1) (.mul (.const 2) (clampE x)))

/-- The tent weight on the uniform law: `1 − |2·clamp x − 1|`.
Source: [[bli-program]] §2.4
Kind: D
Fidelity: exact -/
def wUE (x : EF) : EF := subE (.const 1) (absE (subE (.mul (.const 2) (clampE x)) (.const 1)))

/-- The tent weight on `δ₁`: `max 0 (2·clamp x − 1)`.
Source: [[bli-program]] §2.4
Kind: D
Fidelity: exact -/
def w1E (x : EF) : EF := .max (.const 0) (subE (.mul (.const 2) (clampE x)) (.const 1))

/-- The three-weight mixture with rational constants: `w₀(x)·c₀ + w_U(x)·c_U + w₁(x)·c₁`.
Source: [[bli-program]] §3.4 (Expressibility: "three rational constants per coordinate")
Kind: D
Fidelity: exact -/
def mix3E (x : EF) (c0 cU c1 : ℚ) : EF :=
  .add (.add (.mul (w0E x) (.const c0)) (.mul (wUE x) (.const cU))) (.mul (w1E x) (.const c1))

/-- The product of a list of `EF` terms (right-nested `mul`, `const 1` for the empty list).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def prodList : List EF → EF
  | [] => .const 1
  | e :: l => .mul e (prodList l)

/-- The tent weights as a rational function of the price, with three constants: the scalar
denotation of `mix3E`.
Source: [[bli-program]] §2.4
Kind: D
Fidelity: exact -/
def tentW (x c0 cU c1 : ℚ) : ℚ :=
  max 0 (1 - 2 * clamp01 x) * c0 + (1 - |2 * clamp01 x - 1|) * cU + max 0 (2 * clamp01 x - 1) * c1

/-- **The mixture identity**: `bli-finite`'s `tent1 d x v` *is* `tentW` at the three constants
`[v = 0]`, `uniform1 d v`, `[v = 1]` — by definition of `tent1`.
Source: [[bli-program]] §2.4 (`ν^tent(t) = max(0,1−2t) δ₀ + (1−|2t−1|) V + max(0,2t−1) δ₁`)
Kind: L
Fidelity: exact -/
lemma tent1_eq_tentW (d : ℕ) (x v : ℚ) :
    tent1 d x v = tentW x (if v = 0 then 1 else 0) (uniform1 d v) (if v = 1 then 1 else 0) := rfl

/-! ### Denotations -/

section Denote

variable (V : ℕ → Sentence → ℚ)

/-- Denotation of `negE`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma denoteRat_negE (a : EF) : (negE a).denoteRat V = -(a.denoteRat V) := by
  simp [negE, EF.denoteRat, EF.denoteRatWith]

/-- Denotation of `subE`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma denoteRat_subE (a b : EF) : (subE a b).denoteRat V = a.denoteRat V - b.denoteRat V := by
  simp [subE, negE, EF.denoteRat, EF.denoteRatWith, sub_eq_add_neg]

/-- Denotation of `minE`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma denoteRat_minE (a b : EF) : (minE a b).denoteRat V = min (a.denoteRat V) (b.denoteRat V) := by
  simp only [minE, negE, EF.denoteRat, EF.denoteRatWith]
  rcases le_total (a.denoteRatWith [] V) (b.denoteRatWith [] V) with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_right (by linarith)]; ring

/-- Denotation of `clampE` is `clamp01`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma denoteRat_clampE (a : EF) : (clampE a).denoteRat V = clamp01 (a.denoteRat V) := by
  simp only [clampE, clamp01]
  show max ((EF.const 0).denoteRatWith [] V) ((minE (.const 1) a).denoteRatWith [] V) = _
  rw [show (minE (.const 1) a).denoteRatWith [] V = (minE (.const 1) a).denoteRat V from rfl,
    denoteRat_minE]
  rfl

/-- Denotation of `absE`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma denoteRat_absE (a : EF) : (absE a).denoteRat V = |a.denoteRat V| := by
  simp only [absE, negE, EF.denoteRat, EF.denoteRatWith]
  rcases le_total 0 (a.denoteRatWith [] V) with h | h
  · rw [abs_of_nonneg h, max_eq_left (by linarith)]
  · rw [abs_of_nonpos h, max_eq_right (by linarith)]; ring

/-- Denotation of `mix3E` is `tentW` at the price.
Source: [[bli-program]] §3.4
Kind: L
Fidelity: exact -/
lemma denoteRat_mix3E (x : EF) (c0 cU c1 : ℚ) :
    (mix3E x c0 cU c1).denoteRat V = tentW (x.denoteRat V) c0 cU c1 := by
  have h0 : (w0E x).denoteRat V = max 0 (1 - 2 * clamp01 (x.denoteRat V)) := by
    simp only [w0E]
    show max ((EF.const 0).denoteRatWith [] V) ((subE (.const 1) (.mul (.const 2) (clampE x))).denoteRatWith [] V) = _
    rw [show (subE (.const 1) (.mul (.const 2) (clampE x))).denoteRatWith [] V =
      (subE (.const 1) (.mul (.const 2) (clampE x))).denoteRat V from rfl, denoteRat_subE]
    show max 0 (1 - (2 * (clampE x).denoteRatWith [] V)) = _
    rw [show (clampE x).denoteRatWith [] V = (clampE x).denoteRat V from rfl, denoteRat_clampE]
  have h1 : (w1E x).denoteRat V = max 0 (2 * clamp01 (x.denoteRat V) - 1) := by
    simp only [w1E]
    show max ((EF.const 0).denoteRatWith [] V) ((subE (.mul (.const 2) (clampE x)) (.const 1)).denoteRatWith [] V) = _
    rw [show (subE (.mul (.const 2) (clampE x)) (.const 1)).denoteRatWith [] V =
      (subE (.mul (.const 2) (clampE x)) (.const 1)).denoteRat V from rfl, denoteRat_subE]
    show max 0 (2 * (clampE x).denoteRatWith [] V - 1) = _
    rw [show (clampE x).denoteRatWith [] V = (clampE x).denoteRat V from rfl, denoteRat_clampE]
  have hU : (wUE x).denoteRat V = 1 - |2 * clamp01 (x.denoteRat V) - 1| := by
    simp only [wUE]
    rw [denoteRat_subE, denoteRat_absE, denoteRat_subE]
    show 1 - |2 * (clampE x).denoteRatWith [] V - 1| = _
    rw [show (clampE x).denoteRatWith [] V = (clampE x).denoteRat V from rfl, denoteRat_clampE]
  simp only [mix3E, tentW]
  show (w0E x).denoteRatWith [] V * c0 + (wUE x).denoteRatWith [] V * cU +
    (w1E x).denoteRatWith [] V * c1 = _
  rw [show (w0E x).denoteRatWith [] V = (w0E x).denoteRat V from rfl,
    show (wUE x).denoteRatWith [] V = (wUE x).denoteRat V from rfl,
    show (w1E x).denoteRatWith [] V = (w1E x).denoteRat V from rfl, h0, h1, hU]

/-- Denotation of `prodList` is the product of the denotations.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma denoteRat_prodList (l : List EF) :
    (prodList l).denoteRat V = (l.map fun e => e.denoteRat V).prod := by
  induction l with
  | nil => rfl
  | cons e l ih =>
      show e.denoteRatWith [] V * (prodList l).denoteRatWith [] V = _
      rw [List.map_cons, List.prod_cons, ← ih]
      rfl

end Denote

/-! ## The scalar tent chain from an initial law -/

/-- **The one-coordinate chain** started from a law `μ` on the day-`(m+1)` grid values, read on
day `m+h+1`: `chainFrom 𝓜 m 0 μ = μ`, and one more step composes with the tent law at the next
day's mesh. Linear in `μ`; the constants of `tentExpr` are its values at `δ₀`, `U`, `δ₁`.
Source: [[bli-program]] §3.4 (the row vector `ν^tent(t) M^{h}`, with day-dependent meshes)
Kind: D
Fidelity: variant: recursion through day-dependent meshes in place of a matrix power -/
def chainFrom (𝓜 : Mesh) (m : ℕ) : ℕ → (ℚ → ℚ) → ℚ → ℚ
  | 0, μ, v => μ v
  | h + 1, μ, v =>
      ∑ v' ∈ gridVals (𝓜.d (m + h + 1)), chainFrom 𝓜 m h μ v' * tent1 (𝓜.d (m + h + 1 + 1)) v' v

/-- Unfolding lemma for `chainFrom` at horizon 0.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma chainFrom_zero (𝓜 : Mesh) (m : ℕ) (μ : ℚ → ℚ) (v : ℚ) : chainFrom 𝓜 m 0 μ v = μ v := rfl

/-- Unfolding lemma for `chainFrom` at horizon `h+1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma chainFrom_succ (𝓜 : Mesh) (m h : ℕ) (μ : ℚ → ℚ) (v : ℚ) :
    chainFrom 𝓜 m (h + 1) μ v =
      ∑ v' ∈ gridVals (𝓜.d (m + h + 1)), chainFrom 𝓜 m h μ v' * tent1 (𝓜.d (m + h + 1 + 1)) v' v := rfl

/-- The chain is linear in the initial law (three-term form).
Source: [[bli-program]] §3.4 ("the `h`-step law of a mixture is the mixture of the `h`-step laws")
Kind: L
Fidelity: exact -/
lemma chainFrom_lin (𝓜 : Mesh) (m : ℕ) (a b c : ℚ) (μ ν ρ : ℚ → ℚ) :
    ∀ (h : ℕ) (v : ℚ),
      chainFrom 𝓜 m h (fun u => a * μ u + b * ν u + c * ρ u) v =
        a * chainFrom 𝓜 m h μ v + b * chainFrom 𝓜 m h ν v + c * chainFrom 𝓜 m h ρ v
  | 0, v => rfl
  | h + 1, v => by
      simp only [chainFrom_succ, chainFrom_lin 𝓜 m a b c μ ν ρ h, add_mul, Finset.sum_add_distrib,
        mul_assoc, Finset.mul_sum]

/-- **The `h`-step tent law is the tent mixture of three fixed `h`-step laws.** The chain started
from `tent1 (d (m+1)) x` equals `tentW x` at the constants `chainFrom h δ₀`, `chainFrom h U`,
`chainFrom h δ₁` — the three rational constants per coordinate of the expression.
`chainFrom_lin` at the three-term form of `tent1`, then `rfl`.
Source: [[bli-program]] §3.4 (Expressibility)
Kind: C
Fidelity: exact
Hyps: (a) none -/
lemma chainFrom_tentW (𝓜 : Mesh) (m h : ℕ) (x v : ℚ) :
    chainFrom 𝓜 m h (tent1 (𝓜.d (m + 1)) x) v =
      tentW x (chainFrom 𝓜 m h (fun u => if u = 0 then 1 else 0) v)
        (chainFrom 𝓜 m h (uniform1 (𝓜.d (m + 1))) v)
        (chainFrom 𝓜 m h (fun u => if u = 1 then 1 else 0) v) := by
  have hμ : tent1 (𝓜.d (m + 1)) x = fun u =>
      max 0 (1 - 2 * clamp01 x) * (if u = 0 then 1 else 0) +
        (1 - |2 * clamp01 x - 1|) * uniform1 (𝓜.d (m + 1)) u +
        max 0 (2 * clamp01 x - 1) * (if u = 1 then 1 else 0) := rfl
  rw [hμ, chainFrom_lin]
  rfl

/-! ## The coordinate marginal of the tent chain -/

variable {𝒮 : SmallIndex}

/-- **The coordinate marginal** of the tent chain started at the day-`m` table `t`, read at the
day-`(m+h+1)` sentence `φ` and value `v`: the tent-kernel coordinate law at horizon 0, composed
with the next day's tent law while the sentence was already small, and the uniform law on the
day the sentence enters.
Source: [[bli-program]] §3.4 (the day-`m` marginal of coordinate `φ`)
Kind: D
Fidelity: exact -/
def coordMarg (𝓜 : Mesh) (m : ℕ) : (h : ℕ) → Table 𝒮 m → ↥(𝒮.S (m + h + 1)) → ℚ → ℚ
  | 0, t, φ, v => tentCoord 𝓜 m t φ v
  | h + 1, t, φ, v =>
      if hφ : φ.1 ∈ 𝒮.S (m + h + 1) then
        ∑ v' ∈ gridVals (𝓜.d (m + h + 1)),
          coordMarg 𝓜 m h t ⟨φ.1, hφ⟩ v' * tent1 (𝓜.d (m + h + 1 + 1)) v' v
      else uniform1 (𝓜.d (m + h + 1 + 1)) v

variable {𝓜 : Mesh} {m : ℕ}

/-- Unfolding lemma at horizon 0.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] lemma coordMarg_zero (t : Table 𝒮 m) (φ : ↥(𝒮.S (m + 0 + 1))) (v : ℚ) :
    coordMarg 𝓜 m 0 t φ v = tentCoord 𝓜 m t φ v := rfl

/-- Unfolding lemma at horizon `h+1`, old sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coordMarg_succ_of_mem {h : ℕ} (t : Table 𝒮 m) {φ : ↥(𝒮.S (m + (h + 1) + 1))} (v : ℚ)
    (hφ : φ.1 ∈ 𝒮.S (m + h + 1)) :
    coordMarg 𝓜 m (h + 1) t φ v =
      ∑ v' ∈ gridVals (𝓜.d (m + h + 1)),
        coordMarg 𝓜 m h t ⟨φ.1, hφ⟩ v' * tent1 (𝓜.d (m + h + 1 + 1)) v' v := by
  show (if _ : φ.1 ∈ 𝒮.S (m + h + 1) then _ else _) = _
  rw [dif_pos hφ]

/-- Unfolding lemma at horizon `h+1`, new sentence.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma coordMarg_succ_of_not_mem {h : ℕ} (t : Table 𝒮 m) {φ : ↥(𝒮.S (m + (h + 1) + 1))} (v : ℚ)
    (hφ : φ.1 ∉ 𝒮.S (m + h + 1)) :
    coordMarg 𝓜 m (h + 1) t φ v = uniform1 (𝓜.d (m + h + 1 + 1)) v := by
  show (if _ : φ.1 ∈ 𝒮.S (m + h + 1) then _ else _) = _
  rw [dif_neg hφ]

/-- A coordinate small on day `m` has the scalar tent chain started at its day-`m` price.
Source: [[bli-program]] §3.4
Kind: L
Fidelity: exact -/
lemma coordMarg_of_mem (t : Table 𝒮 m) :
    ∀ (h : ℕ) (φ : ↥(𝒮.S (m + h + 1))) (v : ℚ) (hφ : φ.1 ∈ 𝒮.S m),
      coordMarg 𝓜 m h t φ v = chainFrom 𝓜 m h (tent1 (𝓜.d (m + 1)) (t ⟨φ.1, hφ⟩)) v
  | 0, φ, v, hφ => by
      rw [coordMarg_zero, chainFrom_zero]
      unfold tentCoord
      rw [dif_pos hφ]
  | h + 1, φ, v, hφ => by
      have hφ' : φ.1 ∈ 𝒮.S (m + h + 1) := 𝒮.mono_le (by omega) hφ
      rw [coordMarg_succ_of_mem t v hφ', chainFrom_succ]
      apply Finset.sum_congr rfl
      intro v' _
      rw [coordMarg_of_mem t h ⟨φ.1, hφ'⟩ v' hφ]

/-- A coordinate not small on day `m` has a marginal independent of the day-`m` table (it enters
uniformly and is then driven only by its own tent chain).
Source: [[bli-program]] §3.4 (new coordinates contribute a constant)
Kind: L
Fidelity: exact -/
lemma coordMarg_const_of_not_mem (t t' : Table 𝒮 m) :
    ∀ (h : ℕ) (φ : ↥(𝒮.S (m + h + 1))) (v : ℚ) (hφ : φ.1 ∉ 𝒮.S m),
      coordMarg 𝓜 m h t φ v = coordMarg 𝓜 m h t' φ v
  | 0, φ, v, hφ => by
      rw [coordMarg_zero, coordMarg_zero]
      unfold tentCoord
      rw [dif_neg hφ, dif_neg hφ]
  | h + 1, φ, v, hφ => by
      by_cases hφ' : φ.1 ∈ 𝒮.S (m + h + 1)
      · rw [coordMarg_succ_of_mem t v hφ', coordMarg_succ_of_mem t' v hφ']
        apply Finset.sum_congr rfl
        intro v' _
        rw [coordMarg_const_of_not_mem t t' h ⟨φ.1, hφ'⟩ v' hφ]
      · rw [coordMarg_succ_of_not_mem t v hφ', coordMarg_succ_of_not_mem t' v hφ']

/-! ## The last-day marginal of the trajectory law, and its factorization -/

section LastMarg

variable {d : ℕ → ℕ}

/-- **The last-day marginal** of the trajectory law: the mass of the horizon-`h` trajectories
from `t` whose last table is `Q` — the superbelief `𝐏_n(𝐐_{n+h} = Q)` of the skeleton.
Source: bli-soto-a-035 (multi-day states by the chain rule); [[bli-program]] §2.4
Kind: D
Fidelity: exact -/
noncomputable def lastMarg (sk : Skeleton 𝒮 d) (n h : ℕ) (t : Table 𝒮 n) (Q : Table 𝒮 (n + h)) : ℚ :=
  ∑ τ ∈ trajGrid 𝒮 d n h, trajLaw sk n h t τ * if τ.last t = Q then 1 else 0

/-- The last table of a carrier trajectory of positive horizon is a grid table.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma Traj.last_mem_grid {n h : ℕ} (t : Table 𝒮 n) {τ : Traj 𝒮 n (h + 1)}
    (hτ : τ ∈ trajGrid 𝒮 d n (h + 1)) : τ.last t ∈ grid 𝒮 d (n + h + 1) := by
  obtain ⟨τ', Q⟩ := τ
  exact (mem_trajGrid_succ.mp hτ).2

/-- The horizon-1 marginal is the kernel's law.
Source: none: infrastructure
Kind: L
Fidelity: exact -/
lemma lastMarg_one (sk : Skeleton 𝒮 d) (n : ℕ) (t : Table 𝒮 n) (Q : Table 𝒮 (n + 1)) :
    lastMarg sk n 1 t Q = (sk.κ n).law t Q := by
  unfold lastMarg
  rw [sum_trajGrid_succ, sum_trajGrid_zero]
  have hterm : ∀ x ∈ grid 𝒮 d (n + 0 + 1),
      trajLaw sk n (0 + 1) t (show Traj 𝒮 n (0 + 1) from (PUnit.unit, x)) *
        (if (show Traj 𝒮 n (0 + 1) from (PUnit.unit, x)).last t = Q then 1 else 0) =
      if x = Q then (sk.κ n).law t x else 0 := by
    intro x _
    rw [trajLaw_succ, trajLaw_zero, one_mul, mul_ite, mul_one, mul_zero]
    rfl
  refine (Finset.sum_congr rfl hterm).trans ?_
  rw [Finset.sum_ite_eq']
  split_ifs with hQ
  · rfl
  · exact ((sk.κ n).law_eq_zero_of_not_mem t hQ).symm

/-- **Chapman–Kolmogorov for the last-day marginal**: one more step composes with the kernel.
Source: bli-soto-a-035 (Soto's two-step display, at every horizon)
Kind: L
Fidelity: exact -/
lemma lastMarg_succ (sk : Skeleton 𝒮 d) (n h : ℕ) (t : Table 𝒮 n) (Q : Table 𝒮 (n + h + 1 + 1)) :
    lastMarg sk n (h + 1 + 1) t Q =
      ∑ Q' ∈ grid 𝒮 d (n + h + 1), lastMarg sk n (h + 1) t Q' * (sk.κ (n + h + 1)).law Q' Q := by
  unfold lastMarg
  rw [sum_trajGrid_succ]
  have hinner : ∀ τ ∈ trajGrid 𝒮 d n (h + 1),
      (∑ Q'' ∈ grid 𝒮 d (n + (h + 1) + 1),
        trajLaw sk n (h + 1 + 1) t (show Traj 𝒮 n (h + 1 + 1) from (τ, Q'')) *
          (if (show Traj 𝒮 n (h + 1 + 1) from (τ, Q'')).last t = Q then 1 else 0)) =
      trajLaw sk n (h + 1) t τ * (sk.κ (n + h + 1)).law (τ.last t) Q := by
    intro τ _
    have : ∀ Q'' ∈ grid 𝒮 d (n + (h + 1) + 1),
        trajLaw sk n (h + 1 + 1) t (show Traj 𝒮 n (h + 1 + 1) from (τ, Q'')) *
          (if (show Traj 𝒮 n (h + 1 + 1) from (τ, Q'')).last t = Q then 1 else 0) =
        if Q'' = Q then trajLaw sk n (h + 1) t τ * (sk.κ (n + h + 1)).law (τ.last t) Q'' else 0 := by
      intro Q'' _
      rw [trajLaw_succ, mul_ite, mul_one, mul_zero]
      rfl
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
    split_ifs with hQ
    · rfl
    · rw [(sk.κ (n + h + 1)).law_eq_zero_of_not_mem _ hQ, mul_zero]
  refine (Finset.sum_congr rfl hinner).trans ?_
  -- expand the right-hand side's `lastMarg` and swap the sums
  have hR : ∀ Q' ∈ grid 𝒮 d (n + h + 1),
      (∑ τ' ∈ trajGrid 𝒮 d n (h + 1), trajLaw sk n (h + 1) t τ' * if τ'.last t = Q' then 1 else 0) *
          (sk.κ (n + h + 1)).law Q' Q =
        ∑ τ' ∈ trajGrid 𝒮 d n (h + 1),
          if τ'.last t = Q' then trajLaw sk n (h + 1) t τ' * (sk.κ (n + h + 1)).law Q' Q else 0 := by
    intro Q' _
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro τ' _
    rw [mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
  rw [Finset.sum_congr rfl hR, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ hτ
  rw [Finset.sum_ite_eq, if_pos (Traj.last_mem_grid t hτ)]

/-- Splitting a product over the day-`(k+1)` sentences into the old sentences (reindexed by the
day-`k` sentences through `SmallIndex.mono`) and the new ones.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prod_S_succ_split {k : ℕ} (f : ↥(𝒮.S (k + 1)) → ℚ) :
    ∏ φ, f φ = (∏ φ' : ↥(𝒮.S k), f ⟨φ'.1, 𝒮.mono k φ'.2⟩) *
      ∏ φ ∈ (Finset.univ : Finset ↥(𝒮.S (k + 1))).filter (fun φ => φ.1 ∉ 𝒮.S k), f φ := by
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun φ : ↥(𝒮.S (k + 1)) => φ.1 ∈ 𝒮.S k)]
  congr 1
  symm
  refine Finset.prod_bij' (fun φ' _ => ⟨φ'.1, 𝒮.mono k φ'.2⟩)
    (fun φ hφ => ⟨φ.1, (Finset.mem_filter.mp hφ).2⟩) ?_ ?_ ?_ ?_ ?_
  · intro φ' _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, φ'.2⟩
  · intro φ _
    exact Finset.mem_univ _
  · intro φ' _
    rfl
  · intro φ _
    rfl
  · intro φ' _
    rfl

/-- **The trajectory marginal factorizes coordinatewise** for the tent skeleton: the last-day
marginal at horizon `h+1` is the product over the day-`(m+h+1)` sentences of the coordinate
marginals. Proof by induction on `h` through Chapman–Kolmogorov and `Finset.prod_univ_sum`
(sum over the intermediate product grid of a product = product of sums).
Source: [[bli-program]] §3.4 ("the state atom's price is the product over the coordinates")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem lastMarg_tent_eq_prod_coordMarg (t : Table 𝒮 m) :
    ∀ (h : ℕ) (Q : Table 𝒮 (m + h + 1)),
      lastMarg (tentSkeleton 𝒮 𝓜) m (h + 1) t Q = ∏ φ, coordMarg 𝓜 m h t φ (Q φ)
  | 0, Q => by
      rw [lastMarg_one]
      rfl
  | h + 1, Q => by
      show lastMarg (tentSkeleton 𝒮 𝓜) m (h + 1 + 1) t Q =
        ∏ φ : ↥(𝒮.S (m + h + 1 + 1)), coordMarg 𝓜 m (h + 1) t φ (Q φ)
      rw [lastMarg_succ]
      simp only [lastMarg_tent_eq_prod_coordMarg t h]
      show ∑ Q' ∈ grid 𝒮 𝓜.d (m + h + 1),
          (∏ φ', coordMarg 𝓜 m h t φ' (Q' φ')) * tentLaw 𝓜 (m + h + 1) Q' Q = _
      -- the right-hand side, split into old and new coordinates
      rw [prod_S_succ_split (k := m + h + 1) (fun φ => coordMarg 𝓜 m (h + 1) t φ (Q φ))]
      have hnew : ∀ φ ∈ (Finset.univ : Finset ↥(𝒮.S (m + h + 1 + 1))).filter
          (fun φ => φ.1 ∉ 𝒮.S (m + h + 1)),
          coordMarg 𝓜 m (h + 1) t φ (Q φ) = uniform1 (𝓜.d (m + h + 1 + 1)) (Q φ) := by
        intro φ hφ
        exact coordMarg_succ_of_not_mem t (Q φ) (Finset.mem_filter.mp hφ).2
      have hold : ∀ φ' : ↥(𝒮.S (m + h + 1)),
          coordMarg 𝓜 m (h + 1) t ⟨φ'.1, 𝒮.mono _ φ'.2⟩ (Q ⟨φ'.1, 𝒮.mono _ φ'.2⟩) =
            ∑ v' ∈ gridVals (𝓜.d (m + h + 1)),
              coordMarg 𝓜 m h t φ' v' * tent1 (𝓜.d (m + h + 1 + 1)) v' (Q ⟨φ'.1, 𝒮.mono _ φ'.2⟩) := by
        intro φ'
        rw [coordMarg_succ_of_mem t _ φ'.2]
      rw [Finset.prod_congr rfl hnew, Finset.prod_congr rfl (fun φ' _ => hold φ')]
      -- the left-hand side: split the tent law the same way
      have htent : ∀ Q' : Table 𝒮 (m + h + 1), tentLaw 𝓜 (m + h + 1) Q' Q =
          (∏ φ' : ↥(𝒮.S (m + h + 1)),
            tent1 (𝓜.d (m + h + 1 + 1)) (Q' φ') (Q ⟨φ'.1, 𝒮.mono _ φ'.2⟩)) *
          ∏ φ ∈ (Finset.univ : Finset ↥(𝒮.S (m + h + 1 + 1))).filter
            (fun φ => φ.1 ∉ 𝒮.S (m + h + 1)), uniform1 (𝓜.d (m + h + 1 + 1)) (Q φ) := by
        intro Q'
        unfold tentLaw
        rw [prod_S_succ_split (fun φ => tentCoord 𝓜 (m + h + 1) Q' φ (Q φ))]
        congr 1
        · apply Finset.prod_congr rfl
          intro φ' _
          unfold tentCoord
          rw [dif_pos φ'.2]
        · apply Finset.prod_congr rfl
          intro φ hφ
          unfold tentCoord
          rw [dif_neg (Finset.mem_filter.mp hφ).2]
      simp only [htent]
      rw [Finset.prod_univ_sum (fun _ => gridVals (𝓜.d (m + h + 1)))
        (fun φ' v' => coordMarg 𝓜 m h t φ' v' * tent1 (𝓜.d (m + h + 1 + 1)) v' (Q ⟨φ'.1, 𝒮.mono _ φ'.2⟩))]
      rw [Finset.sum_mul]
      unfold grid
      apply Finset.sum_congr rfl
      intro Q' _
      rw [Finset.prod_mul_distrib]
      ring

end LastMarg

/-! ## The expression -/

/-- The order on the day-`k` small sentences by FAF code, so that the product of coordinate
terms is a *computable* list (no `Finset.toList`).
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def encLE (𝒮 : SmallIndex) (k : ℕ) (φ ψ : ↥(𝒮.S k)) : Prop :=
  Encodable.encode φ.1 ≤ Encodable.encode ψ.1

instance (𝒮 : SmallIndex) (k : ℕ) : DecidableRel (encLE 𝒮 k) := fun _ _ => Nat.decLe _ _
instance (𝒮 : SmallIndex) (k : ℕ) : IsTrans ↥(𝒮.S k) (encLE 𝒮 k) :=
  ⟨fun _ _ _ h₁ h₂ => le_trans h₁ h₂⟩
instance (𝒮 : SmallIndex) (k : ℕ) : Std.Antisymm (encLE 𝒮 k) :=
  ⟨fun _ _ h₁ h₂ => Subtype.ext (Encodable.encode_injective (le_antisymm h₁ h₂))⟩
instance (𝒮 : SmallIndex) (k : ℕ) : Std.Total (encLE 𝒮 k) := ⟨fun _ _ => le_total _ _⟩

/-- The product of a function over the sorted list of day-`k` sentences is the `Finset` product.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma prod_sort_eq (𝒮 : SmallIndex) (k : ℕ) (f : ↥(𝒮.S k) → ℚ) :
    (((Finset.univ : Finset ↥(𝒮.S k)).sort (encLE 𝒮 k)).map f).prod = ∏ φ, f φ := by
  rw [((Finset.sort_perm_toList (Finset.univ : Finset ↥(𝒮.S k)) (encLE 𝒮 k)).map f).prod_eq,
    Finset.prod_map_toList]

/-- **The coordinate term** at the day-`(m+h+1)` sentence `φ` and grid value `v`: for a sentence
small on day `m`, the three-weight mixture of `price φ m` with the constants `chainFrom h δ₀`,
`chainFrom h U`, `chainFrom h δ₁` at `v`; for a sentence entering later, the rational constant
`coordMarg h (zero table) φ v`.
Source: [[bli-program]] §3.4 (Expressibility; this run's construction)
Kind: D
Fidelity: exact -/
def coordExpr (𝓜 : Mesh) (m h : ℕ) (φ : ↥(𝒮.S (m + h + 1))) (v : ℚ) : EF :=
  if hφ : φ.1 ∈ 𝒮.S m then
    mix3E (.price φ.1 m) (chainFrom 𝓜 m h (fun u => if u = 0 then 1 else 0) v)
      (chainFrom 𝓜 m h (uniform1 (𝓜.d (m + 1))) v)
      (chainFrom 𝓜 m h (fun u => if u = 1 then 1 else 0) v)
  else .const (coordMarg 𝓜 m h (fun _ => 0) φ v)

/-- **`tentExpr`**: the `EF` term for the price of the written-out day-`(m+h+1)` state `Q` under
the tent chain started on day `m` — the product of the coordinate terms over the day-`(m+h+1)`
small sentences (sorted by FAF code). Closed; leaves `price φ m` for `φ ∈ S m` only; no
`safeRecip`, `var` or `letE`.
Source: [[bli-program]] §3.4 (the `expr` map)
Kind: D
Fidelity: exact -/
def tentExpr (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1)) : EF :=
  prodList (((Finset.univ : Finset ↥(𝒮.S (m + h + 1))).sort (encLE 𝒮 (m + h + 1))).map
    fun φ => coordExpr 𝓜 m h φ (Q φ))

/-- **`tentExpr₁`**: the one-step term (`h = 0`), for the day-`(m+1)` state `Q`.
Source: [[bli-program]] §3.4
Kind: D
Fidelity: exact -/
def tentExpr₁ (𝓜 : Mesh) (m : ℕ) (Q : Table 𝒮 (m + 1)) : EF := tentExpr 𝓜 m 0 Q

/-- The coordinate term denotes the coordinate marginal at the history's day-`m` table, for
**every** rational history (the clamp is inside the term).
Source: [[bli-program]] §3.4
Kind: L
Fidelity: exact -/
lemma denoteRat_coordExpr (𝓜 : Mesh) (m h : ℕ) (φ : ↥(𝒮.S (m + h + 1))) (v : ℚ)
    (V : ℕ → Sentence → ℚ) :
    (coordExpr 𝓜 m h φ v).denoteRat V = coordMarg 𝓜 m h (actualTable 𝒮 V m) φ v := by
  unfold coordExpr
  split_ifs with hφ
  · rw [denoteRat_mix3E, coordMarg_of_mem _ h φ v hφ, chainFrom_tentW]
    rfl
  · rw [coordMarg_const_of_not_mem _ (actualTable 𝒮 V m) h φ v hφ]
    rfl

/-- The term denotes the product of the coordinate marginals.
Source: [[bli-program]] §3.4
Kind: L
Fidelity: exact -/
lemma denoteRat_tentExpr_prod (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1)) (V : ℕ → Sentence → ℚ) :
    (tentExpr 𝓜 m h Q).denoteRat V = ∏ φ, coordMarg 𝓜 m h (actualTable 𝒮 V m) φ (Q φ) := by
  unfold tentExpr
  rw [denoteRat_prodList, List.map_map, ← prod_sort_eq 𝒮 (m + h + 1)]
  congr 1
  apply List.map_congr_left
  intro φ _
  exact denoteRat_coordExpr 𝓜 m h φ (Q φ) V

/-- **E2(c), `h`-step expressibility.** For every rational history `V`, the exact rational
denotation of `tentExpr 𝓜 m h Q` is the day-`(m+h+1)` marginal of the tent chain started at the
history's day-`m` table: `𝐏_m(𝐐_{m+h+1} = Q)` in the skeleton. No unit-cube hypothesis (the
clamp is in the term); `denoteRat`, not `denote`.
Composition of `denoteRat_tentExpr_prod` with `lastMarg_tent_eq_prod_coordMarg` (the content is
in those two and in `denoteRat_coordExpr`).
Source: [[bli-program]] §3.4 (Expressibility, the property Route T needs); bli-slides-003
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem tentExpr_denoteRat (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1)) (V : ℕ → Sentence → ℚ) :
    (tentExpr 𝓜 m h Q).denoteRat V =
      lastMarg (tentSkeleton 𝒮 𝓜) m (h + 1) (actualTable 𝒮 V m) Q := by
  rw [denoteRat_tentExpr_prod, lastMarg_tent_eq_prod_coordMarg]

/-- **E2(b), one-step expressibility.** For every rational history `V`, `tentExpr₁ 𝓜 m Q` denotes
the tent law at the history's day-`m` table: `tentLaw 𝓜 m (actualTable 𝒮 V m) Q`.
`denoteRat_tentExpr_prod` at `h = 0` (the content is in `denoteRat_coordExpr`).
Source: [[bli-program]] §3.4; bli-slides-003 ("naively assuming independence")
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem tentExpr₁_denoteRat (𝓜 : Mesh) (m : ℕ) (Q : Table 𝒮 (m + 1)) (V : ℕ → Sentence → ℚ) :
    (tentExpr₁ 𝓜 m Q).denoteRat V = tentLaw 𝓜 m (actualTable 𝒮 V m) Q := by
  unfold tentExpr₁
  rw [denoteRat_tentExpr_prod]
  rfl

/-! ## Leaves: closed terms whose only price leaves are day-`n` sentences of `A` -/

/-- `PriceLeavesIn A n e`: every leaf of `e` is a constant or a price `price φ n` with `φ ∈ A`,
and `e` uses only `add`/`mul`/`max` (no `safeRecip`, `var`, `letE`) — the shape the transfer
theorem's hypothesis (i) asks for (closed terms with same-day small leaves).
Source: [[bli-program]] §3.1 (hypothesis (i) of the transfer theorem); mandate design decision 3
Kind: D
Fidelity: exact -/
def PriceLeavesIn (A : Finset Sentence) (n : ℕ) : EF → Prop
  | .price φ k => φ ∈ A ∧ k = n
  | .const _ => True
  | .add a b => PriceLeavesIn A n a ∧ PriceLeavesIn A n b
  | .mul a b => PriceLeavesIn A n a ∧ PriceLeavesIn A n b
  | .max a b => PriceLeavesIn A n a ∧ PriceLeavesIn A n b
  | .safeRecip _ => False
  | .var _ => False
  | .letE _ _ => False

/-- A term with day-`n` leaves has rank at most `n`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma rank_le_of_priceLeavesIn {A : Finset Sentence} {n : ℕ} :
    ∀ {e : EF}, PriceLeavesIn A n e → e.rank ≤ n
  | .price _ _, h => by rw [EF.rank_price, h.2]
  | .const _, _ => Nat.zero_le _
  | .add a b, h => by
      rw [EF.rank_add]
      exact max_le (rank_le_of_priceLeavesIn h.1) (rank_le_of_priceLeavesIn h.2)
  | .mul a b, h => by
      rw [EF.rank_mul]
      exact max_le (rank_le_of_priceLeavesIn h.1) (rank_le_of_priceLeavesIn h.2)
  | .max a b, h => by
      rw [EF.rank_max]
      exact max_le (rank_le_of_priceLeavesIn h.1) (rank_le_of_priceLeavesIn h.2)
  | .safeRecip _, h => h.elim
  | .var _, h => h.elim
  | .letE _ _, h => h.elim

section Leaves

variable {A : Finset Sentence} {n : ℕ}

/-- Leaves of the algebra's helpers.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma priceLeavesIn_mix3E {x : EF} (hx : PriceLeavesIn A n x) (c0 cU c1 : ℚ) :
    PriceLeavesIn A n (mix3E x c0 cU c1) := by
  simp only [mix3E, w0E, wUE, w1E, clampE, minE, negE, subE, absE, PriceLeavesIn, hx, and_self,
    true_and, and_true]

/-- Leaves of a product.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma priceLeavesIn_prodList {l : List EF} (hl : ∀ e ∈ l, PriceLeavesIn A n e) :
    PriceLeavesIn A n (prodList l) := by
  induction l with
  | nil => trivial
  | cons e l ih =>
      show PriceLeavesIn A n e ∧ PriceLeavesIn A n (prodList l)
      exact ⟨hl e (List.mem_cons_self ..), ih fun e' he' => hl e' (List.mem_cons_of_mem _ he')⟩

end Leaves

/-- **The leaves of `tentExpr` are exactly day-`m` prices of day-`m` small sentences**, and the
term is closed and free of `safeRecip`/`var`/`letE`.
Structural induction over the term's grammar.
Source: [[bli-program]] §3.1 (hypothesis (i)), §3.4; mandate design decision 3
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem tentExpr_priceLeavesIn (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1)) :
    PriceLeavesIn (𝒮.S m) m (tentExpr 𝓜 m h Q) := by
  unfold tentExpr
  apply priceLeavesIn_prodList
  intro e he
  rw [List.mem_map] at he
  obtain ⟨φ, -, rfl⟩ := he
  unfold coordExpr
  split_ifs with hφ
  · exact priceLeavesIn_mix3E (x := .price φ.1 m) (show φ.1 ∈ 𝒮.S m ∧ m = m from ⟨hφ, rfl⟩) _ _ _
  · trivial

/-- `tentExpr` has rank at most `m` (it inspects no day after `m`).
Source: none: infrastructure
Kind: L
Fidelity: exact -/
lemma tentExpr_rank_le (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1)) : (tentExpr 𝓜 m h Q).rank ≤ m :=
  rank_le_of_priceLeavesIn (tentExpr_priceLeavesIn 𝓜 m h Q)

/-! ## Size -/

/-- Cost of a product of terms each of cost at most `K`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cost_prodList_le (K : ℕ) : ∀ (l : List EF), (∀ e ∈ l, e.cost ≤ K) →
    (prodList l).cost ≤ (K + 1) * l.length + 1
  | [], _ => by simp [prodList, EF.cost]
  | e :: l, hl => by
      have ih := cost_prodList_le K l fun e' he' => hl e' (List.mem_cons_of_mem _ he')
      have he := hl e (List.mem_cons_self ..)
      simp only [prodList, EF.cost, List.length_cons]
      nlinarith

/-- Every coordinate term has cost at most `87` (the constant branch has cost `1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
lemma cost_coordExpr_le (𝓜 : Mesh) (m h : ℕ) (φ : ↥(𝒮.S (m + h + 1))) (v : ℚ) :
    (coordExpr 𝓜 m h φ v).cost ≤ 87 := by
  unfold coordExpr
  split_ifs
  · simp [mix3E, w0E, wUE, w1E, clampE, minE, negE, subE, absE, EF.cost]
  · simp [EF.cost]

/-- **E2(d), the size bound (node count).** `tentExpr 𝓜 m h Q` has at most `88·|S (m+h+1)| + 1`
nodes — linear in the number of day-`(m+h+1)` small sentences, with an absolute constant,
uniformly in `h`, `d` and `Q`. The rational constants are single `const` nodes; their *bit-size*
is not measured by `cost` — it is the half of the program's claim FAF's `EfficientlyComputable`
meters, and it is proved in `Bits.lean` (`tentExpr_constsBounded`, `tentExpr_digitize_length_le`).
Source: [[bli-program]] §3.4 (size `O(|S_m| · poly)`), stated in `EF.cost`
Kind: P
Fidelity: variant: stronger in the node count (linear in `|S (m+h+1)|`, no `h`/`log d` factor);
the constants' bit-size is a separate statement (`Bits.lean`)
Hyps: (a) none -/
theorem tentExpr_cost_le (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1)) :
    (tentExpr 𝓜 m h Q).cost ≤ 88 * (𝒮.S (m + h + 1)).card + 1 := by
  unfold tentExpr
  have := cost_prodList_le 87 (((Finset.univ : Finset ↥(𝒮.S (m + h + 1))).sort (encLE 𝒮 (m + h + 1))).map
    fun φ => coordExpr 𝓜 m h φ (Q φ)) (by
      intro e he
      rw [List.mem_map] at he
      obtain ⟨φ, -, rfl⟩ := he
      exact cost_coordExpr_le 𝓜 m h φ (Q φ))
  rw [List.length_map, Finset.length_sort, Finset.card_univ, Fintype.card_coe] at this
  omega

/-- **E2(d), the size bound (token count).** The serialized token stream of `tentExpr 𝓜 m h Q`
(`EF.serialize`, the token form; FAF's class is bit-metered through `digitize`) has length at most
`3·(88·|S (m+h+1)| + 1)`, via `serialize_length_le_cost`. Each rational constant is one token
(`Encodable.encode q`); the magnitude of that token is not bounded here but in `Bits.lean`
(`encode_rat_lt` with `tentExpr_constsBounded`), and the bit-metered stream length is
`tentExpr_digitize_length_le`.
Source: [[bli-program]] §3.4, stated in `EF.serialize.length`
Kind: C
Fidelity: variant: stronger in the token count (linear in `|S (m+h+1)|`, uniform in `h` and `d`);
the constants' bit-size is a separate statement (`Bits.lean`)
Hyps: (a) none -/
theorem tentExpr_size_le (𝓜 : Mesh) (m h : ℕ) (Q : Table 𝒮 (m + h + 1)) :
    (tentExpr 𝓜 m h Q).serialize.length ≤ 3 * (88 * (𝒮.S (m + h + 1)).card + 1) :=
  (EF.serialize_length_le_cost _).trans (Nat.mul_le_mul_left 3 (tentExpr_cost_le 𝓜 m h Q))

end Cleanroom.Bli.BliSuperbelief
