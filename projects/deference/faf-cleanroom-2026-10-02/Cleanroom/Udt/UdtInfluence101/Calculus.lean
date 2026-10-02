import Cleanroom.Udt.UdtInfluence101.Atoms

/-!
# `Cleanroom.Udt.UdtInfluence101.Calculus`: Assumptions 1–2 as theorems, Lemma 1, `f^n`, Lemma 2

Targets T1–T3 of [[udt-influence-101-mandate]].

* `SmoothLaw` makes every mass and every conditional (on a positive event) differentiable in `ε`
  at `0`: Post 6's **Assumption 1** holds on the support (`A1_of_smoothLaw`).
* **Assumption 2** (Post 6) is the law of total expectation over the next observation — a theorem
  of every finite weight function, with the junk cases exactly where an event is null
  (`condExpJunk_eq_sum_nextObs`).
* **Lemma 1** (Post 6): the probability/quality split of the influence on expected utility is the
  product rule for the derivative of `Σ_o ℙ^ε(o)·𝔼^ε[U | o]` (`lemma1_split`).
* `fS h μ n`: Post 8's recursively defined score `f^n_{h,S̄_h}(μ)`, and **Lemma 2**: it is affine in
  `μ` (`fS_affine`), via **Post 8 Lemma 1** (`IE_ofDist_affine`).
-/

set_option linter.unusedSectionVars false

namespace Cleanroom.Udt.UdtInfluence101

noncomputable section

open Finset Filter Topology Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree

variable {O Act Ξ : Type} [Fintype O] [DecidableEq O] [Fintype Act] [DecidableEq Act]
  [Fintype Ξ] [DecidableEq Ξ] {N : ℕ} {Ω : Type} [Fintype Ω] [DecidableEq Ω]

namespace PlaySpace

variable (S : PlaySpace O Act Ξ N Ω)

/-! ### Derivatives of masses and conditionals in `ε` -/

/-- The derivative at `0` of the mass of `E` under ε-play, as a sum of coordinate derivatives.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def dmass (A : Alg O Act Ξ N) (h : Node O N) (E : Finset Ω) : ℝ :=
  ∑ ω ∈ E, deriv (fun ε => S.law A h ε ω) 0

/-- The derivative at `0` of `Σ_{ω ∈ E} law_ε(ω) f(ω)` under ε-play.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def dwsum (A : Alg O Act Ξ N) (h : Node O N) (E : Finset Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω ∈ E, deriv (fun ε => S.law A h ε ω) 0 * f ω

/-- Supporting lemma `hasDerivAt_mass`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hasDerivAt_mass (hS : S.SmoothLaw) (A : Alg O Act Ξ N) (h : Node O N) (E : Finset Ω) :
    HasDerivAt (fun ε => mass (S.law A h ε) E) (S.dmass A h E) 0 := by
  unfold mass dmass
  apply HasDerivAt.fun_sum
  intro ω _
  obtain ⟨c, hc⟩ := hS A h ω
  rw [hc.deriv]; exact hc

/-- Supporting lemma `hasDerivAt_wsum`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem hasDerivAt_wsum (hS : S.SmoothLaw) (A : Alg O Act Ξ N) (h : Node O N) (E : Finset Ω)
    (f : Ω → ℝ) :
    HasDerivAt (fun ε => ∑ ω ∈ E, S.law A h ε ω * f ω) (S.dwsum A h E f) 0 := by
  unfold dwsum
  apply HasDerivAt.fun_sum
  intro ω _
  obtain ⟨c, hc⟩ := hS A h ω
  rw [hc.deriv]; exact hc.mul_const _

/-- Supporting lemma `eventually_mass_pos` (a positive event stays positive for `ε` near `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem eventually_mass_pos (hS : S.SmoothLaw) (A : Alg O Act Ξ N) (h : Node O N) {E : Finset Ω}
    (hpos : 0 < mass S.ℙ.w E) : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < mass (S.law A h ε) E := by
  have hc := (S.hasDerivAt_mass hS A h E).continuousAt
  have h0 : mass (S.law A h 0) E = mass S.ℙ.w E := by rw [S.law_zero]
  exact continuousAt_const.eventually_lt hc (by rw [h0]; exact hpos)

/-- **`ℙ^ε_{h₁:ₙ}(F)` is differentiable at `ε = 0` on a positive atom** (quotient rule).
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 1, first limit
Kind: L
Fidelity: exact
Hyps: none -/
theorem hasDerivAt_pr (hS : S.SmoothLaw) (A : Alg O Act Ξ N) (h : Node O N) {n : ℕ} {ω : Ω}
    (hpos : 0 < mass S.ℙ.w (S.atom n ω)) (F : Finset Ω) :
    HasDerivAt (fun ε => S.pr (S.law A h ε) n F ω)
      ((S.dmass A h (F ∩ S.atom n ω) * mass S.ℙ.w (S.atom n ω) -
        mass S.ℙ.w (F ∩ S.atom n ω) * S.dmass A h (S.atom n ω)) / (mass S.ℙ.w (S.atom n ω)) ^ 2) 0 := by
  have hm := S.hasDerivAt_mass hS A h (S.atom n ω)
  have hm' := S.hasDerivAt_mass hS A h (F ∩ S.atom n ω)
  have h0 : mass (S.law A h 0) (S.atom n ω) = mass S.ℙ.w (S.atom n ω) := by rw [S.law_zero]
  have hdiv := hm'.div hm (by rw [h0]; exact hpos.ne')
  simp only [S.law_zero] at hdiv
  refine hdiv.congr_of_eventuallyEq ?_
  filter_upwards [S.eventually_mass_pos hS A h hpos] with ε hε
  simp only [pr, condProbJunk, hε.ne', if_false, Pi.div_apply]

/-- **`𝔼^ε_{h₁:ₙ}[f | E]` is differentiable at `ε = 0` on a positive event** (quotient rule).
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 1, second and third limits
Kind: L
Fidelity: exact
Hyps: none -/
theorem hasDerivAt_cexp (hS : S.SmoothLaw) (A : Alg O Act Ξ N) (h : Node O N) {n : ℕ} {ω : Ω}
    {E : Finset Ω} (hpos : 0 < mass S.ℙ.w (S.atom n ω ∩ E)) (f : Ω → ℝ) :
    HasDerivAt (fun ε => S.cexp (S.law A h ε) n E f ω)
      ((S.dwsum A h (S.atom n ω ∩ E) f * mass S.ℙ.w (S.atom n ω ∩ E) -
        (∑ ω' ∈ S.atom n ω ∩ E, S.ℙ.w ω' * f ω') * S.dmass A h (S.atom n ω ∩ E)) /
          (mass S.ℙ.w (S.atom n ω ∩ E)) ^ 2) 0 := by
  have hm := S.hasDerivAt_mass hS A h (S.atom n ω ∩ E)
  have hw := S.hasDerivAt_wsum hS A h (S.atom n ω ∩ E) f
  have h0 : mass (S.law A h 0) (S.atom n ω ∩ E) = mass S.ℙ.w (S.atom n ω ∩ E) := by rw [S.law_zero]
  have hdiv := hw.div hm (by rw [h0]; exact hpos.ne')
  simp only [S.law_zero] at hdiv
  refine hdiv.congr_of_eventuallyEq ?_
  filter_upwards [S.eventually_mass_pos hS A h hpos] with ε hε
  simp only [cexp, condExpJunk, hε.ne', if_false, Pi.div_apply]

/-- **Post 6's Assumption 1 is a theorem of every smooth play space, on the support.**
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 1 (udt-rep-080); mandate T7
Kind: P
Fidelity: weaker: on the support (off it the junk `0` at `ε = 0` can break the limit; see `A1`)
Hyps: (a) `SmoothLaw` (a theorem of the model of record) -/
theorem A1_of_smoothLaw (hS : S.SmoothLaw) : S.A1 := by
  intro n A h o ω hω
  refine ⟨⟨_, S.hasDerivAt_pr hS A h (S.mass_atom_pos hω) _⟩, fun hpos => ⟨_, S.hasDerivAt_cexp hS A h hpos _⟩,
    ⟨_, S.hasDerivAt_cexp hS A h (by rw [Finset.inter_univ]; exact S.mass_atom_pos hω) _⟩⟩

/-! ### Assumption 2: the law of total expectation over the next observation -/

/-- Supporting lemma `atom_inter_nextObs_eq_filter`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem atom_inter_nextObs_eq_filter {n : ℕ} (hn : n < N) (ω : Ω) (o : O) :
    S.atom n ω ∩ S.nextObs n o = (S.atom n ω).filter (fun ω' => S.obs ω' ⟨n, hn⟩ = o) := by
  ext ω'
  simp only [Finset.mem_inter, Finset.mem_filter, S.mem_nextObs hn]

/-- Supporting lemma `sum_nextObs_fiberwise` (the next observation partitions the atom).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_nextObs_fiberwise {n : ℕ} (hn : n < N) (ω : Ω) (g : Ω → ℝ) :
    ∑ o, ∑ ω' ∈ S.atom n ω ∩ S.nextObs n o, g ω' = ∑ ω' ∈ S.atom n ω, g ω' := by
  simp only [S.atom_inter_nextObs_eq_filter hn]
  exact Finset.sum_fiberwise (S.atom n ω) (fun ω' => S.obs ω' ⟨n, hn⟩) g

/-- **Post 6's Assumption 2 is a theorem** (the law of total expectation over the next observation),
for every weight function `w` such that a null `atom ∩ {o}` carries a null weighted sum of `f` (true
for non-negative `w`, and for any `w` when every `atom ∩ {o}` is non-null). Post 6 calls it an
assumption and offers a Dutch book for its violation; in a single-prior finite model it is the
tower property. The junk `0` enters only where an event is null — exactly where the post divides by
zero.
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 2 (udt-rep-080); mandate T1
Kind: P
Fidelity: exact (both displayed identities, the second being the case `w = ℙ`)
Hyps: (a) none beyond the null-event clause -/
theorem condExpJunk_eq_sum_nextObs {n : ℕ} (hn : n < N) (ω : Ω) (w f : Ω → ℝ)
    (hnull : ∀ o, mass w (S.atom n ω ∩ S.nextObs n o) = 0 →
      ∑ ω' ∈ S.atom n ω ∩ S.nextObs n o, w ω' * f ω' = 0) :
    condExpJunk w f (S.atom n ω) 0 =
      ∑ o, condProbJunk w (S.nextObs n o) (S.atom n ω) 0 *
        condExpJunk w f (S.atom n ω ∩ S.nextObs n o) 0 := by
  by_cases hA : mass w (S.atom n ω) = 0
  · simp [condExpJunk, condProbJunk, hA]
  · rw [condExpJunk, if_neg hA]
    have hterm : ∀ o, condProbJunk w (S.nextObs n o) (S.atom n ω) 0 *
        condExpJunk w f (S.atom n ω ∩ S.nextObs n o) 0 =
        (∑ ω' ∈ S.atom n ω ∩ S.nextObs n o, w ω' * f ω') / mass w (S.atom n ω) := by
      intro o
      rw [condProbJunk, if_neg hA, Finset.inter_comm]
      by_cases ho : mass w (S.atom n ω ∩ S.nextObs n o) = 0
      · rw [condExpJunk, if_pos ho, mul_zero, hnull o ho, zero_div]
      · rw [condExpJunk, if_neg ho]
        field_simp
    simp only [hterm, div_eq_mul_inv]
    rw [← Finset.sum_mul, S.sum_nextObs_fiberwise hn]

/-- Assumption 2 under the prior (non-negative weights, no side condition).
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 2, second display
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem cexp_eq_sum_nextObs_prior {n : ℕ} (hn : n < N) (ω : Ω) (f : Ω → ℝ) :
    S.cexp S.ℙ.w n univ f ω =
      ∑ o, S.pr S.ℙ.w n (S.nextObs n o) ω * S.cexp S.ℙ.w n (S.nextObs n o) f ω := by
  simp only [cexp, pr, Finset.inter_univ]
  refine S.condExpJunk_eq_sum_nextObs hn ω S.ℙ.w f fun o ho => ?_
  exact Finset.sum_eq_zero fun ω' hω' => by
    rw [weight_eq_zero_of_mass_eq_zero S.ℙ.nonneg ho hω', zero_mul]

/-! ### Lemma 1: the probability/quality split is the product rule -/

/-- Supporting lemma `mass_atom_pos_of_posObs`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem mass_atom_pos_of_posObs {n : ℕ} (hn : n < N) {ω : Ω} (hpos : S.PosObs n ω) :
    0 < mass S.ℙ.w (S.atom n ω) :=
  lt_of_lt_of_le (hpos (S.obs ω ⟨n, hn⟩))
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_left fun ω' _ _ => S.ℙ.nonneg ω')

/-- Supporting lemma `eventually_cexp_eq_sum` (Assumption 2 holds along the whole ε-family near `0`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem eventually_cexp_eq_sum (hS : S.SmoothLaw) {n : ℕ} (hn : n < N) {ω : Ω} (hpos : S.PosObs n ω)
    (A : Alg O Act Ξ N) (h : Node O N) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), S.cexp (S.law A h ε) n univ S.U ω =
      ∑ o, S.pr (S.law A h ε) n (S.nextObs n o) ω * S.cexp (S.law A h ε) n (S.nextObs n o) S.U ω := by
  have hall : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ o, 0 < mass (S.law A h ε) (S.atom n ω ∩ S.nextObs n o) := by
    rw [Filter.eventually_all]
    intro o
    exact S.eventually_mass_pos hS A h (hpos o)
  filter_upwards [hall] with ε hε
  simp only [cexp, pr, Finset.inter_univ]
  exact S.condExpJunk_eq_sum_nextObs hn ω _ _ fun o ho => absurd ho (hε o).ne'

/-- **Post 6 Lemma 1 as a product rule**: on a smooth play space, at a time-`n` atom from which every
next observation is possible, the influence on expected utility splits into a probability part and a
quality part,
`𝕀^𝔼_{h₁:ₙ}(A,h) = Σ_o (ℙ_{h₁:ₙ}(o)·𝕀^𝔼_{h₁:ₙ}(A,h,o) + 𝕀^ℙ_{h₁:ₙ}(A,h,o)·𝔼_{h₁:ₙ}[U|o])`.
The three influences are the derivatives at `0` of the *same* ε-family, Assumption 2 holds along it
(`eventually_cexp_eq_sum`), and the cross term Diffractor writes as `ε·𝕀^ℙ·𝕀^𝔼 → 0` is the product
rule. The positivity of every `atom ∩ {o}` under `ℙ` is where the post divides by `ℙ_{h₁:ₙ}(o)`; a
null `o` that ε-play makes positive would contribute `𝕀^ℙ(o)·lim_ε 𝔼^ε[U|o]`, not `𝕀^ℙ(o)·0`, so the
identity with junk `0` is false without it ([[udt-influence-101-findings]]).
Source: `references/udt101/06-basics-of-algorithm.md` Lemma 1 (udt-rep-080); mandate T2
Kind: P
Fidelity: exact (under the stated positivity, which the post leaves implicit)
Hyps: (a) `SmoothLaw` (a theorem of the model of record); (a) `PosObs n ω` (regularity, checked on
the instances) -/
theorem lemma1_split (hS : S.SmoothLaw) {n : ℕ} (hn : n < N) {ω : Ω} (hpos : S.PosObs n ω)
    (A : Alg O Act Ξ N) (h : Node O N) :
    S.IE n A h ω = ∑ o, (S.pr S.ℙ.w n (S.nextObs n o) ω * S.IEo n A h o ω +
      S.IP n A h o ω * S.cexp S.ℙ.w n (S.nextObs n o) S.U ω) := by
  have hatom := S.mass_atom_pos_of_posObs hn hpos
  have hd : HasDerivAt (fun ε => ∑ o, S.pr (S.law A h ε) n (S.nextObs n o) ω *
      S.cexp (S.law A h ε) n (S.nextObs n o) S.U ω)
      (∑ o, (S.IP n A h o ω * S.cexp S.ℙ.w n (S.nextObs n o) S.U ω +
        S.pr S.ℙ.w n (S.nextObs n o) ω * S.IEo n A h o ω)) 0 := by
    apply HasDerivAt.fun_sum
    intro o _
    have h1 := S.hasDerivAt_pr hS A h hatom (S.nextObs n o)
    have h2 := S.hasDerivAt_cexp hS A h (hpos o) S.U
    have h12 := h1.mul h2
    simp only [S.law_zero] at h12
    rw [← h1.deriv, ← h2.deriv] at h12
    exact h12
  rw [IE, Filter.EventuallyEq.deriv_eq (S.eventually_cexp_eq_sum hS hn hpos A h), hd.deriv]
  exact Finset.sum_congr rfl fun o _ => by ring

/-! ### Post 8's score `f^n_{h,S̄_h}` and Lemma 2 -/

/-- Supporting lemma `cexp_congr_on_pos` (the conditional expectation reads `f` on the
positive-mass worlds of the event only).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem cexp_congr_on_pos {n : ℕ} {E : Finset Ω} {f g : Ω → ℝ} {ω : Ω}
    (hfg : ∀ ω' ∈ S.atom n ω ∩ E, 0 < S.ℙ.w ω' → f ω' = g ω') :
    S.cexp S.ℙ.w n E f ω = S.cexp S.ℙ.w n E g ω := by
  simp only [S.cexp_eq_div]
  congr 1
  refine Finset.sum_congr rfl fun ω' hω' => ?_
  rcases (S.ℙ.nonneg ω').lt_or_eq with h0 | h0
  · rw [hfg ω' hω' h0]
  · rw [← h0, zero_mul, zero_mul]

/-- The **causal term** of Post 8's score: `Σ_o (ℙ_{h₁:ₙ}(o)·𝕀^𝔼_{h₁:ₙ}(μ,h,o) + 𝕀^ℙ_{h₁:ₙ}(μ,h,o)·𝔼_{h₁:ₙ}[U|o])`
for the constant algorithm `μ`.
Source: `references/udt101/08-actual-algorithm.md` §3.1 (definition of `f^n`), §3.4 ("ordinary causal influence")
Kind: D
Fidelity: exact
Hyps: n/a -/
def fBase (h : Node O N) (μ : FinDist Act) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ o, (S.pr S.ℙ.w n (S.nextObs n o) ω * S.IEo n (ofDist μ) h o ω +
    S.IP n (ofDist μ) h o ω * S.cexp S.ℙ.w n (S.nextObs n o) S.U ω)

/-- The **deferral-correction term** of Post 8's score:
`ℙ_{h₁:ₙ}(h_{n+1})·𝔼_{h₁:ₙ}[𝕀^𝔼_{h₁:ₙ₊₁}(μ,h) | h_{n+1}]`, for `n < |h|`.
Source: `references/udt101/08-actual-algorithm.md` §3.1, §3.4 ("compensating for the fact that … future-us [will] mess up")
Kind: D
Fidelity: exact
Hyps: n/a -/
def fMid (h : Node O N) (μ : FinDist Act) (n : ℕ) (hn : n < h.1.val) (ω : Ω) : ℝ :=
  S.pr S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) ω *
    S.cexp S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) (fun ω' => S.IE (n + 1) (ofDist μ) h ω') ω

/-- The **reweighting ratio** `ℙ_{h₁:ₙ}(h) / ℙ_{h₁:ₙ₊₁}(h)` of Post 8's score. **Junk point**: Lean's
`x / 0 = 0`, so on a world whose time-`(n+1)` atom cannot reach `h` the ratio is `0`; on the
support of `reach h` both conditionals are positive (`ratio_pos_on_support`) and the junk never fires.
Source: `references/udt101/08-actual-algorithm.md` §3.1, §3.4 ("what's the deal with that ℙ_{h₁:ₙ}(h)/ℙ_{h₁:ₙ₊₁}(h) thing")
Kind: D
Fidelity: exact on the support of `reach h`; junk `0` where `ℙ_{h₁:ₙ₊₁}(h) = 0`
Hyps: n/a -/
def ratio (h : Node O N) (n : ℕ) (ω : Ω) : ℝ :=
  S.pr S.ℙ.w n (S.reach h) ω / S.pr S.ℙ.w (n + 1) (S.reach h) ω

/-- **Post 8's score `f^n_{h,S̄_h}(μ)`**, by downward recursion from `n = |h|`: the causal term, minus
the deferral-correction term, plus the reweighted score at `n + 1` (for `n < |h|`); the causal term
alone at `n = |h|`. The state sequence `S̄_h` enters through the world `ω` (every conditional is read
at `ω`'s atoms). For `n > |h|` (never used) it returns the causal term.
Source: `references/udt101/08-actual-algorithm.md` §3.1 (udt-rep-081); mandate T3
Kind: D
Fidelity: exact (with the ratio's junk point disclosed in `ratio`)
Hyps: n/a -/
def fS (h : Node O N) (μ : FinDist Act) : ℕ → Ω → ℝ
  | n => fun ω =>
    if hn : n < h.1.val then
      S.fBase h μ n ω - S.fMid h μ n hn ω + S.ratio h n ω * fS h μ (n + 1) ω
    else S.fBase h μ n ω
termination_by n => h.1.val - n

/-- Supporting lemma `fS_of_lt`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem fS_of_lt (h : Node O N) (μ : FinDist Act) {n : ℕ} (hn : n < h.1.val) (ω : Ω) :
    S.fS h μ n ω = S.fBase h μ n ω - S.fMid h μ n hn ω + S.ratio h n ω * S.fS h μ (n + 1) ω := by
  rw [fS]
  simp only [dif_pos hn]

/-- Supporting lemma `fS_of_ge`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem fS_of_ge (h : Node O N) (μ : FinDist Act) {n : ℕ} (hn : ¬ n < h.1.val) (ω : Ω) :
    S.fS h μ n ω = S.fBase h μ n ω := by
  rw [fS]
  simp only [dif_neg hn]

/-- Supporting lemma `play_ofDist`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
@[simp] theorem play_ofDist (μ : FinDist Act) (h : Node O N) (ω : Ω) :
    S.play (ofDist μ) h ω = μ := rfl

/-- Supporting lemma `constOnAtom_ofDist`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem constOnAtom_ofDist (n : ℕ) (μ : FinDist Act) (h : Node O N) (ω : Ω) :
    S.ConstOnAtom n (ofDist μ) h ω := fun _ _ => rfl

/-- Supporting lemma `along_of_reach` (a world reaching `h` is along `h` at every time `n ≤ |h|`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem along_of_reach {h : Node O N} {n : ℕ} (hn : n ≤ h.1.val) {ω : Ω} (hr : ω ∈ S.reach h) :
    S.Along h n hn ω := fun i hi => S.obs_eq_of_reach hr i _

/-- Supporting lemma `along_succ` (a world of the time-`n` atom of a world along `h`, with the
observation `h_{n+1}` at time `n`, is along `h` at time `n + 1`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem along_succ {h : Node O N} {n : ℕ} (hn : n < h.1.val) {ω ω' : Ω} (hal : S.Along h n hn.le ω)
    (hat : S.AtomEq n ω ω') (hnext : ω' ∈ S.nextObs n (h.2 ⟨n, hn⟩)) : S.Along h (n + 1) hn ω' := by
  intro i hi
  have hnN : n < N := lt_trans hn h.1.isLt
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi' | hi'
  · rw [← hat.1 i hi', hal i hi']
  · have hi'' : i = ⟨n, hnN⟩ := Fin.ext hi'
    subst hi''
    exact (S.mem_nextObs hnN).1 hnext

/-- **Post 8's Assumption 5 for constant algorithms** is the special case of `A5` (recovering the
post's literal statement from the form the proofs use).
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 (udt-rep-081)
Kind: L
Fidelity: exact
Hyps: (b) `A5` -/
theorem A5_ofDist {h : Node O N} (hA5 : S.A5 h) {n : ℕ} (hn : n ≤ h.1.val) (μ : FinDist Act) {ω : Ω}
    (hω : 0 < S.ℙ.w ω) (hal : S.Along h n hn ω) (o : O) :
    S.IP n (ofDist μ) h o ω = ∑ a, μ.w a * S.IP n (ofAct a) h o ω ∧
      S.IEo n (ofDist μ) h o ω = ∑ a, μ.w a * S.IEo n (ofAct a) h o ω :=
  hA5 n hn (ofDist μ) ω hω hal (S.constOnAtom_ofDist n μ h ω) o

/-- Supporting lemma `sum_affine_combo` (the algebra of Post 8's "use affineness of influence, then
linearity of expectation").
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem sum_affine_combo (μ : FinDist Act) (p s : O → ℝ) (F G : Act → O → ℝ) :
    ∑ o, (p o * ∑ a, μ.w a * F a o + (∑ a, μ.w a * G a o) * s o) =
      ∑ a, μ.w a * ∑ o, (p o * F a o + G a o * s o) := by
  calc ∑ o, (p o * ∑ a, μ.w a * F a o + (∑ a, μ.w a * G a o) * s o)
      = ∑ o, ∑ a, μ.w a * (p o * F a o + G a o * s o) := by
        refine Finset.sum_congr rfl fun o _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring
    _ = ∑ a, ∑ o, μ.w a * (p o * F a o + G a o * s o) := Finset.sum_comm
    _ = ∑ a, μ.w a * ∑ o, (p o * F a o + G a o * s o) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]

/-- The causal term is affine in the mixed action (Post 8 Lemma 2, base case).
Source: `references/udt101/08-actual-algorithm.md` Lemma 2 (base case)
Kind: L
Fidelity: exact
Hyps: (b) `A5` -/
theorem fBase_affine {h : Node O N} (hA5 : S.A5 h) {n : ℕ} (hn : n ≤ h.1.val) (μ : FinDist Act)
    {ω : Ω} (hω : 0 < S.ℙ.w ω) (hal : S.Along h n hn ω) :
    S.fBase h μ n ω = ∑ a, μ.w a * S.fBase h (FinDist.delta a) n ω := by
  unfold fBase
  have h5 := S.A5_ofDist hA5 hn μ hω hal
  simp only [(h5 _).1, (h5 _).2]
  exact sum_affine_combo μ _ _ _ _

/-- **Post 8 Lemma 1**: the influence on expected utility of a constant algorithm is the average of
the influences of its pure actions, `𝕀^𝔼_{h₁:ₙ}(μ,h) = E_{a∼μ}[𝕀^𝔼_{h₁:ₙ}(a,h)]`. Proof: Lemma 1 for `μ`
and for each `a`, then `A5`. The post routes through Assumption 3 for `μ` (via `μ̄ = μ`), but that
instance of A3 is the identity `𝕀(μ,…) = 𝕀(μ,…)` and is not needed ([[udt-influence-101-findings]]).
Source: `references/udt101/08-actual-algorithm.md` Lemma 1 (udt-rep-081); mandate T3(ii)
Kind: P
Fidelity: exact
Hyps: (a) `SmoothLaw`; (a) `PosObs n ω`; (b) `A5` -/
theorem IE_ofDist_affine (hS : S.SmoothLaw) {h : Node O N} (hA5 : S.A5 h) {n : ℕ} (hn : n ≤ h.1.val)
    (μ : FinDist Act) {ω : Ω} (hω : 0 < S.ℙ.w ω) (hal : S.Along h n hn ω) (hpos : S.PosObs n ω) :
    S.IE n (ofDist μ) h ω = ∑ a, μ.w a * S.IE n (ofAct a) h ω := by
  have hnN : n < N := lt_of_le_of_lt hn h.1.isLt
  rw [S.lemma1_split hS hnN hpos]
  have : ∀ a, S.IE n (ofAct a) h ω = S.fBase h (FinDist.delta a) n ω := fun a =>
    S.lemma1_split hS hnN hpos _ h
  simp only [this]
  exact S.fBase_affine hA5 hn μ hω hal

/-- The deferral-correction term is affine in the mixed action.
Source: `references/udt101/08-actual-algorithm.md` Lemma 2 (induction step, middle term)
Kind: L
Fidelity: exact
Hyps: (a) `SmoothLaw`; (a) `AllPosObs`; (b) `A5` -/
theorem fMid_affine (hS : S.SmoothLaw) (hall : S.AllPosObs) {h : Node O N} (hA5 : S.A5 h) {n : ℕ}
    (hn : n < h.1.val) (μ : FinDist Act) {ω : Ω} (hω : 0 < S.ℙ.w ω) (hal : S.Along h n hn.le ω) :
    S.fMid h μ n hn ω = ∑ a, μ.w a * S.fMid h (FinDist.delta a) n hn ω := by
  unfold fMid
  have hnN : n < N := lt_trans hn h.1.isLt
  have hpos : 0 < mass S.ℙ.w (S.atom n ω ∩ S.nextObs n (h.2 ⟨n, hn⟩)) := hall n hnN ω hω _
  rw [S.cexp_congr_on_pos (g := fun ω' => ∑ a, μ.w a * S.IE (n + 1) (ofAct a) h ω') fun ω' hω'm hω' =>
    S.IE_ofDist_affine hS hA5 hn μ hω'
      (S.along_succ hn hal (S.mem_atom.1 (Finset.mem_inter.1 hω'm).1) (Finset.mem_inter.1 hω'm).2)
      (hall (n + 1) (by omega) ω' hω')]
  rw [← S.cexp_sum hpos, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [S.cexp_const_mul]
  simp only [ofAct]
  ring

/-- **Post 8 Lemma 2 (affineness of `f^n`)**: `f^n_{h,S̄_h}(μ) = E_{a∼μ}[f^n_{h,S̄_h}(a)]` for every
`n ≤ |h|`, at every positive-mass world. The ratio needs no positivity: it is a scalar multiplying
an affine function, so affineness survives its junk value — which is why Lemma 2 is cheap and
Theorem 1 is not.
Source: `references/udt101/08-actual-algorithm.md` Lemma 2 (udt-rep-081); mandate T3(i)
Kind: P
Fidelity: exact ("affine" in the corpus's sense `f(μ) = E_{a∼μ} f(a)`, the statement itself)
Hyps: (a) `SmoothLaw`; (a) `AllPosObs`; (b) `A5` (Post 8 Assumption 5, taken as the post takes it);
stated at worlds reaching `h` (the only ones where Theorem 1 reads the score) -/
theorem fS_affine (hS : S.SmoothLaw) (hall : S.AllPosObs) {h : Node O N} (hA5 : S.A5 h)
    (μ : FinDist Act) :
    ∀ (n : ℕ), n ≤ h.1.val → ∀ ω, 0 < S.ℙ.w ω → ω ∈ S.reach h →
      S.fS h μ n ω = ∑ a, μ.w a * S.fS h (FinDist.delta a) n ω := by
  suffices key : ∀ k n, n + k = h.1.val → ∀ ω, 0 < S.ℙ.w ω → ω ∈ S.reach h →
      S.fS h μ n ω = ∑ a, μ.w a * S.fS h (FinDist.delta a) n ω by
    intro n hn ω hω hr
    exact key (h.1.val - n) n (by omega) ω hω hr
  intro k
  induction k with
  | zero =>
    intro n hn ω hω hr
    have hn' : ¬ n < h.1.val := by omega
    simp only [S.fS_of_ge h _ hn']
    exact S.fBase_affine hA5 (by omega) μ hω (S.along_of_reach _ hr)
  | succ k ih =>
    intro n hn ω hω hr
    have hlt : n < h.1.val := by omega
    simp only [S.fS_of_lt h _ hlt]
    rw [S.fBase_affine hA5 hlt.le μ hω (S.along_of_reach _ hr),
      S.fMid_affine hS hall hA5 hlt μ hω (S.along_of_reach _ hr),
      ih (n + 1) (by omega) ω hω hr, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring

/-- **The ratio is honest on the support**: at a positive-mass world reaching `h`, both
`ℙ_{h₁:ₙ}(h)` and `ℙ_{h₁:ₙ₊₁}(h)` are positive, so `ratio` is a genuine quotient (and positive).
Source: `references/udt101/08-actual-algorithm.md` §3.1; mandate T3(iii)
Kind: L
Fidelity: exact
Hyps: none -/
theorem pr_reach_pos {h : Node O N} (n : ℕ) {ω : Ω} (hω : 0 < S.ℙ.w ω) (hr : ω ∈ S.reach h) :
    0 < S.pr S.ℙ.w n (S.reach h) ω := by
  rw [S.pr_eq_div]
  exact div_pos (mass_pos_of_mem S.ℙ.nonneg (Finset.mem_inter.2 ⟨hr, S.self_mem_atom n ω⟩) hω)
    (S.mass_atom_pos hω)

/-- Supporting lemma `ratio_pos_on_support` (T3(iii)).
Source: mandate T3(iii)
Kind: L
Fidelity: exact
Hyps: none -/
theorem ratio_pos_on_support {h : Node O N} (n : ℕ) {ω : Ω} (hω : 0 < S.ℙ.w ω) (hr : ω ∈ S.reach h) :
    0 < S.ratio h n ω :=
  div_pos (S.pr_reach_pos n hω hr) (S.pr_reach_pos (n + 1) hω hr)

end PlaySpace

end

end Cleanroom.Udt.UdtInfluence101
