import Cleanroom.Udt.UdtPolicyCalc
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# `Cleanroom.Udt.UdtInfluence101.Defs`: play spaces, atoms, influences, the averaged algorithm

Definitions of record for the `udt-influence-101` package ([[udt-influence-101-mandate]] §3, T1).
Sources: Diffractor's UDT1.01 Posts 6–8 (`references/udt101/06-basics-of-algorithm.md`,
`07-conservation-of-expected-gain.md`, `08-actual-algorithm.md`).

* `Alg`: a mixed algorithm reading the plannable history and the unplannable states along it.
* `PlaySpace`: a finite probability space `ℙ` over worlds `Ω` with observations, states, utility,
  and an **ε-play family** `law A h ε` (a signed weight function for every real `ε`; a genuine
  distribution for `ε ∈ [0,1]`, equal to `ℙ` at `ε = 0`).
* atoms `atom n ω` (the epistemic state at time `n`: the first `n` observations and the states up
  to time `n`), `nextObs n o`, `reach h`; conditionals with junk value `0`.
* the three influences `IP`, `IEo`, `IE` as `deriv … 0` of the ε-family; `SmoothLaw` and Post 6's
  `A1`.
* the averaged algorithm `avg A h n` (Post 6 `Ā_{h,n}`), and the predicates `A3`, `A4`, `A5`, `CEI`.

Design notes (all disclosed in docstrings):
* `law` returns a *signed* weight for `ε ∉ [0,1]`: Mathlib's `deriv` is two-sided, and the natural
  ε-family (a mixture `(1-ε)·B + ε·A`) extends polynomially to all real `ε`; its two-sided derivative
  at `0` is Diffractor's one-sided limit. Clamping `ε` to `[0,1]` would make every influence a junk
  value ([[STANDARDS]] §3), so this is the honest choice.
* Every conditional has junk value `0` off its support; every headline states where it is read.
-/

namespace Cleanroom.Udt.UdtInfluence101

noncomputable section

open Finset Cleanroom.Udt.UdtPolicyCalc Cleanroom.Udt.UdtPolicyCalc.Tree

/-- **Mixed algorithms of record** (Post 6 §1; bli-soto-b-2-021 Claim 5's object): at the plannable
history `m` (a node of depth `m.1`) with the `m.1 + 1` unplannable states received on the way to
`m` (Diffractor's `S̄_m = 𝕊_{m₁:₀} … 𝕊_{m₁:|m|}`), a distribution over actions. It reads the states
along its own prefix only — never future states, never other branches (Claim 5: an oracle-querying
control algorithm, queries `𝕊_c` for `c ⊑ m`). Complexity bounds are not modelled.
Source: `references/udt101/06-basics-of-algorithm.md` §1 (udt-rep-080); [[udt-influence-101-mandate]] §3, T12b
Kind: D
Fidelity: variant: no complexity bounds; states are an abstract finite alphabet `Ξ`
Hyps: n/a -/
abbrev Alg (O Act Ξ : Type) [Fintype Act] (N : ℕ) :=
  (m : Node O N) → (Fin (m.1.val + 1) → Ξ) → FinDist Act

variable {O Act Ξ : Type} [Fintype O] [DecidableEq O] [Fintype Act] [DecidableEq Act]
  [Fintype Ξ] [DecidableEq Ξ] {N : ℕ}

/-- The constant algorithm "play the mixed action `μ` everywhere" (Post 8's abbreviation `μ`).
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 (udt-rep-081)
Kind: D
Fidelity: exact
Hyps: n/a -/
def ofDist (μ : FinDist Act) : Alg O Act Ξ N := fun _ _ => μ

/-- The constant algorithm "play action `a` everywhere" (Post 8's abbreviation `a`).
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 (udt-rep-081)
Kind: D
Fidelity: exact
Hyps: n/a -/
def ofAct (a : Act) : Alg O Act Ξ N := ofDist (FinDist.delta a)

/-- The pointwise mixture `(1 - t)·μ + t·ν` of two finite distributions, for `t ∈ [0,1]`.
Source: none: infrastructure
Kind: D
Fidelity: n/a
Hyps: n/a -/
def FinDist.mixDist {X : Type} [Fintype X] (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (μ ν : FinDist X) :
    FinDist X where
  w x := (1 - t) * μ.w x + t * ν.w x
  nonneg x := by
    have := μ.nonneg x; have := ν.nonneg x
    have : 0 ≤ 1 - t := by linarith
    positivity
  sum_one := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, μ.sum_one, ν.sum_one]; ring

/-- **A play space** ([[udt-influence-101-mandate]] §3): a finite prior `ℙ` on worlds `Ω`, each world
carrying a completed observation history `obs`, a full sequence of `N + 1` unplannable states
`states`, and a utility `U`; plus the **ε-play family** `law A h ε`: the weight function of the
world when algorithm `A` is ε-played at the plannable history `h` (Post 6 "A is ε-played at h").
`law A h 0 = ℙ.w`; for `ε ∈ [0,1]` it is a probability distribution; outside `[0,1]` it is a signed
weight (the polynomial extension; see the module docstring). The abstract layer assumes nothing
about how `law` depends on `A`; the model of record (`ProfileModel`) constructs it.
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 1 (udt-rep-080); mandate §3
Kind: D
Fidelity: variant: Diffractor's epistemic states `𝕊_{h₁:ₙ}` are rendered as one prior `ℙ` on worlds,
conditioned on the time-`n` atom; ε-play is a parametrized family of weights on the same worlds
Hyps: n/a -/
structure PlaySpace (O Act Ξ : Type) [Fintype O] [Fintype Act] [Fintype Ξ] (N : ℕ)
    (Ω : Type) [Fintype Ω] where
  /-- The prior over worlds. -/
  ℙ : FinDist Ω
  /-- The completed plannable history of the world. -/
  obs : Ω → Leaf O N
  /-- The unplannable states received at times `0, …, N`. -/
  states : Ω → (Fin (N + 1) → Ξ)
  /-- The utility of the world. -/
  U : Ω → ℝ
  /-- The ε-play family: the weight of each world when `A` is ε-played at `h`. -/
  law : Alg O Act Ξ N → Node O N → ℝ → Ω → ℝ
  /-- At `ε = 0` nothing is played: the law is the prior. -/
  law_zero : ∀ A h, law A h 0 = ℙ.w
  /-- For `ε ∈ [0,1]` the ε-law is a genuine distribution (non-negative). -/
  law_nonneg : ∀ A h ε, 0 ≤ ε → ε ≤ 1 → ∀ ω, 0 ≤ law A h ε ω
  /-- The ε-law has total mass one for every real `ε` (polynomial extension of a distribution). -/
  law_sum : ∀ A h ε, ∑ ω, law A h ε ω = 1

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

namespace PlaySpace

variable (S : PlaySpace O Act Ξ N Ω)

/-- Two worlds share the **time-`n` epistemic state**: the same first `n` observations and the same
states at times `≤ n` (Diffractor's `h₁:ₙ` together with `𝕊_{h₁:₀} … 𝕊_{h₁:ₙ}`).
Source: `references/udt101/08-actual-algorithm.md` §3.1 (`S̄_h`); mandate §3 (the filtration)
Kind: D
Fidelity: exact
Hyps: n/a -/
def AtomEq (n : ℕ) (ω ω' : Ω) : Prop :=
  (∀ i : Fin N, i.val < n → S.obs ω i = S.obs ω' i) ∧
    (∀ i : Fin (N + 1), i.val ≤ n → S.states ω i = S.states ω' i)

instance (n : ℕ) (ω ω' : Ω) : Decidable (S.AtomEq n ω ω') := by
  unfold AtomEq; infer_instance

/-- The **time-`n` atom** of `ω`: the set of worlds sharing its time-`n` epistemic state. The
epistemic state `𝕊_{h₁:ₙ}` of the posts is `ℙ` conditioned on this atom.
Source: mandate §3 (the filtration by atoms)
Kind: D
Fidelity: exact
Hyps: n/a -/
def atom (n : ℕ) (ω : Ω) : Finset Ω := event (fun ω' => S.AtomEq n ω ω')

/-- The event "the observation at time `n` (the `(n+1)`-st, Post 6's `o`) is `o`"; empty if `n ≥ N`.
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 2 (the partition by the next observation)
Kind: D
Fidelity: exact
Hyps: n/a -/
def nextObs (n : ℕ) (o : O) : Finset Ω :=
  if hn : n < N then event (fun ω => S.obs ω ⟨n, hn⟩ = o) else ∅

/-- The event "the world reaches the plannable history `h`" (its observations extend `h`).
Source: `references/udt101/08-actual-algorithm.md` (`𝟙_h`, `ℙ_{h₁:ₙ}(h)`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def reach (h : Node O N) : Finset Ω := event (fun ω => LeafExt h (S.obs ω))

/-- The states received on the way to `h` in world `ω`: Diffractor's `S̄_h` (`|h| + 1` states).
Source: `references/udt101/08-actual-algorithm.md` §3.1
Kind: D
Fidelity: exact
Hyps: n/a -/
def statesAlong (ω : Ω) (h : Node O N) : Fin (h.1.val + 1) → Ξ :=
  fun i => S.states ω (Fin.castLE (by have := h.1.isLt; omega) i)

/-- `A(h, S̄_h)` in world `ω`: the action distribution the algorithm plays at `h` there.
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 (`A(h, S̄_h)`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def play (A : Alg O Act Ξ N) (h : Node O N) (ω : Ω) : FinDist Act := A h (S.statesAlong ω h)

/-- Conditional expectation of `f` under the weight `w` given the time-`n` atom of `ω` intersected
with `E`; junk value `0` when that event has mass `0` under `w`. Diffractor's `𝔼_{h₁:ₙ}[f | E]`.
Source: mandate §3 (`ℙ_n[f | E]`)
Kind: D
Fidelity: exact (junk `0` disclosed)
Hyps: n/a -/
def cexp (w : Ω → ℝ) (n : ℕ) (E : Finset Ω) (f : Ω → ℝ) (ω : Ω) : ℝ :=
  condExpJunk w f (S.atom n ω ∩ E) 0

/-- Probability of `F` under the weight `w` given the time-`n` atom of `ω`; junk `0` when the atom
has mass `0`. Diffractor's `ℙ_{h₁:ₙ}(F)`.
Source: mandate §3
Kind: D
Fidelity: exact (junk `0` disclosed)
Hyps: n/a -/
def pr (w : Ω → ℝ) (n : ℕ) (F : Finset Ω) (ω : Ω) : ℝ := condProbJunk w F (S.atom n ω) 0

/-- A function of worlds is **`𝔽_n`-measurable** when it factors through the time-`n` atom.
Source: mandate §3 (the filtration)
Kind: D
Fidelity: exact
Hyps: n/a -/
def MeasAt (n : ℕ) (g : Ω → ℝ) : Prop := ∀ ω ω', S.AtomEq n ω ω' → g ω = g ω'

/-- **Influence on probability** `𝕀^ℙ_{h₁:ₙ}(A, h, o)`: the derivative at `ε = 0` of
`ℙ_{h₁:ₙ}(o | A is ε-played at h)` in `ε`, where `o` is the observation at time `n` (the next one).
`deriv` is a junk value (`0`) where the derivative does not exist ([[STANDARDS]] §3); `SmoothLaw`
(or Post 6's `A1`) is what makes it honest, and every headline carries one of them.
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 1 (udt-rep-080)
Kind: D
Fidelity: exact: Diffractor's one-sided limit `lim_{ε→0} (1/ε)(ℙ(o | ε-play) − ℙ(o))` is the two-sided
derivative of the polynomially extended ε-family (module docstring)
Hyps: n/a -/
def IP (n : ℕ) (A : Alg O Act Ξ N) (h : Node O N) (o : O) (ω : Ω) : ℝ :=
  deriv (fun ε => S.pr (S.law A h ε) n (S.nextObs n o) ω) 0

/-- **Influence on conditional expected utility** `𝕀^𝔼_{h₁:ₙ}(A, h, o)`: the derivative at `ε = 0`
of `𝔼_{h₁:ₙ}[U | o ∧ A is ε-played at h]`. Junk conventions as for `IP`.
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 1 (udt-rep-080)
Kind: D
Fidelity: exact (see `IP`)
Hyps: n/a -/
def IEo (n : ℕ) (A : Alg O Act Ξ N) (h : Node O N) (o : O) (ω : Ω) : ℝ :=
  deriv (fun ε => S.cexp (S.law A h ε) n (S.nextObs n o) S.U ω) 0

/-- **Influence on expected utility** `𝕀^𝔼_{h₁:ₙ}(A, h)`: the derivative at `ε = 0` of
`𝔼_{h₁:ₙ}[U | A is ε-played at h]`. Junk conventions as for `IP`.
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 1 (udt-rep-080)
Kind: D
Fidelity: exact (see `IP`)
Hyps: n/a -/
def IE (n : ℕ) (A : Alg O Act Ξ N) (h : Node O N) (ω : Ω) : ℝ :=
  deriv (fun ε => S.cexp (S.law A h ε) n univ S.U ω) 0

/-- **Smoothness of ε-play**: every coordinate `ε ↦ law A h ε ω` is differentiable at `0`. In the
model of record every coordinate is a polynomial in `ε`, so this is a theorem there; in the abstract
layer it is the regularity hypothesis from which Post 6's Assumption 1 follows on the support
(`A1_of_smoothLaw`).
Source: mandate §3 (`A1` "is a theorem" in the model), T7
Kind: D
Fidelity: stronger: implies Post 6's A1 on the support, and is what the model delivers
Hyps: n/a -/
def SmoothLaw : Prop := ∀ (A : Alg O Act Ξ N) (h : Node O N) (ω : Ω),
  ∃ c, HasDerivAt (fun ε => S.law A h ε ω) c 0

/-- **Post 6's Assumption 1, on the support**: at every world of positive prior mass, the three
ε-families whose derivatives define `IP`, `IEo`, `IE` have derivatives at `0` (the second one on
observations of positive conditional probability, where its value at `0` is not junk).
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 1 (udt-rep-080)
Kind: D
Fidelity: weaker: restricted to the support (off it the junk value `0` at `ε = 0` can break the limit)
Hyps: n/a -/
def A1 : Prop := ∀ (n : ℕ) (A : Alg O Act Ξ N) (h : Node O N) (o : O) (ω : Ω), 0 < S.ℙ.w ω →
  (∃ c, HasDerivAt (fun ε => S.pr (S.law A h ε) n (S.nextObs n o) ω) c 0) ∧
  (0 < mass S.ℙ.w (S.atom n ω ∩ S.nextObs n o) →
    ∃ c, HasDerivAt (fun ε => S.cexp (S.law A h ε) n (S.nextObs n o) S.U ω) c 0) ∧
  (∃ c, HasDerivAt (fun ε => S.cexp (S.law A h ε) n univ S.U ω) c 0)

/-- Supporting lemma `condExpJunk_sum` (linearity of the junk conditional expectation over a finite
sum of integrands, on an event of positive mass).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: none -/
theorem _root_.Cleanroom.Udt.UdtPolicyCalc.condExpJunk_sum {X ι : Type} {w : X → ℝ} {E : Finset X}
    (h : 0 < mass w E) (s : Finset ι) (g : ι → X → ℝ) :
    ∑ i ∈ s, condExpJunk w (g i) E 0 = condExpJunk w (fun x => ∑ i ∈ s, g i x) E 0 := by
  simp only [condExpJunk_of_pos h, div_eq_mul_inv]
  rw [← Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]

/-- The event over which the averaged algorithm averages: worlds reaching `h` whose states at times
`≤ n` agree with the given state sequence `s` along `h`. For `ω` reaching `h` and `n ≤ |h|` this is
`atom n ω ∩ reach h` when `s = S̄_h(ω)` (`avgEvent_eq`).
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 3 (`Ā_{h,n}`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def avgEvent (h : Node O N) (n : ℕ) (s : Fin (h.1.val + 1) → Ξ) : Finset Ω :=
  event (fun ω' => ∀ i : Fin (N + 1), i.val ≤ n → ∀ hi : i.val < h.1.val + 1,
    S.states ω' i = s ⟨i.val, hi⟩) ∩ S.reach h

/-- The action distribution of the averaged algorithm at `h` with states `s`: play `a` with
probability `ℙ_{h₁:ₙ}(A(h, S̄_h) = a | h)`, the conditional expectation of `A(h, S̄_h)(a)` over
`avgEvent h n s`. **Junk**: when that event is null the conditional is undefined and we return
`A h s` itself (disclosed; every headline reads it on positive events).
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 3 (udt-rep-2-002(b))
Kind: D
Fidelity: exact on positive events; junk `A h s` on null ones
Hyps: n/a -/
def avgDist (A : Alg O Act Ξ N) (h : Node O N) (n : ℕ) (s : Fin (h.1.val + 1) → Ξ) :
    FinDist Act :=
  if hE : mass S.ℙ.w (S.avgEvent h n s) = 0 then A h s else
  { w := fun a => condExpJunk S.ℙ.w (fun ω' => (S.play A h ω').w a) (S.avgEvent h n s) 0
    nonneg := fun a => by
      have hpos : 0 < mass S.ℙ.w (S.avgEvent h n s) :=
        lt_of_le_of_ne (mass_nonneg S.ℙ.nonneg _) (Ne.symm hE)
      exact le_condExpJunk_of_le S.ℙ.nonneg hpos fun ω' _ => (S.play A h ω').nonneg a
    sum_one := by
      have hpos : 0 < mass S.ℙ.w (S.avgEvent h n s) :=
        lt_of_le_of_ne (mass_nonneg S.ℙ.nonneg _) (Ne.symm hE)
      rw [condExpJunk_sum hpos]
      exact condExpJunk_const_on (fun ω' _ => (S.play A h ω').sum_one) hpos }

/-- **The averaged algorithm `Ā_{h,n}`** (Post 6 Assumption 3): at `h` it plays `avgDist A h n`,
"randomize according to how time-`n`-you thought `A` would behave at `h`"; elsewhere it is `A`.
It is `𝔽_n`-measurable at `h` (`avg_measAt`), `avg (ofDist μ) h n = ofDist μ` (`avg_ofDist`), and
the clipping identity `avg (avg A h n) h (n+1) = avg A h n` holds (`avg_avg`).
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 3 (udt-rep-2-002(b)); Post 7 §2.9
Kind: D
Fidelity: exact
Hyps: n/a -/
def avg (A : Alg O Act Ξ N) (h : Node O N) (n : ℕ) : Alg O Act Ξ N :=
  fun m s => if hm : m = h then
    S.avgDist A h n (fun i => s ⟨i.val, by rw [hm]; exact i.isLt⟩) else A m s

/-- `A`'s action at `h` is constant on the time-`n` atom of `ω` ("a time-`n` precommitment").
Source: none: infrastructure for `A5`
Kind: D
Fidelity: n/a
Hyps: n/a -/
def ConstOnAtom (n : ℕ) (A : Alg O Act Ξ N) (h : Node O N) (ω : Ω) : Prop :=
  ∀ ω' ∈ S.atom n ω, S.play A h ω' = S.play A h ω

/-- The observations of `ω` agree with `h` up to time `n`: `ω`'s time-`n` epistemic state is one
"received at `h₁:ₙ`" (the posts quantify their assumptions over these).
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 1 ("epistemic state 𝕊_{h₁:ₙ} received at h₁:ₙ")
Kind: D
Fidelity: exact
Hyps: n/a -/
def Along (h : Node O N) (n : ℕ) (hn : n ≤ h.1.val) (ω : Ω) : Prop :=
  ∀ i : Fin N, (hi : i.val < n) → S.obs ω i = h.2 ⟨i.val, lt_of_lt_of_le hi hn⟩

/-- **Post 6 Assumption 3 ("only average behaviour matters") at `h`**, stated exactly as the post
does, over the epistemic states along `h` (worlds of positive prior mass reaching `h`): for every
`n ≤ |h|`, algorithm `A` and observation `o`, the influence on the probability of `o` of `A` equals
that of its average `Ā_{h,n}`; and the influence on expected utility conditional on `o` equals that
of the average **whenever `o ≠ h_{n+1}`** (the escape clause; vacuous at `n = |h|`).
Source: `references/udt101/06-basics-of-algorithm.md` Assumption 3 (udt-rep-080, 086)
Kind: D
Fidelity: exact (restricted to positive-mass worlds along `h`)
Hyps: n/a -/
def A3 (h : Node O N) : Prop :=
  ∀ (n : ℕ), n ≤ h.1.val → ∀ (A : Alg O Act Ξ N) (ω : Ω), 0 < S.ℙ.w ω → ω ∈ S.reach h →
    (∀ o, S.IP n A h o ω = S.IP n (S.avg A h n) h o ω) ∧
    (∀ o, (∀ hn : n < h.1.val, o ≠ h.2 ⟨n, hn⟩) → S.IEo n A h o ω = S.IEo n (S.avg A h n) h o ω)

/-- **Post 7 Assumption 4 (Conservation of Expected Gain) at `h`**, exactly as the post states it,
over the epistemic states along `h`: for `n < |h|`, the time-`n` gap between `A` and its average
`Ā_{h,n}` in the influence on expected utility down the `h_{n+1}` branch equals the time-`n`
conditional expectation, given `h_{n+1}`, of the time-`(n+1)` gap (with the *same* `Ā_{h,n}`).
Source: `references/udt101/07-conservation-of-expected-gain.md` Assumption 4 (udt-rep-085)
Kind: D
Fidelity: exact (restricted to positive-mass worlds along `h`)
Hyps: n/a -/
def A4 (h : Node O N) : Prop :=
  ∀ (n : ℕ) (hn : n < h.1.val) (A : Alg O Act Ξ N) (ω : Ω), 0 < S.ℙ.w ω → ω ∈ S.reach h →
    S.IEo n A h (h.2 ⟨n, hn⟩) ω - S.IEo n (S.avg A h n) h (h.2 ⟨n, hn⟩) ω =
      S.cexp S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩))
        (fun ω' => S.IE (n + 1) A h ω' - S.IE (n + 1) (S.avg A h n) h ω') ω

/-- **Post 8 Assumption 5 (affineness of influence) at `h`, in the form Post 8's proofs use it**:
for every time-`n` precommitment at `h` — an algorithm `A` whose action at `h` is constant on the
time-`n` atom (`ConstOnAtom`; Diffractor's "μ : ΔA" seen from time `n`, and in particular his
`Ā_{h,n}` and every constant algorithm `ofDist μ`) — the influences of `A` are the `A(h, S̄_h)`-average
of the influences of the pure actions. Post 8 states it for constant algorithms only (`A5_ofDist`
recovers that statement) but applies it to `Ā_{h,n}` in the proof of Theorem 1 ("Use affineness of
influence", `E_{a∼Ā_{h,n}}`); the extension is exactly what that step needs
([[udt-influence-101-findings]]).
Source: `references/udt101/08-actual-algorithm.md` Assumption 5 and the proof of Theorem 1 (udt-rep-081, 082)
Kind: D
Fidelity: stronger: Post 8's A5 is the special case of constant algorithms; the extension to
time-`n` precommitments is the form the Theorem 1 proof uses; quantified over the epistemic states
along `h` (`Along`), as the posts do
Hyps: n/a -/
def A5 (h : Node O N) : Prop :=
  ∀ (n : ℕ) (hn : n ≤ h.1.val) (A : Alg O Act Ξ N) (ω : Ω), 0 < S.ℙ.w ω → S.Along h n hn ω →
    S.ConstOnAtom n A h ω →
    ∀ o, S.IP n A h o ω = ∑ a, (S.play A h ω).w a * S.IP n (ofAct a) h o ω ∧
      S.IEo n A h o ω = ∑ a, (S.play A h ω).w a * S.IEo n (ofAct a) h o ω

/-- **Conservation of Expected Influence** (Post 7 §2.1, the "dream scenario" that fails) at
`(n, A, h, ω)`: the time-`n` influence on expected utility down the `h_{n+1}` branch equals the
time-`n` conditional expectation, given `h_{n+1}`, of the time-`(n+1)` influence.
Source: `references/udt101/07-conservation-of-expected-gain.md` §2.1 (udt-rep-085)
Kind: D
Fidelity: exact
Hyps: n/a -/
def CEI (n : ℕ) (A : Alg O Act Ξ N) (h : Node O N) (ω : Ω) : Prop :=
  ∀ hn : n < h.1.val,
    S.IEo n A h (h.2 ⟨n, hn⟩) ω =
      S.cexp S.ℙ.w n (S.nextObs n (h.2 ⟨n, hn⟩)) (fun ω' => S.IE (n + 1) A h ω') ω

/-- Every next observation has positive conditional probability at the time-`n` atom of `ω`.
Lemma 1 (Post 6) divides by `ℙ_{h₁:ₙ}(o)`; this is the positivity it silently assumes.
Source: `references/udt101/06-basics-of-algorithm.md` Lemma 1 (the division by `ℙ_{h₁:ₙ}(o)`); mandate T2
Kind: D
Fidelity: exact
Hyps: n/a -/
def PosObs (n : ℕ) (ω : Ω) : Prop := ∀ o, 0 < mass S.ℙ.w (S.atom n ω ∩ S.nextObs n o)

/-- Full support of the next observation at every positive atom before the horizon.
Source: mandate T2/T4 (the positivity "everywhere the source divides")
Kind: D
Fidelity: exact
Hyps: n/a -/
def AllPosObs : Prop := ∀ n, n < N → ∀ ω, 0 < S.ℙ.w ω → S.PosObs n ω

/-- Every positive atom at a time `n ≤ |h|` whose observations so far agree with `h` can still
reach `h` with positive probability. Post 8's proof of Theorem 1 divides by `ℙ_{h₁:ₙ₊₁}(h)` at every
time-`(n+1)` atom below `h_{n+1}`; this is the positivity it silently assumes
([[udt-influence-101-findings]]).
Source: `references/udt101/08-actual-algorithm.md` Theorem 1 proof ("unpack the conditional expectation"); mandate T4
Kind: D
Fidelity: exact
Hyps: n/a -/
def ReachPos (h : Node O N) : Prop :=
  ∀ (n : ℕ) (hn : n ≤ h.1.val) (ω : Ω), 0 < S.ℙ.w ω → S.Along h n hn ω →
    0 < mass S.ℙ.w (S.atom n ω ∩ S.reach h)

end PlaySpace

end

end Cleanroom.Udt.UdtInfluence101
