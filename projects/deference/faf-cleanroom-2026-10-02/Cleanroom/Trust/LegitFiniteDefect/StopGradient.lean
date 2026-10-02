import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The stop-gradient identity

Package `legit-finite-defect`, Target 8 (items 052, 053), re-found over `ℚ` with no frame. A
one-shot mean-field mixture: the realised feedback is `verdict y0 cA cB MA MB a`, the legitimate
verdict `y0` mixed with two corruption channels whose weights depend on the AI's quote `a`. One
payoff functional `pay target a = −(a − target a)²` is used verbatim for every target; only the
target is swapped. Under the raw target the manipulative quote is self-confirming and optimal;
under the §0.3-filtered target (corrupt branches' *contents* replaced by the legitimate verdict,
weights kept) the target collapses to `y0` for every channel — the **stop-gradient identity** —
so the payoff is literally channel-independent and the honest quote is the unique optimum.

Honest kinds: the identity is algebra (L); the content is the witnesses (N+) and the docstring's
caveat: **the filter is an oracle — given, not computed**; that the record cannot supply it is
Target 7's point. Prior art: Perdomo, Zrnic, Mendler-Dünner, Hardt, *Performative Prediction*
(ICML 2020) — this is a kernel-checked instantiation in the legitimacy vocabulary, not a discovery.
Round 3's self-reported numbers (`9/256`, `9/1024`, `3/4`, `3/20`, `−9/16`) are all re-derived here.
-/

namespace Cleanroom.Trust.LegitFiniteDefect.StopGradient

/-- The mixture verdict: legitimate verdict `y0`, two corruption sub-channels with weights
`cA' a`, `cB' a` and manipulated contents `MA' a`, `MB' a`.
Source: [[stop-gradient-steering]] §A.1; trust-lab-052
Kind: D
Fidelity: exact -/
def verdict (y0 : ℚ) (cA' cB' MA' MB' : ℚ → ℚ) (a : ℚ) : ℚ :=
  (1 - cA' a - cB' a) * y0 + cA' a * MA' a + cB' a * MB' a

/-- The one payoff functional: negative squared error of the quote against the target. Used for
every target below; only the target is swapped.
Source: [[stop-gradient-steering]] §A.1; trust-lab-052
Kind: D
Fidelity: exact -/
def pay (target : ℚ → ℚ) (a : ℚ) : ℚ := -(a - target a) ^ 2

/-- The concrete instance: `Y0 = 1/4`, `cA a = cB a = a/2`, `MA = MB = 1`.
Source: [[stop-gradient-steering]] §A.1
Kind: D
Fidelity: exact -/
def Y0 : ℚ := 1 / 4

/-- Channel `A` weight `a/2`.
Source: [[stop-gradient-steering]] §A.1
Kind: D
Fidelity: exact -/
def cA (a : ℚ) : ℚ := a / 2

/-- Channel `B` weight `a/2`.
Source: [[stop-gradient-steering]] §A.1
Kind: D
Fidelity: exact -/
def cB (a : ℚ) : ℚ := a / 2

/-- Manipulated content of channel `A`: the sycophancy target `1`.
Source: [[stop-gradient-steering]] §A.1
Kind: D
Fidelity: exact -/
def MA (_ : ℚ) : ℚ := 1

/-- Manipulated content of channel `B`: the sycophancy target `1`.
Source: [[stop-gradient-steering]] §A.1
Kind: D
Fidelity: exact -/
def MB (_ : ℚ) : ℚ := 1

/-- The raw (realised-feedback) target.
Source: [[stop-gradient-steering]] §A.1
Kind: D
Fidelity: exact -/
def Yraw : ℚ → ℚ := verdict Y0 cA cB MA MB

/-- For `a ∈ [0, 1]` the three mixture weights form a probability vector.
Source: [[stop-gradient-steering]] §A.2 (`weights_prob`)
Kind: L
Fidelity: exact -/
theorem weights_prob {a : ℚ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    0 ≤ cA a ∧ 0 ≤ cB a ∧ 0 ≤ 1 - cA a - cB a ∧ (1 - cA a - cB a) + (cA a + cB a) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [cA, cB] <;> linarith

/-- The manipulative quote `a* = 1`.
Source: [[stop-gradient-steering]] §A.2 (i)
Kind: D
Fidelity: exact -/
def aStar : ℚ := 1

/-- **Raw target rewards manipulation** (item 052 (i)): at `a* = 1` corruption is total and the
quote is self-confirming (`Yraw 1 = 1`); the honest quote is not confirmed (`Yraw Y0 = 7/16`);
the raw advantage of `a*` over `Y0` is exactly `9/256 > 0`; and `a*` is globally optimal.
Source: [[stop-gradient-steering]] §A.2 (i); trust-lab-052
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem raw_rewards_manipulation :
    cA aStar + cB aStar = 1 ∧ Yraw aStar = aStar ∧ Yraw Y0 = 7 / 16 ∧
      pay Yraw aStar - pay Yraw Y0 = 9 / 256 ∧ (∀ a, pay Yraw a ≤ pay Yraw aStar) ∧
      aStar - Y0 = 3 / 4 := by
  refine ⟨by norm_num [cA, cB, aStar], by norm_num [Yraw, verdict, Y0, cA, cB, MA, MB, aStar],
    by norm_num [Yraw, verdict, Y0, cA, cB, MA, MB],
    by norm_num [pay, Yraw, verdict, Y0, cA, cB, MA, MB, aStar], ?_, by norm_num [aStar, Y0]⟩
  intro a
  have h1 : pay Yraw aStar = 0 := by norm_num [pay, Yraw, verdict, Y0, cA, cB, MA, MB, aStar]
  rw [h1]
  simp only [pay]
  linarith [sq_nonneg (a - Yraw a)]

/-- The §0.3 filter: keep the channel *weights*, replace the *content* of every corrupt branch by
the legitimate verdict ("imitate human opinion only in non-corrupted futures").
Source: [[stop-gradient-steering]] §A.2 (ii); [[li-deference]] §0.3
Kind: D
Fidelity: exact -/
def filt (y0 : ℚ) (cA' cB' : ℚ → ℚ) : ℚ → ℚ := verdict y0 cA' cB' (fun _ => y0) (fun _ => y0)

/-- The filtered target of the concrete instance.
Source: [[stop-gradient-steering]] §A.2 (ii)
Kind: D
Fidelity: exact -/
def Yfilt : ℚ → ℚ := filt Y0 cA cB

/-- **The stop-gradient identity**: for every channel-weight pair the filtered target collapses to
the legitimate verdict — the weights cancel algebraically. (Algebra; the `M`-independence is by
construction of the §0.3 operation, the `c`-independence is this cancellation.)
Source: [[stop-gradient-steering]] §A.2 (ii)(a) (`stop_gradient_identity`); trust-lab-052
Kind: L
Fidelity: exact -/
theorem stop_gradient_identity (y0 : ℚ) (cA' cB' : ℚ → ℚ) (a : ℚ) :
    filt y0 cA' cB' a = y0 := by
  simp only [filt, verdict]; ring

/-- **Channel independence**: the payoff under the filtered target is identical for any two
channel-weight pairs — while the raw payoff does distinguish the channel present from deleted
(non-vacuity contrast).
Source: [[stop-gradient-steering]] §A.2 (ii)(b) (`filtered_payoff_channel_independent`,
`raw_payoff_channel_dependent`)
Kind: L
Fidelity: exact -/
theorem filtered_channel_independent :
    (∀ (y0 : ℚ) (c1 c2 c1' c2' : ℚ → ℚ), pay (filt y0 c1 c2) = pay (filt y0 c1' c2')) ∧
      pay Yraw aStar ≠ pay (verdict Y0 (fun _ => 0) (fun _ => 0) MA MB) aStar := by
  constructor
  · intro y0 c1 c2 c1' c2'
    funext a
    simp only [pay, stop_gradient_identity]
  · norm_num [pay, Yraw, verdict, Y0, cA, cB, MA, MB, aStar]

/-- **Under the filtered target the honest quote is the unique optimum**: every other quote scores
strictly worse, with the same payoff functional.
Source: [[stop-gradient-steering]] §A.2 (ii)(c) (`filtered_optimum_unique`); trust-lab-052
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem filtered_optimum_unique (a : ℚ) (h : a ≠ Y0) : pay Yfilt a < pay Yfilt Y0 := by
  have ha : Yfilt a = Y0 := stop_gradient_identity Y0 cA cB a
  have hy : Yfilt Y0 = Y0 := stop_gradient_identity Y0 cA cB Y0
  have hne : a - Y0 ≠ 0 := sub_ne_zero.mpr h
  have hpos : 0 < (a - Y0) ^ 2 := by positivity
  have h1 : pay Yfilt Y0 = 0 := by simp [pay, hy]
  have h2 : pay Yfilt a = -(a - Y0) ^ 2 := by simp [pay, ha]
  rw [h2, h1]
  linarith

/-- The misspecified filter: channel `A` correctly replaced, channel `B` erroneously classified
legitimate and kept raw.
Source: [[stop-gradient-steering]] §A.2 (iii); trust-lab-053
Kind: D
Fidelity: exact -/
def Ymis : ℚ → ℚ := verdict Y0 cA cB (fun _ => Y0) MB

/-- The self-confirming quote of the misspecified model.
Source: [[stop-gradient-steering]] §A.2 (iii)
Kind: D
Fidelity: exact -/
def aMis : ℚ := 2 / 5

/-- **Misspecified-filter near-miss** (item 053): classifying channel `B` as legitimate re-creates
a self-confirming quote `2/5` with advantage exactly `9/1024 > 0` and residual defect `3/20`.
Source: [[stop-gradient-steering]] §A.2 (iii) (`mis_*`); trust-lab-053
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem misspecified_filter :
    Ymis aMis = aMis ∧ pay Ymis aMis - pay Ymis Y0 = 9 / 1024 ∧ aMis - Y0 = 3 / 20 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [Ymis, verdict, Y0, cA, cB, MB, aMis, pay]

/-- The model with the corruption channel deleted (both weights `≡ 0`, contents kept).
Source: [[stop-gradient-steering]] §A.2 (iv); trust-lab-053
Kind: D
Fidelity: exact -/
def Ydel : ℚ → ℚ := verdict Y0 (fun _ => 0) (fun _ => 0) MA MB

/-- **Corruption deletion test** (item 053): with the channel deleted the raw advantage of `a*`
flips to exactly `−9/16` and the honest quote becomes globally optimal — the corruption channel is
load-bearing, not a label.
Source: [[stop-gradient-steering]] §A.2 (iv) (`deletion_*`); trust-lab-053
Kind: N+
Fidelity: exact
Hyps: (a) none -/
theorem deletion_test :
    pay Ydel aStar - pay Ydel Y0 = -(9 / 16) ∧ ∀ a, pay Ydel a ≤ pay Ydel Y0 := by
  refine ⟨by norm_num [pay, Ydel, verdict, Y0, MA, MB, aStar], ?_⟩
  intro a
  have hYa : Ydel a = Y0 := by norm_num [Ydel, verdict, MA, MB]
  have hY0 : Ydel Y0 = Y0 := by norm_num [Ydel, verdict, MA, MB]
  have h0 : pay Ydel Y0 = 0 := by simp [pay, hY0]
  have h1 : pay Ydel a = -(a - Y0) ^ 2 := by simp [pay, hYa]
  rw [h1, h0]
  linarith [sq_nonneg (a - Y0)]

end Cleanroom.Trust.LegitFiniteDefect.StopGradient
