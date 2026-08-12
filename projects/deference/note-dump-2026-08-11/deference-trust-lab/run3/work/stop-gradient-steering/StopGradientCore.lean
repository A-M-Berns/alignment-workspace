/-
  StopGradientCore.lean — run3 TODO 3 `stop-gradient-steering`, part (A): the LEAN core.

  STANDALONE file (run3\GROUND-RULES.md §2): imports Mathlib only. Nothing is copied from
  LeanDeference — the model here is new to this TODO. The round-1 lab files
  `deference-trust-lab\lean\legitimacy.lean` / `legitimacy-corrigibility.lean` are OFF-LIMITS
  objects (defect-sign / comply-decline machinery with pointwise-overstatement hypotheses);
  none of their definitions or hypothesis shapes appears here. The target object of this file
  is different: the INCENTIVE DIFFERENCE of one fixed payoff functional under a target swap
  (raw feedback vs. §0.3-filtered feedback).

  MODEL (finite, exact rationals — a finite shadow of li-deference.md §0.3, NOT an LI theorem):

  * quote a ∈ [0,1] ⊂ ℚ                     — the AI's published estimate;
  * autonomous verdict Y0 = 1/4              — the human's opinion in the non-corrupted
                                               future; a CONSTANT of the model (independent
                                               of a: the "blind"/autonomy reading, v6 §6.5);
  * two corruption sub-channels A and B with weights cA a = a/2 and cB a = a/2 and
    manipulated contents MA a = 1, MB a = 1  — quoting high both PREDICTS high and PUSHES
                                               the human toward the sycophancy target 1;
                                               total corruption mass cA a + cB a = a;
  * realized feedback  Yraw a = (1 − cA a − cB a)·Y0 + cA a·MA a + cB a·MB a
                              = (1 − a)·(1/4) + a·1 ;
  * ONE payoff functional  pay target a = −(a − target a)²  — used verbatim for EVERY
    target below; only the target is swapped (this is the shadow-test obligation (c)).

  KERNEL-CHECKED CLAIMS (spec items (i)–(iv) of TODOS.md TODO 3, part A):

  (i)   RAW target Yraw: the manipulative quote a* = 1 is exactly self-confirming
        (Yraw 1 = 1, `apparent_accuracy`), carries a computed strictly positive payoff
        advantage 9/256 over the honest quote Y0 (`raw_advantage_value`,
        `raw_advantage_pos`), is globally optimal (`raw_manipulation_optimal`), and its
        legitimacy defect is γ = a* − Y0 = 3/4 (`legitimacy_defect`).
  (ii)  FILTERED target ("predict human opinion only through non-corrupted futures"):
        the filter keeps the channel WEIGHTS but replaces the CONTENT of every corrupt
        branch by the legitimate verdict. The stop-gradient identity
        (`stop_gradient_identity`) computes that the filtered target collapses to Y0 for
        every channel-weight pair — the weights cancel algebraically — hence the payoff
        under the filtered target is literally independent of the corruption channel
        (`filtered_payoff_channel_independent`), while the raw payoff is NOT
        (`raw_payoff_channel_dependent` — the non-vacuity contrast). Under the filtered
        target the honest quote is the UNIQUE optimum (`filtered_optimum_unique`).
  (iii) NEAR-MISS: the misspecified filter that classifies branch B as legitimate
        re-creates a strictly positive manipulation advantage 9/1024 at the self-confirming
        quote 2/5, with residual defect 3/20 (`mis_*`).
  (iv)  CORRUPTION DELETION TEST: with c ≡ 0 the raw advantage of a* provably vanishes —
        indeed flips strictly negative (−9/16) — and the honest quote becomes optimal
        (`deletion_*`). So the corruption channel is load-bearing, not a label.

  Prior art: the stop-gradient / non-performativity mechanism is KNOWN (Perdomo, Zrnic,
  Mendler-Dünner, Hardt, "Performative Prediction", ICML 2020; cited in v6 §6.5). This file
  is a kernel-checked instantiation in the legitimacy vocabulary, not a discovery of it.
-/
import Mathlib

namespace StopGradient

/-- Generic mixture verdict: legitimate (autonomous) verdict `y0`, two corruption
    sub-channels with weights `cA' a`, `cB' a` and manipulated contents `MA' a`, `MB' a`. -/
def verdict (y0 : ℚ) (cA' cB' MA' MB' : ℚ → ℚ) (a : ℚ) : ℚ :=
  (1 - cA' a - cB' a) * y0 + cA' a * MA' a + cB' a * MB' a

/-- THE payoff functional (negative squared error of the quote against the target).
    This single definition is used for every target below; only the target is swapped. -/
def pay (target : ℚ → ℚ) (a : ℚ) : ℚ := -(a - target a) ^ 2

/-! ### The concrete model instance -/

def Y0 : ℚ := 1/4
def cA (a : ℚ) : ℚ := a / 2
def cB (a : ℚ) : ℚ := a / 2
def MA (_ : ℚ) : ℚ := 1
def MB (_ : ℚ) : ℚ := 1

/-- The raw (realized-feedback) target. -/
def Yraw : ℚ → ℚ := verdict Y0 cA cB MA MB

/-- Hygiene: for a ∈ [0,1] the three mixture weights form a probability vector. -/
theorem weights_prob {a : ℚ} (h0 : 0 ≤ a) (h1 : a ≤ 1) :
    0 ≤ cA a ∧ 0 ≤ cB a ∧ 0 ≤ 1 - cA a - cB a ∧
      (1 - cA a - cB a) + (cA a + cB a) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [cA, cB] <;> linarith

/-! ### (i) the raw target rewards manipulation -/

/-- The manipulative quote. -/
def aStar : ℚ := 1

/-- Corruption is total at the manipulative quote (why it can self-confirm). -/
theorem corruption_total_at_aStar : cA aStar + cB aStar = 1 := by
  norm_num [cA, cB, aStar]

/-- (i)(a) self-confirmation: the manipulative quote is exactly confirmed by the
    realized feedback — perfect APPARENT accuracy. -/
theorem apparent_accuracy : Yraw aStar = aStar := by
  norm_num [Yraw, verdict, Y0, cA, cB, MA, MB, aStar]

/-- (i)(b) the honest quote is NOT confirmed under the raw channel: quoting the
    legitimate verdict still gets corrupted feedback 7/16 ≠ 1/4. -/
theorem honest_quote_corrupted : Yraw Y0 = 7/16 := by
  norm_num [Yraw, verdict, Y0, cA, cB, MA, MB]

/-- (i)(c) the computed strict raw manipulation advantage: exactly 9/256. -/
theorem raw_advantage_value : pay Yraw aStar - pay Yraw Y0 = 9/256 := by
  norm_num [pay, Yraw, verdict, Y0, cA, cB, MA, MB, aStar]

/-- (i)(c') …and it is strictly positive. -/
theorem raw_advantage_pos : pay Yraw Y0 < pay Yraw aStar := by
  norm_num [pay, Yraw, verdict, Y0, cA, cB, MA, MB, aStar]

/-- (i)(d) manipulation is even globally optimal under the raw target. -/
theorem raw_manipulation_optimal (a : ℚ) : pay Yraw a ≤ pay Yraw aStar := by
  have h1 : pay Yraw aStar = 0 := by
    norm_num [pay, Yraw, verdict, Y0, cA, cB, MA, MB, aStar]
  rw [h1]
  simp only [pay]
  linarith [sq_nonneg (a - Yraw a)]

/-- (i)(e) the legitimacy defect of the manipulative quote: γ = 3/4 > 0 explicit. -/
theorem legitimacy_defect : aStar - Y0 = 3/4 := by norm_num [aStar, Y0]

/-! ### (ii) the §0.3 filter and the stop-gradient identity -/

/-- The §0.3 filter: keep the model's channel WEIGHTS but replace the CONTENT of every
    corrupt branch by the legitimate verdict ("the AI should only be trying to imitate
    human opinion in non-corrupted futures", li-deference.md §0.3). -/
def filt (y0 : ℚ) (cA' cB' : ℚ → ℚ) : ℚ → ℚ :=
  verdict y0 cA' cB' (fun _ => y0) (fun _ => y0)

/-- The filtered target of the concrete model. -/
def Yfilt : ℚ → ℚ := filt Y0 cA cB

/-- (ii)(a) STOP-GRADIENT IDENTITY: for EVERY channel-weight pair the filtered target
    collapses to the autonomous verdict — the weights cancel algebraically. (The
    M-independence is by construction of the §0.3 operation itself; the c-independence
    is this computed cancellation.) -/
theorem stop_gradient_identity (y0 : ℚ) (cA' cB' : ℚ → ℚ) (a : ℚ) :
    filt y0 cA' cB' a = y0 := by
  simp only [filt, verdict]; ring

/-- (ii)(b) the payoff under the filtered target is literally independent of the
    corruption channel: any two models agreeing on the legitimate verdict give
    IDENTICAL filtered payoff functions, whatever their corruption channels. -/
theorem filtered_payoff_channel_independent (y0 : ℚ) (c1 c2 c1' c2' : ℚ → ℚ) :
    pay (filt y0 c1 c2) = pay (filt y0 c1' c2') := by
  funext a
  simp only [pay, stop_gradient_identity]

/-- Non-vacuity contrast for (ii)(b): the RAW payoff DOES distinguish corruption
    channels — same quote, same payoff functional, channel present vs. deleted. -/
theorem raw_payoff_channel_dependent :
    pay Yraw aStar ≠ pay (verdict Y0 (fun _ => 0) (fun _ => 0) MA MB) aStar := by
  norm_num [pay, Yraw, verdict, Y0, cA, cB, MA, MB, aStar]

/-- (ii)(c) under the filtered target the honest quote is the UNIQUE optimum:
    every other quote scores strictly worse. Same payoff functional as (i). -/
theorem filtered_optimum_unique (a : ℚ) (h : a ≠ Y0) :
    pay Yfilt a < pay Yfilt Y0 := by
  have ha : Yfilt a = Y0 := stop_gradient_identity Y0 cA cB a
  have hy : Yfilt Y0 = Y0 := stop_gradient_identity Y0 cA cB Y0
  have hne : a - Y0 ≠ 0 := sub_ne_zero.mpr h
  have hpos : 0 < (a - Y0) ^ 2 := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · nlinarith
    · nlinarith
  have h1 : pay Yfilt Y0 = 0 := by
    simp [pay, hy]
  have h2 : pay Yfilt a = -(a - Y0) ^ 2 := by
    simp [pay, ha]
  rw [h2, h1]
  linarith

/-! ### (iii) near-miss: a misspecified filter re-creates the manipulation advantage -/

/-- Misspecified filter: branch A's content correctly replaced by the legitimate
    verdict, branch B erroneously classified legitimate and kept raw. -/
def Ymis : ℚ → ℚ := verdict Y0 cA cB (fun _ => Y0) MB

/-- The self-confirming quote of the misspecified model. -/
def aMis : ℚ := 2/5

theorem mis_self_confirming : Ymis aMis = aMis := by
  norm_num [Ymis, verdict, Y0, cA, cB, MB, aMis]

/-- (iii) the misspecified filter re-creates a computed strictly positive
    manipulation advantage: exactly 9/1024. -/
theorem mis_advantage_value : pay Ymis aMis - pay Ymis Y0 = 9/1024 := by
  norm_num [pay, Ymis, verdict, Y0, cA, cB, MB, aMis]

theorem mis_advantage_pos : pay Ymis Y0 < pay Ymis aMis := by
  norm_num [pay, Ymis, verdict, Y0, cA, cB, MB, aMis]

/-- The misspecified optimum sits away from the honest quote: residual defect 3/20. -/
theorem mis_defect : aMis - Y0 = 3/20 := by norm_num [aMis, Y0]

/-! ### (iv) corruption deletion test: c ≡ 0 kills the raw advantage -/

/-- The model with the corruption channel deleted (both weights ≡ 0, contents kept). -/
def Ydel : ℚ → ℚ := verdict Y0 (fun _ => 0) (fun _ => 0) MA MB

/-- (iv)(a) with the channel deleted, (i)'s advantage provably vanishes — indeed
    flips strictly negative: exactly −9/16. -/
theorem deletion_kills_advantage : pay Ydel aStar - pay Ydel Y0 = -(9/16) := by
  norm_num [pay, Ydel, verdict, Y0, MA, MB, aStar]

theorem deletion_advantage_neg : pay Ydel aStar < pay Ydel Y0 := by
  norm_num [pay, Ydel, verdict, Y0, MA, MB, aStar]

/-- (iv)(b) …and the honest quote becomes (globally) optimal. -/
theorem deletion_honest_optimal (a : ℚ) : pay Ydel a ≤ pay Ydel Y0 := by
  have hYa : Ydel a = Y0 := by norm_num [Ydel, verdict, MA, MB]
  have hY0 : Ydel Y0 = Y0 := by norm_num [Ydel, verdict, MA, MB]
  have h0 : pay Ydel Y0 = 0 := by simp [pay, hY0]
  have h1 : pay Ydel a = -(a - Y0) ^ 2 := by simp [pay, hYa]
  rw [h1, h0]
  linarith [sq_nonneg (a - Y0)]

end StopGradient

#print axioms StopGradient.weights_prob
#print axioms StopGradient.apparent_accuracy
#print axioms StopGradient.honest_quote_corrupted
#print axioms StopGradient.raw_advantage_value
#print axioms StopGradient.raw_advantage_pos
#print axioms StopGradient.raw_manipulation_optimal
#print axioms StopGradient.legitimacy_defect
#print axioms StopGradient.stop_gradient_identity
#print axioms StopGradient.filtered_payoff_channel_independent
#print axioms StopGradient.raw_payoff_channel_dependent
#print axioms StopGradient.filtered_optimum_unique
#print axioms StopGradient.mis_self_confirming
#print axioms StopGradient.mis_advantage_value
#print axioms StopGradient.mis_advantage_pos
#print axioms StopGradient.mis_defect
#print axioms StopGradient.deletion_kills_advantage
#print axioms StopGradient.deletion_advantage_neg
#print axioms StopGradient.deletion_honest_optimal
