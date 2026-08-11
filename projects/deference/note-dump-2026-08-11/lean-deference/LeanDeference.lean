/-
  Kernel-checked core of the LI Value proof (deference-in-logical-induction.md, sec. 3).

  TWO parts:
  * `Deference`       — the finite EXACT algebraic skeleton (identity + CM ⇒ Value),
                        defects taken as exactly 0.
  * `DeferenceAsymp`  — the ACTUAL sec. 3 argument: the `≂ₙ`/`≳ₙ` calculus is modeled as
                        real-sequence asymptotics, the five Logical-Induction results are
                        taken as hypotheses (as agreed: we trust the LI paper, we don't
                        re-prove it), and `Value` is derived:  E_now(Ŝ) ≳ₙ E_now(Oⁱ).

  NOT modeled (the agreed boundary): logically uncertain variables, the market/trader
  construction, or proofs of thm:ccee/cee/loe/expprovind themselves.  Those enter only as
  the named hypotheses below.
-/
import Mathlib

open Finset Filter Topology

namespace Deference

/-- **Keystone identity.**  For *every* finite frame, menu and weight family,
    `gap i = D_CM + D_UM i + soft i`.  Pure linearity — no hypothesis on the frame. -/
theorem decomposition
    {K : Type*} [CommRing K] {W J : Type*} [Fintype W] [Fintype J]
    (π : W → K) (P : W → W → K) (O : J → W → K) (α : J → W → K) (i : J) :
    (∑ w, π w * (∑ j, α j w * O j w)) - (∑ w, π w * O i w)
      =
      (∑ w, π w * (∑ j, α j w * (O j w - ∑ v, P w v * O j v)))
    + ((∑ w, π w * (∑ v, P w v * O i v)) - (∑ w, π w * O i w))
    + (∑ w, π w * ((∑ j, α j w * (∑ v, P w v * O j v)) - (∑ v, P w v * O i v))) := by
  -- distribute every subtraction through the sums; the goal becomes
  --   A - B = (A - C) + (D - B) + (C - D),  closed by `ring`.
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

/-- **Value from vanishing defects** (exact finite version). -/
theorem value_of_defects
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {W J : Type*} [Fintype W] [Fintype J]
    (π : W → K) (P : W → W → K) (O : J → W → K) (α : J → W → K) (i : J)
    (hCM : (∑ w, π w * (∑ j, α j w * (O j w - ∑ v, P w v * O j v))) = 0)
    (hUM : (∑ w, π w * (∑ v, P w v * O i v)) - (∑ w, π w * O i w) = 0)
    (hsoft : 0 ≤ ∑ w, π w * ((∑ j, α j w * (∑ v, P w v * O j v)) - (∑ v, P w v * O i v))) :
    0 ≤ (∑ w, π w * (∑ j, α j w * O j w)) - (∑ w, π w * O i w) := by
  have h := decomposition π P O α i
  rw [h, hCM, hUM]; simpa using hsoft

/-- The soft term is nonnegative for argmax selection (`∑ⱼ αⱼ mⱼ = maxⱼ mⱼ ≥ mᵢ`). -/
theorem soft_nonneg
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {W J : Type*} [Fintype W] [Fintype J]
    (π : W → K) (P : W → W → K) (O : J → W → K) (α : J → W → K) (i : J)
    (hπ : ∀ w, 0 ≤ π w)
    (hmax : ∀ w, (∑ v, P w v * O i v) ≤ ∑ j, α j w * (∑ v, P w v * O j v)) :
    0 ≤ ∑ w, π w * ((∑ j, α j w * (∑ v, P w v * O j v)) - (∑ v, P w v * O i v)) := by
  apply Finset.sum_nonneg
  intro w _
  exact mul_nonneg (hπ w) (by linarith [hmax w])

/-- **Conditional martingale ⇒ Value** (exact finite version). -/
theorem value_of_CM
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {W J : Type*} [Fintype W] [Fintype J]
    (π : W → K) (P : W → W → K) (O : J → W → K) (α : J → W → K) (i : J)
    (hπ : ∀ w, 0 ≤ π w)
    (hCM : (∑ w, π w * (∑ j, α j w * (O j w - ∑ v, P w v * O j v))) = 0)
    (hUM : (∑ w, π w * (∑ v, P w v * O i v)) - (∑ w, π w * O i w) = 0)
    (hmax : ∀ w, (∑ v, P w v * O i v) ≤ ∑ j, α j w * (∑ v, P w v * O j v)) :
    0 ≤ (∑ w, π w * (∑ j, α j w * O j w)) - (∑ w, π w * O i w) :=
  value_of_defects π P O α i hCM hUM (soft_nonneg π P O α i hπ hmax)

end Deference

/- ======================================================================================
   The actual sec. 3 argument, modulo the Logical-Induction results.
   ====================================================================================== -/
namespace DeferenceAsymp

/-- LI's `a ≂ₙ b`: present-expectation sequences agree up to vanishing error. -/
def Approx (a b : ℕ → ℝ) : Prop := Tendsto (fun n => a n - b n) atTop (𝓝 0)

/-- `a ≲ b` :  `aₙ ≤ bₙ + o(1)`.  (So LI's `b ≳ₙ a` is `AsympLE a b`.) -/
def AsympLE (a b : ℕ → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, a n ≤ b n + ε

namespace Approx
variable {a b c : ℕ → ℝ}

theorem rfl' (a : ℕ → ℝ) : Approx a a := by
  simp only [Approx, sub_self]; exact tendsto_const_nhds

theorem symm (h : Approx a b) : Approx b a := by
  simpa [Approx, neg_sub] using h.neg

theorem trans (h1 : Approx a b) (h2 : Approx b c) : Approx a c := by
  simpa [Approx, sub_add_sub_cancel] using h1.add h2

/-- `≂ₙ` refines `≲`. -/
theorem asympLE (h : Approx a b) : AsympLE a b := by
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h ε hε
  filter_upwards [eventually_atTop.2 ⟨N, fun n hn => hN n hn⟩] with n hn
  have : |a n - b n| < ε := by simpa [Real.dist_eq] using hn
  have := (abs_lt.1 this).2
  linarith
end Approx

namespace AsympLE
variable {a b c : ℕ → ℝ}

theorem trans (h1 : AsympLE a b) (h2 : AsympLE b c) : AsympLE a c := by
  intro ε hε
  filter_upwards [h1 (ε/2) (by linarith), h2 (ε/2) (by linarith)] with n hn1 hn2
  linarith

/-- `a ≲ b` then `b ≂ₙ c`  gives  `a ≲ c`. -/
theorem trans_approx (h1 : AsympLE a b) (h2 : Approx b c) : AsympLE a c :=
  h1.trans h2.asympLE
end AsympLE

/-- Finite sums respect `≂ₙ` (this packages thm:loe's additivity over the menu). -/
theorem approx_sum {J : Type*} [Fintype J] {f g : J → ℕ → ℝ}
    (h : ∀ j, Approx (f j) (g j)) :
    Approx (fun n => ∑ j, f j n) (fun n => ∑ j, g j n) := by
  have key : Tendsto (fun n => ∑ j, (f j n - g j n)) atTop (𝓝 (∑ _j : J, (0 : ℝ))) :=
    tendsto_finset_sum _ (fun j _ => h j)
  simpa [Approx, Finset.sum_sub_distrib] using key

/--
  **Value, modulo the Logical-Induction coherence theorems.**

  All sequences are present-day expectations `E_now(·)` (indexed by day `n`); families are
  indexed by the finite menu `J`, with `i : J` the chosen target option:

  * `ES   = E_now(Ŝ)`            present value of the future-self-selected bet `Ŝ = ∑ⱼ αⱼ Oⱼ`
  * `Eo j = E_now(Oⱼ)`           present value of option `j`        (target is `Eo i`)
  * `Ee j = E_now(E_later Oⱼ)`   present value of the future estimate of option `j`
  * `a j  = E_now(αⱼ · Oⱼ)`,  `b j = E_now(αⱼ · E_later Oⱼ)`
  * `c    = E_now(∑ⱼ αⱼ · E_later Oⱼ)`,  `δ` the softmax gap (`→ 0`)

  Hypotheses = the LI results (trusted, not re-proved):
  * `hAdd1`,`hAdd2`  thm:loe  (linearity of `E_now` over the finite menu)
  * `hCcee`          thm:ccee (No Expected Net Update under Conditionals), one per option
  * `hCee`           thm:cee  (No Expected Net Update), one per option
  * `hδ`,`hSoft`     thm:expprovind (monotonicity) applied to the softmax bound
                     `∑ⱼ αⱼ·E_later Oⱼ ≥ E_later Oⁱ − δₙ`, with `δₙ → 0`

  Conclusion: `E_now(Oⁱ) ≲ E_now(Ŝ)`, i.e. `E_now(Ŝ) ≳ₙ E_now(Oⁱ)` — **Value**.
-/
theorem value_asymptotic
    {J : Type*} [Fintype J] (i : J)
    (ES c δ : ℕ → ℝ) (a b Eo Ee : J → ℕ → ℝ)
    (hAdd1 : Approx ES (fun n => ∑ j, a j n))
    (hCcee : ∀ j, Approx (a j) (b j))
    (hAdd2 : Approx (fun n => ∑ j, b j n) c)
    (hCee  : ∀ j, Approx (Ee j) (Eo j))
    (hδ    : Tendsto δ atTop (𝓝 0))
    (hSoft : ∀ᶠ n in atTop, Ee i n ≤ c n + δ n) :
    AsympLE (Eo i) ES := by
  -- E_now(Ŝ)  ≂ₙ  ∑ⱼ a j  ≂ₙ  ∑ⱼ b j  ≂ₙ  c
  have hES_c : Approx ES c := hAdd1.trans ((approx_sum hCcee).trans hAdd2)
  -- E_now(E_later Oⁱ)  ≲  c     (softmax bound, with δ → 0)
  have hEd_c : AsympLE (Ee i) c := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hδ ε hε
    filter_upwards [hSoft, eventually_atTop.2 ⟨N, fun n hn => hN n hn⟩] with n hn1 hn2
    have : |δ n| < ε := by simpa [Real.dist_eq] using hn2
    have := (abs_lt.1 this).2
    linarith
  -- chain:  Eo i ≂ₙ Ee i ≲ c ≂ₙ ES  ⟹  Eo i ≲ ES
  exact (((hCee i).symm).asympLE.trans hEd_c).trans_approx hES_c.symm

end DeferenceAsymp

/- ======================================================================================
   Follow-ups: (a) the softmax bound that backs `hSoft`, now PROVED (not assumed);
               (b) the finite-collapse core of §5.2.
   ====================================================================================== -/
namespace DeferenceExtra
open Finset

/-- **(a) Softmax bound.**  The temperature-`δ` softmax-weighted mean of `m` is within
    `(card J)·δ` of the maximum, hence `≥ m i − (card J)·δ` for every option `i`.
    (The note quotes the tight entropy constant `δ·log(card J)`; this proves the cruder
    `(card J)·δ`, which is all the `δ→0` argument needs — and removes the softmax bound
    from the *assumed* facts.)  Uses only `Real.add_one_le_exp`. -/
theorem softmax_lower_bound {J : Type*} [Fintype J] [Nonempty J]
    (m : J → ℝ) (δ : ℝ) (hδ : 0 < δ) (i : J) :
    m i - (Fintype.card J : ℝ) * δ
      ≤ ∑ j, (Real.exp (m j / δ) / ∑ k, Real.exp (m k / δ)) * m j := by
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  set Z : ℝ := ∑ k, Real.exp (m k / δ) with hZdef
  have hZpos : 0 < Z := Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨i, Finset.mem_univ i⟩
  obtain ⟨j0, hj0⟩ := Finite.exists_max m
  set M : ℝ := m j0 with hMdef
  -- weights sum to 1
  have hsum1 : (∑ j, Real.exp (m j / δ) / Z) = 1 := by
    rw [← Finset.sum_div, ← hZdef]; exact div_self (ne_of_gt hZpos)
  -- per-option bound:  wⱼ·(M − mⱼ) ≤ δ
  have hterm : ∀ j, (Real.exp (m j / δ) / Z) * (M - m j) ≤ δ := by
    intro j
    have hd : 0 ≤ M - m j := sub_nonneg.2 (hj0 j)
    have hexpM : Real.exp (M / δ) ≤ Z :=
      Finset.single_le_sum (f := fun k => Real.exp (m k / δ))
        (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ j0)
    have hwle : Real.exp (m j / δ) / Z ≤ Real.exp (-((M - m j) / δ)) := by
      have h1 : Real.exp (m j / δ) / Z ≤ Real.exp (m j / δ) / Real.exp (M / δ) := by
        gcongr
      have h2 : Real.exp (m j / δ) / Real.exp (M / δ) = Real.exp (-((M - m j) / δ)) := by
        rw [← Real.exp_sub]; congr 1; ring
      rwa [h2] at h1
    calc (Real.exp (m j / δ) / Z) * (M - m j)
        ≤ Real.exp (-((M - m j) / δ)) * (M - m j) := mul_le_mul_of_nonneg_right hwle hd
      _ ≤ δ := by
          have hu : ((M - m j) / δ) * Real.exp (-((M - m j) / δ)) ≤ 1 := by
            rw [Real.exp_neg, ← div_eq_mul_inv]
            exact (div_le_one (Real.exp_pos _)).2
              (by linarith [Real.add_one_le_exp ((M - m j) / δ)])
          have heq : Real.exp (-((M - m j) / δ)) * (M - m j)
                   = δ * (((M - m j) / δ) * Real.exp (-((M - m j) / δ))) := by
            field_simp
          rw [heq]; nlinarith [mul_le_mul_of_nonneg_left hu hδ.le]
  -- assemble:  ∑ wⱼ mⱼ = M·1 − ∑ wⱼ(M − mⱼ) ≥ M − card·δ ≥ mᵢ − card·δ
  have hexpand : (∑ j, (Real.exp (m j / δ) / Z) * m j)
      = M * (∑ j, Real.exp (m j / δ) / Z) - ∑ j, (Real.exp (m j / δ) / Z) * (M - m j) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have hbound : (∑ j, (Real.exp (m j / δ) / Z) * (M - m j)) ≤ (Fintype.card J : ℝ) * δ := by
    calc (∑ j, (Real.exp (m j / δ) / Z) * (M - m j))
        ≤ ∑ _j : J, δ := Finset.sum_le_sum (fun j _ => hterm j)
      _ = (Fintype.card J : ℝ) * δ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [hsum1, mul_one] at hexpand
  have hMi : m i ≤ M := hj0 i
  linarith [hexpand, hbound, hMi]

section
open scoped Classical

/-- **(b) Finite collapse (core of §5.2).**  If the conditional-martingale identity
    `E_w(X) = E_π(X | fiber w)` holds at a world `w` (with `fiber w := {v | P v = P w}`),
    then the expert is **immodest** there: `P_w(fiber w) = 1`.  This is exactly the note's
    one-line argument — instantiate the identity at the fiber's own indicator.

    (What is NOT formalized here: the soft-⇒-hard reduction that, on a *finite* frame, forces
    this hypothesis — the "no spectral gap" step. That is the part needing an infinite frame,
    and is left as the prose argument of §5.2.) -/
theorem CM_implies_immodest {W : Type*} [Fintype W]
    (π : W → ℝ) (P : W → W → ℝ) (hπ : ∀ v, 0 ≤ π v) (w : W) (hw : 0 < π w)
    (hCM : ∀ X : W → ℝ,
        (∑ v, P w v * X v)
        = (∑ v, π v * (if P v = P w then (1 : ℝ) else 0) * X v)
          / (∑ v, π v * (if P v = P w then (1 : ℝ) else 0))) :
    (∑ v, P w v * (if P v = P w then (1 : ℝ) else 0)) = 1 := by
  -- the fiber's π-mass is positive (w sees itself)
  have hden : 0 < ∑ v, π v * (if P v = P w then (1 : ℝ) else 0) := by
    have hle : π w * (if P w = P w then (1 : ℝ) else 0)
            ≤ ∑ v, π v * (if P v = P w then (1 : ℝ) else 0) :=
      Finset.single_le_sum (f := fun v => π v * (if P v = P w then (1 : ℝ) else 0))
        (fun v _ => mul_nonneg (hπ v) (by by_cases h : P v = P w <;> simp [h]))
        (Finset.mem_univ w)
    rw [if_pos rfl, mul_one] at hle
    linarith
  -- instantiate the identity at the fiber indicator; the indicator is idempotent
  have key := hCM (fun v => if P v = P w then (1 : ℝ) else 0)
  simp only [] at key
  have hnum : (∑ v, π v * (if P v = P w then (1 : ℝ) else 0) * (if P v = P w then (1 : ℝ) else 0))
            = ∑ v, π v * (if P v = P w then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl (fun v _ => by by_cases h : P v = P w <;> simp [h])
  rw [hnum, div_self (ne_of_gt hden)] at key
  exact key

end

end DeferenceExtra

-- Axiom audit: each must depend ONLY on [propext, Classical.choice, Quot.sound]
-- (the standard Mathlib axioms) and NOT on `sorryAx`.
#print axioms Deference.decomposition
#print axioms Deference.value_of_CM
#print axioms DeferenceAsymp.value_asymptotic
#print axioms DeferenceExtra.softmax_lower_bound
#print axioms DeferenceExtra.CM_implies_immodest


/- ======================================================================================
   ARGMAX Value (added): the hard-argmax strategy `Ŝ = O^{jstar}` satisfies Value
     (1) directly via the UNCONDITIONAL martingale (no ccee, no softmax gap), and
     (2) as the softmax limit, gated on the L¹ weight distance → 0 (the near-tie mass).
   Same methodology as above: exact finite backbones are PROVED; the LI coherence results
   enter only as named asymptotic hypotheses (`Approx`/`AsympLE` from `DeferenceAsymp`).
   ====================================================================================== -/
namespace DeferenceArgmax
open Finset
open DeferenceAsymp

/-- **(1a) Argmax Value — exact finite backbone.**
    `m j w := ∑ v, P w v * O j v` = the future self's value of option `j` at world `w`;
    `jstar w` is ANY maximizer (`hstar`), so the statement is tie-break-free.  Given the
    unconditional-martingale identities for the selected strategy `Ŝ w = O (jstar w) w`
    (`hUM_S`) and for `Oⁱ` (`hUM_i`):  `E_π(Oⁱ) ≤ E_π(Ŝ)`. -/
theorem value_of_argmax
    {W J : Type*} [Fintype W] [Fintype J]
    (π : W → ℝ) (P : W → W → ℝ) (O : J → W → ℝ) (i : J) (jstar : W → J)
    (hπ : ∀ w, 0 ≤ π w)
    (hstar : ∀ w j, (∑ v, P w v * O j v) ≤ ∑ v, P w v * O (jstar w) v)
    (hUM_S : (∑ w, π w * O (jstar w) w) = ∑ w, π w * (∑ v, P w v * O (jstar w) v))
    (hUM_i : (∑ w, π w * (∑ v, P w v * O i v)) = ∑ w, π w * O i w) :
    (∑ w, π w * O i w) ≤ ∑ w, π w * O (jstar w) w := by
  rw [hUM_S, ← hUM_i]
  exact Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left (hstar w i) (hπ w))

/-- **(1b) Argmax Value — asymptotic, UNCONDITIONAL martingale only.**
    `hUM_S : E_now(Ŝ) ≂ₙ E_now(M)`  (thm:cee on the single LUV `Ŝ`, using `E_later Ŝ = M`);
    `hMon  : E_now(mᵢ) ≲ E_now(M)`  (thm:expprovind from `M ≥ mᵢ`);
    `hCee  : E_now(Oⁱ) ≂ₙ E_now(mᵢ)` (thm:cee on `Oⁱ`).   ⟹  `E_now(Oⁱ) ≲ E_now(Ŝ)`. -/
theorem value_argmax_asymptotic
    (ES Em Emi Eoi : ℕ → ℝ)
    (hUM_S : Approx ES Em) (hMon : AsympLE Emi Em) (hCee : Approx Eoi Emi) :
    AsympLE Eoi ES :=
  ((hCee.asympLE).trans hMon).trans_approx hUM_S.symm

/-- **(2a) Softmax–argmax payoff gap ≤ L¹ weight distance** (exact; options in `[0,1]`).
    With `β` = hard argmax and `α` = softmax, the RHS is `E_π‖α−β‖₁`, the near-tie mass. -/
theorem payoff_gap_le_l1
    {W J : Type*} [Fintype W] [Fintype J]
    (π : W → ℝ) (O : J → W → ℝ) (α β : J → W → ℝ)
    (hπ : ∀ w, 0 ≤ π w) (hO : ∀ j w, 0 ≤ O j w ∧ O j w ≤ 1) :
    |(∑ w, π w * (∑ j, α j w * O j w)) - (∑ w, π w * (∑ j, β j w * O j w))|
      ≤ ∑ w, π w * (∑ j, |α j w - β j w|) := by
  have hrw : (∑ w, π w * (∑ j, α j w * O j w)) - (∑ w, π w * (∑ j, β j w * O j w))
      = ∑ w, π w * (∑ j, (α j w - β j w) * O j w) := by
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hrw]
  calc |∑ w, π w * (∑ j, (α j w - β j w) * O j w)|
      ≤ ∑ w, |π w * (∑ j, (α j w - β j w) * O j w)| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ w, π w * |∑ j, (α j w - β j w) * O j w| := by
          refine Finset.sum_congr rfl (fun w _ => ?_)
          rw [abs_mul, abs_of_nonneg (hπ w)]
    _ ≤ ∑ w, π w * (∑ j, |α j w - β j w|) := by
          refine Finset.sum_le_sum (fun w _ => mul_le_mul_of_nonneg_left ?_ (hπ w))
          calc |∑ j, (α j w - β j w) * O j w|
              ≤ ∑ j, |(α j w - β j w) * O j w| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ ∑ j, |α j w - β j w| := by
                  refine Finset.sum_le_sum (fun j _ => ?_)
                  rw [abs_mul]
                  have hO1 : |O j w| ≤ 1 := by
                    rw [abs_of_nonneg (hO j w).1]; exact (hO j w).2
                  calc |α j w - β j w| * |O j w|
                      ≤ |α j w - β j w| * 1 := mul_le_mul_of_nonneg_left hO1 (abs_nonneg _)
                    _ = |α j w - β j w| := mul_one _

/-- `aₙ ≂ₙ bₙ` whenever `|aₙ − bₙ| ≤ Δₙ → 0` (squeeze). -/
theorem approx_of_abs_le {a b Δ : ℕ → ℝ}
    (hb : ∀ n, |a n - b n| ≤ Δ n) (hΔ : Tendsto Δ atTop (𝓝 0)) :
    Approx a b := by
  show Tendsto (fun n => a n - b n) atTop (𝓝 0)
  exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact hb n) hΔ

/-- **(2b) Argmax Value via the softmax limit.**  Softmax Value (`hSoft`) plus the payoff
    gap squeezed to 0 by `Δ → 0` (the near-tie / margin condition)  ⟹  argmax Value. -/
theorem value_argmax_via_softmax
    {Eoi ESa ESb Δ : ℕ → ℝ}
    (hSoft : AsympLE Eoi ESa)
    (hb : ∀ n, |ESa n - ESb n| ≤ Δ n) (hΔ : Tendsto Δ atTop (𝓝 0)) :
    AsympLE Eoi ESb :=
  hSoft.trans_approx (approx_of_abs_le hb hΔ)

end DeferenceArgmax

#print axioms DeferenceArgmax.value_of_argmax
#print axioms DeferenceArgmax.value_argmax_asymptotic
#print axioms DeferenceArgmax.payoff_gap_le_l1
#print axioms DeferenceArgmax.value_argmax_via_softmax


/- ======================================================================================
   THE CONVERSE (added): Value ⟹ Total Trust, finite-exact (DDB Lemma 7.1, §2.2).
   Witness menu {X, const s}; followed strategy  Ŝ w = if s ≤ E_w(X) then X w else s,
   with E_w(X) = ∑ v, P w v * X v.  The keystone is the exact identity `witness_identity`;
   the converse iff is immediate.  Everything here is PROVED (no LI hypotheses, no
   asymptotics) — it is the two-option-menu algebra, exactly as DDB's Lemma 7.1.
   ====================================================================================== -/
namespace DeferenceConverse
open Finset
open scoped Classical

/-- **Keystone identity (two-option witness).**  The followed-strategy Value gap over the
    constant option `s` equals the conditional Total-Trust mass
    `∑_{w: Ew(X)≥s} π w (X w − s)`.  Arbitrary `π` (no `∑π=1`), any `Fintype W`. -/
theorem witness_identity {W : Type*} [Fintype W]
    (π : W → ℝ) (P : W → W → ℝ) (X : W → ℝ) (s : ℝ) :
    (∑ w, π w * (if s ≤ (∑ v, P w v * X v) then X w else s)) - s * (∑ w, π w)
      = ∑ w, (if s ≤ (∑ v, P w v * X v) then π w * (X w - s) else 0) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases h : s ≤ (∑ v, P w v * X v)
  · simp only [if_pos h]; ring
  · simp only [if_neg h]; ring

/-- Value-on-witness ⟺ Total-Trust nonnegativity (raw form). -/
theorem value_witness_iff_totalTrust {W : Type*} [Fintype W]
    (π : W → ℝ) (P : W → W → ℝ) (X : W → ℝ) (s : ℝ) :
    (s * (∑ w, π w) ≤ ∑ w, π w * (if s ≤ (∑ v, P w v * X v) then X w else s))
      ↔ (0 ≤ ∑ w, (if s ≤ (∑ v, P w v * X v) then π w * (X w - s) else 0)) := by
  rw [← sub_nonneg, witness_identity π P X s]

/-- Split the Total-Trust mass: `∑_{Ew≥s} π(X−s) = ∑_{Ew≥s} πX − s·∑_{Ew≥s} π`. -/
theorem totalTrust_sum_split {W : Type*} [Fintype W]
    (π : W → ℝ) (P : W → W → ℝ) (X : W → ℝ) (s : ℝ) :
    (∑ w, (if s ≤ (∑ v, P w v * X v) then π w * (X w - s) else 0))
      = (∑ w, (if s ≤ (∑ v, P w v * X v) then π w * X w else 0))
        - s * (∑ w, (if s ≤ (∑ v, P w v * X v) then π w else 0)) := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  by_cases h : s ≤ (∑ v, P w v * X v)
  · simp only [if_pos h]; ring
  · simp only [if_neg h]; ring

/-- **Value-on-witness ⟺ Total Trust at `s`** (standard conditional-mass form):
    `s · π{Ew(X)≥s} ≤ E_π(X · 1[Ew(X)≥s])`, i.e. `E_π(X | Ew(X) ≥ s) ≥ s`. -/
theorem value_witness_iff_totalTrust_mass {W : Type*} [Fintype W]
    (π : W → ℝ) (P : W → W → ℝ) (X : W → ℝ) (s : ℝ) :
    (s * (∑ w, π w) ≤ ∑ w, π w * (if s ≤ (∑ v, P w v * X v) then X w else s))
      ↔ (s * (∑ w, (if s ≤ (∑ v, P w v * X v) then π w else 0))
          ≤ ∑ w, (if s ≤ (∑ v, P w v * X v) then π w * X w else 0)) := by
  rw [value_witness_iff_totalTrust π P X s, totalTrust_sum_split π P X s, sub_nonneg]

/-- **The converse proper (DDB Lemma 7.1): Value ⟹ Total Trust.**  If `π` Values the future
    self on every witness menu `{X, const s}`, then Total Trust holds at every threshold. -/
theorem totalTrust_of_value {W : Type*} [Fintype W]
    (π : W → ℝ) (P : W → W → ℝ)
    (hVal : ∀ (X : W → ℝ) (s : ℝ),
        s * (∑ w, π w) ≤ ∑ w, π w * (if s ≤ (∑ v, P w v * X v) then X w else s)) :
    ∀ (X : W → ℝ) (s : ℝ),
      s * (∑ w, (if s ≤ (∑ v, P w v * X v) then π w else 0))
        ≤ ∑ w, (if s ≤ (∑ v, P w v * X v) then π w * X w else 0) :=
  fun X s => (value_witness_iff_totalTrust_mass π P X s).mp (hVal X s)

/-- **Combined finite-exact equivalence over witness menus: Value ⟺ Total Trust.**
    The LI finite-frame analog of DDB Theorem 2.2 restricted to two-option menus. -/
theorem value_iff_totalTrust {W : Type*} [Fintype W]
    (π : W → ℝ) (P : W → W → ℝ) :
    (∀ (X : W → ℝ) (s : ℝ),
        s * (∑ w, π w) ≤ ∑ w, π w * (if s ≤ (∑ v, P w v * X v) then X w else s))
      ↔ (∀ (X : W → ℝ) (s : ℝ),
          s * (∑ w, (if s ≤ (∑ v, P w v * X v) then π w else 0))
            ≤ ∑ w, (if s ≤ (∑ v, P w v * X v) then π w * X w else 0)) :=
  ⟨fun h X s => (value_witness_iff_totalTrust_mass π P X s).mp (h X s),
   fun h X s => (value_witness_iff_totalTrust_mass π P X s).mpr (h X s)⟩

/- Non-vacuity: DDB's anti-expert frame.  Worlds `Fin 2`; π=(½,½); P=⅕ on the diagonal, ⅘
   off; X = 1[world 0]; s = ½.  The unconditional martingale holds (`stationary`, πP=π) yet
   Total Trust fails (`TT_negative`, mass = −¼), so Value fails on the witness — the two
   failures coincide, witnessing that the converse is non-vacuous. -/
namespace AntiExpert

noncomputable def π : Fin 2 → ℝ := fun _ => 1/2
noncomputable def P : Fin 2 → Fin 2 → ℝ := fun w v => if w = v then 1/5 else 4/5
def X : Fin 2 → ℝ := fun w => if w = 0 then 1 else 0

theorem E0_lt : ¬ ((1/2 : ℝ) ≤ (∑ v, P (0 : Fin 2) v * X v)) := by
  norm_num [P, X, Fin.sum_univ_two]

theorem E1_ge : (1/2 : ℝ) ≤ (∑ v, P (1 : Fin 2) v * X v) := by
  norm_num [P, X, Fin.sum_univ_two]

theorem stationary : ∀ v : Fin 2, (∑ w, π w * P w v) = π v := by
  intro v
  fin_cases v <;> simp [π, P, Fin.sum_univ_two] <;> norm_num

theorem TT_negative :
    (∑ w, (if (1/2 : ℝ) ≤ (∑ v, P w v * X v) then π w * (X w - 1/2) else 0)) = -1/4 := by
  rw [Fin.sum_univ_two, if_neg E0_lt, if_pos E1_ge]
  norm_num [π, X]

theorem value_fails :
    ¬ ((1/2 : ℝ) * (∑ w, π w)
        ≤ ∑ w, π w * (if (1/2 : ℝ) ≤ (∑ v, P w v * X v) then X w else (1/2 : ℝ))) := by
  rw [value_witness_iff_totalTrust π P X (1/2), TT_negative]
  norm_num

end AntiExpert
end DeferenceConverse

#print axioms DeferenceConverse.witness_identity
#print axioms DeferenceConverse.value_witness_iff_totalTrust
#print axioms DeferenceConverse.totalTrust_sum_split
#print axioms DeferenceConverse.value_witness_iff_totalTrust_mass
#print axioms DeferenceConverse.totalTrust_of_value
#print axioms DeferenceConverse.value_iff_totalTrust
#print axioms DeferenceConverse.AntiExpert.stationary
#print axioms DeferenceConverse.AntiExpert.TT_negative
#print axioms DeferenceConverse.AntiExpert.value_fails


/- ======================================================================================
   §3 FOLDING (added): cee/ccee coincide exactly when the expert KNOWS the weight.
   If a weight `g` is constant on each expert's support (P w v ≠ 0 → g v = g w), the
   per-world conditional defect vanishes (E_w(X·g) = g w · E_w(X)); summed against π the
   conditional martingale collapses to the unconditional one.  The anti-expert frame is the
   contrast: its conditioning weight 1[E(X)≥½] is NOT expert-known (`fold_hypothesis_fails`).
   ====================================================================================== -/
namespace DeferenceFold
open Finset

/-- **Per-world fold (expert-known weight).**  If the expert at `w` puts no mass off the
    `g`-fiber of `w`, then `E_w(X·g) = g w · E_w(X)`. -/
theorem fold_pointwise {W : Type*} [Fintype W]
    (P : W → W → ℝ) (X g : W → ℝ) (w : W)
    (hknow : ∀ v, P w v ≠ 0 → g v = g w) :
    (∑ v, P w v * (X v * g v)) = g w * (∑ v, P w v * X v) := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  by_cases hv : P w v = 0
  · simp [hv]
  · rw [hknow v hv]; ring

/-- **Summed fold: ccee collapses to cee under expert-known weights.** -/
theorem fold_sum {W : Type*} [Fintype W]
    (π : W → ℝ) (P : W → W → ℝ) (X g : W → ℝ)
    (hknow : ∀ w v, P w v ≠ 0 → g v = g w) :
    (∑ w, π w * (∑ v, P w v * (X v * g v)))
      = ∑ w, π w * (g w * (∑ v, P w v * X v)) := by
  refine Finset.sum_congr rfl (fun w _ => ?_)
  rw [fold_pointwise P X g w (hknow w)]

/-- The fold hypothesis FAILS on the anti-expert frame for the weight `g = 1[E(X) ≥ ½]`:
    world 0 lies in world 1's support but carries a different `g`-value. -/
theorem fold_hypothesis_fails :
    ¬ (∀ w v : Fin 2, DeferenceConverse.AntiExpert.P w v ≠ 0 →
        (if (1/2 : ℝ) ≤
            (∑ u, DeferenceConverse.AntiExpert.P v u * DeferenceConverse.AntiExpert.X u)
          then (1 : ℝ) else 0)
          = (if (1/2 : ℝ) ≤
              (∑ u, DeferenceConverse.AntiExpert.P w u * DeferenceConverse.AntiExpert.X u)
            then (1 : ℝ) else 0)) := by
  intro h
  have hP : DeferenceConverse.AntiExpert.P (1 : Fin 2) (0 : Fin 2) ≠ 0 := by
    norm_num [DeferenceConverse.AntiExpert.P]
  have key := h 1 0 hP
  rw [if_neg DeferenceConverse.AntiExpert.E0_lt,
      if_pos DeferenceConverse.AntiExpert.E1_ge] at key
  norm_num at key

end DeferenceFold

#print axioms DeferenceFold.fold_pointwise
#print axioms DeferenceFold.fold_sum
#print axioms DeferenceFold.fold_hypothesis_fails


/- ======================================================================================
   THE ASYMPTOTIC CONVERSE (added): Value ⟹ Total Trust, soft/LI form (§2.2 continuum
   caveat; §3.1).  Soft analog of the finite-exact `DeferenceConverse`, modeled exactly as
   `DeferenceAsymp.value_asymptotic`: the genuine LI coherence results enter ONLY as named
   `Approx`/`AsympLE` hypotheses, and the asymptotic Total-Trust INEQUALITY is derived as
   their valid composition.  Unnormalized (no division -- dodges the zero-mass case).
   Soft weight w_n = Ind_{δ_n}(E_{f(n)}(X_n) > t), δ_n → 0.  Sequences:
     Exw = E_now(X·w),  Eew = E_now(E_later(X)·w),  Ew = E_now(w),  E1 = E_now(1),
     ESsoft = E_now(Ŝ_soft) on the witness menu {X, const s}.
   ====================================================================================== -/
namespace DeferenceConverseAsymp
open Filter Topology
open DeferenceAsymp

/-- **(1) The `ccee` ⟹ Total-Trust bridge, asymptotic.**  From the conditional-martingale
    equality (`hCcee`, thm:ccee at the soft weight) plus the threshold bound (`hThr`,`hδ`,
    thm:expprovind: `E_later(X)·w ≥ t·w` in every consistent world, with the `c↑t` slack
    `δ_n→0`), conclude the unnormalized asymptotic Total Trust `t·E_now(w) ≲ E_now(X·w)`. -/
theorem totalTrust_asymptotic
    (t : ℝ) (Exw Eew Ew δ : ℕ → ℝ)
    (hCcee : Approx Exw Eew)
    (hδ    : Tendsto δ atTop (𝓝 0))
    (hThr  : ∀ᶠ n in atTop, t * Ew n ≤ Eew n + δ n) :
    AsympLE (fun n => t * Ew n) Exw := by
  have hTE : AsympLE (fun n => t * Ew n) Eew := by
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hδ ε hε
    filter_upwards [hThr, eventually_atTop.2 ⟨N, fun n hn => hN n hn⟩] with n hn1 hn2
    show t * Ew n ≤ Eew n + ε
    have hlt : |δ n| < ε := by simpa [Real.dist_eq] using hn2
    have := (abs_lt.1 hlt).2
    linarith
  exact hTE.trans_approx hCcee.symm

/-- **(2) The genuine `Value ⟹ Total Trust` arrow, asymptotic.**  Soft analog of the finite
    `DeferenceConverse.totalTrust_of_value`.  From `hLoe` (thm:loe: linearity of `E_now` over
    `Ŝ_soft = X·w + s·1 − s·w`) and `hVal` (Value on the witness menu `{X, const s}`:
    `s·E_now(1) ≲ E_now(Ŝ_soft)`), conclude `s·E_now(w) ≲ E_now(X·w)` — Total Trust at `s`.
    Neither hypothesis is the conclusion. -/
theorem totalTrust_of_value_asymptotic
    (s : ℝ) (Exw Ew E1 ESsoft : ℕ → ℝ)
    (hLoe : Approx ESsoft (fun n => Exw n + s * E1 n - s * Ew n))
    (hVal : AsympLE (fun n => s * E1 n) ESsoft) :
    AsympLE (fun n => s * Ew n) Exw := by
  have h1 : AsympLE (fun n => s * E1 n) (fun n => Exw n + s * E1 n - s * Ew n) :=
    hVal.trans_approx hLoe
  intro ε hε
  filter_upwards [h1 ε hε] with n hn
  show s * Ew n ≤ Exw n + ε
  linarith

/-- **(2′) The reverse arrow: Total Trust ⟹ Value, asymptotic.**  Companion to
    `totalTrust_of_value_asymptotic`.  From `hLoe` (thm:loe: linearity of the soft followed
    strategy `Ŝ_soft = X·w + s·1 − s·w`) and asymptotic Total Trust at `s`
    (`s·E_now(w) ≲ E_now(X·w)`), conclude Value on the soft witness menu
    (`s·E_now(1) ≲ E_now(Ŝ_soft)`).  Same linearity input as the forward arrow, run backwards. -/
theorem value_of_totalTrust_asymptotic
    (s : ℝ) (Exw Ew E1 ESsoft : ℕ → ℝ)
    (hLoe : Approx ESsoft (fun n => Exw n + s * E1 n - s * Ew n))
    (hTT  : AsympLE (fun n => s * Ew n) Exw) :
    AsympLE (fun n => s * E1 n) ESsoft := by
  have h1 : AsympLE (fun n => s * E1 n) (fun n => Exw n + s * E1 n - s * Ew n) := by
    intro ε hε
    filter_upwards [hTT ε hε] with n hn
    show s * E1 n ≤ (Exw n + s * E1 n - s * Ew n) + ε
    linarith
  exact h1.trans_approx hLoe.symm

/-- **The asymptotic `Value ⟺ Total Trust` biconditional** — the timely-manner (`≈ₙ`/`≲`) LI
    analog of the finite-exact `DeferenceConverse.value_iff_totalTrust`, and the direct LI
    counterpart of DDB's Theorem 2.2.  Given only linearity of the soft followed strategy
    (`hLoe`), Value on the soft witness menu and asymptotic Total Trust at `s` are equivalent,
    BOTH arrows.  This is `Value ⟺ Total Trust` (the deference *inequality*); lifting Total
    Trust to the full tower *equality* is the separate continuum family-squeeze (§5), not here. -/
theorem value_iff_totalTrust_asymptotic
    (s : ℝ) (Exw Ew E1 ESsoft : ℕ → ℝ)
    (hLoe : Approx ESsoft (fun n => Exw n + s * E1 n - s * Ew n)) :
    AsympLE (fun n => s * E1 n) ESsoft ↔ AsympLE (fun n => s * Ew n) Exw :=
  ⟨totalTrust_of_value_asymptotic s Exw Ew E1 ESsoft hLoe,
   value_of_totalTrust_asymptotic s Exw Ew E1 ESsoft hLoe⟩

/-- Non-vacuity for (1): constant sequences satisfy all hypotheses (so it is not vacuous). -/
theorem ccee_bridge_satisfiable :
    ∃ (t : ℝ) (Exw Eew Ew δ : ℕ → ℝ),
      Approx Exw Eew ∧ Tendsto δ atTop (𝓝 0) ∧
      (∀ᶠ n in atTop, t * Ew n ≤ Eew n + δ n) :=
  ⟨1/2, (fun _ => 1/2), (fun _ => 1/2), (fun _ => 1), (fun _ => 0),
   Approx.rfl' _, tendsto_const_nhds,
   Filter.Eventually.of_forall (fun _ => by norm_num)⟩

/-- Non-vacuity for (2): constant sequences satisfying linearity and Value. -/
theorem value_side_satisfiable :
    ∃ (s : ℝ) (Exw Ew E1 ESsoft : ℕ → ℝ),
      Approx ESsoft (fun n => Exw n + s * E1 n - s * Ew n) ∧
      AsympLE (fun n => s * E1 n) ESsoft :=
  ⟨1/2, (fun _ => 1/2), (fun _ => 1), (fun _ => 1),
   (fun _ => (1/2 : ℝ) + (1/2) * 1 - (1/2) * 1),
   Approx.rfl' _,
   by
     intro ε hε
     filter_upwards [] with n
     show (1/2 : ℝ) * 1 ≤ ((1/2 : ℝ) + (1/2) * 1 - (1/2) * 1) + ε
     linarith⟩

end DeferenceConverseAsymp

#print axioms DeferenceConverseAsymp.totalTrust_asymptotic
#print axioms DeferenceConverseAsymp.totalTrust_of_value_asymptotic
#print axioms DeferenceConverseAsymp.value_of_totalTrust_asymptotic
#print axioms DeferenceConverseAsymp.value_iff_totalTrust_asymptotic
#print axioms DeferenceConverseAsymp.ccee_bridge_satisfiable
#print axioms DeferenceConverseAsymp.value_side_satisfiable


/- ======================================================================================
   THE DIRECT TRADER (added): the no-Dutch-book view of Tower ⟹ Value (§2.4).
   A trader that, on seeing a Value gap, sells Oⁱ and buys the expert's pick Ŝ at day-n
   prices `en`, then unwinds at day-f prices `ef`.  Per-round net cash =
     (day-n leg)  (en i − en jstar)   +   (day-f unwind)  (ef jstar − ef i).
   With `jstar` a maximizer of `ef` (the expert prices its own pick at the max), the unwind
   is ≥ 0, so the round nets AT LEAST the Value gap `en i − en jstar`.  Hence a positive gap
   forces positive guaranteed profit — the contradiction the criterion forbids.  This is the
   exact ARITHMETIC core; the exploit itself (unbounded profit, bounded risk) is the trusted
   logical-induction criterion, not formalized here.
   ====================================================================================== -/
namespace DeferenceTrader

/-- **Round profit ≥ Value gap** (exact).  `en`, `ef` are the day-`n` and day-`f` option
    prices; `jstar` a maximizer of `ef` (so the expert prices its own pick `Ŝ = O^{jstar}` at
    the max).  The two-leg round nets `(en i − en jstar) + (ef jstar − ef i)`, and the unwind
    `ef jstar − ef i ≥ 0`, so the round nets at least the gap `en i − en jstar`. -/
theorem round_profit_ge_gap {J : Type*} (en ef : J → ℝ) (i jstar : J)
    (hmax : ∀ j, ef j ≤ ef jstar) :
    en i - en jstar ≤ (en i - en jstar) + (ef jstar - ef i) := by
  have hunwind : 0 ≤ ef jstar - ef i := by linarith [hmax i]
  linarith

/-- A positive Value gap ⇒ strictly positive guaranteed round profit (the arbitrage that the
    no-Dutch-book criterion rules out, forcing Value). -/
theorem gap_pos_imp_profit_pos {J : Type*} (en ef : J → ℝ) (i jstar : J)
    (hmax : ∀ j, ef j ≤ ef jstar) (hgap : 0 < en i - en jstar) :
    0 < (en i - en jstar) + (ef jstar - ef i) := by
  have hunwind : 0 ≤ ef jstar - ef i := by linarith [hmax i]
  linarith

end DeferenceTrader

#print axioms DeferenceTrader.round_profit_ge_gap
#print axioms DeferenceTrader.gap_pos_imp_profit_pos
