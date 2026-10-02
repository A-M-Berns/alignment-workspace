import Cleanroom.Bli.BliExactness.Defs
import Cleanroom.Bli.BliTrajectory.SelfTrust

/-!
# `bli-exactness` — X6 (v): exact self-trust implies the smoothed (`ctsInd`) inequality

bli-soto-b-027's target (i): "exact self-trust from day one" implies the LI paper's Theorem 4.12.4
inequality (slide 40's displayed `𝔼ₙ(𝟙(φ)·Ind_δ(ℙ_m(φ) ≥ p)) ≥ p·𝔼ₙ(Ind_δ(ℙ_m(φ) ≥ p))`) at
**every** `n < m`, in the quote-cell form: for a cell family `cells` and `P` satisfying
`ExactSelfTrustX quoteAt cells P`,
`∑_{I ∈ cells m} P_n(φ ⋏ χ_I) · ctsInd δ (mid I) p ≥ p · ∑_{I ∈ cells m} P_n(χ_I) · ctsInd δ (mid I) p`.
This is the quote-cell analogue of `bli-trajectory`'s `e2x_smoothed_self_trust` (state atoms in
place of quote cells), reusing its lemmas `mul_ctsInd_ge`/`ctsInd_nonneg`. One termwise step
(Kind L, audit r1 N6). The antecedent's inhabitants (repair round 2): Soto's two-clause bundle
market `sotoBundleHistory` (`Defs.lean`; `sotoBundle_smoothed` applies the inequality to it) and
the zero history — **both N−**: the midpoint antecedent `ExactSelfTrustX` over every sentence has
no `⊤`-coherent inhabitant with positive mass on a cell of midpoint `≠ 1` (`Defs.lean`
`coherentTop_forces_zero`), so no N+ exists for it; the inequality's content for a logical inductor
is FAF's asymptotic `lic_self_trust_closed` (`Backbone.lean` `self_trust_smoothed_const`).

Target (ii), "strictly stronger", is X3's witness (`Perturb.lean`): an inductor satisfying
FAF's `thm:st` (every inductor does) that violates the exact identity on day 1.
-/

namespace Cleanroom.Bli.BliExactness

open LogicalInduction LO.Propositional Finset
open Cleanroom.Bli.BliTrajectory

/-- **Exact ⟹ smoothed, at every day** (bli-soto-b-027 (i); slide 40's displayed inequality in
cell form). Under `ExactSelfTrustX quoteAt cells P`, for every `n < m`, every `φ`, every `δ > 0`
and every threshold `p`, with nonnegative cell masses on `cells m`:
`p · ∑_{I ∈ cells m} P_n(χ_I)·ctsInd δ (mid I) p ≤ ∑_{I ∈ cells m} P_n(φ ⋏ χ_I)·ctsInd δ (mid I) p`.
Proof: termwise `P_n(φ ⋏ χ_I) = mid I · P_n(χ_I)` and `p · ctsInd δ x p ≤ x · ctsInd δ x p` (the
ramp is zero unless `x > p`).
Source: [[bli-soto-b-inventory]] 027 (i); slide 40 bullet 3 ([[bli-slides-inventory]] 042);
mandate X6 (v); cf. `bli-trajectory` `e2x_smoothed_self_trust`
Kind: L
Fidelity: exact (cell form with the midpoint over the family; FAF's `ctsInd` ramp `(p, p+δ]`)
Hyps: antecedent `ExactSelfTrustX quoteAt cells P` (inhabited by `sotoBundleHistory` and the
zero history, both N− — no N+ exists, `coherentTop_forces_zero`); (a) nonnegative cell masses
(explicit) -/
theorem exactSelfTrustX_imp_smoothed {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} {P : History} (h : ExactSelfTrustX quoteAt cells P) {δ : ℚ}
    (hδ : 0 < δ) {n m : ℕ} (hnm : n < m) (φ : Sentence) (p : ℝ)
    (hP : ∀ I ∈ cells m, 0 ≤ P n (quoteAt m φ I.1 I.2)) :
    p * ∑ I ∈ cells m, P n (quoteAt m φ I.1 I.2) * ctsInd δ ((mid I : ℚ) : ℝ) p ≤
      ∑ I ∈ cells m, P n (φ ⋏ quoteAt m φ I.1 I.2) * ctsInd δ ((mid I : ℚ) : ℝ) p := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun I hI => ?_
  rw [h n m hnm φ I hI]
  have hv := mul_ctsInd_ge hδ ((mid I : ℚ) : ℝ) p
  have hPI := hP I hI
  have hind := ctsInd_nonneg δ ((mid I : ℚ) : ℝ) p
  have key := mul_le_mul_of_nonneg_left hv hPI
  nlinarith [key, hPI, hind]

/-- The same inequality for the all-zero history (both sides `0`): the N− inhabitant of the
antecedent exercises nothing — recorded so the row says so.
Source: mandate X6 (v)
Kind: N-
Fidelity: n/a
Hyps: (a) -/
theorem zeroHistory_smoothed (quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence)
    (cells : ℕ → Finset (ℚ × ℚ)) {δ : ℚ} (hδ : 0 < δ) {n m : ℕ} (hnm : n < m) (φ : Sentence)
    (p : ℝ) :
    p * ∑ I ∈ cells m, (fun _ _ => (0 : ℝ)) n (quoteAt m φ I.1 I.2) * ctsInd δ ((mid I : ℚ) : ℝ) p ≤
      ∑ I ∈ cells m, (fun _ _ => (0 : ℝ)) n (φ ⋏ quoteAt m φ I.1 I.2) *
        ctsInd δ ((mid I : ℚ) : ℝ) p :=
  exactSelfTrustX_imp_smoothed (zeroHistory_exactSelfTrustX quoteAt cells) hδ hnm φ p
    (fun _ _ => le_rfl)

/-- **The inequality at Soto's bundle market**: the two-clause bundle history (nonnegative masses
`w`) satisfies the smoothed inequality at every `n < m`, by `exactSelfTrustX_imp_smoothed`. Grade
**N−** (repair round 2, audit r2 adversarial N5 / B2): the antecedent is exercised by a history
with positive cell masses, but a by-definition, `⊤`-incoherent one — and `coherentTop_forces_zero`
shows the midpoint antecedent admits nothing better. Recorded so the row says exactly that.
Source: mandate X6 (v) (non-vacuity); audit r1 fidelity B2 (iii); audit r2 adversarial N5
Kind: N-
Fidelity: n/a
Hyps: (a) `hinj`, `hne` (discharged for `quoteAt T` in `Perturb.lean`); (a) `hw` -/
theorem sotoBundle_smoothed {quoteAt : ℕ → Sentence → ℚ → ℚ → Sentence}
    {cells : ℕ → Finset (ℚ × ℚ)} (hinj : CellInjective quoteAt cells) (hne : ConjDisjoint quoteAt)
    {w : ℚ × ℚ → ℝ} (hw : ∀ I, 0 ≤ w I) {δ : ℚ} (hδ : 0 < δ) {n m : ℕ} (hnm : n < m)
    (φ : Sentence) (p : ℝ) :
    p * ∑ I ∈ cells m, sotoBundleHistory quoteAt cells w n (quoteAt m φ I.1 I.2) *
        ctsInd δ ((mid I : ℚ) : ℝ) p ≤
      ∑ I ∈ cells m, sotoBundleHistory quoteAt cells w n (φ ⋏ quoteAt m φ I.1 I.2) *
        ctsInd δ ((mid I : ℚ) : ℝ) p :=
  exactSelfTrustX_imp_smoothed (sotoBundle_exactSelfTrustX hinj hne w) hδ hnm φ p
    (fun I hI => by rw [sotoBundle_quote hinj w hnm φ hI]; exact hw I)

end Cleanroom.Bli.BliExactness
