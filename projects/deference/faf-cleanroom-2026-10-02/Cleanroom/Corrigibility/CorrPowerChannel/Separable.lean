import Cleanroom.Corrigibility.CorrPowerChannel.J3

/-!
# `corr-power-channel` — T4(b): the structural gap under separability, and the mandate's instance

The unrestricted "structural gap" inequality `VOI(s | q) ≥ VOI(ρ-component)` is false
(`gap_counterexample`, `Gap.lean`; finding F-1). This file proves the nearest well-posed version
and the instance the mandate asks for (repair round 1, B1).

**Separable setting.** `Ω = Ω₁ × Ω₂` (the `π`-side and the `ρ`-side), `P = P₁ ⊗ P₂`
(`prodDistr`), options `A = A₁ × A₂` with the set `B₁ ×ˢ B₂`, value table
`V((ω₁, ω₂), (a₁, a₂)) = V₁ ω₁ a₁ + V₂ ω₂ a₂` (`sepV`), the channel `q = expComap Prod.fst q₁`
(any experiment on `Ω₁`, read on the product: it depends on `ω₁` only), the scan `s = perfectExp`.

* `voiExp_sep_fst` — `VOI(q) = VOI₁(q₁)`: a `π`-only channel is worth exactly what it is worth on
  the `π`-problem alone (the `ρ`-coordinate is chosen on the prior whatever the signal);
  `voiExp_sep_snd` is the mirror image. `evpi_sep` — `EVPI = EVPI₁ + EVPI₂`.
* `voiExp_prod_perfect_eq_evpi` — `VOI(k, perfect) = EVPI` for every `k` (general; the Blackwell
  squeeze used twice in `J3.lean`/`Gap.lean`, named).
* **`voiExp_marginal_sep_eq`** — `VOI(s | q) = (EVPI₁ − VOI₁(q₁)) + EVPI₂`.
* **`voiExp_marginal_ge_rho_sep`** — the mandate's `voiExp_marginal_ge_rho`, under separability:
  `VOI(s | q) ≥ VOI(ρ-component)` for every `q₁`, including the perfect one (`δ = 0`), where the
  `ρ`-component's VOI is `voiExp … (ofMap Prod.snd) …` (`= EVPI₂`, `voiExp_rho_sep`).
* **`e3rho_marginal`** — the mandate's instance: E3 at `n+1` plans times a uniform `ρ ∈ Fin (m+1)`
  with a bet at stake `σ ≥ 0`: `VOI(s | q) = δ(1 − 1/(n+1)) + σ(1 − 1/(m+1))` and
  `VOI(ρ) = σ(1 − 1/(m+1))`.
* `marginal_perfect_antitone` — D16's displayed inequality `VOI(s | q) ≥ VOI(s | q, π)` holds for
  every `q`, `π` by Blackwell **when `a = s` is the perfect scan**; for an `a` revealing `ρ` alone
  the display is false (`d16_display_fails_for_rho_only_a`, `Gap.lean`; F-19). What
  `gap_counterexample` refutes is the further identification, in P2, of `VOI(s | q, π)` with the
  *unconditional* `EVPI^ρ`; under separability that identification is `voiExp_marginal_sep_eq`.
* `voiExp_ofMap_eq_evpi_of_factors` (repair round 2) — `VOI(ofMap f) = EVPI` whenever the value
  table on `B` factors through `f`: a scan is worth `EVPI` iff it reveals everything
  decision-relevant. With it, **`e3rho_marginal_piRho`**: the instance with the mandate's own
  `(π, ρ)`-scan has the same marginal `δ(1 − 1/(n+1)) + σ(1 − 1/(m+1))` as the perfect scan.
* `marginal_sep_perfect`, `marginal_sep_singleton` (repair round 2) — the content boundary of
  `voiExp_marginal_ge_rho_sep`: at `δ = 0` it is an equality, and with a singleton `B₂` it is
  `voiExp_le_evpi` on the `π`-problem; the theorem says something beyond its ingredients only
  when both sides are live, as in the instance.

Sources: power-wisdom-final.md S2 (l. 103, "General case"), D16 (l. 73), P2 (l. 159);
[[corr-power-channel-mandate]] T4(b); [[corr-power-channel-findings]] F-1, F-19;
[[corr-power-channel-audit-r1-fidelity]] B1, [[corr-power-channel-audit-r1-adversarial]] B1/N8;
[[corr-power-channel-audit-r2-adversarial]] N2, N6 (probes lifted),
[[corr-power-channel-audit-r2-fidelity]] N1, N2.
-/

namespace Cleanroom.Corrigibility.CorrPowerChannel

open FactoredSpaces Cleanroom.Found.CorrThreeStep Cleanroom.Found.LitDdbFrames.Blackwell
open Cleanroom.Corrigibility.CorrChannelVoi (expProd expProd_k trivialExp perfectExp expComap
  expComap_k blackwellLE_right_prod blackwellLE_left_prod)
open Finset hiding expect expect_const

noncomputable section

set_option linter.unusedSectionVars false

/-! ## General: the product with the perfect experiment is worth `EVPI`; D16's display -/

section General

variable {A Ω : Type} [Fintype A] [DecidableEq A] [Fintype Ω] [DecidableEq Ω]

/-- **A perfect scan on top of any channel is worth `EVPI`**: `VOI(k, perfect) = EVPI` for every
`k` — the Blackwell squeeze `VOI(perfect) ≤ VOI(k, perfect) ≤ EVPI` with `VOI(perfect) = EVPI`.
Source: power-wisdom-final.md D16 (l. 73, "`VOI_t(s | q) = VOI_t(s, q) − VOI_t(q)`" with `s` the
perfect scan); used inline in `e3_voiExp_prod` and `gap_counterexample`
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem voiExp_prod_perfect_eq_evpi {S : Type} [Fintype S] (P : Distr Ω) (V : Ω → A → ℝ)
    (k : Experiment Ω S) {B : Finset A} (hB : B.Nonempty) :
    voiExp P V (expProd k perfectExp) B hB = evpi P V B hB := by
  apply le_antisymm
  · exact voiExp_le_evpi _ _ _ _
  · rw [← voiExp_perfect_eq_evpi P V hB]
    exact voiExp_mono_blackwell _ _ (blackwellLE_right_prod _ _) _

/-- **D16's displayed inequality, exact: `VOI(s | q, π) ≤ VOI(s | q)`** for a perfect scan `s` and
every pair of channels `q`, `π` — the marginal value of perfect information can only fall as more
is already known, because `VOI(s | q) − VOI(s | q, π) = VOI(q, π) − VOI(q) ≥ 0` (Blackwell:
`q` is a garbling of `(q, π)`). The source's P2 goes further and identifies `VOI(s | q, π)` with
the unconditional `EVPI^ρ`; that step is what `gap_counterexample` refutes (F-1). The restriction
to a perfect `a` is necessary: for an `a` that reveals `ρ` alone the display is false — information
can be complementary (`d16_display_fails_for_rho_only_a`, `Gap.lean`; F-19).
Source: power-wisdom-final.md D16 (l. 73, "`VOI_t(a | q) ≥ VOI_t(a | q, π)`")
Kind: C
Fidelity: exact for `a = s` perfect; the display as written, for a `ρ`-revealing `a`, is false
(F-19)
Hyps: (a) none -/
theorem marginal_perfect_antitone {S T : Type} [Fintype S] [Fintype T] [DecidableEq S]
    (P : Distr Ω) (V : Ω → A → ℝ) (q : Experiment Ω S) (π : Experiment Ω T) {B : Finset A}
    (hB : B.Nonempty) :
    voiExp P V (expProd (expProd q π) perfectExp) B hB - voiExp P V (expProd q π) B hB ≤
      voiExp P V (expProd q perfectExp) B hB - voiExp P V q B hB := by
  rw [voiExp_prod_perfect_eq_evpi, voiExp_prod_perfect_eq_evpi]
  have := voiExp_mono_blackwell P V (blackwellLE_left_prod q π) hB
  linarith

/-- `EVPI` of a singleton option set is `0`.
Source: none: infrastructure ([[corr-power-channel-audit-r2-adversarial]] N6 probe, lifted)
Kind: L
Fidelity: n/a -/
theorem evpi_singleton (P : Distr Ω) (V : Ω → A → ℝ) (b : A) :
    evpi P V {b} (singleton_nonempty b) = 0 := by
  unfold evpi power bestMix attainable mixValue
  simp only [sup'_singleton]
  exact sub_self _

/-! ### A scan is worth `EVPI` iff it reveals everything decision-relevant (repair round 2) -/

open Classical in
/-- An option attaining `attainable` at some world of the fibre of `f` over `s` (any member of `B`
if the fibre is empty).
Source: none: infrastructure ([[corr-power-channel-audit-r2-adversarial]] N2 probe, lifted)
Kind: D
Fidelity: n/a -/
def fibreBest {S : Type} (V : Ω → A → ℝ) (f : Ω → S) {B : Finset A} (hB : B.Nonempty) (s : S) :
    A :=
  if h : ∃ ω, f ω = s then (exists_mem_eq_sup' hB (V h.choose)).choose else hB.choose

/-- `fibreBest` lands in `B`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem fibreBest_mem {S : Type} (V : Ω → A → ℝ) (f : Ω → S) {B : Finset A} (hB : B.Nonempty)
    (s : S) : fibreBest V f hB s ∈ B := by
  unfold fibreBest
  split_ifs with h
  · exact (exists_mem_eq_sup' hB (V h.choose)).choose_spec.1
  · exact hB.choose_spec

/-- When the value table on `B` factors through `f`, `fibreBest` at `f ω` attains `attainable` at
`ω` itself. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem fibreBest_spec {S : Type} (V : Ω → A → ℝ) (f : Ω → S) {B : Finset A} (hB : B.Nonempty)
    (hV : ∀ a ∈ B, ∀ ω ω', f ω = f ω' → V ω a = V ω' a) (ω : Ω) :
    V ω (fibreBest V f hB (f ω)) = attainable V B hB ω := by
  have h : ∃ ω', f ω' = f ω := ⟨ω, rfl⟩
  unfold fibreBest
  rw [dif_pos h]
  obtain ⟨ha, hatt⟩ := (exists_mem_eq_sup' hB (V h.choose)).choose_spec
  have hf : f h.choose = f ω := h.choose_spec
  rw [hV _ ha ω h.choose hf.symm, ← hatt]
  unfold attainable
  exact sup'_congr hB rfl (fun a ha' => hV a ha' h.choose ω hf)

/-- **`VOI(ofMap f) = EVPI` when the value table on `B` factors through `f`**: a deterministic
scan that reveals everything decision-relevant is worth as much as the perfect one (on each fibre
of `f` the attaining option is common to the fibre, so the fibre-wise best is the pointwise best;
`≤` is `voiExp_le_evpi`). Closes the "argued, not proved" step of `e3rho_marginal`'s round-1
docstring (`e3rho_marginal_piRho`).
Source: power-wisdom-final.md D16 (l. 73; the scan `s` "reveals `(π, ρ)`" — what matters is
that it reveals what the options depend on); [[corr-power-channel-audit-r2-adversarial]] N2
(probe `ScanFactors.lean`, lifted)
Kind: P
Fidelity: exact
Hyps: (a) the factoring property, named -/
theorem voiExp_ofMap_eq_evpi_of_factors {S : Type} [Fintype S] [DecidableEq S] (P : Distr Ω)
    (V : Ω → A → ℝ) (f : Ω → S) {B : Finset A} (hB : B.Nonempty)
    (hV : ∀ a ∈ B, ∀ ω ω', f ω = f ω' → V ω a = V ω' a) :
    voiExp P V (ofMap f) B hB = evpi P V B hB := by
  apply le_antisymm (voiExp_le_evpi P V _ hB)
  unfold voiExp evpi
  refine sub_le_sub_right ?_ _
  have h2 : ∀ ω, ∑ s, P.mass ω * (ofMap f).k ω s * V ω (fibreBest V f hB s) =
      P.mass ω * V ω (fibreBest V f hB (f ω)) := by
    intro ω
    simp only [ofMap]
    rw [sum_eq_single (f ω)]
    · simp
    · intro s _ hs
      simp [Ne.symm hs]
    · intro h; exact absurd (mem_univ _) h
  calc power P V B hB = ∑ ω, P.mass ω * V ω (fibreBest V f hB (f ω)) := by
        unfold power expect
        exact sum_congr rfl fun ω _ => by rw [fibreBest_spec V f hB hV ω]
    _ = ∑ ω, ∑ s, P.mass ω * (ofMap f).k ω s * V ω (fibreBest V f hB s) :=
        sum_congr rfl fun ω _ => (h2 ω).symm
    _ = ∑ s, ∑ ω, P.mass ω * (ofMap f).k ω s * V ω (fibreBest V f hB s) := sum_comm
    _ ≤ ∑ s, B.sup' hB (fun b => ∑ ω, P.mass ω * (ofMap f).k ω s * V ω b) :=
        sum_le_sum fun s _ =>
          le_sup' (fun b => ∑ ω, P.mass ω * (ofMap f).k ω s * V ω b) (fibreBest_mem V f hB s)

end General

/-! ## The separable setting -/

section Separable

variable {Ω₁ Ω₂ A₁ A₂ : Type} [Fintype Ω₁] [Fintype Ω₂] [Fintype A₁] [Fintype A₂]
  [DecidableEq A₁] [DecidableEq A₂]

/-- **The product posterior** `P₁ ⊗ P₂` on `Ω₁ × Ω₂` (independent `π`- and `ρ`-sides), as its mass
function.
Source: power-wisdom-final.md D16 (l. 73, "`ω = (π, ρ)`"); [[corr-power-channel-mandate]] T4(b)
Kind: D
Fidelity: exact -/
def prodDistr (P₁ : Distr Ω₁) (P₂ : Distr Ω₂) : Distr (Ω₁ × Ω₂) where
  mass := fun ω => P₁.mass ω.1 * P₂.mass ω.2
  nonneg := fun ω => mul_nonneg (P₁.nonneg _) (P₂.nonneg _)
  sum_eq_one := by
    rw [Fintype.sum_prod_type]
    show ∑ a, ∑ b, P₁.mass a * P₂.mass b = 1
    rw [← sum_mul_sum univ univ P₁.mass P₂.mass, P₁.sum_eq_one, P₂.sum_eq_one, one_mul]

/-- Mass of the product posterior. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem prodDistr_mass (P₁ : Distr Ω₁) (P₂ : Distr Ω₂) (ω : Ω₁ × Ω₂) :
    (prodDistr P₁ P₂).mass ω = P₁.mass ω.1 * P₂.mass ω.2 := rfl

/-- **An additively separable value table** over a product option set:
`V((ω₁, ω₂), (a₁, a₂)) = V₁ ω₁ a₁ + V₂ ω₂ a₂` — the `π`-side and the `ρ`-side of the decision
do not interact. This is the hypothesis the source's "general case" needs (F-1).
Source: [[corr-power-channel-findings]] F-1 ("nearest well-posed version"); power-wisdom-final.md
S2 (l. 103)
Kind: D
Fidelity: exact -/
def sepV (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ) : Ω₁ × Ω₂ → A₁ × A₂ → ℝ :=
  fun ω a => V₁ ω.1 a.1 + V₂ ω.2 a.2

/-- Value of a separable table. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
@[simp] theorem sepV_apply (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ) (ω : Ω₁ × Ω₂) (a : A₁ × A₂) :
    sepV V₁ V₂ ω a = V₁ ω.1 a.1 + V₂ ω.2 a.2 := rfl

/-- `sup'` over a product set of a function that splits as `f a₁ + g a₂` is the sum of the two
`sup'`s. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sup'_prod_add {B₁ : Finset A₁} {B₂ : Finset A₂} (h₁ : B₁.Nonempty) (h₂ : B₂.Nonempty)
    (F : A₁ × A₂ → ℝ) (f : A₁ → ℝ) (g : A₂ → ℝ) (hF : ∀ a, F a = f a.1 + g a.2) :
    (B₁ ×ˢ B₂).sup' (h₁.product h₂) F = B₁.sup' h₁ f + B₂.sup' h₂ g := by
  apply le_antisymm
  · rw [sup'_le_iff]
    intro a ha
    rw [mem_product] at ha
    rw [hF a]
    exact add_le_add (le_sup' f ha.1) (le_sup' g ha.2)
  · obtain ⟨a₁, ha₁, e₁⟩ := exists_mem_eq_sup' h₁ f
    obtain ⟨a₂, ha₂, e₂⟩ := exists_mem_eq_sup' h₂ g
    rw [e₁, e₂, ← hF (a₁, a₂)]
    exact le_sup' F (mem_product.2 ⟨ha₁, ha₂⟩)

/-- The mixture value of a separable table under the product posterior splits.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem mixValue_sep (P₁ : Distr Ω₁) (P₂ : Distr Ω₂) (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ)
    (a : A₁ × A₂) :
    mixValue (prodDistr P₁ P₂) (sepV V₁ V₂) a = mixValue P₁ V₁ a.1 + mixValue P₂ V₂ a.2 := by
  have e : mixValue P₁ V₁ a.1 + mixValue P₂ V₂ a.2 =
      (∑ ω₁, P₁.mass ω₁ * V₁ ω₁ a.1) * (∑ ω₂, P₂.mass ω₂) +
        (∑ ω₁, P₁.mass ω₁) * (∑ ω₂, P₂.mass ω₂ * V₂ ω₂ a.2) := by
    simp only [mixValue, expect, P₁.sum_eq_one, P₂.sum_eq_one, mul_one, one_mul]
  rw [e, sum_mul_sum, sum_mul_sum, ← sum_add_distrib]
  unfold mixValue expect
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun ω₁ _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun ω₂ _ => ?_
  simp only [prodDistr_mass, sepV_apply]
  ring

/-- `bestMix` of a separable table on a product option set is the sum of the two.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem bestMix_sep (P₁ : Distr Ω₁) (P₂ : Distr Ω₂) (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ)
    {B₁ : Finset A₁} {B₂ : Finset A₂} (h₁ : B₁.Nonempty) (h₂ : B₂.Nonempty) :
    bestMix (prodDistr P₁ P₂) (sepV V₁ V₂) (B₁ ×ˢ B₂) (h₁.product h₂) =
      bestMix P₁ V₁ B₁ h₁ + bestMix P₂ V₂ B₂ h₂ := by
  unfold bestMix
  exact sup'_prod_add h₁ h₂ _ _ _ (fun a => mixValue_sep P₁ P₂ V₁ V₂ a)

/-- The attainable value of a separable table splits pointwise.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem attainable_sep (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ) {B₁ : Finset A₁} {B₂ : Finset A₂}
    (h₁ : B₁.Nonempty) (h₂ : B₂.Nonempty) (ω : Ω₁ × Ω₂) :
    attainable (sepV V₁ V₂) (B₁ ×ˢ B₂) (h₁.product h₂) ω =
      attainable V₁ B₁ h₁ ω.1 + attainable V₂ B₂ h₂ ω.2 := by
  unfold attainable
  exact sup'_prod_add h₁ h₂ _ _ _ (fun a => rfl)

/-- Expectation of a sum of one-sided functions under the product posterior.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem expect_prodDistr_add (P₁ : Distr Ω₁) (P₂ : Distr Ω₂) (f : Ω₁ → ℝ) (g : Ω₂ → ℝ) :
    expect (prodDistr P₁ P₂) (fun ω => f ω.1 + g ω.2) = expect P₁ f + expect P₂ g := by
  have e : expect P₁ f + expect P₂ g =
      (∑ ω₁, P₁.mass ω₁ * f ω₁) * (∑ ω₂, P₂.mass ω₂) +
        (∑ ω₁, P₁.mass ω₁) * (∑ ω₂, P₂.mass ω₂ * g ω₂) := by
    simp only [expect, P₁.sum_eq_one, P₂.sum_eq_one, mul_one, one_mul]
  rw [e, sum_mul_sum, sum_mul_sum, ← sum_add_distrib]
  unfold expect
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun ω₁ _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun ω₂ _ => ?_
  simp only [prodDistr_mass]
  ring

/-- `POWER` of a separable table under the product posterior is the sum of the two.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem power_sep (P₁ : Distr Ω₁) (P₂ : Distr Ω₂) (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ)
    {B₁ : Finset A₁} {B₂ : Finset A₂} (h₁ : B₁.Nonempty) (h₂ : B₂.Nonempty) :
    power (prodDistr P₁ P₂) (sepV V₁ V₂) (B₁ ×ˢ B₂) (h₁.product h₂) =
      power P₁ V₁ B₁ h₁ + power P₂ V₂ B₂ h₂ := by
  unfold power
  rw [show attainable (sepV V₁ V₂) (B₁ ×ˢ B₂) (h₁.product h₂) =
      fun ω => attainable V₁ B₁ h₁ ω.1 + attainable V₂ B₂ h₂ ω.2 from
    funext (attainable_sep V₁ V₂ h₁ h₂)]
  exact expect_prodDistr_add P₁ P₂ _ _

/-- **`EVPI` is additive over a separable decision**: `EVPI(B₁ × B₂) = EVPI₁(B₁) + EVPI₂(B₂)`.
Source: [[corr-power-channel-findings]] F-1 (nearest well-posed version); power-wisdom-final.md
D12 (l. 61)
Kind: P
Fidelity: exact
Hyps: (a) none (separability is the shape of the objects) -/
theorem evpi_sep (P₁ : Distr Ω₁) (P₂ : Distr Ω₂) (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ)
    {B₁ : Finset A₁} {B₂ : Finset A₂} (h₁ : B₁.Nonempty) (h₂ : B₂.Nonempty) :
    evpi (prodDistr P₁ P₂) (sepV V₁ V₂) (B₁ ×ˢ B₂) (h₁.product h₂) =
      evpi P₁ V₁ B₁ h₁ + evpi P₂ V₂ B₂ h₂ := by
  unfold evpi
  rw [power_sep P₁ P₂ V₁ V₂ h₁ h₂, bestMix_sep P₁ P₂ V₁ V₂ h₁ h₂]
  ring

/-- The signal gain of a `π`-only channel on a separable table: the `π`-part's signal gain plus the
signal's mass times the `ρ`-part's mixture value.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem inner_sep_fst {S : Type} [Fintype S] (P₁ : Distr Ω₁) (P₂ : Distr Ω₂)
    (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ) (q₁ : Experiment Ω₁ S) (s : S) (a : A₁ × A₂) :
    ∑ ω : Ω₁ × Ω₂, (prodDistr P₁ P₂).mass ω * (expComap Prod.fst q₁).k ω s * sepV V₁ V₂ ω a =
      (∑ ω₁, P₁.mass ω₁ * q₁.k ω₁ s * V₁ ω₁ a.1) +
        (∑ ω₁, P₁.mass ω₁ * q₁.k ω₁ s) * mixValue P₂ V₂ a.2 := by
  have e : (∑ ω₁, P₁.mass ω₁ * q₁.k ω₁ s * V₁ ω₁ a.1) +
      (∑ ω₁, P₁.mass ω₁ * q₁.k ω₁ s) * mixValue P₂ V₂ a.2 =
      (∑ ω₁, P₁.mass ω₁ * q₁.k ω₁ s * V₁ ω₁ a.1) * (∑ ω₂, P₂.mass ω₂) +
        (∑ ω₁, P₁.mass ω₁ * q₁.k ω₁ s) * (∑ ω₂, P₂.mass ω₂ * V₂ ω₂ a.2) := by
    simp only [mixValue, expect, P₂.sum_eq_one, mul_one]
  rw [e, sum_mul_sum, sum_mul_sum, ← sum_add_distrib, Fintype.sum_prod_type]
  refine sum_congr rfl fun ω₁ _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun ω₂ _ => ?_
  simp only [prodDistr_mass, expComap_k, sepV_apply]
  ring

/-- The signal gain of a `ρ`-only channel on a separable table (mirror of `inner_sep_fst`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem inner_sep_snd {T : Type} [Fintype T] (P₁ : Distr Ω₁) (P₂ : Distr Ω₂)
    (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ) (q₂ : Experiment Ω₂ T) (t : T) (a : A₁ × A₂) :
    ∑ ω : Ω₁ × Ω₂, (prodDistr P₁ P₂).mass ω * (expComap Prod.snd q₂).k ω t * sepV V₁ V₂ ω a =
      (∑ ω₂, P₂.mass ω₂ * q₂.k ω₂ t) * mixValue P₁ V₁ a.1 +
        (∑ ω₂, P₂.mass ω₂ * q₂.k ω₂ t * V₂ ω₂ a.2) := by
  have e : (∑ ω₂, P₂.mass ω₂ * q₂.k ω₂ t) * mixValue P₁ V₁ a.1 +
      (∑ ω₂, P₂.mass ω₂ * q₂.k ω₂ t * V₂ ω₂ a.2) =
      (∑ ω₁, P₁.mass ω₁ * V₁ ω₁ a.1) * (∑ ω₂, P₂.mass ω₂ * q₂.k ω₂ t) +
        (∑ ω₁, P₁.mass ω₁) * (∑ ω₂, P₂.mass ω₂ * q₂.k ω₂ t * V₂ ω₂ a.2) := by
    simp only [mixValue, expect, P₁.sum_eq_one, one_mul]
    ring
  rw [e, sum_mul_sum, sum_mul_sum, ← sum_add_distrib, Fintype.sum_prod_type]
  refine sum_congr rfl fun ω₁ _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun ω₂ _ => ?_
  simp only [prodDistr_mass, expComap_k, sepV_apply]
  ring

/-- The signal masses of a channel sum to one: `∑ s, ∑ ω, P ω · k ω s = 1`.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem sum_signal_mass {Ω S : Type} [Fintype Ω] [Fintype S] (P : Distr Ω) (k : Experiment Ω S) :
    ∑ s, ∑ ω, P.mass ω * k.k ω s = 1 := by
  rw [sum_comm]
  simp only [← mul_sum, experiment_row_sum, mul_one]
  exact P.sum_eq_one

/-- **A `π`-only channel is worth, on the separable decision, exactly what it is worth on the
`π`-problem**: `VOI(expComap fst q₁) = VOI₁(q₁)`. On every signal the `ρ`-coordinate is chosen on
the prior, so the `ρ`-side contributes `bestMix₂` both to the informed value and to the baseline.
Source: [[corr-power-channel-findings]] F-1 (nearest well-posed version); power-wisdom-final.md
D16 (l. 73, "`q` uninformative about `ρ`")
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem voiExp_sep_fst {S : Type} [Fintype S] (P₁ : Distr Ω₁) (P₂ : Distr Ω₂)
    (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ) (q₁ : Experiment Ω₁ S) {B₁ : Finset A₁}
    {B₂ : Finset A₂} (h₁ : B₁.Nonempty) (h₂ : B₂.Nonempty) :
    voiExp (prodDistr P₁ P₂) (sepV V₁ V₂) (expComap Prod.fst q₁) (B₁ ×ˢ B₂) (h₁.product h₂) =
      voiExp P₁ V₁ q₁ B₁ h₁ := by
  unfold voiExp
  rw [bestMix_sep P₁ P₂ V₁ V₂ h₁ h₂]
  have hs : ∀ s, (B₁ ×ˢ B₂).sup' (h₁.product h₂)
      (fun b => ∑ ω, (prodDistr P₁ P₂).mass ω * (expComap Prod.fst q₁).k ω s * sepV V₁ V₂ ω b) =
      B₁.sup' h₁ (fun b => ∑ ω₁, P₁.mass ω₁ * q₁.k ω₁ s * V₁ ω₁ b) +
        (∑ ω₁, P₁.mass ω₁ * q₁.k ω₁ s) * bestMix P₂ V₂ B₂ h₂ := by
    intro s
    rw [sup'_prod_add h₁ h₂ _ (fun b => ∑ ω₁, P₁.mass ω₁ * q₁.k ω₁ s * V₁ ω₁ b)
      (fun b => (∑ ω₁, P₁.mass ω₁ * q₁.k ω₁ s) * mixValue P₂ V₂ b)
      (fun a => inner_sep_fst P₁ P₂ V₁ V₂ q₁ s a)]
    rw [sup'_const_mul h₂ (sum_nonneg fun ω₁ _ =>
      mul_nonneg (P₁.nonneg ω₁) (experiment_nonneg q₁ ω₁ s))]
    rfl
  simp only [hs]
  rw [sum_add_distrib, ← sum_mul, sum_signal_mass, one_mul]
  ring

/-- **A `ρ`-only channel is worth exactly what it is worth on the `ρ`-problem**:
`VOI(expComap snd q₂) = VOI₂(q₂)` (mirror of `voiExp_sep_fst`).
Source: [[corr-power-channel-findings]] F-1; power-wisdom-final.md D16 (l. 73)
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem voiExp_sep_snd {T : Type} [Fintype T] (P₁ : Distr Ω₁) (P₂ : Distr Ω₂)
    (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ) (q₂ : Experiment Ω₂ T) {B₁ : Finset A₁}
    {B₂ : Finset A₂} (h₁ : B₁.Nonempty) (h₂ : B₂.Nonempty) :
    voiExp (prodDistr P₁ P₂) (sepV V₁ V₂) (expComap Prod.snd q₂) (B₁ ×ˢ B₂) (h₁.product h₂) =
      voiExp P₂ V₂ q₂ B₂ h₂ := by
  unfold voiExp
  rw [bestMix_sep P₁ P₂ V₁ V₂ h₁ h₂]
  have hs : ∀ t, (B₁ ×ˢ B₂).sup' (h₁.product h₂)
      (fun b => ∑ ω, (prodDistr P₁ P₂).mass ω * (expComap Prod.snd q₂).k ω t * sepV V₁ V₂ ω b) =
      (∑ ω₂, P₂.mass ω₂ * q₂.k ω₂ t) * bestMix P₁ V₁ B₁ h₁ +
        B₂.sup' h₂ (fun b => ∑ ω₂, P₂.mass ω₂ * q₂.k ω₂ t * V₂ ω₂ b) := by
    intro t
    rw [sup'_prod_add h₁ h₂ _ (fun b => (∑ ω₂, P₂.mass ω₂ * q₂.k ω₂ t) * mixValue P₁ V₁ b)
      (fun b => ∑ ω₂, P₂.mass ω₂ * q₂.k ω₂ t * V₂ ω₂ b)
      (fun a => inner_sep_snd P₁ P₂ V₁ V₂ q₂ t a)]
    rw [sup'_const_mul h₁ (sum_nonneg fun ω₂ _ =>
      mul_nonneg (P₂.nonneg ω₂) (experiment_nonneg q₂ ω₂ t))]
    rfl
  simp only [hs]
  rw [sum_add_distrib, ← sum_mul, sum_signal_mass, one_mul]
  ring

/-- The `ρ`-coordinate's revealing experiment `ofMap Prod.snd` is the perfect experiment on `Ω₂`
read on the product. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem ofMap_snd_eq_comap_perfect [DecidableEq Ω₂] :
    (ofMap Prod.snd : Experiment (Ω₁ × Ω₂) Ω₂) = expComap Prod.snd perfectExp := rfl

/-- **The value of the `ρ`-component alone is `EVPI₂`** on a separable decision:
`VOI(ofMap snd) = EVPI₂(B₂)`.
Source: power-wisdom-final.md S2 (l. 103, "`VOI_t(ρ)`"), P2 (l. 159, "`EVPI^ρ_t`")
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem voiExp_rho_sep [DecidableEq Ω₂] (P₁ : Distr Ω₁) (P₂ : Distr Ω₂) (V₁ : Ω₁ → A₁ → ℝ)
    (V₂ : Ω₂ → A₂ → ℝ) {B₁ : Finset A₁} {B₂ : Finset A₂} (h₁ : B₁.Nonempty) (h₂ : B₂.Nonempty) :
    voiExp (prodDistr P₁ P₂) (sepV V₁ V₂) (ofMap Prod.snd) (B₁ ×ˢ B₂) (h₁.product h₂) =
      evpi P₂ V₂ B₂ h₂ := by
  rw [ofMap_snd_eq_comap_perfect, voiExp_sep_snd P₁ P₂ V₁ V₂ perfectExp h₁ h₂,
    voiExp_perfect_eq_evpi P₂ V₂ h₂]

/-- **The structural gap under separability, exact: `VOI(s | q) = (EVPI₁ − VOI₁(q₁)) + EVPI₂`**
for a perfect scan `s` and any `π`-only channel `q = expComap fst q₁`. The first bracket is the
residual the channel leaves on the `π`-side; the second is the whole `ρ`-side. The proof is three
named rewrites (`voiExp_prod_perfect_eq_evpi`, `evpi_sep`, `voiExp_sep_fst`) and `ring`: the
content is in `voiExp_sep_fst` and `evpi_sep` (both P); this identity is their composition.
Source: power-wisdom-final.md S2 (l. 103, "General case"), D16 (l. 73), P2 (l. 159); the
nearest well-posed version of the refuted unrestricted claim ([[corr-power-channel-findings]] F-1)
Kind: C
Fidelity: variant: the source's claim with the separability hypothesis (product posterior,
product option set, additive values, `π`-only channel) that it needs — without it the claim is
false (`gap_counterexample`)
Hyps: (a) none -/
theorem voiExp_marginal_sep_eq [DecidableEq Ω₁] [DecidableEq Ω₂] {S : Type} [Fintype S]
    (P₁ : Distr Ω₁) (P₂ : Distr Ω₂) (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ)
    (q₁ : Experiment Ω₁ S) {B₁ : Finset A₁} {B₂ : Finset A₂} (h₁ : B₁.Nonempty)
    (h₂ : B₂.Nonempty) :
    voiExp (prodDistr P₁ P₂) (sepV V₁ V₂) (expProd (expComap Prod.fst q₁) perfectExp) (B₁ ×ˢ B₂)
        (h₁.product h₂) -
      voiExp (prodDistr P₁ P₂) (sepV V₁ V₂) (expComap Prod.fst q₁) (B₁ ×ˢ B₂) (h₁.product h₂) =
      (evpi P₁ V₁ B₁ h₁ - voiExp P₁ V₁ q₁ B₁ h₁) + evpi P₂ V₂ B₂ h₂ := by
  rw [voiExp_prod_perfect_eq_evpi _ _ _ (h₁.product h₂), evpi_sep P₁ P₂ V₁ V₂ h₁ h₂,
    voiExp_sep_fst P₁ P₂ V₁ V₂ q₁ h₁ h₂]
  ring

/-- **The mandate's `voiExp_marginal_ge_rho`, under separability: `VOI(s | q) ≥ VOI(ρ-component)`
for every `π`-only channel `q₁`, including the perfect one (`δ = 0`, where it is an equality).**
The `ρ`-component's value is `voiExp … (ofMap Prod.snd) …` — the same object `gap_counterexample`
uses — and equals `EVPI₂`. The slack is `EVPI₁ − VOI₁(q₁) ≥ 0` (`voiExp_le_evpi`). Content
boundary: at a perfect `q₁` (`δ = 0`) the inequality is an equality (`marginal_sep_perfect`), so
S2's "`> 0` for every `δ`" is precisely the hypothesis `0 < EVPI₂`; with a singleton `B₂` it
collapses to `voiExp_le_evpi` on the `π`-problem (`marginal_sep_singleton`); it says something
beyond its ingredients only when both sides are live, as in `e3rho_marginal` (`σ > 0`, `n ≥ 1`).
Source: power-wisdom-final.md S2 (l. 103, "`VOI_t(s | q) ≥ VOI_t(ρ)` for every `δ`"),
P2 (l. 159); [[corr-power-channel-mandate]] T4(b) (`voiExp_marginal_ge_rho`)
Kind: C
Fidelity: variant: with the separability hypothesis the source omits (see
`voiExp_marginal_sep_eq`); the "`> 0`" clause of S2 is `0 < EVPI₂`, i.e. the `ρ`-side is
decision-relevant, not a theorem
Hyps: (a) none -/
theorem voiExp_marginal_ge_rho_sep [DecidableEq Ω₁] [DecidableEq Ω₂] {S : Type} [Fintype S]
    (P₁ : Distr Ω₁) (P₂ : Distr Ω₂) (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ)
    (q₁ : Experiment Ω₁ S) {B₁ : Finset A₁} {B₂ : Finset A₂} (h₁ : B₁.Nonempty)
    (h₂ : B₂.Nonempty) :
    voiExp (prodDistr P₁ P₂) (sepV V₁ V₂) (ofMap Prod.snd) (B₁ ×ˢ B₂) (h₁.product h₂) ≤
      voiExp (prodDistr P₁ P₂) (sepV V₁ V₂) (expProd (expComap Prod.fst q₁) perfectExp)
          (B₁ ×ˢ B₂) (h₁.product h₂) -
        voiExp (prodDistr P₁ P₂) (sepV V₁ V₂) (expComap Prod.fst q₁) (B₁ ×ˢ B₂)
          (h₁.product h₂) := by
  rw [voiExp_marginal_sep_eq P₁ P₂ V₁ V₂ q₁ h₁ h₂, voiExp_rho_sep P₁ P₂ V₁ V₂ h₁ h₂]
  linarith [voiExp_le_evpi P₁ V₁ q₁ h₁]

/-- **At `δ = 0` (a perfect `π`-channel) the separable marginal is exactly `EVPI₂`**:
`VOI(s | q) = VOI(ρ)`, so S2's "`> 0` for every `δ`" is precisely the hypothesis `0 < EVPI₂`.
Source: power-wisdom-final.md S2 (l. 103); [[corr-power-channel-audit-r2-adversarial]] N6
(probe `SepBoundary.lean`, lifted)
Kind: L
Fidelity: exact (the boundary cell of `voiExp_marginal_ge_rho_sep`)
Hyps: (a) none -/
theorem marginal_sep_perfect [DecidableEq Ω₁] [DecidableEq Ω₂] (P₁ : Distr Ω₁) (P₂ : Distr Ω₂)
    (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ) {B₁ : Finset A₁} {B₂ : Finset A₂} (h₁ : B₁.Nonempty)
    (h₂ : B₂.Nonempty) :
    voiExp (prodDistr P₁ P₂) (sepV V₁ V₂) (expProd (expComap Prod.fst perfectExp) perfectExp)
          (B₁ ×ˢ B₂) (h₁.product h₂) -
        voiExp (prodDistr P₁ P₂) (sepV V₁ V₂) (expComap Prod.fst perfectExp) (B₁ ×ˢ B₂)
          (h₁.product h₂) =
      voiExp (prodDistr P₁ P₂) (sepV V₁ V₂) (ofMap Prod.snd) (B₁ ×ˢ B₂) (h₁.product h₂) := by
  rw [voiExp_marginal_sep_eq P₁ P₂ V₁ V₂ perfectExp h₁ h₂, voiExp_rho_sep P₁ P₂ V₁ V₂ h₁ h₂,
    voiExp_perfect_eq_evpi P₁ V₁ h₁]
  ring

/-- **With a trivial `ρ`-side the theorem reduces to `voiExp_le_evpi` on the `π`-problem**:
`VOI(ρ) = 0` and the marginal is `EVPI₁ − VOI₁(q₁)`.
Source: [[corr-power-channel-audit-r2-adversarial]] N6 (probe `SepBoundary.lean`, lifted)
Kind: L
Fidelity: exact (the other boundary cell of `voiExp_marginal_ge_rho_sep`)
Hyps: (a) none -/
theorem marginal_sep_singleton [DecidableEq Ω₁] [DecidableEq Ω₂] {S : Type} [Fintype S]
    (P₁ : Distr Ω₁) (P₂ : Distr Ω₂) (V₁ : Ω₁ → A₁ → ℝ) (V₂ : Ω₂ → A₂ → ℝ) (q₁ : Experiment Ω₁ S)
    {B₁ : Finset A₁} (h₁ : B₁.Nonempty) (b : A₂) :
    voiExp (prodDistr P₁ P₂) (sepV V₁ V₂) (ofMap Prod.snd) (B₁ ×ˢ {b})
        (h₁.product (singleton_nonempty b)) = 0 ∧
      voiExp (prodDistr P₁ P₂) (sepV V₁ V₂) (expProd (expComap Prod.fst q₁) perfectExp)
            (B₁ ×ˢ {b}) (h₁.product (singleton_nonempty b)) -
          voiExp (prodDistr P₁ P₂) (sepV V₁ V₂) (expComap Prod.fst q₁) (B₁ ×ˢ {b})
            (h₁.product (singleton_nonempty b)) =
        evpi P₁ V₁ B₁ h₁ - voiExp P₁ V₁ q₁ B₁ h₁ := by
  refine ⟨?_, ?_⟩
  · rw [voiExp_rho_sep P₁ P₂ V₁ V₂ h₁ (singleton_nonempty b), evpi_singleton]
  · rw [voiExp_marginal_sep_eq P₁ P₂ V₁ V₂ q₁ h₁ (singleton_nonempty b), evpi_singleton]
    ring

end Separable

/-! ## The mandate's instance: E3 × a uniform `ρ` with a bet at stake `σ` -/

section Instance

/-- **The bet on `ρ`**: `ρ` uniform on `Fin (m+1)`, option `i` worth `σ·𝟙[i = ρ]` — the
`ρ`-dependent options "of positive residual" of the source's general case.
Source: [[corr-power-channel-mandate]] T4(b) ("`ρ` uniform on `Fin m` at stake `σ`")
Kind: D
Fidelity: exact (indexed by `m+1` values so that `m ≥ 1` is automatic) -/
def betV (m : ℕ) (σ : ℝ) : Fin (m + 1) → Fin (m + 1) → ℝ := fun ρ i => σ * if ρ = i then 1 else 0

/-- Mass of the uniform law on `Fin (m+1)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem uniform_mass_fin_succ (m : ℕ) (ρ : Fin (m + 1)) :
    (Distr.uniform : Distr (Fin (m + 1))).mass ρ = ((m : ℝ) + 1)⁻¹ := by
  simp [Distr.uniform]

/-- The attainable value of the bet is `σ` under every `ρ` (`σ ≥ 0`).
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem bet_attainable (m : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) (ρ : Fin (m + 1)) :
    attainable (betV m σ) univ univ_nonempty ρ = σ := by
  unfold attainable
  exact sup'_univ_scaled_indicator hσ ρ

/-- `POWER(bet) = σ`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem bet_power (m : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    power (Distr.uniform : Distr (Fin (m + 1))) (betV m σ) univ univ_nonempty = σ := by
  unfold power
  rw [show attainable (betV m σ) univ univ_nonempty = fun _ => σ from funext (bet_attainable m hσ)]
  exact expect_const _ σ

/-- The mixture value of every bet is `σ/(m+1)`. Source: none: infrastructure. Kind: L.
Fidelity: n/a -/
theorem bet_mixValue (m : ℕ) (σ : ℝ) (i : Fin (m + 1)) :
    mixValue (Distr.uniform : Distr (Fin (m + 1))) (betV m σ) i = σ * ((m : ℝ) + 1)⁻¹ := by
  unfold mixValue expect
  simp only [betV, uniform_mass_fin_succ]
  rw [sum_eq_single i]
  · rw [if_pos rfl]; ring
  · intro ρ _ hρ; simp [hρ]
  · intro h; exact absurd (mem_univ i) h

/-- `bestMix(bet) = σ/(m+1)`. Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem bet_bestMix (m : ℕ) (σ : ℝ) :
    bestMix (Distr.uniform : Distr (Fin (m + 1))) (betV m σ) univ univ_nonempty =
      σ * ((m : ℝ) + 1)⁻¹ := by
  unfold bestMix
  rw [show mixValue (Distr.uniform : Distr (Fin (m + 1))) (betV m σ) = fun _ => σ * ((m : ℝ) + 1)⁻¹
    from funext (bet_mixValue m σ)]
  exact sup'_const _ _

/-- **`EVPI` of the bet on a uniform `ρ ∈ Fin (m+1)` at stake `σ ≥ 0` is `σ(1 − 1/(m+1))`** — the
`ρ`-component's value in the mandate's instance.
Source: [[corr-power-channel-mandate]] T4(b) ("`σ(1 − 1/m)`")
Kind: P
Fidelity: exact (indexed by `m+1`)
Hyps: (a) `0 ≤ σ` -/
theorem bet_evpi (m : ℕ) {σ : ℝ} (hσ : 0 ≤ σ) :
    evpi (Distr.uniform : Distr (Fin (m + 1))) (betV m σ) univ univ_nonempty =
      σ * (1 - ((m : ℝ) + 1)⁻¹) := by
  unfold evpi
  rw [bet_power m hσ, bet_bestMix]
  ring

/-- **The mandate's instance (T4(b)): on E3 at `n+1` plans joined with a uniform `ρ ∈ Fin (m+1)`
and a bet at stake `σ ≥ 0` — `Ω = (Fin (n+1) × Bool) × Fin (m+1)` (`π`, `mind`, `ρ`),
`P = (uniform ⊗ (1−μ, μ)) ⊗ uniform`, options `(plan j, bet i)` worth `𝟙[j = π] + σ·𝟙[i = ρ]`,
the channel `q = e3Q` on the `π`-side, the scan perfect — the marginal is
`VOI(s | q) = δ(1 − 1/(n+1)) + σ(1 − 1/(m+1))`, and `VOI(ρ) = σ(1 − 1/(m+1))`.** At `δ = 0` the
marginal is exactly `VOI(ρ)`; for `σ > 0` the `ρ`-side keeps the scan's marginal value positive
at every `δ`, which is the brain-reader point the source makes.
Source: [[corr-power-channel-mandate]] T4(b) ("the instance `VOI(s | q) = δ(1 − 1/n) + σ(1 − 1/m)`");
power-wisdom-final.md S2 (l. 103), P2 (l. 159)
Kind: N+
Fidelity: exact (indexed by `n+1` plans and `m+1` values of `ρ`; the scan here is the perfect
experiment on `(π, mind, ρ)` — with the mandate's `(π, ρ)`-scan the marginal is the same number,
`e3rho_marginal_piRho`, proved in repair round 2 via `voiExp_ofMap_eq_evpi_of_factors`)
Hyps: (a) `0 ≤ σ` -/
theorem e3rho_marginal (n m : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h δ : ℝ)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) {σ : ℝ} (hσ : 0 ≤ σ) :
    voiExp (prodDistr (e3P n μ hμ) (Distr.uniform : Distr (Fin (m + 1))))
          (sepV (e3V n h) (betV m σ)) (expProd (expComap Prod.fst (e3Q n δ hδ)) perfectExp)
          (e3Plans n ×ˢ univ) ((e3Plans_nonempty n).product univ_nonempty) -
        voiExp (prodDistr (e3P n μ hμ) (Distr.uniform : Distr (Fin (m + 1))))
          (sepV (e3V n h) (betV m σ)) (expComap Prod.fst (e3Q n δ hδ))
          (e3Plans n ×ˢ univ) ((e3Plans_nonempty n).product univ_nonempty) =
        δ * (1 - ((n : ℝ) + 1)⁻¹) + σ * (1 - ((m : ℝ) + 1)⁻¹) ∧
      voiExp (prodDistr (e3P n μ hμ) (Distr.uniform : Distr (Fin (m + 1))))
          (sepV (e3V n h) (betV m σ)) (ofMap Prod.snd)
          (e3Plans n ×ˢ univ) ((e3Plans_nonempty n).product univ_nonempty) =
        σ * (1 - ((m : ℝ) + 1)⁻¹) := by
  refine ⟨?_, ?_⟩
  · rw [voiExp_marginal_sep_eq _ _ _ _ _ (e3Plans_nonempty n) univ_nonempty, e3_evpi, e3_voiExp_q,
      bet_evpi m hσ]
    ring
  · rw [voiExp_rho_sep _ _ _ _ (e3Plans_nonempty n) univ_nonempty, bet_evpi m hσ]

/-! ### The instance with the mandate's own `(π, ρ)`-scan (repair round 2, adversarial N2) -/

/-- The `(π, ρ)` coordinates of an E3ρ world — the mandate's scan `s` reveals these and not
`mind`. Source: [[corr-power-channel-mandate]] T4(b). Kind: D. Fidelity: exact -/
def piRho (n m : ℕ) (ω : (E3Ω n) × Fin (m + 1)) : Fin (n + 1) × Fin (m + 1) := (ω.1.1, ω.2)

/-- On `plans ×ˢ univ` the E3ρ value table factors through `(π, ρ)`: `mind` is decision-irrelevant.
Source: none: infrastructure. Kind: L. Fidelity: n/a -/
theorem e3rho_factors (n m : ℕ) (h σ : ℝ) :
    ∀ a ∈ e3Plans n ×ˢ (univ : Finset (Fin (m + 1))), ∀ ω ω' : (E3Ω n) × Fin (m + 1),
      piRho n m ω = piRho n m ω' →
        sepV (e3V n h) (betV m σ) ω a = sepV (e3V n h) (betV m σ) ω' a := by
  rintro ⟨a1, a2⟩ ha ω ω' hf
  rw [mem_product] at ha
  obtain ⟨j, _, hj⟩ := mem_map.1 ha.1
  simp only [Function.Embedding.coeFn_mk] at hj
  subst hj
  simp only [piRho, Prod.mk.injEq] at hf
  simp only [sepV_apply, e3V_plan, betV, hf.1, hf.2]

/-- **The `(π, ρ)`-scan is worth `EVPI` on the E3ρ carrier** — the same as the perfect scan.
Source: [[corr-power-channel-mandate]] T4(b); [[corr-power-channel-audit-r2-adversarial]] N2
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem e3rho_scan_piRho_eq_evpi (n m : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h σ : ℝ) :
    voiExp (prodDistr (e3P n μ hμ) (Distr.uniform : Distr (Fin (m + 1))))
        (sepV (e3V n h) (betV m σ)) (ofMap (piRho n m))
        (e3Plans n ×ˢ univ) ((e3Plans_nonempty n).product univ_nonempty) =
      evpi (prodDistr (e3P n μ hμ) (Distr.uniform : Distr (Fin (m + 1))))
        (sepV (e3V n h) (betV m σ)) (e3Plans n ×ˢ univ)
        ((e3Plans_nonempty n).product univ_nonempty) :=
  voiExp_ofMap_eq_evpi_of_factors _ _ _ _ (e3rho_factors n m h σ)

/-- **The mandate's instance with the mandate's scan**: with `s` revealing `(π, ρ)` only, the
marginal `VOI(s | q)` is `δ(1 − 1/(n+1)) + σ(1 − 1/(m+1))`, exactly as with the perfect scan
(`e3rho_marginal`). Blackwell squeeze: `VOI(q, s_{πρ}) ≤ EVPI = VOI(s_{πρ})`. So the instance is
the mandate's, not a cousin: the round-1 caveat ("argued, not proved") is discharged.
Source: [[corr-power-channel-mandate]] T4(b) ("`s` reveals `(π, ρ)`"); power-wisdom-final.md S2
(l. 103), P2 (l. 159); [[corr-power-channel-audit-r2-adversarial]] N2 (probe lifted)
Kind: N+
Fidelity: exact (indexed by `n+1`, `m+1`; the scan is `ofMap (π, ρ)`)
Hyps: (a) `0 ≤ σ` -/
theorem e3rho_marginal_piRho (n m : ℕ) (μ : ℝ) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) (h δ : ℝ)
    (hδ : δ ∈ Set.Icc (0 : ℝ) 1) {σ : ℝ} (hσ : 0 ≤ σ) :
    voiExp (prodDistr (e3P n μ hμ) (Distr.uniform : Distr (Fin (m + 1))))
          (sepV (e3V n h) (betV m σ))
          (expProd (expComap Prod.fst (e3Q n δ hδ)) (ofMap (piRho n m)))
          (e3Plans n ×ˢ univ) ((e3Plans_nonempty n).product univ_nonempty) -
        voiExp (prodDistr (e3P n μ hμ) (Distr.uniform : Distr (Fin (m + 1))))
          (sepV (e3V n h) (betV m σ)) (expComap Prod.fst (e3Q n δ hδ))
          (e3Plans n ×ˢ univ) ((e3Plans_nonempty n).product univ_nonempty) =
      δ * (1 - ((n : ℝ) + 1)⁻¹) + σ * (1 - ((m : ℝ) + 1)⁻¹) := by
  have hprod : voiExp (prodDistr (e3P n μ hμ) (Distr.uniform : Distr (Fin (m + 1))))
      (sepV (e3V n h) (betV m σ))
      (expProd (expComap Prod.fst (e3Q n δ hδ)) (ofMap (piRho n m)))
      (e3Plans n ×ˢ univ) ((e3Plans_nonempty n).product univ_nonempty) =
      evpi (prodDistr (e3P n μ hμ) (Distr.uniform : Distr (Fin (m + 1))))
        (sepV (e3V n h) (betV m σ)) (e3Plans n ×ˢ univ)
        ((e3Plans_nonempty n).product univ_nonempty) := by
    apply le_antisymm (voiExp_le_evpi _ _ _ _)
    rw [← e3rho_scan_piRho_eq_evpi n m μ hμ h σ]
    exact voiExp_mono_blackwell _ _ (blackwellLE_right_prod _ _) _
  rw [hprod, ← voiExp_prod_perfect_eq_evpi _ _ (expComap Prod.fst (e3Q n δ hδ))
    ((e3Plans_nonempty n).product univ_nonempty)]
  exact (e3rho_marginal n m μ hμ h δ hδ hσ).1

end Instance

end

end Cleanroom.Corrigibility.CorrPowerChannel
