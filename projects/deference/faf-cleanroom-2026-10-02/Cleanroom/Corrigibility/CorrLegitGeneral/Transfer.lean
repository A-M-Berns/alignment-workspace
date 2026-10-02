import Cleanroom.Corrigibility.CorrLegitGeneral.Defs
import Cleanroom.Found.LitDdbFrames.Value
import Cleanroom.Lit.LitDdbAccuracyMm.Accuracy

/-!
# corr-legit-general — T1 and T5: the transfer theorems and the odds condition

Conditioning on `L` changes only the deferrer, so every finite-frame theorem of DDB transfers to
`π_L` (T1(b)): `L`-conditioned Total Trust ⟺ `L`-conditioned Value (Theorem 2.2) ⟺ the
hull-and-modestly-informed condition on the normalized legitimate deferrer (Theorem 4.1) ⟺
accuracy increase on every gsp measure (Theorem 3.2 via `totalTrust_iff_forall_totalTrustOn`);
and, because Theorem 3.2 is local in `X`, the accuracy equivalence survives localization to a
question `Q` — the one DDB equivalence that transfers to the local form without a new argument.
Every theorem needs the simplex point `(mass π L)⁻¹ • restrict π L`, reached through
`restrict_normalize_mem` under `0 < mass π L` and the homogeneity lemmas.

T5: the delegation value splits along `L`/`Lᶜ` (`delegation_split`), the legitimate part is
nonnegative under `L`-conditioned Value (`legitValue_gain_nonneg`, `_of_pos`), delegation is
rational iff the odds condition holds in product form (`delegation_iff_odds`, the split
rearranged — kind L, audit r1 B1), and under Value a non-losing illegitimate part suffices
(`delegation_of_legitValue_of_illegit_nonpos`). The witness is `WitnessesLeak.lean`'s ddb-I5.6
frame.
-/

namespace Cleanroom.Corrigibility.CorrLegitGeneral

open Finset Cleanroom.Found.LitDdbFrames Cleanroom.Corrigibility.CorrReflectFrames
  Cleanroom.Lit.LitDdbAccuracyMm

noncomputable section

set_option linter.unusedSectionVars false

variable {W C : Type} [Fintype W] [DecidableEq W] [Fintype C] [DecidableEq C]

/-! ## T1(b): the global transfer -/

/-- **Theorem 2.2 for `π_L`**: `L`-conditioned Total Trust ⟺ `L`-conditioned Value — the
legitimacy-conditioned Good's theorem. Transfer: both predicates are homogeneous in the deferrer
and `(mass π L)⁻¹ • restrict π L` is a simplex point under `0 < mass π L`.
Source: [[ddb]] I5.2(a) l. 128; [[mm]] I5.1 l. 146; [[legitimacy-general-final]] Statement 1 l. 43
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, `0 < mass π L` (the vacuity guard, Known issues 1) -/
theorem legitimizingTT_iff_legitValue {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    {L : Finset W} (hL : 0 < mass π L) : LegitimizingTT π F L ↔ LegitValue π F L := by
  have hc : (0 : ℝ) < (mass π L)⁻¹ := inv_pos.2 hL
  unfold LegitimizingTT LegitValue
  rw [← totalTrust_smul_iff hc, ← value_smul_iff hc, value_iff_totalTrust (restrict_normalize_mem hπ hL)]

/-- **Theorem 4.1 for `π_L`**: `L`-conditioned Total Trust ⟺ the normalized legitimate deferrer
lies in the convex hull of the legitimate candidates `C_{π_L} = {P_w : w ∈ L, π w > 0}`
(`cands_restrict`) and every legitimate candidate is modestly informed — a checkable criterion
in terms of the legitimate candidates only.
Source: [[ddb]] I5.2(c) l. 128; [[legitimacy-general-final]] Statement 1 l. 43
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, `0 < mass π L` -/
theorem legitimizingTT_iff_hullAndModestlyInformed {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    {L : Finset W} (hL : 0 < mass π L) :
    LegitimizingTT π F L ↔ HullAndModestlyInformed ((mass π L)⁻¹ • restrict π L) F := by
  unfold LegitimizingTT
  rw [← totalTrust_smul_iff (inv_pos.2 hL),
    totalTrust_iff_hullAndModestlyInformed (restrict_normalize_mem hπ hL)]

/-- **Theorem 3.2/5.1 for `π_L`**: `L`-conditioned Total Trust ⟺ conditional on `L` the
expert's estimate of every `X` is expected more accurate than the deferrer's on every gsp measure.
Source: [[ddb]] I5.2(b) l. 128; [[legitimacy-general-final]] Statement 1 l. 43
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, `0 < mass π L` -/
theorem legitimizingTT_iff_epistemicValue {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w) {F : Frame W}
    {L : Finset W} (hL : 0 < mass π L) :
    LegitimizingTT π F L ↔ ∀ X, EpistemicValueOn X ((mass π L)⁻¹ • restrict π L) F := by
  unfold LegitimizingTT
  rw [← totalTrust_smul_iff (inv_pos.2 hL), totalTrust_iff_forall_totalTrustOn]
  exact forall_congr' (fun X => totalTrustOn_iff_epistemicValueOn (restrict_normalize_mem hπ hL) F)

/-! ## T1(b), local: the accuracy equivalence survives localization -/

/-- Total Trust with respect to `Q` is the per-variable two-sided form on the `Q`-measurable
variables (`−X` is `Q`-measurable with `X`, which supplies the dual inequality).
Source: none: infrastructure (T1(b), via `totalTrust_iff_forall_totalTrustOn`)
Kind: L
Fidelity: exact -/
theorem totalTrustWrt_iff_forall_totalTrustOn {Q : W → C} {π : W → ℝ} {F : Frame W} :
    TotalTrustWrt Q π F ↔ ∀ X, MeasurableWrt Q X → TotalTrustOn X π F := by
  constructor
  · intro h X hX
    exact ⟨fun s => h X hX s, fun s => totalTrustWrt_iff_dual.1 h X hX s⟩
  · intro h X hX s
    exact (h X hX).1 s

/-- **Theorem 3.2 for `π_L`, localized**: `L`-conditioned Total Trust with respect to `Q` ⟺
conditional on `L`, the expert's estimate of every `Q`-measurable `X` is expected more accurate
on every gsp measure. Theorem 3.2 is local in `X`, so localization costs nothing — this is the
one DDB equivalence that transfers to the local criterion without a new argument (the Value
equivalence is T4).
Source: [[ddb]] I5.4 l. 130 ("Theorem 3.2 is local, so the accuracy equivalence survives");
[[legitimacy]] R5.1 l. 97
Kind: C
Fidelity: exact
Hyps: (a) `∀ w, 0 ≤ π w`, `0 < mass π L` -/
theorem legitTotalTrustWrt_iff_epistemicValueOn {Q : W → C} {π : W → ℝ} (hπ : ∀ w, 0 ≤ π w)
    {F : Frame W} {L : Finset W} (hL : 0 < mass π L) :
    LegitTotalTrustWrt Q π F L ↔
      ∀ X, MeasurableWrt Q X → EpistemicValueOn X ((mass π L)⁻¹ • restrict π L) F := by
  unfold LegitTotalTrustWrt
  rw [← totalTrustWrt_smul_iff (inv_pos.2 hL) Q, totalTrustWrt_iff_forall_totalTrustOn]
  exact forall_congr' (fun X => imp_congr_right
    (fun _ => totalTrustOn_iff_epistemicValueOn (restrict_normalize_mem hπ hL) F))

/-- Local legitimacy-conditioned Value is implied by the global one (restriction of menus).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem LegitValue.wrt {π : W → ℝ} {F : Frame W} {L : Finset W} (h : LegitValue π F L)
    (Q : W → C) : LegitValuesWrt Q π F L :=
  Value.wrt h Q

/-! ## T5: the odds condition -/

/-- The value of a strategy is additive in the deferrer.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem stratValue_add_left (π₁ π₂ : W → ℝ) (S : W → (W → ℝ)) :
    stratValue (π₁ + π₂) S = stratValue π₁ S + stratValue π₂ S := by
  simp only [stratValue, Pi.add_apply, add_mul, sum_add_distrib]

/-- **The delegation value splits along `L` and `Lᶜ`** (mm I5.2's decomposition in product
form): `E_π(S) − E_π(O) = (E_{π_L}(S) − E_{π_L}(O)) + (E_{π_{Lᶜ}}(S) − E_{π_{Lᶜ}}(O))`, where
`E_{π_L}` is the unnormalized `restrict` — the summands are `π(L) · E_π(S − O | L)` and
`π(Lᶜ) · E_π(S − O | Lᶜ)`.
Source: [[mm]] I5.2 l. 147; [[legitimacy]] R5.4 l. 101
Kind: L
Fidelity: exact (product form)
Hyps: (a) none -/
theorem delegation_split (π : W → ℝ) (L : Finset W) (S : W → (W → ℝ)) (o : W → ℝ) :
    stratValue π S - E π o =
      (stratValue (restrict π L) S - E (restrict π L) o) +
        (stratValue (restrict π Lᶜ) S - E (restrict π Lᶜ) o) := by
  have h := restrict_add_restrict_compl π L
  rw [compl_eq_univ_sdiff]
  conv_lhs => rw [← h]
  rw [stratValue_add_left, E_add_left]; ring

/-- Under `L`-conditioned Value the legitimate summand is nonnegative: for every recommended
strategy `S` and option `O`, `π(L) · E_π(S − O | L) ≥ 0`.
Source: [[mm]] I5.2 l. 147 ("Under conditional Value the first conditional expectation is ≥ 0")
Kind: L
Fidelity: exact -/
theorem legitValue_gain_nonneg {π : W → ℝ} {F : Frame W} {L : Finset W} (h : LegitValue π F L)
    {𝒪 : DecisionProblem W} (hne : 𝒪.Nonempty) {S : W → (W → ℝ)} (hS : F.Recommended 𝒪 S)
    {o : W → ℝ} (ho : o ∈ 𝒪) : 0 ≤ stratValue (restrict π L) S - E (restrict π L) o :=
  sub_nonneg.2 (h 𝒪 hne S hS o ho)

/-- **Delegation is rational iff the odds condition holds** (mm I5.2, product form): with `a`
the conditional gain on `L` and `b` the conditional loss on `Lᶜ`, characterized by the product
identities `π(L) · a = E_{π_L}(S) − E_{π_L}(O)` and `π(Lᶜ) · b = E_{π_{Lᶜ}}(O) − E_{π_{Lᶜ}}(S)`
(the ratio form `π(L)/π(Lᶜ) ≥ b/a` cross-multiplied, never a division), `E_π(O) ≤ E_π(S)` iff
`π(Lᶜ) · b ≤ π(L) · a`. This is `delegation_split` rearranged — bookkeeping, not a theorem about
Value (audit r1 B1: the earlier one-directional `delegation_of_odds` was this statement kinded
`C`). T5's content is the split together with `legitValue_gain_nonneg` and the two corollaries
below.
Source: [[mm]] I5.2 l. 147; [[legitimacy]] R5.4 l. 101 (the four-world instance)
Kind: L
Fidelity: exact (the split identity rearranged into the source's "iff")
Hyps: (a) the two product identities defining `a`, `b` -/
theorem delegation_iff_odds (π : W → ℝ) (L : Finset W) (S : W → (W → ℝ)) (o : W → ℝ) {a b : ℝ}
    (ha : mass π L * a = stratValue (restrict π L) S - E (restrict π L) o)
    (hb : mass π Lᶜ * b = E (restrict π Lᶜ) o - stratValue (restrict π Lᶜ) S) :
    E π o ≤ stratValue π S ↔ mass π Lᶜ * b ≤ mass π L * a := by
  have := delegation_split π L S o
  constructor <;> intro h <;> linarith

/-- **Under `L`-conditioned Value the conditional gain is nonnegative**: for a recommended `S`,
an option `O` of the menu and `0 < π(L)`, the `a` of the product identity satisfies `a ≥ 0` — so
in the odds condition only the illegitimate side `b` can be adverse: the condition is the price
of the illegitimate part.
Source: [[mm]] I5.2 l. 147 ("Under conditional Value the first conditional expectation is ≥ 0")
Kind: L (one Value instance plus a cancellation; re-kinded from C, audit r2 fidelity N6 / adversarial N3)
Fidelity: exact
Hyps: (a) `LegitValue π F L`, `F.Recommended 𝒪 S`, `o ∈ 𝒪`, `0 < mass π L`, the identity for
`a` -/
theorem legitValue_gain_nonneg_of_pos {π : W → ℝ} {F : Frame W} {L : Finset W}
    (h : LegitValue π F L) (hL : 0 < mass π L) {𝒪 : DecisionProblem W} (hne : 𝒪.Nonempty)
    {S : W → (W → ℝ)} (hS : F.Recommended 𝒪 S) {o : W → ℝ} (ho : o ∈ 𝒪) {a : ℝ}
    (ha : mass π L * a = stratValue (restrict π L) S - E (restrict π L) o) : 0 ≤ a := by
  have h0 := legitValue_gain_nonneg h hne hS ho
  rw [← ha] at h0
  exact le_of_mul_le_mul_left (by rw [mul_zero]; exact h0) hL

/-- **Delegation under `L`-conditioned Value when the illegitimate part does not lose**: if the
legitimate part values the recommended `S` (`LegitValue`) and on `Lᶜ` the strategy is worth at
least the option (`b ≤ 0` in product form), then `E_π(O) ≤ E_π(S)`. This is the one direction of
mm I5.2 with content: the split, the legitimate gain `≥ 0` from Value, and the illegitimate
side supplied as a hypothesis rather than defined into the conclusion.
Source: [[mm]] I5.2 l. 147; [[legitimacy]] R5.4 l. 101
Kind: L (one Value instance plus the split identity; re-kinded from C, audit r2 adversarial N3)
Fidelity: exact (sufficient condition; the general "iff" is `delegation_iff_odds`)
Hyps: (a) `LegitValue π F L`, `F.Recommended 𝒪 S`, `o ∈ 𝒪`; `E_{π_{Lᶜ}}(O) ≤ E_{π_{Lᶜ}}(S)` -/
theorem delegation_of_legitValue_of_illegit_nonpos {π : W → ℝ} {F : Frame W} {L : Finset W}
    (h : LegitValue π F L) {𝒪 : DecisionProblem W} (hne : 𝒪.Nonempty) {S : W → (W → ℝ)}
    (hS : F.Recommended 𝒪 S) {o : W → ℝ} (ho : o ∈ 𝒪)
    (hb : E (restrict π Lᶜ) o ≤ stratValue (restrict π Lᶜ) S) : E π o ≤ stratValue π S := by
  have h1 := legitValue_gain_nonneg h hne hS ho
  have h2 := delegation_split π L S o
  linarith

end

end Cleanroom.Corrigibility.CorrLegitGeneral
