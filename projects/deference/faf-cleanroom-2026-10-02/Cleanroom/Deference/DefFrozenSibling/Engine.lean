import Cleanroom.Deference.DefFrozenSibling.Tracking

/-!
# `def-frozen-sibling` · Engine: T3, the on-`G` engine on both sides

[[frozen-deliberation-deference-v6]] §5.5 ("On `G`, the quote is early-revealed truth:
`a_n ≈ₙ Y_n ≈ₙ 𝟙(P^{(n)})`") and T3 (the conditional tower `ccee(H⁺ → A)`), anson-020,
root-deference-040/041, lean-deference-022 — the squeeze family of [[AUDIT]] §3.3
(`conditional_tower` with its `hcarry`, `quote_is_truth_on_G`, `TS_on_G`) replaced by theorems
whose hypothesis is **settlement** (the carrier's `determinedA`/`determinedH`, from the ledger
construction) and whose conclusion carries the bound. Every on-`G` conclusion has the D3 shape
`AgreeAlong t x y` along an e.c. sub-fragment `G' = {n | t n = 0}` with `t` a `UnaryRuler` and
`hG : ∀ n, t n = 0 → Timely S ε n`; the whole-`G` forms take the fragment's own ruler as a
certificate and are labelled (c) (`*_ofCert`).

* **A-side, grade (a), no `hz`** (`engineA`): along `G'`, the predictor's expectation of the
  contract `𝔼^A_n(C_n)` — the published quote `a n` — agrees with its own price of the
  proposition `A_n(P^{(n)})`. Route: `gated_pin` in `A`'s process with `X = C_n` settled at `Y n`
  (`determinedA`) and `φ = P^{(n)}`, whose payout in every completed-theory world is `truthAt`
  (`truthAt_holds_A`), within `ε n → 0` of `Y n` on `G'` (the definition of `G`).
* **A-to-truth** (`engineA_truth`): along `G'`, `a n ≈ truthAt n` — T1 (`hz`) composed with the
  tolerance clause (root-deference-040's "early-revealed truth"; kind L over T1). The `hz`-free
  alternative `engineA_truth_ofPattern` needs the polarity pattern on `G'` to be e.c. (`hpat`), and
  is then `lic_provind` for `A` alone — finding F4: under `hpat` the quote is redundant.
* **H-side, the conditional tower** (`condTower_onG`): along `G'`, the advised reasoner's price of
  `P^{(n)}` agrees with its expectation of the quote item `𝔼^{H}_n(α_{0,n})` (the ledger LUV
  settled at `a n`, the source's `⌜a_n⌝`) — `gated_pin` in `Hplus`'s process with `X = α_{0,n}`
  settled at `a n` (`determinedH`) and `φ = P^{(n)}`, the gap `a n − truthAt n`
  vanishing along `G'` by `engineA_truth`. The only non-(a) hypothesis is T1's `hz`. **No
  `hcarry`.** The weighted form factors the weight (`condTower_onG_weighted`), which is idle on `G`
  (v6's own remark); it is not `def-lattice`'s `CondTower` (see the docstring).

No `hcons` hypothesis: the global non-vacuity of the shared process's theory is derived from the
carrier's `hworldA` by FAF's compactness (`FrozenSystem.base_theoryWorld`).
-/

namespace Cleanroom.Deference.DefFrozenSibling

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefTrackingPin
open Filter Topology

/-- The shared process's theory is non-vacuous: one world is consistent with every stage of
`base` (FAF's compactness on `hworldA`, restricted through `shared`). This is the mandate's
`hcons`, derived rather than assumed.
Source: mandate D2 (`hcons`); FAF `DeductiveProcess.exists_consistentWithTheory`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem FrozenSystem.base_theoryWorld (S : FrozenSystem) :
    ∃ v : PCWorld, v.ConsistentWithTheory S.base := by
  obtain ⟨v, hv⟩ := DeductiveProcess.exists_consistentWithTheory _ S.hworldA
  exact ⟨v, S.consistentWithTheory_base_of_subset S.base_subset_processA hv⟩

/-! ## A. The A-side engine, grade (a) -/

/-- **T3, A-side (headline; grade (a), no `hz`, no polarity certificate).** Along every e.c.
sub-fragment `G'` of `G` (a ruler `t` with `t n = 0 → Timely S ε n`), with the tolerance
`ε → 0`: the predictor's day-`n` expectation of the contract LUV `C_n` agrees with its own day-`n`
price of the contract proposition `P^{(n)}`:
`∀ δ > 0, ∀ᶠ n, t n = 0 → |𝔼^A_n(C_n) − A_n(P^{(n)})| ≤ δ`.
Route: `gated_pin` in `A`'s process — `C_n` is settled at `Y n` (`determinedA`, the ledger
construction), and in every completed-theory world of `A`'s process `P^{(n)}` pays `truthAt n`
(`truthAt_holds_A`, through `shared` and the decided clause of `Timely`), which is within `ε n` of
`Y n` by the tolerance clause; FAF's vanishing-error affine provability induction does the rest.
**The quote agrees with `A`'s own price of the proposition on `G'`**. Roles: `A` the predictor;
the sibling enters only through the settled value. **Two-way** (`A_inductor` over a ledger
settled to the sibling's verdict): `partial: over timely_cofinite_const` at `S` — the `base0`
pair with the diagonal property, whose last conjunct supplies every hypothesis here with `t ≡ 0`
(`engineA_of_diagonal`, `OnG.lean` §G); at the bare existence row `frozenSystem_exists`'s pin
non-emptiness of `G` is not established (repair round 2, audit r2 adversarial B1). The one-way
N+ instance is `engineA_onG` (`OnG.lean`, at `onGSystem` with `t ≡ 0`; in the quote-redundant
regime of findings F4).
Source: [[frozen-deliberation-deference-v6]] §5.5 ("On `G`, the quote is early-revealed truth"), T3 proof (lines 100–104; anson-020); [[deference-in-logical-induction-v6]] §5.5 T3 (root-deference-041); lean-deference-022 (`quote_is_truth_on_G`, [[AUDIT]] §3.3)
Kind: C
Fidelity: variant: along e.c. sub-fragments (the whole-`G` form is `engineA_ofCert`, (c)); plain trader class; settlement as `DeterminedVia`; exact rational contract
Hyps: (a) none (`ht`, `hG`, `hε` are the fragment's data: which e.c. sub-fragment, and that the tolerance vanishes) -/
theorem engineA (S : FrozenSystem) (ε : ℕ → ℚ) (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    {t : ℕ → ℕ} (ht : UnaryRuler t) (hG : ∀ n, t n = 0 → Timely S ε n) :
    AgreeAlong t (fun n => (ledgerLuv 0 n).expect S.A n) (fun n => S.A n (S.contract n)) := by
  haveI := S.A_inductor
  refine gated_pin S.A S.processA S.hworldA ht (ledgerLuv_thresholdCodes 0) S.contract_codes
    (fun n => (S.Y n : ℝ)) (fun n _ w hw => S.determinedA n w hw) ?_
  intro δ hδ
  filter_upwards [agreeAlong_Y_truthAt S ε t hG hε δ hδ] with n hn h0 w hw
  rw [payout_contract_eq_truthAt (hG n h0).1
    (S.consistentWithTheory_base_of_subset S.base_subset_processA hw)]
  exact hn h0

/-- **T3, A-side, in terms of the published quote**: `engineA` with `a n = 𝔼^A_n(C_n)` (`a_eq`).
Source: as `engineA`
Kind: L
Fidelity: as `engineA`
Hyps: (a) none -/
theorem engineA_quote (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ} (ht : UnaryRuler t)
    (hG : ∀ n, t n = 0 → Timely S ε n) :
    AgreeAlong t (fun n => (S.a n : ℝ)) (fun n => S.A n (S.contract n)) := by
  have he : (fun n => (S.a n : ℝ)) = fun n => (ledgerLuv 0 n).expect S.A n := funext S.a_eq
  rw [he]
  exact engineA S ε hε ht hG

/-- **T3, A-side, whole-`G` form under a certificate** (c): if the timely fragment itself is the
zero set of a unary ruler (`hcert`), the conclusion holds on all of `G`. The certificate is a
modelling hypothesis (finding F1: membership in `G` costs a sibling run to `F n`, not an FP test).
Source: anson-020 flag (i); mandate D2 (F1), T3 ("the whole-`G` form is allowed only … labelled (c)")
Kind: L
Fidelity: as `engineA`
Hyps: (c) `hcert` — an FP indicator of `G`; all else (a) -/
theorem engineA_ofCert (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ} (ht : UnaryRuler t)
    (hcert : ∀ n, t n = 0 ↔ Timely S ε n) :
    ∀ δ > 0, ∀ᶠ n in atTop, Timely S ε n →
      |(ledgerLuv 0 n).expect S.A n - S.A n (S.contract n)| ≤ δ := by
  intro δ hδ
  filter_upwards [engineA S ε hε ht (fun n h => (hcert n).1 h) δ hδ] with n hn hT
  exact hn ((hcert n).2 hT)

/-! ## B. A-to-truth: the quote is early-revealed truth on `G'` -/

/-- **T3, A-to-truth** (root-deference-040's "on `G` the quote is early-revealed truth"): along
`G'`, the published quote agrees with the decided value, `∀ δ > 0, ∀ᶠ n, t n = 0 →
|a_n − truthAt n| ≤ δ`. T1 (`a ≈ₙ Y`, costing `hz`) composed with the tolerance clause of `G`
(`agreeAlong_Y_truthAt`) — `def-tracking-pin`'s `asympEq_restrict_of_near` in `AgreeAlong` form.
Kind L over T1: the forcing is T1's. Roles: `A` the predictor. **Two-way**: `partial: over
timely_cofinite_const` (the on-`G` pair of record, repair round 2) and `hz` at that pair.
Source: [[deference-in-logical-induction-v6]] §5.5 line 588 (root-deference-040); [[frozen-deliberation-deference-v6]] §5.5 ("first `≈`: T1; second: membership in `G`")
Kind: L
Fidelity: exact (along e.c. sub-fragments)
Hyps: (c) `hz` through T1 (checklist row 6); all else (a) -/
theorem engineA_truth (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ}
    (hG : ∀ n, t n = 0 → Timely S ε n) (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) :
    AgreeAlong t (fun n => (S.a n : ℝ)) (fun n => (truthAt S n : ℝ)) :=
  (AgreeAlong.of_asympEq (tracking S zhat hz hlim)).trans (agreeAlong_Y_truthAt S ε t hG hε)

/-- **The `hz`-free route to truth needs an e.c. polarity pattern** (finding F4). If the two
subfamilies of `G'` — the days where the decided value is `1` and where it is `0` — are e.c. as
sentence families (`hpat₁`, `hpat₀`: the contract on the subfamily, a trivial filler off it), then
`A`'s own provability induction (FAF's `lic_provind_true`/`_false`) gives `A_n(P^{(n)}) → truthAt n`
along `G'`, and with `engineA_quote` the quote reaches the truth with **no `hz`**. Under `hpat` the
quote is redundant: the predictor and the advised reasoner each reach the truth on `G'` by their
own provability induction. So the construction's uplift lives exactly where the pattern is not
e.c., and there the forcing to truth costs `hz` — the honest FAF content of "exponentially earlier
than `F(n)`", a complexity claim with no carrier in one trader class.
Source: mandate T3 (`engineA_truth_ofPattern`, F4); [[frozen-deliberation-deference-v6]] §5.5
Kind: C
Fidelity: variant: polarity pattern as e.c. sentence families (the plain trader class)
Hyps: (c) `hpat₁`, `hpat₀` — e.c. certificates of the polarity pattern on `G'` (in place of `hz`); all else (a) -/
theorem engineA_truth_ofPattern (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ} (ht : UnaryRuler t)
    (hG : ∀ n, t n = 0 → Timely S ε n)
    (hpat₁ : MachineSentenceCodes
      (fun n => if t n = 0 ∧ truthAt S n = 1 then S.contract n else ⊤))
    (hpat₀ : MachineSentenceCodes
      (fun n => if t n = 0 ∧ truthAt S n = 0 then S.contract n else ∼(⊤ : Sentence))) :
    AgreeAlong t (fun n => (S.a n : ℝ)) (fun n => (truthAt S n : ℝ)) := by
  haveI := S.A_inductor
  have h1 := lic_provind_true S.A S.processA _ hpat₁ (fun n v hv => by
    by_cases hc : t n = 0 ∧ truthAt S n = 1
    · rw [if_pos hc]
      exact (truthAt_holds_A (hG n hc.1).1 hv).2 hc.2
    · rw [if_neg hc]
      exact PCWorld.holds_top v) S.hworldA
  have h0 := lic_provind_false S.A S.processA _ hpat₀ (fun n v hv => by
    by_cases hc : t n = 0 ∧ truthAt S n = 0
    · rw [if_pos hc, PCWorld.holds_neg]
      intro hh
      have := (truthAt_holds_A (hG n hc.1).1 hv).1 hh
      rw [hc.2] at this
      norm_num at this
    · rw [if_neg hc, PCWorld.holds_neg, PCWorld.holds_neg, not_not]
      exact PCWorld.holds_top v) S.hworldA
  refine (engineA_quote S ε hε ht hG).trans ?_
  intro δ hδ
  filter_upwards [asympEq_iff_eventuallyWithin.1 h1 δ hδ,
    asympEq_iff_eventuallyWithin.1 h0 δ hδ] with n hn1 hn0 h0t
  rcases truthAt_eq_zero_or_one S n with hz | ho
  · rw [if_pos ⟨h0t, hz⟩] at hn0
    rw [hz]
    simpa using hn0
  · rw [if_pos ⟨h0t, ho⟩] at hn1
    rw [ho]
    simpa using hn1

/-! ## C. The H-side: the conditional tower on `G'`, weight factored -/

/-- **T3, H-side — the conditional tower `ccee(H⁺ → A)` on `G'`** (headline). Along every e.c.
sub-fragment `G'` of `G`, the advised reasoner's day-`n` price of the contract proposition agrees
with its day-`n` expectation of the **quote item** `α_{0,n}` it reads from the ledger (the LUV
`ledgerLuv 0 n`, settled at the published number `a_n` — the source's `⌜a_n⌝`, not the contract):
`∀ δ > 0, ∀ᶠ n, t n = 0 → |Hplus_n(P^{(n)}) − 𝔼^{Hplus}_n(α_{0,n})| ≤ δ`.
Route: `gated_pin` in `Hplus`'s process — the ledger LUV `α_{0,n}` is settled at the published
quote `a n` (`determinedH`), `P^{(n)}` pays `truthAt n` in every completed-theory world
(`truthAt_holds_H`), and `a n − truthAt n → 0` along `G'` by `engineA_truth`. **The only non-(a)
hypothesis is T1's `hz`; there is no `hcarry`**: the link to truth comes from T1 (forced) and
membership in `G` (the definition), exactly as v6's proof says ("the ledger supplies only the
referent for `a_n`"). The estimate is the *contract's* price, a relayed expert with no `Expert`
carrier: this is **not** `def-lattice`'s `CondTower` (which quantifies over all e.c. sources and
takes an `Expert` whose estimate is `A`'s deferred expectation of the same LUV); no fake `Expert`
is built to make the names match. Roles: `Hplus` the advised reasoner, `A` the predictor (through
T1). **Two-way**: `partial: over timely_cofinite_const` (the on-`G` pair of record, repair round
2) and `hz` at that pair; the one-way N+ instance is `condTower_onG_onG`
(`OnG.lean` §E, at `onGSystem` with `ẑ := Y0`, `t ≡ 0`; in the quote-redundant regime of findings
F4).
Source: [[frozen-deliberation-deference-v6]] T3 (lines 98–104; anson-020); [[deference-in-logical-induction-v6]] §5.5 T3 (root-deference-041); lean-deference-022 (`conditional_tower` with `hcarry`, [[AUDIT]] §3.3 — the squeeze this replaces)
Kind: C
Fidelity: variant: single family (the contract enumeration), along e.c. sub-fragments; weight factored (`condTower_onG_weighted`); the estimate is the contract's price (no `Expert`); plain trader class
Hyps: (c) `hz` through T1 (checklist row 6); all else (a) -/
theorem condTower_onG (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ} (ht : UnaryRuler t)
    (hG : ∀ n, t n = 0 → Timely S ε n) (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) :
    AgreeAlong t (fun n => S.Hplus n (S.contract n)) (fun n => (ledgerLuv 0 n).expect S.Hplus n) := by
  haveI := S.Hplus_inductor
  have hAt := engineA_truth S ε hε hG zhat hz hlim
  refine (gated_pin S.Hplus S.processH S.hworldH ht (ledgerLuv_thresholdCodes 0) S.contract_codes
    (fun n => (S.a n : ℝ)) (fun n _ w hw => S.determinedH 0 n w hw) ?_).symm
  intro δ hδ
  filter_upwards [hAt δ hδ] with n hn h0 w hw
  rw [payout_contract_eq_truthAt (hG n h0).1
    (S.consistentWithTheory_base_of_subset S.base_subset_processH hw)]
  exact hn h0

/-- **T3, H-side, weighted form**: for every bounded weight `w : ℕ → ℚ` in `[0,1]`, the weighted
gap `w_n · (Hplus_n(P^{(n)}) − 𝔼^{Hplus}_n(α_{0,n}))` vanishes along `G'`. The weight **factors**
and is **idle** on `G` (v6's own remark: "`H⁺`'s linearity splits the weight, which factors because
`A` knows its own quote"): the weighted form is the unweighted one times a bounded sequence, and
no generability of `w` is used — it is not sold as `ccee`. Kind L over `condTower_onG`. **The
weight sits outside the expectation** (`w_n · 𝔼_n(α_{0,n})`); the source's `w(a_n)` sits inside
(`𝔼^{H⁺}_n(𝟙(P)·w)` against `𝔼^{H⁺}_n(⌜a_n·w⌝)`), and over FAF neither form implies the other
without the H-side pin of findings F14 — so this is a variant, stated at `w ≡ 1` by
`condTower_onG` (audit r2 fidelity N5).
Source: [[frozen-deliberation-deference-v6]] T3 statement ("for every bounded readable continuous weight `w = w(a_n)`")
Kind: L
Fidelity: variant: the weight is multiplied outside the expectation (any bounded rational sequence; readability and continuity idle); the source's inside-weight form is stated only at `w ≡ 1` (`condTower_onG`)
Hyps: (c) `hz` through T1; all else (a) -/
theorem condTower_onG_weighted (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ} (ht : UnaryRuler t)
    (hG : ∀ n, t n = 0 → Timely S ε n) (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0))
    (w : ℕ → ℚ) (hw0 : ∀ n, 0 ≤ w n) (hw1 : ∀ n, w n ≤ 1) :
    AgreeAlong t (fun n => (w n : ℝ) * S.Hplus n (S.contract n))
      (fun n => (w n : ℝ) * (ledgerLuv 0 n).expect S.Hplus n) := by
  intro δ hδ
  filter_upwards [condTower_onG S ε hε ht hG zhat hz hlim δ hδ] with n hn h0
  have hw0' : (0 : ℝ) ≤ w n := by exact_mod_cast hw0 n
  have hw1' : (w n : ℝ) ≤ 1 := by exact_mod_cast hw1 n
  rw [← mul_sub, abs_mul, abs_of_nonneg hw0']
  calc (w n : ℝ) * |S.Hplus n (S.contract n) - (ledgerLuv 0 n).expect S.Hplus n|
      ≤ 1 * |S.Hplus n (S.contract n) - (ledgerLuv 0 n).expect S.Hplus n| :=
        mul_le_mul_of_nonneg_right hw1' (abs_nonneg _)
    _ = |S.Hplus n (S.contract n) - (ledgerLuv 0 n).expect S.Hplus n| := one_mul _
    _ ≤ δ := hn h0

/-- **T3, H-side, whole-`G` form under a certificate** (c): as `engineA_ofCert`.
Source: anson-020 flag (i); mandate T3
Kind: L
Fidelity: as `condTower_onG`
Hyps: (c) `hcert` — an FP indicator of `G`; (c) `hz` through T1; all else (a) -/
theorem condTower_onG_ofCert (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ} (ht : UnaryRuler t)
    (hcert : ∀ n, t n = 0 ↔ Timely S ε n) (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) :
    ∀ δ > 0, ∀ᶠ n in atTop, Timely S ε n →
      |S.Hplus n (S.contract n) - (ledgerLuv 0 n).expect S.Hplus n| ≤ δ := by
  intro δ hδ
  filter_upwards [condTower_onG S ε hε ht (fun n h => (hcert n).1 h) zhat hz hlim δ hδ]
    with n hn hT
  exact hn ((hcert n).2 hT)

end Cleanroom.Deference.DefFrozenSibling
