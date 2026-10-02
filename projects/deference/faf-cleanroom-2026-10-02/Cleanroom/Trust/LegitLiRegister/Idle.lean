import Cleanroom.Trust.LegitLiRegister.Defs
import Cleanroom.Deference.DefFrozenSibling.Gated
import Cleanroom.Deference.DefFrozenSibling.Limits
import LogicalInduction.Properties.AffineCoherence
import LogicalInduction.Construction.Quotation.DeferralFibre

/-!
# `legit-li-register` · Idle: the influence defect on the timely fragment (Target 2)

[[legitimacy-theory-v1]] §2.2 ("on the decidable fragment `d_n` is asymptotically idle: both runs
converge to the truth value, so `d_n → 0` there regardless of influence"), root-fa-2-007 (ii).
The sibling's half is the definition of `G` read asymptotically (`agreeAlong_Y_truthAt`). The
advised reasoner's half — `Hplus (F n) (contract n) → truthAt n` along an e.c. sub-fragment of
`G` — is the content, and **it is not free**:

* **What settlement forces** (grade (a), `horizon_price_agree_anticipation`): along `G'`, the
  advised reasoner's horizon price of `P^{(n)}` agrees with its own horizon *expectation of the
  settled-value item* `α_{1,n}` — the ledger LUV that will be published at `eY n > F n` and is
  determined at `Y n` in its theory — by `def-frozen-sibling`'s gated engine (`gated_pin`) on the
  reindexed families. Two market quantities agree; neither is pinned to the truth.
* **What reaching the truth costs** (grade (c), the headline
  `defect_agreeAlong_zero_onG_ofPattern`): an e.c. certificate of the polarity pattern of the
  reindexed contract family *in the advised reasoner's language* (`hpat₁`, `hpat₀`) — then FAF's
  provability induction (`lic_provind_true/false`) for `Hplus` on the two subfamilies gives the
  horizon price, and the tolerance clause does the rest. This is the dependency's finding F4
  (`engineA_truth_ofPattern`) on the `H`-side, and `def-tracking-pin`'s `ledger_atom_learned`
  shape: the *timely* reading (the day-`F n` price of a sentence decided by day `F n`) costs
  `hpat`, the *eventual* reading (`limitingBelief`, `limit_agree_of_decidedBy`) is (a).
* **Why no (a)-grade route exists for the general pattern**: FAF's criterion constrains prices
  only through traders, and a trader cannot read the stage; a decided-by-day-`m` family whose
  polarity pattern is pseudorandom relative to the reader's generable weightings is priced at its
  frequency (`li-pseudorandom`'s subject; `def-tracking-pin`'s docstring on `ledger_atom_learned`
  says the same of the ledger atoms). The mandate's grade-(a) route (pin the expectation of the
  determined indicator LUV to its value "with no generability of the value") misreads
  `gated_pin`, which pins an expectation to a *price*, never to a world value. The grade-(a)
  statement is therefore recorded OPEN (`horizon_idleness_grade_a_open`) with its negation's
  shape OPEN beside it (`horizon_idleness_fails_exists_open`); see
  [[legit-li-register-findings]] F1.
* **Where (a) holds**: whenever the polarity pattern is e.c. — in particular for a constant
  contract decided at some stage (`defect_agreeAlong_zero_onG_const`, root-fa-2-007's reading (i)),
  and at the inhabitant `onGSystem` (even/odd pattern; `Witness.lean`).

Every statement is along an e.c. sub-fragment `G' = {n | t n = 0}` of `G` (D3), with
`hG : ∀ n, t n = 0 → Timely S ε n`, `ε → 0`, and `hinj : Function.Injective S.F.f` (FAF's
`DeferralFunction` is not injective by type; discharged at `succDeferral` in every witness).
Roles: `Hplus` the advised reasoner, `sib n` the sealed sibling, `A` enters nowhere here (no `hz`).
-/

namespace Cleanroom.Trust.LegitLiRegister

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Deference.DefFrozenSibling
open Filter Topology

/-! ## A. The horizon gate: reindexing `G'` along the horizon -/

/-- **The horizon gate**: a ruler on the advised reasoner's clock that is zero exactly at the
image days `m = F n` of fragment days `n` (`t n = 0`): `(1 − flag m) + t (F⁻¹ m)` with FAF's
bounded-scan `deferralImageFlag`/`deferralPreimage`.
Source: mandate Target 2 (the reindexed family); `def-self-trust` `Witness.lean` (the idiom)
Kind: D
Fidelity: n/a -/
def horizonGate (S : FrozenSystem) (t : ℕ → ℕ) (m : ℕ) : ℕ :=
  (1 - deferralImageFlag S.F m) + t (deferralPreimage S.F m)

/-- The horizon gate is a unary ruler when `t` is.
Source: none: infrastructure (FAF `unaryRuler_deferralImageFlag`, `unaryRuler_deferralPreimage`)
Kind: L
Fidelity: n/a -/
theorem horizonGate_ruler (S : FrozenSystem) {t : ℕ → ℕ} (ht : UnaryRuler t) :
    UnaryRuler (horizonGate S t) :=
  ((UnaryRuler.const 1).sub (unaryRuler_deferralImageFlag S.F)).add
    (ht.comp (unaryRuler_deferralPreimage S.F))

/-- The gate is zero iff `m` is an image day whose preimage is on the fragment.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem horizonGate_eq_zero_iff (S : FrozenSystem) (t : ℕ → ℕ) (m : ℕ) :
    horizonGate S t m = 0 ↔
      deferralImageFlag S.F m = 1 ∧ t (deferralPreimage S.F m) = 0 := by
  unfold horizonGate
  rcases deferralImageFlag_zero_or_one S.F m with h | h <;> rw [h] <;> omega

/-- At an image day the gate reads the fragment: `horizonGate S t (F n) = t n` (`hinj`).
Source: none: infrastructure (FAF `deferralImageFlag_at`, `deferralPreimage_at`)
Kind: L
Fidelity: n/a -/
theorem horizonGate_at (S : FrozenSystem) (t : ℕ → ℕ) (hinj : Function.Injective S.F.f)
    (n : ℕ) : horizonGate S t (S.F.f n) = t n := by
  unfold horizonGate
  rw [deferralImageFlag_at, deferralPreimage_at S.F hinj]
  omega

/-- Eventually on the reader's clock, every image day's preimage is large: for `m` beyond
`max_{n < N} F n`, `flag m = 1 → N ≤ F⁻¹ m` (`hinj`).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem eventually_preimage_ge (S : FrozenSystem) (hinj : Function.Injective S.F.f) (N : ℕ) :
    ∀ᶠ m in atTop, deferralImageFlag S.F m = 1 → N ≤ deferralPreimage S.F m := by
  rw [Filter.eventually_atTop]
  refine ⟨(Finset.range N).sup S.F.f + 1, fun m hm hflag => ?_⟩
  by_contra hlt
  have hlt' : deferralPreimage S.F m < N := not_le.1 hlt
  obtain ⟨-, hFm⟩ := deferralPreimage_spec S.F hinj hflag
  have : S.F.f (deferralPreimage S.F m) ≤ (Finset.range N).sup S.F.f :=
    Finset.le_sup (f := S.F.f) (Finset.mem_range.2 hlt')
  omega

/-! ## B. Grade (a): what settlement forces at the horizon -/

/-- **The horizon price agrees with the anticipation of the settled value** (grade (a), no `hz`,
no certificate). Along every e.c. sub-fragment `G'` of `G` with `ε → 0`: the advised reasoner's
day-`F n` price of `P^{(n)}` agrees with its day-`F n` expectation of the **settled-value item**
`α_{1,n}` — the ledger LUV published at `eY n ≥ σ n > F n`, hence *not yet in the stage at the
horizon*, but determined at `Y n` in the theory (`determinedH 1 n`) — which is within `ε n` of the
decided value (`Timely`). Route: `gated_pin` in `Hplus`'s process on the reindexed, horizon-gated
families (`X m := α_{1, F⁻¹ m}`, `φ m := P^{(F⁻¹ m)}`), read back at `m = F n`. **Two market
quantities agree; neither is forced to the truth** — this is exactly what the criterion gives at
the horizon without a certificate (compare `engineA`, `condTower_onG`). Two-way:
`partial: over timely_cofinite_const` as the dependency's on-`G` rows.
Source: mandate Target 2 (the engine, corrected: what `gated_pin` actually pins); root-fa-2-007 (ii)
Kind: C
Fidelity: variant: the price is pinned to the reader's own anticipation of the settled value, not to the truth (the truth needs `hpat`, below)
Hyps: (a) none (`ht`, `hG`, `hε`, `hinj` are the fragment's data; checklist rows 5, 7, 13, 14) -/
theorem horizon_price_agree_anticipation (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ} (ht : UnaryRuler t)
    (hG : ∀ n, t n = 0 → Timely S ε n) (hinj : Function.Injective S.F.f) :
    AgreeAlong t (fun n => S.Hplus (S.F.f n) (S.contract n))
      (fun n => (ledgerLuv 1 n).expect S.Hplus (S.F.f n)) := by
  haveI := S.Hplus_inductor
  have hpin := gated_pin S.Hplus S.processH S.hworldH (horizonGate_ruler S ht)
    ((ledgerLuv_thresholdCodes 1).reindex (unaryRuler_deferralPreimage S.F))
    (S.contract_codes.comp (unaryRuler_deferralPreimage S.F))
    (fun m => (S.Y (deferralPreimage S.F m) : ℝ))
    (fun m _ w hw => by
      have h := S.determinedH 1 (deferralPreimage S.F m) w hw
      rwa [frozenTable_succ] at h) ?_
  · intro δ hδ
    filter_upwards [S.F.tendsto_atTop.eventually (hpin δ hδ)] with n hn ht0
    have hg : horizonGate S t (S.F.f n) = 0 := by rw [horizonGate_at S t hinj]; exact ht0
    have := hn hg
    rw [deferralPreimage_at S.F hinj] at this
    rw [abs_sub_comm]
    exact this
  · intro δ hδ
    have h2 : ∀ᶠ n in atTop, |(ε n : ℝ)| ≤ δ := by
      have := hε.abs
      rw [abs_zero] at this
      exact this.eventually (eventually_le_nhds hδ)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 h2
    filter_upwards [eventually_preimage_ge S hinj N] with m hm hg w hw
    obtain ⟨hflag, ht0⟩ := (horizonGate_eq_zero_iff S t m).1 hg
    have hT := hG _ ht0
    rw [payout_contract_eq_truthAt hT.1
      (S.consistentWithTheory_base_of_subset S.base_subset_processH hw)]
    have h' : |(S.Y (deferralPreimage S.F m) : ℝ) - (truthAt S (deferralPreimage S.F m) : ℝ)| ≤
        (ε (deferralPreimage S.F m) : ℝ) := by exact_mod_cast hT.2
    exact h'.trans ((le_abs_self _).trans (hN _ (hm hflag)))

/-! ## C. Grade (c): reaching the truth costs an `H`-side polarity certificate -/

/-- The reindexed contract family on the positive-polarity part of `G'`: `P^{(F⁻¹ m)}` at image
days on the fragment whose decided value is `1`, the filler `⊤` elsewhere.
Source: mandate Target 2; `def-frozen-sibling` `engineA_truth_ofPattern` (the `H`-side twin)
Kind: D
Fidelity: n/a -/
def horizonFamilyPos (S : FrozenSystem) (t : ℕ → ℕ) (m : ℕ) : Sentence :=
  if horizonGate S t m = 0 ∧ truthAt S (deferralPreimage S.F m) = 1 then
    S.contract (deferralPreimage S.F m) else ⊤

/-- The negative-polarity part: `P^{(F⁻¹ m)}` where the decided value is `0`, the refutable filler
`∼⊤` elsewhere.
Source: as `horizonFamilyPos`
Kind: D
Fidelity: n/a -/
def horizonFamilyNeg (S : FrozenSystem) (t : ℕ → ℕ) (m : ℕ) : Sentence :=
  if horizonGate S t m = 0 ∧ truthAt S (deferralPreimage S.F m) = 0 then
    S.contract (deferralPreimage S.F m) else ∼(⊤ : Sentence)

/-- **The horizon price reaches the truth under an `H`-side polarity certificate** (grade (c)).
If the two polarity subfamilies of the reindexed contract family are e.c. in the advised
reasoner's language (`hpat₁`, `hpat₀`), FAF's provability induction for `Hplus` on each gives
`Hplus (F n) (P^{(n)}) → truthAt n` along `G'`. No `hz`, no `A` at all: the cost is the
certificate, which is the *human-side read-cheap* hypothesis of checklist row 4 in FAF's one
trader class — not row 6. Two-way: `partial: over timely_cofinite_const`.
Source: mandate Target 2 (`hplus_horizon_truth_onG`), at the grade it has; `def-frozen-sibling` F4 (`engineA_truth_ofPattern`); `def-tracking-pin` `ledger_atom_learned` (the `hpat` shape)
Kind: C
Fidelity: variant: polarity pattern as e.c. sentence families (the plain trader class); along e.c. sub-fragments
Hyps: (c) `hpat₁`, `hpat₀` — e.c. certificates of the polarity pattern of the reindexed contract family (checklist row 4, read-cheap, in place of a complexity class); all else (a) (rows 5, 7, 13, 14) -/
theorem hplus_horizon_truth_ofPattern (S : FrozenSystem) (ε : ℕ → ℚ) {t : ℕ → ℕ}
    (hG : ∀ n, t n = 0 → Timely S ε n) (hinj : Function.Injective S.F.f)
    (hpat₁ : MachineSentenceCodes (horizonFamilyPos S t))
    (hpat₀ : MachineSentenceCodes (horizonFamilyNeg S t)) :
    AgreeAlong t (fun n => S.Hplus (S.F.f n) (S.contract n)) (fun n => (truthAt S n : ℝ)) := by
  haveI := S.Hplus_inductor
  have h1 := lic_provind_true S.Hplus S.processH _ hpat₁ (fun m v hv => by
    unfold horizonFamilyPos
    by_cases hc : horizonGate S t m = 0 ∧ truthAt S (deferralPreimage S.F m) = 1
    · rw [if_pos hc]
      have hg := (horizonGate_eq_zero_iff S t m).1 hc.1
      exact (truthAt_holds_H (hG _ hg.2).1 hv).2 hc.2
    · rw [if_neg hc]
      exact PCWorld.holds_top v) S.hworldH
  have h0 := lic_provind_false S.Hplus S.processH _ hpat₀ (fun m v hv => by
    unfold horizonFamilyNeg
    by_cases hc : horizonGate S t m = 0 ∧ truthAt S (deferralPreimage S.F m) = 0
    · rw [if_pos hc, PCWorld.holds_neg]
      intro hh
      have hg := (horizonGate_eq_zero_iff S t m).1 hc.1
      have := (truthAt_holds_H (hG _ hg.2).1 hv).1 hh
      rw [hc.2] at this
      norm_num at this
    · rw [if_neg hc, PCWorld.holds_neg, PCWorld.holds_neg, not_not]
      exact PCWorld.holds_top v) S.hworldH
  intro δ hδ
  have hev : ∀ᶠ m in atTop, |S.Hplus m (horizonFamilyPos S t m) - 1| ≤ δ ∧
      |S.Hplus m (horizonFamilyNeg S t m) - 0| ≤ δ := by
    filter_upwards [asympEq_iff_eventuallyWithin.1 h1 δ hδ,
      asympEq_iff_eventuallyWithin.1 h0 δ hδ] with m hm1 hm0
    exact ⟨hm1, hm0⟩
  filter_upwards [S.F.tendsto_atTop.eventually hev] with n hn ht0
  have hgate : horizonGate S t (S.F.f n) = 0 := by rw [horizonGate_at S t hinj]; exact ht0
  have hpre : deferralPreimage S.F (S.F.f n) = n := deferralPreimage_at S.F hinj n
  rcases truthAt_eq_zero_or_one S n with h0' | h1'
  · have hfam : horizonFamilyNeg S t (S.F.f n) = S.contract n := by
      unfold horizonFamilyNeg
      rw [hpre, if_pos ⟨hgate, h0'⟩]
    rw [hfam] at hn
    rw [h0']
    simpa using hn.2
  · have hfam : horizonFamilyPos S t (S.F.f n) = S.contract n := by
      unfold horizonFamilyPos
      rw [hpre, if_pos ⟨hgate, h1'⟩]
    rw [hfam] at hn
    rw [h1']
    simpa using hn.1

/-- **Idleness on the timely fragment, under the `H`-side polarity certificate** (headline, the
grade Target 2 actually has). Along every e.c. sub-fragment `G'` of `G` with `ε → 0` and `F`
injective, if the polarity pattern of the reindexed contract family is e.c. in the advised
reasoner's language, then `d_n → 0` along `G'`: `AgreeAlong t (defect S) 0`. The sibling's half
is the definition of `G` (`agreeAlong_Y_truthAt`), the advised reasoner's half is
`hplus_horizon_truth_ofPattern`. **No `hz`** (checklist row 6 is not used); the cost is row 4's
read-cheap certificate, and it is load-bearing: without it the statement is OPEN
(`horizon_idleness_grade_a_open`) and believed false. Two-way:
`partial: over timely_cofinite_const` (the on-`G` pair of record; at `frozenSystem_exists`'s pin
non-emptiness of `G` is not established); one-way N+: `defect_onG_tendsto_zero` (`Witness.lean`,
at `onGSystem`, where the pattern is even/odd and the certificates are discharged).
Source: root-fa-2-007 (ii); [[legitimacy-theory-v1]] §2.2 l. 45 ("asymptotically idle on the decidable fragment"); mandate Target 2 (headline), at the grade the dependency's F4 allows
Kind: C
Fidelity: weaker: the source says "regardless of influence" at grade (a); over FAF the advised reasoner's horizon price reaches the decided value only under an e.c. polarity certificate (or where the pattern is e.c.); "decidable fragment" read as the timely fragment (known issue 1)
Hyps: (c) `hpat₁`, `hpat₀` (checklist row 4); all else (a) (rows 1, 3, 5, 7, 13, 14) -/
theorem defect_agreeAlong_zero_onG_ofPattern (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ}
    (hG : ∀ n, t n = 0 → Timely S ε n) (hinj : Function.Injective S.F.f)
    (hpat₁ : MachineSentenceCodes (horizonFamilyPos S t))
    (hpat₀ : MachineSentenceCodes (horizonFamilyNeg S t)) :
    AgreeAlong t (defect S) (fun _ => 0) := by
  have hY := agreeAlong_Y_truthAt S ε t hG hε
  have hH := hplus_horizon_truth_ofPattern S ε hG hinj hpat₁ hpat₀
  have hYH := hY.trans hH.symm
  intro δ hδ
  filter_upwards [hYH δ hδ] with n hn ht0
  unfold defect
  rw [sub_zero, abs_abs]
  exact hn ht0

/-- `LegitimateAlong` form of the headline.
Source: as `defect_agreeAlong_zero_onG_ofPattern`
Kind: L
Fidelity: as there
Hyps: as there -/
theorem legitimateAlong_onG_ofPattern (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ}
    (hG : ∀ n, t n = 0 → Timely S ε n) (hinj : Function.Injective S.F.f)
    (hpat₁ : MachineSentenceCodes (horizonFamilyPos S t))
    (hpat₀ : MachineSentenceCodes (horizonFamilyNeg S t)) :
    LegitimateAlong S t :=
  defect_agreeAlong_zero_onG_ofPattern S ε hε hG hinj hpat₁ hpat₀

/-! ## D. Grade (a) where the pattern is e.c.: a constant decided contract (reading (i)) -/

/-- A stage of the shared process never holds both polarities of a sentence (every stage of the
advised reasoner's process has a consistent world, and the shared stage sits inside it).
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem not_both_polarities (S : FrozenSystem) {φ : Sentence} {s s' : ℕ}
    (h₁ : φ ∈ S.base.D s) (h₂ : ∼φ ∈ S.base.D s') : False := by
  obtain ⟨v, hv⟩ := S.hworldH (max s s')
  have hsub : ∀ k ≤ max s s', S.base.D k ⊆ S.processH.D (max s s') := fun k hk =>
    (S.base.mono_le hk).trans (S.base_subset_processH _)
  have hφ : v.Holds φ := hv _ (hsub s (le_max_left _ _) h₁)
  have hnφ : v.Holds (∼φ) := hv _ (hsub s' (le_max_right _ _) h₂)
  rw [PCWorld.holds_neg] at hnφ
  exact hnφ hφ

/-- For a constant contract decided at some stage, the decided value is the same on every decided
day: `1` if the sentence is a stage member, `0` if its negation is.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem truthAt_const_contract (S : FrozenSystem) {φ : Sentence} (hc : ∀ n, S.contract n = φ)
    {m₀ : ℕ} (hdec : φ ∈ S.base.D m₀ ∨ ∼φ ∈ S.base.D m₀) {n : ℕ} (hn : DecidedBy S n) :
    truthAt S n = if φ ∈ S.base.D m₀ then 1 else 0 := by
  unfold truthAt
  rw [hc]
  unfold DecidedBy at hn
  rw [hc] at hn
  rcases hdec with h | h
  · rw [if_pos h]
    rcases hn with hn | hn
    · rw [if_pos hn]
    · exact absurd (not_both_polarities S h hn) id
  · have hnot : φ ∉ S.base.D m₀ := fun hφ => not_both_polarities S hφ h
    rw [if_neg hnot]
    rcases hn with hn | hn
    · exact absurd (not_both_polarities S hn h) id
    · rw [if_neg (fun hφ => not_both_polarities S hφ h)]

/-- **Idleness at grade (a) for a constant decided contract** (root-fa-2-007's reading (i)): if
every `P^{(n)}` is one sentence `φ` decided at some stage of the shared process, the polarity
pattern is constant on the decided days, both certificates are discharged by one
`MachineSentenceCodes.ifZero` on the horizon gate (needs `ht : UnaryRuler t`), and `d_n → 0` along
every e.c. sub-fragment of `G`. The source's reading (i) ("a single decided sentence, both markets
inductors") holds with no `hz` and no certificate — because the certificate is trivial there.
Source: root-fa-2-007 (i); mandate Target 2 (reading (i))
Kind: L (the headline with its certificates discharged)
Fidelity: exact (reading (i))
Hyps: (a) none (rows 1, 3, 5, 7, 13, 14) -/
theorem defect_agreeAlong_zero_onG_const (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ} (ht : UnaryRuler t)
    (hG : ∀ n, t n = 0 → Timely S ε n) (hinj : Function.Injective S.F.f) {φ : Sentence}
    (hc : ∀ n, S.contract n = φ) {m₀ : ℕ} (hdec : φ ∈ S.base.D m₀ ∨ ∼φ ∈ S.base.D m₀) :
    AgreeAlong t (defect S) (fun _ => 0) := by
  have hgate := horizonGate_ruler S ht
  have hval : ∀ m, horizonGate S t m = 0 →
      truthAt S (deferralPreimage S.F m) = if φ ∈ S.base.D m₀ then 1 else 0 := fun m hm =>
    truthAt_const_contract S hc hdec (hG _ ((horizonGate_eq_zero_iff S t m).1 hm).2).1
  refine defect_agreeAlong_zero_onG_ofPattern S ε hε hG hinj ?_ ?_
  · by_cases hφ : φ ∈ S.base.D m₀
    · refine (MachineSentenceCodes.ifZero (MachineSentenceCodes.const φ)
        (MachineSentenceCodes.const ⊤) hgate).of_eq (fun m => ?_)
      unfold horizonFamilyPos
      by_cases hm : horizonGate S t m = 0
      · rw [if_pos hm, if_pos ⟨hm, by rw [hval m hm, if_pos hφ]⟩, hc]
      · rw [if_neg hm, if_neg (fun h => hm h.1)]
    · refine (MachineSentenceCodes.const ⊤).of_eq (fun m => ?_)
      unfold horizonFamilyPos
      rw [if_neg]
      rintro ⟨hm, h1⟩
      rw [hval m hm, if_neg hφ] at h1
      norm_num at h1
  · by_cases hφ : φ ∈ S.base.D m₀
    · refine (MachineSentenceCodes.const (∼(⊤ : Sentence))).of_eq (fun m => ?_)
      unfold horizonFamilyNeg
      rw [if_neg]
      rintro ⟨hm, h0⟩
      rw [hval m hm, if_pos hφ] at h0
      norm_num at h0
    · refine (MachineSentenceCodes.ifZero (MachineSentenceCodes.const φ)
        (MachineSentenceCodes.const (∼(⊤ : Sentence))) hgate).of_eq (fun m => ?_)
      unfold horizonFamilyNeg
      by_cases hm : horizonGate S t m = 0
      · rw [if_pos hm, if_pos ⟨hm, by rw [hval m hm, if_neg hφ]⟩, hc]
      · rw [if_neg hm, if_neg (fun h => hm h.1)]

/-! ## E. The slow fragment: limits agree, the horizon defect is unconstrained -/

/-- **On every decided day the limits agree exactly** (the eventual grade, (a)): for a contract
decided at *any* stage, the sibling's and the advised reasoner's limiting beliefs on `P^{(n)}`
coincide (`def-frozen-sibling`'s `limit_pinned_of_decidedAt`). This is the per-`n` limit
statement; it says nothing about the day-`F n` defect, which on the slow fragment (decided after
the horizon) is unconstrained — the dichotomy of findings F2: limits agree on the decided
fragment, the horizon defect vanishes on the timely fragment under a certificate.
Source: root-fa-2-007 (reading (i), the limit form); `def-frozen-sibling` F16; mandate Target 2 (`defect_slow_decided_limit`)
Kind: L (instance of `limit_pinned_of_decidedAt`)
Fidelity: exact (limits, per `n`)
Hyps: (a) none (rows 7, 10, 13) -/
theorem limit_defect_zero_of_decidedAt (S : FrozenSystem) (n : ℕ) (h : DecidedAt S n) :
    limitingBelief (S.sib n) (S.contract n) = limitingBelief S.Hplus (S.contract n) := by
  obtain ⟨c, -, h₁, h₂, -⟩ := limit_pinned_of_decidedAt S n h
  rw [h₁, h₂]

/-! ## F. OPEN: the grade-(a) statement and its negation -/

/-- **OPEN — the mandate's grade-(a) idleness** (load-bearing 1 as written): `d_n → 0` along every
e.c. sub-fragment of `G` with no certificate. **Believed false** (findings F1): the hypotheses
constrain `Hplus` only through FAF's criterion, and a trader cannot read the stage, so a contract
family decided by the horizon whose polarity pattern is pseudorandom relative to `Hplus`'s
generable weightings is priced at its frequency at the horizon (`li-pseudorandom`'s subject),
while the siblings can be made timely day by day by finite perturbation (as `onGSystem` does).
Neither proved nor refuted on disk; the refutation's shape is `horizon_idleness_fails_exists_open`.
The mandate's proposed route (pin the expectation of the determined indicator LUV to its value
with no generability of the value) is not what `gated_pin` does (it pins an expectation to a
price). What *is* proved at grade (a) is `horizon_price_agree_anticipation`.
Source: mandate Target 2 (headline as written); root-fa-2-007 (ii)
Kind: OPEN
Fidelity: as the mandate's statement
Hyps: (a) as stated — which is why it is believed false -/
theorem horizon_idleness_grade_a_open (S : FrozenSystem) (ε : ℕ → ℚ)
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0)) {t : ℕ → ℕ} (ht : UnaryRuler t)
    (hG : ∀ n, t n = 0 → Timely S ε n) (hinj : Function.Injective S.F.f) :
    AgreeAlong t (defect S) (fun _ => 0) := by
  sorry

/-- **OPEN — the refutation's shape**: a frozen-deliberation system, every day timely at a
vanishing tolerance, with an injective horizon, at which the defect does **not** vanish along the
trivial ruler. Route (findings F1): shared process `li-pseudorandom`'s `atomDP a x g` with a
pseudorandom truth stream `x` decided at delay `g n ≤ F n`; siblings FAF's LIA perturbed at
`(F n, contract n)` to the truth (`perturbAt`, as `onGSystem`); `Hplus` FAF's LIA over the ledger
process, which is a causal builder of the truth stream once the ledger's own publication days are
accounted for (`liaHistory_union_atomDP_causal`'s pattern) — then `lic_learning_pseudorandom_
frequency_of_historicalVerifiers` prices the reindexed contract family at `p ∈ (0,1)` and
`defect = |x n − p|` is bounded away from `0`. `partial: over li-pseudorandom`'s causal-builder
machinery applied to the ledger process (not done).
Source: findings F1 (this package); root-fa-2-007 (ii)'s own caveat ("an e.c. family of decidable sentences does not in general have `P_n(φ_n) ≈ Thm(φ_n)`")
Kind: OPEN
Fidelity: n/a
Hyps: n/a -/
theorem horizon_idleness_fails_exists_open :
    ∃ (S : FrozenSystem) (ε : ℕ → ℚ), Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0) ∧
      Function.Injective S.F.f ∧ (∀ n, Timely S ε n) ∧
      ¬ AgreeAlong (fun _ => 0) (defect S) (fun _ => 0) := by
  sorry

end Cleanroom.Trust.LegitLiRegister
