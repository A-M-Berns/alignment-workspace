import Cleanroom.Deference.DefFrozenSibling.Defs
import Cleanroom.Deference.DefTrackingPin.Pin

/-!
# `legit-li-register` · Defs: the legitimacy predicates over the imported defect, and the
relaxed carrier

Package `Cleanroom.Trust.LegitLiRegister` ([[legit-li-register-mandate]] Targets 1, 3 and the
carrier convention). **Nothing here redefines the influence defect**: `d_n` is
`def-frozen-sibling`'s `defect S n = |Y n − Hplus (F n) (contract n)|` (root-fa-2-011 (i),
[[legitimacy-theory-v1]] §2.1), the gap at the horizon between the advised reasoner's price and
the sealed sibling's verdict, over the carrier `FrozenSystem` (two inductors over FAF deductive
processes sharing the base `D` and differing only in the ledger — checklist rows 3 and 13 of
[[def-frozen-sibling-hypotheses]]). This file adds only what the legitimacy note *names* on top
of it: `ε`-legitimacy of a day, legitimacy along an e.c. sub-fragment (the D3 statement shape
`AgreeAlong`), and the small lemmas about the accumulated defect `Dist`.

**The relaxed carrier `FrozenSystemL`** (mandate, "Carrier and conventions"). `FrozenSystem`
requires its contract family to be free of the ledger family (`contract_ledgerFree`) and of the
projection family (`contract_projFree`); `def-frozen-sibling`'s finding F5 is that the
anti-inductive (quote-referencing) contract is therefore unavailable in the base language. Claim 1
of the legitimacy note ([[legitimacy-theory-v1]] §3) is *about* that contract: the diagonal
`g_n = ∼⌜a_n > ½⌝` reads the ledger. So this package states Claim 1 over `FrozenSystemL`, which is
`FrozenSystem` with those two freeness fields removed and every other field verbatim
(`toL` forgets them). **What transfers**: everything whose proof reads only the
`A`-side fields (`A_inductor`, `determinedA`, `hworldA`, `a_eq`) — T1 `tracking` is re-proved
below as `trackingL` (same proof, same hypotheses); the `[0,1]` ranges; the stage inclusions. **What
does not transfer**: anything resting on `hworldH`'s conservativity over a ledger-free base
(`base_subset_processH` still holds, but `truthAt_holds_H`-style facts about *base-language*
contracts — `DecidedBy`, `Timely`, `truthAt` — are not restated here, since a ledger literal is
never decided in the shared process, `def-frozen-sibling`'s `ledgerLiteral_not_mem_of_tagFree`),
and `li-projection`'s T7 off-`G` rows (`contract_projFree`). The defect over the relaxed carrier is
`FrozenSystemL.defect`, with `defect_toL` identifying it with the definition of record
on the image of `toL`.

Roles (as in the dependency): `A` the predictor, `Hplus` the advised reasoner, `sib n` the sealed
sibling of index `n`, `base` the shared process, `contract n` the question `P^{(n)}`, `Y n` the
sibling's verdict, `a n` the published quote, `F` the horizon.
-/

namespace Cleanroom.Trust.LegitLiRegister

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiAsympCalc
  Cleanroom.Found.LiQuoteLane Cleanroom.Li.LiCoupledPair Cleanroom.Deference.DefFrozenSibling
  Cleanroom.Deference.DefTrackingPin
open Filter Topology

/-! ## A. The legitimacy predicates (Target 1) -/

/-- **`ε`-legitimate feedback on day `n`** ([[legitimacy-theory-v1]] §2.1: "feedback on question
`n` is `ε`-legitimate iff `d_n ≤ ε`"), over the definition of record `defect`. A predicate on a
day, nothing more: "legitimate" here means exactly "the counterfactual gap is small" — FAF's
deductive process has no provenance, so this is the only carrier of the word in the run
(checklist row 2 of [[def-frozen-sibling-hypotheses]] stays unmodelled).
Source: root-fa-041; [[legitimacy-theory-v1]] §2.1 l. 39
Kind: D
Fidelity: exact
Hyps: n/a -/
def EpsLegitimate (S : FrozenSystem) (ε : ℝ) (n : ℕ) : Prop := defect S n ≤ ε

/-- **Legitimate along an e.c. sub-fragment**: `d_n → 0` along the zero set of the ruler `t`
([[legitimacy-theory-v1]] §2.1: "a training process is legitimate on a family iff `d_n → 0` along
it"), in `def-frozen-sibling`'s D3 shape `AgreeAlong t (defect S) 0` — never for a free set.
Vacuous on a finite zero set (as every `AgreeAlong` statement; disclosed as the dependency does).
Source: root-fa-041; [[legitimacy-theory-v1]] §2.1 l. 39; mandate Target 1
Kind: D
Fidelity: exact (along e.c. sub-fragments)
Hyps: n/a -/
def LegitimateAlong (S : FrozenSystem) (t : ℕ → ℕ) : Prop :=
  AgreeAlong t (defect S) (fun _ => 0)

/-- `LegitimateAlong` unfolded: for every `δ > 0`, eventually on the fragment `defect S n ≤ δ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem legitimateAlong_iff (S : FrozenSystem) (t : ℕ → ℕ) :
    LegitimateAlong S t ↔ ∀ δ > 0, ∀ᶠ n in atTop, t n = 0 → defect S n ≤ δ := by
  unfold LegitimateAlong AgreeAlong
  constructor
  · intro h δ hδ
    filter_upwards [h δ hδ] with n hn ht
    have hd : 0 ≤ defect S n := abs_nonneg _
    have := hn ht
    rwa [sub_zero, abs_of_nonneg hd] at this
  · intro h δ hδ
    filter_upwards [h δ hδ] with n hn ht
    have hd : 0 ≤ defect S n := abs_nonneg _
    rw [sub_zero, abs_of_nonneg hd]
    exact hn ht

/-- Legitimacy along a fragment is `ε`-legitimacy eventually on it, for every `ε > 0`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem LegitimateAlong.eventually_epsLegitimate {S : FrozenSystem} {t : ℕ → ℕ}
    (h : LegitimateAlong S t) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, t n = 0 → EpsLegitimate S ε n :=
  (legitimateAlong_iff S t).1 h ε hε

/-- **The defect lies in `[0,1]`**: both terms are prices in `[0,1]` (`Y_mem_Icc` from
settlement, `IsLogicalInductor.price_mem_Icc` for the advised reasoner).
Source: mandate Target 1 (`defect_mem_Icc`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem defect_mem_Icc (S : FrozenSystem) (n : ℕ) : 0 ≤ defect S n ∧ defect S n ≤ 1 := by
  haveI := S.Hplus_inductor
  obtain ⟨hY0, hY1⟩ := S.Y_mem_Icc n
  obtain ⟨hH0, hH1⟩ := IsLogicalInductor.price_mem_Icc (P := S.Hplus) (DP := S.processH)
    (S.F.f n) (S.contract n)
  have hY0' : (0 : ℝ) ≤ S.Y n := by exact_mod_cast hY0
  have hY1' : (S.Y n : ℝ) ≤ 1 := by exact_mod_cast hY1
  refine ⟨abs_nonneg _, ?_⟩
  unfold defect
  rw [abs_le]
  constructor <;> linarith

/-! ## B. The accumulated defect (Target 3) -/

/-- `Dist` is a sum of non-negative terms.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Dist_nonneg (S : FrozenSystem) (ε : ℕ → ℚ) (N : ℕ) :
    0 ≤ Deference.DefFrozenSibling.Dist S ε N := by
  unfold Deference.DefFrozenSibling.Dist
  refine Finset.sum_nonneg (fun n _ => ?_)
  split_ifs
  · exact le_rfl
  · exact abs_nonneg _

/-- **`Dist` is monotone in the day**: adding a day adds a non-negative term.
Source: root-fa-2-011 (i) (the accumulated defect); mandate Target 3
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem Dist_mono_N (S : FrozenSystem) (ε : ℕ → ℚ) (N : ℕ) :
    Deference.DefFrozenSibling.Dist S ε N ≤ Deference.DefFrozenSibling.Dist S ε (N + 1) := by
  unfold Deference.DefFrozenSibling.Dist
  rw [Finset.sum_range_succ (n := N + 1)]
  have : (0 : ℝ) ≤ if Timely S ε (N + 1) then 0 else defect S (N + 1) := by
    split_ifs
    · exact le_rfl
    · exact abs_nonneg _
  linarith

/-- A larger tolerance keeps every timely day timely.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem Timely.mono_tol {S : FrozenSystem} {ε ε' : ℕ → ℚ} (h : ∀ n, ε n ≤ ε' n) {n : ℕ}
    (hT : Timely S ε n) : Timely S ε' n :=
  ⟨hT.1, hT.2.trans (h n)⟩

/-- **`Dist` is antitone in the tolerance**: a larger tolerance enlarges `G`, which removes
summands (every summand is non-negative). This is the only monotonicity of "grow `G`" that holds
in the tolerance clause; in the horizon only the decided clause is monotone (`decidedBy_mono`,
`Misc.lean`), and the tolerance clause is not (`timely_not_horizon_only`, `timely_not_mono_open`).
Source: root-fa-2-011 (ii); [[legitimacy-theory-v1]] §7.2 ("grow `G`"); mandate Target 3
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem Dist_antitone_tol (S : FrozenSystem) {ε ε' : ℕ → ℚ} (h : ∀ n, ε n ≤ ε' n) (N : ℕ) :
    Deference.DefFrozenSibling.Dist S ε' N ≤ Deference.DefFrozenSibling.Dist S ε N := by
  unfold Deference.DefFrozenSibling.Dist
  refine Finset.sum_le_sum (fun n _ => ?_)
  by_cases hT : Timely S ε n
  · rw [if_pos hT, if_pos (Timely.mono_tol h hT)]
  · rw [if_neg hT]
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl

/-- **`Dist` is bounded by the number of off-`G` days** up to `N` (every defect is at most `1`).
Source: root-fa-2-011 (i); mandate Target 3 (`Dist_le_offG_count`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem Dist_le_offG_count (S : FrozenSystem) (ε : ℕ → ℚ) (N : ℕ) :
    Deference.DefFrozenSibling.Dist S ε N ≤
      ((Finset.range (N + 1)).filter (fun n => ¬ Timely S ε n)).card := by
  unfold Deference.DefFrozenSibling.Dist
  calc (∑ n ∈ Finset.range (N + 1), if Timely S ε n then (0 : ℝ) else defect S n)
      ≤ ∑ n ∈ Finset.range (N + 1), (if ¬ Timely S ε n then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum (fun n _ => ?_)
        by_cases hT : Timely S ε n
        · simp [hT]
        · simp only [hT, not_false_eq_true, if_true, if_false]
          exact (defect_mem_Icc S n).2
    _ = ((Finset.range (N + 1)).filter (fun n => ¬ Timely S ε n)).card := by
        rw [Finset.sum_boole]

/-! ## C. Evidence versus influence: what the fragments read (Target 1, §2.2) -/

/-- **The decided clause reads only the shared data**: two systems with the same shared process,
contract family and horizon decide the same days. With `truthAt_of_shared_eq` and
`timely_of_shared_eq`: `DecidedBy`, `truthAt` and `Timely` are functions of `(base, contract, F, Y)`
alone — the stages the sibling and the advised reasoner share — whereas `defect` additionally
reads `Hplus`, an inductor over a process containing the quote. This is the only formal shape over
FAF of the note's "evidence is what moves both runs; influence is what moves only the coupled one"
(the interpretation is recorded in [[legit-li-register-findings]], labelled INTERPRETATION).
Source: [[legitimacy-theory-v1]] §2.2 l. 51; mandate Target 1
Kind: L
Fidelity: n/a (a congruence)
Hyps: (a) none -/
theorem decidedBy_of_shared_eq (S S' : FrozenSystem) (hb : S'.base = S.base)
    (hc : S'.contract = S.contract) (hF : S'.F = S.F) (n : ℕ) :
    DecidedBy S' n ↔ DecidedBy S n := by
  unfold DecidedBy
  rw [hb, hc, hF]

/-- `truthAt` reads only the shared data.
Source: [[legitimacy-theory-v1]] §2.2 l. 51; mandate Target 1
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem truthAt_of_shared_eq (S S' : FrozenSystem) (hb : S'.base = S.base)
    (hc : S'.contract = S.contract) (hF : S'.F = S.F) (n : ℕ) :
    truthAt S' n = truthAt S n := by
  unfold truthAt
  rw [hb, hc, hF]

/-- `Timely` reads only the shared data and the sibling's verdict.
Source: [[legitimacy-theory-v1]] §2.2 l. 51; mandate Target 1
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem timely_of_shared_eq (S S' : FrozenSystem) (hb : S'.base = S.base)
    (hc : S'.contract = S.contract) (hF : S'.F = S.F) (hY : S'.Y = S.Y) (ε : ℕ → ℚ) (n : ℕ) :
    Timely S' ε n ↔ Timely S ε n := by
  unfold Timely
  rw [decidedBy_of_shared_eq S S' hb hc hF, truthAt_of_shared_eq S S' hb hc hF, hY]

/-! ## D. The relaxed carrier for ledger-referencing contracts -/

/-- **The frozen-deliberation system with a ledger-referencing contract allowed**: `FrozenSystem`
without `contract_ledgerFree` and `contract_projFree`, every other field verbatim (see the module
docstring for what transfers). Carrier, not claim. Needed because Claim 1's diagonal contract
`gDiag n = ∼⌜a_n > ½⌝` *is* a ledger literal (`def-frozen-sibling` F5); stated over
`FrozenSystem` the headline would be vacuous.
Source: mandate "Carrier and conventions" (`FrozenSystemL`); `def-frozen-sibling` D1 (the fields)
Kind: D
Fidelity: variant: the two freeness fields dropped; otherwise the dependency's carrier
Hyps: n/a (a structure) -/
structure FrozenSystemL where
  /-- The shared world process `D`. -/
  base : DeductiveProcess
  /-- The predictor's base process `D_A`. -/
  DPA0 : DeductiveProcess
  /-- `D_A ⊇ D`. -/
  shared : ∀ n, base.D n ⊆ DPA0.D n
  /-- Publication of the quote `a n` into the `H`-side ledger (item `0`). -/
  eq : PublicationSchedule
  /-- Publication of the settled value `Y n` into the `H`-side ledger (item `1`). -/
  eY : PublicationSchedule
  /-- The horizon `F`. -/
  F : DeferralFunction
  /-- Settlement of the contract into the predictor's process. -/
  σ : PublicationSchedule
  /-- The quote is published before the horizon. -/
  eq_lt_F : ∀ n, eq.e n < F.f n
  /-- The horizon precedes settlement. -/
  F_lt_σ : ∀ n, F.f n < σ.e n
  /-- The settled value reaches the `H`-side no earlier than settlement. -/
  σ_le_eY : ∀ n, σ.e n ≤ eY.e n
  /-- The contract propositions `P^{(n)}` — **may** be ledger literals. -/
  contract : ℕ → Sentence
  /-- The contract family is e.c. -/
  contract_codes : MachineSentenceCodes contract
  /-- The predictor `A`. -/
  A : History
  /-- The advised reasoner `H⁺`. -/
  Hplus : History
  /-- The sealed siblings `H^{[N]}`. -/
  sib : ℕ → History
  /-- The published quote table. -/
  a : ℕ → ℚ
  /-- The settled values. -/
  Y : ℕ → ℚ
  /-- The contract settles to the sibling's exact day-`F n` price of `P^{(n)}`. -/
  Y_eq : ∀ n, (Y n : ℝ) = sib n (F.f n) (contract n)
  /-- The quote is `A`'s day-`n` expectation of the contract LUV. -/
  a_eq : ∀ n, (a n : ℝ) = (ledgerLuv 0 n).expect A n
  /-- `A` is an inductor over its base plus the contract ledger (settled at `σ` to `Y`). -/
  A_inductor : IsLogicalInductor A (ledgerProcess DPA0 (fun _ n => Y n) (fun _ => σ))
  /-- `H⁺` is an inductor over the shared process plus the two-item ledger. -/
  Hplus_inductor : IsLogicalInductor Hplus (ledgerProcess base (frozenTable a Y) (frozenSched eq eY))
  /-- Sibling `N` is an inductor over the two-item ledger frozen at day `N`. -/
  sib_inductor : ∀ N, IsLogicalInductor (sib N)
    (siblingProcess base (frozenTable a Y) (frozenSched eq eY) N)
  /-- Every stage of `A`'s process has a consistent world. -/
  hworldA : ∀ n, ∃ v : PCWorld,
    v.ConsistentWith ((ledgerProcess DPA0 (fun _ n => Y n) (fun _ => σ)).D n)
  /-- Every stage of `H⁺`'s process has a consistent world. -/
  hworldH : ∀ n, ∃ v : PCWorld,
    v.ConsistentWith ((ledgerProcess base (frozenTable a Y) (frozenSched eq eY)).D n)
  /-- Every stage of every sibling's process has a consistent world. -/
  hworldSib : ∀ N n, ∃ v : PCWorld,
    v.ConsistentWith ((siblingProcess base (frozenTable a Y) (frozenSched eq eY) N).D n)
  /-- `A`'s contract LUV is determined, in `A`'s process, at `Y n`. -/
  determinedA : ∀ n, LUV.DeterminedVia (ledgerLuv 0 n)
    (ledgerProcess DPA0 (fun _ n => Y n) (fun _ => σ)) (Y n)
  /-- Every `H`-side ledger LUV is determined, in `H⁺`'s process, at the table. -/
  determinedH : ∀ j n, LUV.DeterminedVia (ledgerLuv j n)
    (ledgerProcess base (frozenTable a Y) (frozenSched eq eY)) (frozenTable a Y j n)
  /-- In sibling `N`, the ledger LUVs of days `n < N` are determined at the table. -/
  determinedSib : ∀ N j n, n < N → LUV.DeterminedVia (ledgerLuv j n)
    (siblingProcess base (frozenTable a Y) (frozenSched eq eY) N) (frozenTable a Y j n)

namespace FrozenSystemL

/-- The predictor's process.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev processA (S : FrozenSystemL) : DeductiveProcess :=
  ledgerProcess S.DPA0 (fun _ n => S.Y n) (fun _ => S.σ)

/-- The advised reasoner's process.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev processH (S : FrozenSystemL) : DeductiveProcess :=
  ledgerProcess S.base (frozenTable S.a S.Y) (frozenSched S.eq S.eY)

/-- **The influence defect over the relaxed carrier**, the same expression as the definition of
record (`defect_toL` below).
Source: root-fa-2-011 (i), transported to the relaxed carrier
Kind: D
Fidelity: exact (the same expression)
Hyps: n/a -/
noncomputable def defect (S : FrozenSystemL) (n : ℕ) : ℝ :=
  |(S.Y n : ℝ) - S.Hplus (S.F.f n) (S.contract n)|

/-- The `[0,1]` range of the settled values (as `FrozenSystem.Y_mem_Icc`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem Y_mem_Icc (S : FrozenSystemL) (n : ℕ) : 0 ≤ S.Y n ∧ S.Y n ≤ 1 := by
  have h := determinedVia_mem_Icc (S.determinedA n) S.hworldA
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- The `[0,1]` range of the published quotes (as `FrozenSystem.a_mem_Icc`).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem a_mem_Icc (S : FrozenSystemL) (n : ℕ) : 0 ≤ S.a n ∧ S.a n ≤ 1 := by
  haveI := S.A_inductor
  have hP : ∀ m φ, 0 ≤ S.A m φ ∧ S.A m φ ≤ 1 := fun m φ =>
    IsLogicalInductor.price_mem_Icc (P := S.A) (DP := S.processA) m φ
  have h0 := (ledgerLuv 0 n).expectApprox_nonneg (S.A n) (n + 1) (fun s => (hP n s).1)
  have h1 := (ledgerLuv 0 n).expectApprox_le_one (S.A n) (n + 1) (fun s => (hP n s).2)
  have ha := S.a_eq n
  rw [LUV.expect] at ha
  exact ⟨by exact_mod_cast ha ▸ h0, by exact_mod_cast ha ▸ h1⟩

/-- `base_subset_processH` over the relaxed carrier.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem base_subset_processH (S : FrozenSystemL) (n : ℕ) : S.base.D n ⊆ S.processH.D n := by
  show S.base.D n ⊆ S.base.D n ∪ _
  exact Finset.subset_union_left

/-- **T1 over the relaxed carrier** — the same theorem as `def-frozen-sibling`'s `tracking`, with
the same proof: `def-tracking-pin`'s `pinning_ofApprox` at the contract LUV in `A`'s process, using
only `A_inductor`, `determinedA`, `hworldA` and `a_eq` (verified by re-proving: no freeness field
is touched). The one non-(a) hypothesis is `hz`, checklist row 6, exactly as there.
**Two-way**: `partial: over the OPEN pair` as the dependency's row (and, with a diagonal contract,
over `li-coupled-pair`'s `sealedSystem_exists`: no inhabitant of `FrozenSystemL` with a
ledger-referencing contract exists in the run).
Source: `def-frozen-sibling` `tracking` (anson-018; root-deference-038); mandate "Carrier and conventions"
Kind: L (instance of `def-tracking-pin`'s `pinning_ofApprox`)
Fidelity: as `tracking`
Hyps: (c) `hz` (checklist row 6); all else (a) -/
theorem trackingL (S : FrozenSystemL) (zhat : ℕ → ℚ) (hz : PGenerableRat S.A zhat)
    (hlim : Tendsto (fun n => (zhat n : ℝ) - S.Y n) atTop (𝓝 0)) :
    (fun n => (S.a n : ℝ)) ≈ₙ (fun n => (S.Y n : ℝ)) := by
  haveI := S.A_inductor
  have h := pinning_ofApprox (P := S.A) (DP := S.processA) (ledgerLuv_thresholdCodes 0)
    S.hworldA (v := fun n => (S.Y n : ℝ)) S.determinedA zhat hz hlim
  have he : (fun n => (S.a n : ℝ)) = fun n => (ledgerLuv 0 n).expect S.A n := funext S.a_eq
  rw [he]
  exact h

end FrozenSystemL

/-- Forgetting the two freeness fields.
Source: mandate "Carrier and conventions" (`FrozenSystem.toL`, named `toL` here)
Kind: D
Fidelity: n/a -/
def toL (S : FrozenSystem) : FrozenSystemL where
  base := S.base
  DPA0 := S.DPA0
  shared := S.shared
  eq := S.eq
  eY := S.eY
  F := S.F
  σ := S.σ
  eq_lt_F := S.eq_lt_F
  F_lt_σ := S.F_lt_σ
  σ_le_eY := S.σ_le_eY
  contract := S.contract
  contract_codes := S.contract_codes
  A := S.A
  Hplus := S.Hplus
  sib := S.sib
  a := S.a
  Y := S.Y
  Y_eq := S.Y_eq
  a_eq := S.a_eq
  A_inductor := S.A_inductor
  Hplus_inductor := S.Hplus_inductor
  sib_inductor := S.sib_inductor
  hworldA := S.hworldA
  hworldH := S.hworldH
  hworldSib := S.hworldSib
  determinedA := S.determinedA
  determinedH := S.determinedH
  determinedSib := S.determinedSib

/-- On the image of `toL` the relaxed defect is the definition of record.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem defect_toL (S : FrozenSystem) (n : ℕ) : (toL S).defect n = defect S n := rfl

end Cleanroom.Trust.LegitLiRegister
