import Cleanroom.Deference.DefObstruction.Blind
import Cleanroom.Deference.DefObstruction.FragmentWitness

/-!
# `def-obstruction` · BlindWitness: tracking is satisfiable, and the diagonal's credence is table-dependent (T8, N+)

Two witnesses for § T8's definitions, over FAF's LIA (repair round 2).

**`TracksFamily` is satisfiable, non-degenerately** (audit r2 N7 asked for a record of this; it
is also the mandate's *benign family* for T12, previously "not built"): over the stronger base
`paperAdjoin`, where the obstruction atom is a stage-`0` fact, the family `obsFamily n` —
`∼obsAtom` on even days, `obsAtom` on odd days — is tag-free and stage-decided alternately false
and true, and the alternating table `aAlt` (`0` even, `1` odd) is the matching `0/1` table:
`adjPair_tracks_obsFamily : TracksFamily adjPair succDeferral obsFamily`. T7(a) along the
deferral: `aAlt_n − 𝔼^H_{n+1}(𝟙 obsFamily_n) → 0`, by `lic_provind_true`/`_false` on the two
constant subfamilies and `thm:ei` on the parity-dispatched family. So `dichotomy_2a_half`'s
conclusion `¬ TracksFamily` is informative, and `externalized_self_trust`'s Tracking antecedent
`hT` is inhabited on a non-constant table and a non-constant family (its three packages are
not).

**The diagonal's credence settlement is table-dependent** (fidelity B1's remark made a theorem):
`BlindSentence` is truth-value blindness; the source's blindness (`SettlementBlind`) is of the
settlement map, i.e. of the credence `Y_n`. For the diagonal the credence reading fails too, on
FAF's LIA: over the same base `paperDP 𝗜𝚺₁` and next-day schedule, `halfPair.Y → 1` while
`altPair.Y` follows the alternating side, so the two credence streams are not asymptotically
equal (`gDiag_credence_table_dependent`). This is the credence-level companion of
`gDiag_not_blind`. It does **not** extend to quote-free families: there the source's "not blind"
(2b's case) is a claim about actual prices on undecided sentences, which no criterion theorem
decides either way (findings F-Dichotomy).

Scope: one-way.
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Found.LiQuoteLane
open Cleanroom.Found.LiAsympCalc Cleanroom.Li.LiDiagonal
open Filter Topology

/-! ## A. The benign family: tracking is satisfiable -/

/-- **The benign family**: `∼obsAtom` on even days, `obsAtom` on odd days — tag-free and, over
`paperAdjoin`, decided false on even days and true on odd days. The matching `0/1` table is
`aAlt`.
Scope: one-way.
Source: mandate T12 (the benign family: "`P^(n)` tag-free and stage-decided alternately true/false, `a 0 n := s'_n` the matching `0/1` table"); audit r2 N7
Kind: D
Fidelity: n/a (the witness's own object)
Hyps: n/a -/
def obsFamily (n : ℕ) : Sentence := if n % 2 = 0 then ∼ obsAtom else obsAtom

/-- The benign family re-indexed by the reading day: `obsFamilyPred (n + 1) = obsFamily n`.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
def obsFamilyPred (m : ℕ) : Sentence := obsFamily (m - 1)

/-- `obsFamilyPred_succ`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem obsFamilyPred_succ (n : ℕ) : obsFamilyPred (n + 1) = obsFamily n := by
  unfold obsFamilyPred; rw [Nat.add_sub_cancel]

/-- The re-indexed benign family is e.c.: FAF's `ifZero` on the parity ruler `m ↦ (m − 1) % 2`
with two constant leaves.
Source: none: infrastructure (a certificate)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem obsFamilyPred_codes : MachineSentenceCodes obsFamilyPred := by
  have h := MachineSentenceCodes.ifZero (MachineSentenceCodes.const (∼ obsAtom))
    (MachineSentenceCodes.const obsAtom) predParity_ruler
  exact MachineSentenceCodes.of_eq h fun m => rfl

/-- The obstruction atom is decided true in the advised reader's process over the stronger base
(`paperAdjoin_decided` transferred through the ledger).
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem adjPair_obsAtom_decided : DecidedTrueAt adjPair.process obsAtom :=
  paperAdjoin_decided.ledger (a := aAlt) (e := fun _ => PublicationSchedule.succ)
    (paperAdjoin_freeOf_ledger _ _) obsAtom_tagFree

/-- Its negation is decided false there.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem adjPair_negObsAtom_decidedFalse : DecidedFalseAt adjPair.process (∼ obsAtom) := by
  obtain ⟨k, hk⟩ := adjPair_obsAtom_decided
  exact ⟨k, fun v hv h => ((PCWorld.holds_neg v obsAtom).mp h) (hk v hv)⟩

/-- **Tracking is satisfiable, non-degenerately (N+)**: over `adjPair` — FAF's LIA over the
stronger base plus the alternating ledger — the alternating table tracks the benign family along
`succDeferral`: `aAlt_n ≈ₙ 𝔼^H_{n+1}(𝟙 obsFamily_n)`. Both sequences vary: the table is the
`0/1` alternating one, the family alternates between a decided-false and a decided-true
sentence. This is T7(a) along the deferral, and the mandate's benign-family Tracking instance
for T12 (`externalized_self_trust`'s `hT` at `X n := 𝟙 (obsFamily n)`).
Scope: one-way.
Source: mandate T12 (the benign family); [[self-referential-settlement-target]] §5.4 (the decided fragment trusts) and §5.1 "what this is and is not" (the "statistical residue" on which Tracking holds); audit r2 N7
Kind: N+
Fidelity: exact (`TracksFamily` as defined; FAF's `expect`)
Hyps: (a) none -/
theorem adjPair_tracks_obsFamily : TracksFamily adjPair succDeferral obsFamily := by
  haveI := adjPair.H_inductor
  -- `thm:ei` on the re-indexed family, read at day `m`
  have hei : Tendsto (fun m => (LUV.indicatorOf (obsFamilyPred m)).expect adjPair.H m
      - adjPair.H m (obsFamilyPred m)) atTop (𝓝 0) :=
    lic_expectation_indicator_unconditional adjPair.H adjPair.process obsFamilyPred
      obsFamilyPred_codes adjPair.hworld
  -- prices of the two constant subfamilies
  have h1 : Tendsto (fun m => adjPair.H m obsAtom) atTop (𝓝 1) :=
    price_tendsto_one_of_decidedTrue adjPair.H adjPair.process adjPair.hworld obsAtom
      adjPair_obsAtom_decided
  have h0 : Tendsto (fun m => adjPair.H m (∼ obsAtom)) atTop (𝓝 0) :=
    price_tendsto_zero_of_decidedFalse adjPair.H adjPair.process adjPair.hworld (∼ obsAtom)
      adjPair_negObsAtom_decidedFalse
  -- shift everything to the reading day `n + 1`
  have hei' : Tendsto (fun n => (LUV.indicatorOf (obsFamily n)).expect adjPair.H (n + 1)
      - adjPair.H (n + 1) (obsFamily n)) atTop (𝓝 0) := by
    have := hei.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using this
  have h1' : Tendsto (fun n => adjPair.H (n + 1) obsAtom) atTop (𝓝 1) := by
    have := h1.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using this
  have h0' : Tendsto (fun n => adjPair.H (n + 1) (∼ obsAtom)) atTop (𝓝 0) := by
    have := h0.comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using this
  -- the table minus the price of the family is squeezed by the two deviations
  have hsq : Tendsto (fun n => (aAlt 0 n : ℝ) - adjPair.H (n + 1) (obsFamily n))
      atTop (𝓝 0) := by
    have hb : Tendsto
        (fun n => |adjPair.H (n + 1) obsAtom - 1| + |adjPair.H (n + 1) (∼ obsAtom)|)
        atTop (𝓝 0) := by
      have := ((h1'.sub_const 1).abs).add (h0'.abs)
      simpa using this
    refine squeeze_zero_norm (fun n => ?_) hb
    unfold obsFamily aAlt
    split_ifs with h
    · simp only [Rat.cast_zero, zero_sub, norm_neg, Real.norm_eq_abs]
      exact le_add_of_nonneg_left (abs_nonneg _)
    · simp only [Rat.cast_one, Real.norm_eq_abs]
      rw [abs_sub_comm]
      exact le_add_of_nonneg_right (abs_nonneg _)
  -- assemble: `a − 𝔼 = (a − P) − (𝔼 − P)`
  show Tendsto (fun n => (adjPair.a 0 n : ℝ)
    - (LUV.indicatorOf (obsFamily n)).expect adjPair.H (succDeferral n)) atTop (𝓝 0)
  have := hsq.sub hei'
  rw [sub_zero] at this
  refine this.congr fun n => ?_
  show (aAlt 0 n : ℝ) - adjPair.H (n + 1) (obsFamily n)
      - ((LUV.indicatorOf (obsFamily n)).expect adjPair.H (n + 1)
        - adjPair.H (n + 1) (obsFamily n)) =
      (aAlt 0 n : ℝ) - (LUV.indicatorOf (obsFamily n)).expect adjPair.H (n + 1)
  ring

/-! ## B. The diagonal's credence settlement is table-dependent -/

/-- **The diagonal's credence is not table-independent** (the source's blindness, credence
reading, for the diagonal): over the same base `paperDP 𝗜𝚺₁` and next-day schedule, the
constant-`½` pair's deferred credence `Y_n → 1` while the alternating pair's follows the
alternating side `𝟙[aAlt_n ≤ ½]`, so the two credence streams are not asymptotically equal.
The credence-level companion of `gDiag_not_blind` (the truth-value reading); both over FAF's
LIA.
Scope: one-way.
Source: [[self-referential-settlement-target]] §4.1 ("the self-referential target violates blindness": the settlement map `n ↦ m*_n` encodes `Y_n`); audit r2 fidelity B1 (the source's blindness is of the credence)
Kind: N+ (two FAF inductors over one base and schedule, one with a non-constant table)
Fidelity: exact (asymptotic inequality of the two credence streams — the source's `∂D_A/∂A ≠ 0` for the diagonal, in the credence reading)
Hyps: (a) none -/
theorem gDiag_credence_table_dependent :
    ¬ (halfPair.Y succDeferral ≈ₙ altPair.Y succDeferral) := by
  intro h
  -- `altPair.Y → 1` would follow
  have hY : Tendsto (altPair.Y succDeferral) atTop (𝓝 1) := by
    have h' : Tendsto (fun n => halfPair.Y succDeferral n - altPair.Y succDeferral n)
        atTop (𝓝 0) := h
    have := halfPair_Y_tendsto_one.sub h'
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    ring
  -- so the side would tend to `1`
  have hside : Tendsto (fun n => side (aAlt 0) n) atTop (𝓝 1) := by
    have h2 : Tendsto (fun n => altPair.Y succDeferral n - side (aAlt 0) n) atTop (𝓝 0) :=
      squeeze_zero_norm (fun n => (Real.norm_eq_abs _).le) altPair_Y_sub_side
    have := hY.sub h2
    rw [sub_zero] at this
    refine this.congr fun n => ?_
    ring
  -- but on odd days the side is `0`
  rw [Metric.tendsto_atTop] at hside
  obtain ⟨N, hN⟩ := hside (1 / 2) (by norm_num)
  have h3 := hN (2 * N + 1) (by omega)
  rw [side_aAlt] at h3
  have hmod : (2 * N + 1) % 2 ≠ 0 := by omega
  rw [if_neg hmod] at h3
  norm_num [Real.dist_eq] at h3

end Cleanroom.Deference.DefObstruction
