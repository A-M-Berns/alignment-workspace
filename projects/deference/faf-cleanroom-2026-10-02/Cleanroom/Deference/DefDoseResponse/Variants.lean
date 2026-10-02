import Cleanroom.Deference.DefDoseResponse.Steering

/-!
# `def-dose-response` · Variants: dose compensation (T2.5) and presence-triggered steering (T7.6)

**T2.5 — dose compensation refutes the per-arm-stream variant** (anson-056; note §2.3 "why one
committed stream", §8). With *per-arm* streams `a i` whose steered prefixes are `v i`, arm `i`'s
destination is `½ + γ(v_i − ½)·p̂_i` (T2(a) with the per-arm stream); choosing
`v_i − ½ = s/(γ p̂_i)` makes every destination `½ + s`, so every cross-arm audit on `u` passes
although every arm was steered (`dose_compensation_audit_passes`). **Finding F5**: the note's
`v_i = ½ + s/p̂_i` yields `½ + γ s`, not `½ + s` (`note_compensation_destination`) — the gradient
is still flattened — and the range condition the note omits is `|s| ≤ γ p̂_i / 2`
(`compensation_admissible_iff`). Pre-registration (one committed stream) is necessary, not
prudent.

**T7.6 — presence-triggered steering is invisible** (the note's "honest negative", §8 "threshold
and basin behavior", deferred there): the arm `armPresence` jumps by `s` as soon as it was exposed
*at all* in the formative window. Any two arms with at least one exposed formative day have the
same destination `½ + s`, so every cross-arm audit passes (`presence_invisible`), while the
destination moved by `s` relative to the never-exposed arm (`presence_moved`): a design whose every
arm has nonzero realized dose on `[0, N)` cannot detect it.

Scope: one-way throughout. Kinds: C over `dose_graded_destination` / `project_indicator_expect_tendsto`.
-/

namespace Cleanroom.Deference.DefDoseResponse

open LogicalInduction LO.Propositional Cleanroom.Bli.BliFound Cleanroom.Li.LiProjection
  Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## T2.5 — dose compensation -/

/-- **Dose compensation flattens the gradient (headline).** On the per-arm stream with steered
prefix `v = ½ + s/(γ p̂)`, the arm's destination is `½ + s`, independent of its dose.
Source: [[dose-response]] §2.3 ("quote `v_i = ½ + s/p̂_i` at arm `i` and the dose-graded destinations become dose-invariant"), §8 ("Necessity of pre-registration"); anson-056
Kind: C
Fidelity: variant: the compensating prefix is `½ + s/(γ p̂_i)` — the note's `½ + s/p̂_i` is off by the factor `γ` (F5)
Hyps: (a) none -/
theorem dose_compensation_flat {base : DeductiveProcess} {c : ℕ → Bool} {ai : ℕ → ℚ}
    [IsLogicalInductor (armBase base c ai) (armProcess base c ai)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c ai).D n))
    {γ : ℚ} (hγ : γ ≠ 0) {N : ℕ} (hN : 0 < N) (hp : realizedDose c N ≠ 0) {s vi : ℚ}
    (hvi : ∀ j < N, ai j = vi) (hcomp : vi = 1 / 2 + s / (γ * realizedDose c N)) :
    limitingBelief (arm base γ N c ai) protSentence = ((1 / 2 + s : ℚ) : ℝ) := by
  rw [dose_graded_destination hworld γ hN hvi, hcomp]
  congr 1
  field_simp
  ring

/-- The expectation form of the flattened destination.
Source: [[dose-response]] §8 ("equalizes all destinations at `½ + s`")
Kind: C
Fidelity: variant (as above)
Hyps: (a) none -/
theorem dose_compensation_expect_tendsto {base : DeductiveProcess} {c : ℕ → Bool} {ai : ℕ → ℚ}
    [IsLogicalInductor (armBase base c ai) (armProcess base c ai)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c ai).D n))
    {γ : ℚ} (hγ : γ ≠ 0) {N : ℕ} (hN : 0 < N) (hp : realizedDose c N ≠ 0) {s vi : ℚ}
    (hvi : ∀ j < N, ai j = vi) (hcomp : vi = 1 / 2 + s / (γ * realizedDose c N)) :
    Tendsto (fun n => (LUV.indicatorOf protSentence).expect (arm base γ N c ai) n) atTop
      (𝓝 ((1 / 2 + s : ℚ) : ℝ)) := by
  have h := dose_graded_expect_tendsto hworld γ hN hvi
  have heq : ((1 / 2 + γ * (vi - 1 / 2) * realizedDose c N : ℚ) : ℝ) = ((1 / 2 + s : ℚ) : ℝ) := by
    congr 1
    rw [hcomp]
    field_simp
    ring
  rwa [heq] at h

/-- **T2.5 (headline): with per-arm streams, every cross-arm audit on `u` passes although every
arm was steered.** Two arms with distinct realized doses, each on its own compensated stream,
have the same destination `½ + s`, so the uniform cross-arm audit tends to `0`.
Source: [[dose-response]] §8 ("steering with a flattened gradient … The audit works iff the auditor forces the advisor to commit coarser than the arm partition"); anson-056
Kind: C
Fidelity: variant (F5)
Hyps: (a) none -/
theorem dose_compensation_audit_passes {base : DeductiveProcess} {ci cj : ℕ → Bool}
    {ai aj : ℕ → ℚ} [IsLogicalInductor (armBase base ci ai) (armProcess base ci ai)]
    [IsLogicalInductor (armBase base cj aj) (armProcess base cj aj)]
    (hworldi : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base ci ai).D n))
    (hworldj : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base cj aj).D n))
    {γ : ℚ} (hγ : γ ≠ 0) {N : ℕ} (hN : 0 < N) (hpi : realizedDose ci N ≠ 0)
    (hpj : realizedDose cj N ≠ 0) {s vi vj : ℚ} (hvi : ∀ j < N, ai j = vi)
    (hvj : ∀ j < N, aj j = vj) (hci : vi = 1 / 2 + s / (γ * realizedDose ci N))
    (hcj : vj = 1 / 2 + s / (γ * realizedDose cj N)) :
    Tendsto (crossArmAudit (arm base γ N ci ai) (arm base γ N cj aj) (LUV.indicatorOf protSentence))
      atTop (𝓝 0) := by
  have hi := dose_compensation_expect_tendsto hworldi hγ hN hpi hvi hci
  have hj := dose_compensation_expect_tendsto hworldj hγ hN hpj hvj hcj
  have h := tendsto_cesaro (hi.sub hj)
  rw [sub_self] at h
  exact h

/-- **Finding F5: the note's compensation `v_i = ½ + s/p̂_i` yields the destination `½ + γ s`**,
not `½ + s` — flattened all the same, but off by the factor `γ`.
Source: [[dose-response]] §2.3 and §8 (the display `v_i = ½ + s/p̂_i`); anson-056; findings F5
Kind: C
Fidelity: exact (the note's formula, its actual destination)
Hyps: (a) none -/
theorem note_compensation_destination {base : DeductiveProcess} {c : ℕ → Bool} {ai : ℕ → ℚ}
    [IsLogicalInductor (armBase base c ai) (armProcess base c ai)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c ai).D n))
    (γ : ℚ) {N : ℕ} (hN : 0 < N) (hp : realizedDose c N ≠ 0) {s vi : ℚ}
    (hvi : ∀ j < N, ai j = vi) (hcomp : vi = 1 / 2 + s / realizedDose c N) :
    limitingBelief (arm base γ N c ai) protSentence = ((1 / 2 + γ * s : ℚ) : ℝ) := by
  rw [dose_graded_destination hworld γ hN hvi, hcomp]
  congr 1
  field_simp
  ring

/-- **The range condition the note omits**: the compensating prefix `½ + s/(γ p̂)` is a `[0,1]`
quote iff `|s| ≤ γ p̂ / 2` (for `γ p̂ > 0`).
Source: [[dose-response]] §8 (no range condition stated); findings F5
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem compensation_admissible_iff {γ p s : ℚ} (hγp : 0 < γ * p) :
    (0 ≤ 1 / 2 + s / (γ * p) ∧ 1 / 2 + s / (γ * p) ≤ 1) ↔ |s| ≤ γ * p / 2 := by
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have : -(1 / 2 : ℚ) ≤ s / (γ * p) := by linarith
      rw [le_div_iff₀ hγp] at this
      linarith
    · have : s / (γ * p) ≤ 1 / 2 := by linarith
      rw [div_le_iff₀ hγp] at this
      linarith
  · rintro ⟨h1, h2⟩
    constructor
    · have : -(1 / 2 : ℚ) ≤ s / (γ * p) := by
        rw [le_div_iff₀ hγp]; linarith
      linarith
    · have : s / (γ * p) ≤ 1 / 2 := by
        rw [div_le_iff₀ hγp]; linarith
      linarith

/-! ## T7.6 — presence-triggered steering -/

/-- **The presence-triggered weight**: `½` through the formative window, then `½ + s` if the arm
was exposed at all in the window, `½` otherwise.
Source: [[dose-response]] §8 ("presence-triggered steering (a disposition that activates only when exposure ever occurs)"); mandate T7.6
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def presenceWeight (s : ℚ) (N : ℕ) (c : ℕ → Bool) : ℕ → ℚ := fun n =>
  by classical exact
    if n < N then 1 / 2 else 1 / 2 + s * (if ∃ j < N, c j = true then 1 else 0)

/-- **The presence-triggered arm**: the projection of the base LIA on `u` with the presence weight.
Source: [[dose-response]] §8; mandate T7.6
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def armPresence (base : DeductiveProcess) (s : ℚ) (N : ℕ) (c : ℕ → Bool)
    (a : ℕ → ℚ) : History :=
  project (armBase base c a) protAtom (presenceWeight s N c)

/-- The presence weight is eventually constant from the window end.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem presenceWeight_jump (s : ℚ) (N : ℕ) (c : ℕ → Bool) :
    ∀ n, N ≤ n → presenceWeight s N c n = presenceWeight s N c N := by
  intro n hn
  simp [presenceWeight, not_lt.mpr hn]

/-- The presence weight at the window end: `½ + s` if exposed at all, `½` otherwise.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem presenceWeight_at (s : ℚ) (N : ℕ) (c : ℕ → Bool) :
    presenceWeight s N c N = 1 / 2 + s * (if ∃ j < N, c j = true then 1 else 0) := by
  simp [presenceWeight]

/-- The presence weight is e.c.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem presenceWeight_machineRatCodes (s : ℚ) (N : ℕ) (c : ℕ → Bool) :
    MachineRatCodes (presenceWeight s N c) :=
  MachineRatCodes.ofFiniteTable _ N (presenceWeight s N c N) (presenceWeight_jump s N c)

/-- The presence weight lives in `[½ − |s|, ½ + |s|]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem presenceWeight_mem (s : ℚ) (N : ℕ) (c : ℕ → Bool) :
    ∀ n, 1 / 2 - |s| ≤ presenceWeight s N c n ∧ presenceWeight s N c n ≤ 1 - (1 / 2 - |s|) := by
  intro n
  have hs := abs_nonneg s
  have h1 := le_abs_self s
  have h2 := neg_abs_le s
  unfold presenceWeight
  split_ifs <;> constructor <;> linarith

/-- The presence-triggered arm is a logical inductor over its exposure ledger for `|s| < ½`
(Lemma A; rests on `li-projection` (A)).
Source: mandate T7.6
Kind: C
Fidelity: exact
Hyps: (a) all; rests on the OPEN rewriters through `project_isLogicalInductor` -/
theorem armPresence_isLogicalInductor {base : DeductiveProcess}
    (hbase : ComputableDeductiveProcess base) (hfree : AtomFreeProcess protAtom base) {s : ℚ}
    (hs : |s| < 1 / 2) (N : ℕ) {c : ℕ → Bool} {a : ℕ → ℚ} (hc : Computable c)
    (ha : Computable a) :
    IsLogicalInductor (armPresence base s N c a) (armProcess base c a) :=
  haveI := armBase_isLogicalInductor hbase hc ha
  project_isLogicalInductor (armBase base c a) (armProcess base c a) protAtom
    (armProcess_atomFree hfree c a) (presenceWeight s N c) (1 / 2 - |s|) (by linarith)
    (presenceWeight_mem s N c) (presenceWeight_machineRatCodes s N c) N
    (presenceWeight_jump s N c)

/-- The presence-triggered arm's expectation of `𝟙(u)` tends to its jump target.
Source: mandate T7.6
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem armPresence_expect_tendsto {base : DeductiveProcess} {c : ℕ → Bool} {a : ℕ → ℚ}
    [IsLogicalInductor (armBase base c a) (armProcess base c a)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c a).D n)) (s : ℚ) (N : ℕ) :
    Tendsto (fun n => (LUV.indicatorOf protSentence).expect (armPresence base s N c a) n) atTop
      (𝓝 (presenceWeight s N c N)) :=
  project_indicator_expect_tendsto (armBase base c a) (armProcess base c a) hworld protAtom
    (presenceWeight s N c) N (presenceWeight_jump s N c)

/-- **An arm exposed at least once in the window settles at `½ + s`.**
Source: mandate T7.6
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem armPresence_destination_exposed {base : DeductiveProcess} {c : ℕ → Bool} {a : ℕ → ℚ}
    [IsLogicalInductor (armBase base c a) (armProcess base c a)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c a).D n)) (s : ℚ) (N : ℕ)
    (hex : ∃ j < N, c j = true) :
    limitingBelief (armPresence base s N c a) protSentence = ((1 / 2 + s : ℚ) : ℝ) := by
  unfold armPresence
  rw [limitingBelief_project_atom (armBase base c a) (armProcess base c a) hworld protAtom
    (presenceWeight s N c) N (presenceWeight_jump s N c), presenceWeight_at, if_pos hex, mul_one]

/-- **A never-exposed arm settles at `½`.**
Source: mandate T7.6
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem armPresence_destination_unexposed {base : DeductiveProcess} {c : ℕ → Bool} {a : ℕ → ℚ}
    [IsLogicalInductor (armBase base c a) (armProcess base c a)]
    (hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base c a).D n)) (s : ℚ) (N : ℕ)
    (hne : ¬ ∃ j < N, c j = true) :
    limitingBelief (armPresence base s N c a) protSentence = ((1 / 2 : ℚ) : ℝ) := by
  unfold armPresence
  rw [limitingBelief_project_atom (armBase base c a) (armProcess base c a) hworld protAtom
    (presenceWeight s N c) N (presenceWeight_jump s N c), presenceWeight_at, if_neg hne, mul_zero,
    add_zero]

/-- **T7.6 (headline): presence-triggered steering is invisible to every design whose arms are
all exposed.** Any two presence-triggered arms with at least one exposed formative day each have
equal destinations, so the uniform cross-arm audit on `u` passes.
Source: [[dose-response]] §8 ("the honest negative that presence-triggered steering … is invisible to any design whose every arm has nonzero dose"); mandate T7.6
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem presence_invisible {base : DeductiveProcess} {ci cj : ℕ → Bool} {a : ℕ → ℚ}
    [IsLogicalInductor (armBase base ci a) (armProcess base ci a)]
    [IsLogicalInductor (armBase base cj a) (armProcess base cj a)]
    (hworldi : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base ci a).D n))
    (hworldj : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base cj a).D n)) (s : ℚ) (N : ℕ)
    (hexi : ∃ j < N, ci j = true) (hexj : ∃ j < N, cj j = true) :
    Tendsto (crossArmAudit (armPresence base s N ci a) (armPresence base s N cj a)
      (LUV.indicatorOf protSentence)) atTop (𝓝 0) := by
  have hi := armPresence_expect_tendsto hworldi s N
  have hj := armPresence_expect_tendsto hworldj s N
  rw [presenceWeight_at, if_pos hexi] at hi
  rw [presenceWeight_at, if_pos hexj] at hj
  have h := tendsto_cesaro (hi.sub hj)
  rw [sub_self] at h
  exact h

/-- **T7.6, the moved destination**: relative to a never-exposed arm, an exposed arm's destination
moved by exactly `s` — the effect the all-exposed design cannot see.
Source: [[dose-response]] §8; mandate T7.6
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem presence_moved {base : DeductiveProcess} {ci cj : ℕ → Bool} {a : ℕ → ℚ}
    [IsLogicalInductor (armBase base ci a) (armProcess base ci a)]
    [IsLogicalInductor (armBase base cj a) (armProcess base cj a)]
    (hworldi : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base ci a).D n))
    (hworldj : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((armProcess base cj a).D n)) (s : ℚ) (N : ℕ)
    (hexi : ∃ j < N, ci j = true) (hnej : ¬ ∃ j < N, cj j = true) :
    limitingBelief (armPresence base s N ci a) protSentence -
      limitingBelief (armPresence base s N cj a) protSentence = (s : ℝ) := by
  rw [armPresence_destination_exposed hworldi s N hexi,
    armPresence_destination_unexposed hworldj s N hnej]
  push_cast
  ring

end Cleanroom.Deference.DefDoseResponse
