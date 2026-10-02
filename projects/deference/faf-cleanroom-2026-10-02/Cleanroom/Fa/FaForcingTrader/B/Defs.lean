import Cleanroom.Fa.FaTheoremA.Defs
import Cleanroom.Found.LiAsympCalc.WeightedAverage
import Cleanroom.Found.DefLattice.Expert
import LogicalInduction.Construction.Quotation.DeferralFibre
import LogicalInduction.Properties.Pseudorandomness

/-!
# `fa-forcing-trader` · angle B · Defs: legibility, the schedule indicator, the scheduled gate

Angle B's copies of the package's shared definitions ([[fa-forcing-trader-mandate]] § Definitions
of record). Angle A had not committed `Defs.lean`/`Schedule.lean` when B started (the directory
`Cleanroom/Fa/FaForcingTrader/` did not exist at 16:40 on 2026-10-01), so, as the mandate
instructs, B carries its own copies under `B/` in the namespace `Cleanroom.Fa.FaForcingTrader.B`;
the reconciler unifies them with A's (same names, same meanings).

* `LegibleOn P x` — "the real sequence `x` is a legal feature progression of `P`'s market": the
  package's one (c)-shape, the corpus's (L).
* `scheduleIndicator d` — the price-free `{0,1}` feature `1[m ∈ im d]`, generable
  (`scheduleIndicator_pgenerable`) from FAF's own image flag of a deferral function
  (`deferralImageFlag`, a `UnaryRuler` by `unaryRuler_deferralImageFlag`), by the
  `evenDays_pgenerable` pattern of `fa-theorem-a`; supported on `im d`.
* `schedGate Y d t δ` — Theorem SS's weighting `w_n = Ind_δ(a_n > t) · 1[n ∈ im d]`, `A`-native.
* `WindowDisjoint f d` — v3's window-disjoint schedule as a `DeferralFunction` (angle A's T2
  object; stated here so B's statements can name it, though B's citation route consumes only
  `StrictlyIncreasingDeferral d`, see `fa-forcing-trader-findings-B.md`).
* The transfer lemmas: a divergent, schedule-supported weighting of `A` that is legible on `H`
  is a divergent, schedule-supported weighting of `H` with the *same numbers*.

Scope: one-way throughout (every feature here is of one market's own prices).
-/

namespace Cleanroom.Fa.FaForcingTrader.B

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice
open Filter Topology

/-! ## A. Legibility: the one (c)-shape -/

/-- **(L) as a hypothesis shape.** `x` is a legal feature progression of `P`'s market: some
`PGenerableWeighting G` (FAF's `def:ece` class) denotes exactly `x n` at `P` on every day. The
corpus's (L) is `LegibleOn H (quoteSeq Y A)` (or of the scheduled gate); v3's joint visibility is
`LegibleOn A (fun n => X.expect H n)`. No two-market inhabitant is known (mandate T11).
Source: vq-wiki-048 (a)–(c); [[unbiasedness-theorem-families]] §6; lean-deference-2-011
Kind: D
Fidelity: exact (the corpus's "the same numbers, legal on both markets")
Hyps: n/a -/
def LegibleOn (P : History) (x : ℕ → ℝ) : Prop :=
  ∃ G : ℕ → EF, PGenerableWeighting G ∧ ∀ n, (G n).denote P = x n

/-- A market's own generable weighting is legible on that market (the same-market instance).
Source: mandate T1 (`legibleOn_quote_self`, generalized to any generable progression)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem legibleOn_self (P : History) {G : ℕ → EF} (hG : PGenerableWeighting G) :
    LegibleOn P (fun n => (G n).denote P) :=
  ⟨G, hG, fun _ => rfl⟩

/-- A `PGenerableRat P q` (FAF's `def:ece` *with* its denotation clause) makes `(q n : ℝ)`
legible on `P`: the generated feature is the witness.
Source: mandate T1 (`legibleOn_of_pgenerableRat`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem legibleOn_of_pgenerableRat (P : History) {q : ℕ → ℚ} (h : PGenerableRat P q) :
    LegibleOn P (fun n => (q n : ℝ)) := by
  obtain ⟨F, hF⟩ := h
  exact ⟨F, ⟨hF.polyTok, hF.rank_le, hF.closed⟩, hF.denote⟩

/-! ## B. The schedule indicator -/

/-- **The schedule indicator** `1[m ∈ im d]` as a price-free `{0,1}` feature: the constant
feature of FAF's image flag `deferralImageFlag d m` (`Construction/Quotation/DeferralFibre.lean`).
Source: mandate T1; [[route-sparse-schedule]] §3 Lemma 1(d) (vq-wiki-046)
Kind: D
Fidelity: exact
Hyps: n/a -/
def scheduleIndicator (d : DeferralFunction) (m : ℕ) : EF :=
  EF.const (deferralImageFlag d m : ℚ)

/-- The indicator denotes FAF's image flag, in any market.
Source: mandate T1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem scheduleIndicator_denote (d : DeferralFunction) (P : History) (m : ℕ) :
    (scheduleIndicator d m).denote P = (deferralImageFlag d m : ℝ) := by
  simp [scheduleIndicator]

/-- The indicator is `1` on the schedule.
Source: mandate T1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem scheduleIndicator_denote_of_mem (d : DeferralFunction) (P : History) (k : ℕ) :
    (scheduleIndicator d (d k)).denote P = 1 := by
  rw [scheduleIndicator_denote, deferralImageFlag_at]
  simp

/-- The indicator is `0` off the schedule.
Source: mandate T1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem scheduleIndicator_denote_of_not_mem (d : DeferralFunction) (P : History) {m : ℕ}
    (hm : ¬ ∃ k, d k = m) : (scheduleIndicator d m).denote P = 0 := by
  rw [scheduleIndicator_denote]
  rcases deferralImageFlag_zero_or_one d m with h | h
  · simp [h]
  · exfalso
    obtain ⟨k, -, hk⟩ := (deferralImageFlag_eq_one_iff d m).1 h
    exact hm ⟨k, hk⟩

/-- The indicator is `{0,1}`-valued.
Source: mandate T1 (`scheduleIndicator_mem_Icc`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem scheduleIndicator_zero_or_one (d : DeferralFunction) (P : History) (m : ℕ) :
    (scheduleIndicator d m).denote P = 0 ∨ (scheduleIndicator d m).denote P = 1 := by
  rw [scheduleIndicator_denote]
  rcases deferralImageFlag_zero_or_one d m with h | h <;> simp [h]

/-- The indicator lies in `[0,1]`.
Source: mandate T1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem scheduleIndicator_mem_Icc (d : DeferralFunction) (P : History) (m : ℕ) :
    0 ≤ (scheduleIndicator d m).denote P ∧ (scheduleIndicator d m).denote P ≤ 1 := by
  rcases scheduleIndicator_zero_or_one d P m with h | h <;> rw [h] <;> norm_num

/-- **The indicator is supported on the schedule** — FAF's `WeightingSupportedOnDeferralImage`,
the support clause of corrected 4.8.16 (PE2), in any market.
Source: mandate T1 (`scheduleIndicator_supported`); FAF `thm:wubexp` (`hsupport`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem scheduleIndicator_supported (d : DeferralFunction) (P : History) :
    WeightingSupportedOnDeferralImage (scheduleIndicator d) P d := by
  intro m hm
  by_contra h
  exact hm (scheduleIndicator_denote_of_not_mem d P h)

/-- **The schedule indicator is a `PGenerableWeighting`** (FAF's `def:ece` class exactly): the
serialization stream dispatches, by `MachineSpliceStream.ifZero` on the image-flag ruler
(`unaryRuler_deferralImageFlag d` — FAF's graph-decider search
`k ≤ m`, polynomial in the unary `m`), between the constant serializations of `0` and `1`; rank
`0`; closed denotation. This is the `evenDays_pgenerable` pattern of `fa-theorem-a` with FAF's
deferral-image flag as the ruler — the mandate's "the `MachineSpliceStream` must come from
`graphFlag_ruler`" (FAF's `deferralImageFlag` is built on exactly that clock).
Source: mandate T1 (`scheduleIndicator_pgenerable`); [[route-sparse-schedule]] §3 Lemma 1(d); FAF `unaryRuler_deferralImageFlag`
Kind: P
Fidelity: exact
Hyps: (a) none -/
theorem scheduleIndicator_pgenerable (d : DeferralFunction) :
    PGenerableWeighting (scheduleIndicator d) where
  polySeg :=
    ((MachineSpliceStream.serialize_const (0 : ℚ)).ifZero
      (MachineSpliceStream.serialize_const (1 : ℚ))
      (unaryRuler_deferralImageFlag d)).of_eq (fun n => by
        rcases deferralImageFlag_zero_or_one d n with h | h
        · simp [scheduleIndicator, h]
        · simp [scheduleIndicator, h])
  rank_le := fun n => by simp [scheduleIndicator]
  closed := fun n ρ V => by simp [scheduleIndicator, EF.denote]

/-! ## C. The scheduled quote gate -/

/-- **Theorem SS's weighting** `w_n = 1[n ∈ im d] · Ind_δ(a_n > t)`: the schedule indicator times
`fa-theorem-a`'s quote ramp `quoteRampAbove Y t δ` — an expressible feature of `A`'s *own* day-`n`
prices (`A`-native), hence generable from `A`'s market alone (`schedGate_pgenerable`); legible on
`H` only under (L).
Source: [[theorem-ss-streamlined]] §0 "The weighting" (vq-wiki-050); [[route-sparse-schedule]] §4; mandate § Definitions (`schedGate`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def schedGate (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ) (n : ℕ) : EF :=
  EF.mul (scheduleIndicator d n) (quoteRampAbove Y t δ n)

/-- The dual weighting `w⁻_n = 1[n ∈ im d] · Ind_δ(a_n < t)`.
Source: [[route-sparse-schedule]] §8 (`w^-_n`)
Kind: D
Fidelity: exact
Hyps: n/a -/
def schedGateBelow (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ) (n : ℕ) : EF :=
  EF.mul (scheduleIndicator d n) (quoteRampBelow Y t δ n)

/-- **The scheduled gate is a `PGenerableWeighting` of `A`'s market** — FAF's
`PGenerableWeighting.mul` of the two certificates (`scheduleIndicator_pgenerable`,
`fa-theorem-a`'s T2 `quoteRampAbove_pgenerable`). This is Theorem SS's "native for `A`" legality.
Source: [[theorem-ss-streamlined]] §0, §4 (L3's "`w̄` is `P̄^A`-generable natively"); mandate § Definitions
Kind: C
Fidelity: exact
Hyps: (a) `hY` (the quote family's e.c. certificate, `CrossQuotePackage.quote_codes`) -/
theorem schedGate_pgenerable (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y)
    (d : DeferralFunction) (t δ : ℚ) : PGenerableWeighting (schedGate Y d t δ) :=
  PGenerableWeighting.mul (scheduleIndicator_pgenerable d) (quoteRampAbove_pgenerable Y hY t δ)

/-- The dual gate is generable.
Source: [[route-sparse-schedule]] §8
Kind: C
Fidelity: exact
Hyps: (a) `hY` -/
theorem schedGateBelow_pgenerable (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y)
    (d : DeferralFunction) (t δ : ℚ) : PGenerableWeighting (schedGateBelow Y d t δ) :=
  PGenerableWeighting.mul (scheduleIndicator_pgenerable d) (quoteRampBelow_pgenerable Y hY t δ)

/-- The gate denotes `1[n ∈ im d] · rampAbove δ t a_n` (`def-lattice`'s `rampAbove`), positive
width.
Source: mandate § Definitions (`schedGate` "denotes `1[n ∈ im d] · rampAbove δ t a_n`")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGate_denote (Y : ℕ → LUV) (d : DeferralFunction) {t δ : ℚ} (hδ : 0 < δ)
    (A : History) (n : ℕ) :
    (schedGate Y d t δ n).denote A =
      (scheduleIndicator d n).denote A * rampAbove δ t (quoteSeq Y A n) := by
  simp only [schedGate, EF.denote_mul, Pi.mul_apply, quoteRampAbove_denote Y hδ, rampAbove,
    quoteSeq]

/-- The dual gate denotes `1[n ∈ im d] · rampBelow δ t a_n`.
Source: [[route-sparse-schedule]] §8
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGateBelow_denote (Y : ℕ → LUV) (d : DeferralFunction) {t δ : ℚ} (hδ : 0 < δ)
    (A : History) (n : ℕ) :
    (schedGateBelow Y d t δ n).denote A =
      (scheduleIndicator d n).denote A * rampBelow δ t (quoteSeq Y A n) := by
  simp only [schedGateBelow, EF.denote_mul, Pi.mul_apply, quoteRampBelow_denote Y hδ, rampBelow,
    quoteSeq]

/-- The gate lies in `[0,1]`.
Source: mandate § Definitions
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGate_mem_Icc (Y : ℕ → LUV) (d : DeferralFunction) {t δ : ℚ} (hδ : 0 < δ)
    (A : History) (n : ℕ) :
    0 ≤ (schedGate Y d t δ n).denote A ∧ (schedGate Y d t δ n).denote A ≤ 1 := by
  rw [schedGate_denote Y d hδ]
  have h1 := scheduleIndicator_mem_Icc d A n
  have h2 := ctsInd_mem_Icc δ (quoteSeq Y A n) (t : ℝ)
  constructor
  · exact mul_nonneg h1.1 h2.1
  · calc (scheduleIndicator d n).denote A * rampAbove δ t (quoteSeq Y A n)
        ≤ 1 * 1 := mul_le_mul h1.2 h2.2 h2.1 zero_le_one
      _ = 1 := one_mul 1

/-- The dual gate lies in `[0,1]`.
Source: [[route-sparse-schedule]] §8
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGateBelow_mem_Icc (Y : ℕ → LUV) (d : DeferralFunction) {t δ : ℚ} (hδ : 0 < δ)
    (A : History) (n : ℕ) :
    0 ≤ (schedGateBelow Y d t δ n).denote A ∧ (schedGateBelow Y d t δ n).denote A ≤ 1 := by
  rw [schedGateBelow_denote Y d hδ]
  have h1 := scheduleIndicator_mem_Icc d A n
  have h2 := ctsInd_mem_Icc δ (t : ℝ) (quoteSeq Y A n)
  constructor
  · exact mul_nonneg h1.1 h2.1
  · calc (scheduleIndicator d n).denote A * rampBelow δ t (quoteSeq Y A n)
        ≤ 1 * 1 := mul_le_mul h1.2 h2.2 h2.1 zero_le_one
      _ = 1 := one_mul 1

/-- **The support law of the gate** (no false positives): positive weight means the day is on the
schedule *and* the quote exceeds `t`. The orientation check of K7: `quoteRampAbove` is
`ctsInd δ a_n t`, positive iff `t < a_n`.
Source: [[route-recurring-ccee]] §4 ("the ramp has no false positives"); mandate K7
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGate_pos_imp (Y : ℕ → LUV) (d : DeferralFunction) {t δ : ℚ} (hδ : 0 < δ)
    (A : History) {n : ℕ} (h : 0 < (schedGate Y d t δ n).denote A) :
    (∃ k, d k = n) ∧ (t : ℝ) < quoteSeq Y A n := by
  rw [schedGate_denote Y d hδ] at h
  refine ⟨?_, ?_⟩
  · by_contra hn
    rw [scheduleIndicator_denote_of_not_mem d A hn, zero_mul] at h
    exact lt_irrefl _ h
  · have h2 : 0 < rampAbove δ t (quoteSeq Y A n) := by
      rcases scheduleIndicator_zero_or_one d A n with h0 | h1
      · rw [h0, zero_mul] at h; exact absurd h (lt_irrefl _)
      · rwa [h1, one_mul] at h
    exact (ctsInd_pos_iff hδ _ _).1 h2

/-- The support law of the dual gate: positive weight means on-schedule and `a_n < t`.
Source: [[route-sparse-schedule]] §8; mandate K7
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGateBelow_pos_imp (Y : ℕ → LUV) (d : DeferralFunction) {t δ : ℚ} (hδ : 0 < δ)
    (A : History) {n : ℕ} (h : 0 < (schedGateBelow Y d t δ n).denote A) :
    (∃ k, d k = n) ∧ quoteSeq Y A n < (t : ℝ) := by
  rw [schedGateBelow_denote Y d hδ] at h
  refine ⟨?_, ?_⟩
  · by_contra hn
    rw [scheduleIndicator_denote_of_not_mem d A hn, zero_mul] at h
    exact lt_irrefl _ h
  · have h2 : 0 < rampBelow δ t (quoteSeq Y A n) := by
      rcases scheduleIndicator_zero_or_one d A n with h0 | h1
      · rw [h0, zero_mul] at h; exact absurd h (lt_irrefl _)
      · rwa [h1, one_mul] at h
    exact (ctsInd_pos_iff hδ _ _).1 h2

/-- **The gate is supported on the schedule** (the support clause of corrected 4.8.16 at `A`).
Source: [[theorem-ss-streamlined]] §4 ("the support of `w̄` is in `im(g)` by construction")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGate_supported (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ) (A : History) :
    WeightingSupportedOnDeferralImage (schedGate Y d t δ) A d := by
  intro n hn
  by_contra h
  apply hn
  simp only [schedGate, EF.denote_mul, Pi.mul_apply]
  rw [scheduleIndicator_denote_of_not_mem d A h, zero_mul]

/-- The dual gate is supported on the schedule.
Source: [[route-sparse-schedule]] §8
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGateBelow_supported (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ)
    (A : History) : WeightingSupportedOnDeferralImage (schedGateBelow Y d t δ) A d := by
  intro n hn
  by_contra h
  apply hn
  simp only [schedGateBelow, EF.denote_mul, Pi.mul_apply]
  rw [scheduleIndicator_denote_of_not_mem d A h, zero_mul]

/-! ## D. Window-disjoint schedules -/

/-- **v3's window-disjoint schedule as a deferral function**: `d` strictly increasing with the
lookahead window of each schedule day closed before the next opens, `f (d k) < d (k+1)`. v3's
"e.c. schedule with `d_{k+1} ≥ 2^{d_k}`" is empty under the paper's "e.c. in the index"
(root-fa-2-003, K1); the `DeferralFunction` class (graph decided in poly time on the unary pair) is
the honest carrier. Angle B's citation route does **not** consume the window condition (FAF's
`luv_wubexp_ofComputation` takes `StrictlyIncreasingDeferral d` and the certificate; the
window is the certificate's business) — recorded in the findings.
Source: [[fa-positive-results-corrected-v3]] §3 "Definitions" with root-fa-2-003's correction; vq-wiki-046 Lemma 1
Kind: D
Fidelity: variant: `DeferralFunction` in place of "e.c. sequence of days"; general lookahead `f` in place of `2^n`
Hyps: n/a -/
def WindowDisjoint (f d : DeferralFunction) : Prop :=
  StrictMono d.f ∧ ∀ k, f.f (d.f k) < d.f (k + 1)

/-- A window-disjoint schedule is a strictly increasing deferral (FAF's class).
Source: mandate T2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem WindowDisjoint.strict {f d : DeferralFunction} (h : WindowDisjoint f d) :
    StrictlyIncreasingDeferral d :=
  h.1

/-! ## E. Transfer under legibility: the same numbers on the other market -/

/-- **Divergence transfers along legibility.** If `G` denotes on `Q` the same numbers that `W`
denotes on `P`, and `W` is divergent on `P`, then `G` is divergent on `Q`. This is the mandate's
`divergent_transfer`: under (L) the divergence hypothesis is stated once, on `A`.
Source: mandate T6 trap (i)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem DivergentWeighting.transfer {P Q : History} {W G : ℕ → EF}
    (heq : ∀ n, (G n).denote Q = (W n).denote P) (hdiv : DivergentWeighting W P) :
    DivergentWeighting G Q := by
  refine ⟨fun n => by rw [heq n]; exact hdiv.1 n, ?_⟩
  have : (fun n => (G n).denote Q) = fun n => (W n).denote P := funext heq
  rw [this]
  exact hdiv.2

/-- **Schedule support transfers along legibility.**
Source: mandate T6 (the `H`-side feature "from `hL` (same numbers)")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem WeightingSupportedOnDeferralImage.transfer {P Q : History} {W G : ℕ → EF}
    (d : DeferralFunction) (heq : ∀ n, (G n).denote Q = (W n).denote P)
    (hs : WeightingSupportedOnDeferralImage W P d) :
    WeightingSupportedOnDeferralImage G Q d := by
  intro n hn
  rw [heq n] at hn
  exact hs n hn

end Cleanroom.Fa.FaForcingTrader.B
