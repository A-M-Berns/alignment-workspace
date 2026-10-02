import Cleanroom.Fa.FaTheoremA.Defs
import Cleanroom.Found.LiAsympCalc.Compactness
import Cleanroom.Found.DefLattice.Expert
import LogicalInduction.Properties.Pseudorandomness

/-!
# `fa-forcing-trader` · Defs: legibility, the schedule indicator, window-disjoint schedules, the gates

Definitions of record shared by both angles of the dual package ([[fa-forcing-trader-mandate]]
§Definitions of record). Written by angle A; angle B imports and does not edit.

* `LegibleOn P x` — "`x` is a legal feature progression of `P`'s market": the package's **one
  (c)-shape**. The corpus's (L) is `LegibleOn H (quoteSeq Y A)`; v3's joint visibility (A1) is
  joint legibility of the violation weight. Closure lemmas (`LegibleOn.mul`, `.rampAbove`,
  `.rampBelow`, `.schedInd`) and the two (a)-grade instances (`legibleOn_of_pgenerableRat`,
  `legibleOn_quote_self`).
* `scheduleIndicator d` — the price-free `{0,1}` feature `1[n ∈ im d]` of a `DeferralFunction`,
  generable by the `evenDays_pgenerable` pattern with FAF's graph decider
  (`unaryRuler_scheduledMatch`) as the ruler; `schedInd d` its real value.
* `WindowDisjoint f d` — v3's "window-disjoint schedule" as a deferral function (root-fa-2-003:
  the literal "e.c. in the index" class is empty), with the consequences used downstream
  (`lookahead_not_mem`, `two_mul_lt`).
* `schedGate` / `schedGateBelow` — Theorem SS's `A`-native weighting
  `1[n ∈ im d] · Ind_δ(a_n > t)` and its mirror.
* `bundle X` — the day-`n` threshold mesh `(X n).expectAffine (n+1)` the `H`-side trader buys;
  `violW` — v3's violation weight `1[n ∈ im d] · Ind_δ(a_n > t) · Ind_δ(h_n < t − ε)` as a real
  sequence (`li-asymp-calc`'s `viol` restricted to the schedule).

Nothing here redefines `TotalTrust`, `ThresholdIneqAbove`, `Expert`, `WeightedApprox`,
`Dominates`, `CrossQuotePackage`, `rampAbove` (plan §0.4 rule 10).
-/

namespace Cleanroom.Fa.FaForcingTrader

open LogicalInduction Cleanroom.Fa.FaTheoremA Cleanroom.Found.LiQuoteLane
  Cleanroom.Found.LiAsympCalc Cleanroom.Found.DefLattice Filter Topology

/-! ## A. Legibility: the package's one (c)-shape -/

/-- **`x` is a legal feature progression of `P`'s market**: some `PGenerableWeighting G` of `P`
denotes `x` day by day. This is the single hypothesis shape through which every cross-market
visibility assumption of the package enters: the corpus's (L) "the quote stream is `H`-generable"
is `LegibleOn H (quoteSeq Y A)`; v3's joint clearing (A1), in the only form FAF can state, is
`LegibleOn A violW ∧ LegibleOn H violW`. No two-market inhabitant with `A ≠ H` is known (T11,
OPEN); the same-market instance is `legibleOn_quote_self`.
Source: vq-wiki-048 (a)–(c); [[unbiasedness-theorem-families]] §6; root-fa-2-003; lean-deference-2-011
Kind: D
Fidelity: variant: (L)'s relativized trader class `Pᴸ` rendered as plain `PGenerableWeighting` of the reader's market
Hyps: n/a -/
def LegibleOn (P : History) (x : ℕ → ℝ) : Prop :=
  ∃ G : ℕ → EF, PGenerableWeighting G ∧ ∀ n, (G n).denote P = x n

/-- A `PGenerableRat` table is legible (FAF's `GeneratedRatFeature` carries exactly the
`PGenerableWeighting` fields plus the denotation clause).
Source: vq-wiki-048 (b); FAF `GeneratedRatFeature`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem legibleOn_of_pgenerableRat {P : History} {q : ℕ → ℚ} (h : PGenerableRat P q) :
    LegibleOn P (fun n => (q n : ℝ)) := by
  obtain ⟨G, hG⟩ := h
  exact ⟨G, ⟨hG.polyTok, hG.rank_le, hG.closed⟩, hG.denote⟩

/-- **The same-market instance of (L)**: a market's own quote `a_n = 𝔼^A_n(Y_n)` is legible on
`A` (fa-theorem-a's `quoteFeature_pgenerable`, "a market is never stale to itself").
Source: vq-wiki-048 (a); fa-theorem-a T2
Kind: L
Fidelity: exact
Hyps: (a) none (`hY` is the e.c. certificate of the quote family) -/
theorem legibleOn_quote_self (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y) (A : History) :
    LegibleOn A (quoteSeq Y A) :=
  ⟨quoteFeature Y, quoteFeature_pgenerable Y hY, fun n => quoteFeature_denote Y A n⟩

/-- Legibility respects pointwise equality.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem LegibleOn.congr {P : History} {x y : ℕ → ℝ} (h : LegibleOn P x) (hxy : ∀ n, x n = y n) :
    LegibleOn P y := by
  obtain ⟨G, hG, hGx⟩ := h
  exact ⟨G, hG, fun n => (hGx n).trans (hxy n)⟩

/-- Legible sequences are closed under products (FAF's `PGenerableWeighting.mul`) — the
"class closed under gates" of trust-lab-045/047, over FAF.
Source: trust-lab-045/047; FAF `PGenerableWeighting.mul`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem LegibleOn.mul {P : History} {x y : ℕ → ℝ} (hx : LegibleOn P x) (hy : LegibleOn P y) :
    LegibleOn P (fun n => x n * y n) := by
  obtain ⟨G, hG, hGx⟩ := hx
  obtain ⟨G', hG', hGy⟩ := hy
  refine ⟨fun n => EF.mul (G n) (G' n), PGenerableWeighting.mul hG hG', fun n => ?_⟩
  rw [EF.denote_mul, Pi.mul_apply, hGx n, hGy n]

/-- A legible sequence stays legible under the upper ramp `Ind_δ(x_n > t)` (FAF's ramp compiler
`ctsIndFeature_generated` against a constant threshold).
Source: vq-wiki-048 (b); fa-theorem-a T2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem LegibleOn.rampAbove {P : History} {x : ℕ → ℝ} (hx : LegibleOn P x) (t : ℚ) {δ : ℚ}
    (hδ : 0 < δ) : LegibleOn P (fun n => rampAbove δ t (x n)) := by
  obtain ⟨G, hG, hGx⟩ := hx
  refine ⟨ctsIndFeature (fun _ => δ) G (fun _ => EF.const t),
    ctsIndFeature_generated _ _ _ (MachineRatCodes.const (1 / δ)) hG (pgenerableWeighting_const t),
    fun n => ?_⟩
  rw [ctsIndFeature_denote _ _ _ (fun _ => hδ), hGx n]
  simp

/-- A legible sequence stays legible under the lower ramp `Ind_δ(x_n < t)`.
Source: vq-wiki-048 (b); fa-theorem-a T2 (dual)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem LegibleOn.rampBelow {P : History} {x : ℕ → ℝ} (hx : LegibleOn P x) (t : ℚ) {δ : ℚ}
    (hδ : 0 < δ) : LegibleOn P (fun n => rampBelow δ t (x n)) := by
  obtain ⟨G, hG, hGx⟩ := hx
  refine ⟨ctsIndFeature (fun _ => δ) (fun _ => EF.const t) G,
    ctsIndFeature_generated _ _ _ (MachineRatCodes.const (1 / δ)) (pgenerableWeighting_const t) hG,
    fun n => ?_⟩
  rw [ctsIndFeature_denote _ _ _ (fun _ => hδ), hGx n]
  simp

/-! ## B. The schedule indicator `1[n ∈ im d]` as a price-free generable feature -/

/-- The number of `k ≤ m` with `d k = m`, as FAF's prefix scan of the graph decider
`scheduledMatch d` (the transposed `graphFlag`) over `k < m + 1`. A machine computes it in
polynomial time on the unary day (`schedCount_ruler`); it is `0` iff `m ∉ im d`
(`schedCount_eq_zero_iff`), because `d k = m` forces `k < m`.
Source: root-fa-2-003 (the day-`n` membership test is what must be poly(`n`)); FAF `scheduledMatch`
Kind: D
Fidelity: n/a
Hyps: n/a -/
def schedCount (d : DeferralFunction) (m : ℕ) : ℕ :=
  segPrefix (scheduledMatch d) m (m + 1)

/-- The scan is `0` iff no `j < r` has `d j = m`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem segPrefix_scheduledMatch_eq_zero_iff (d : DeferralFunction) (m : ℕ) :
    ∀ r, segPrefix (scheduledMatch d) m r = 0 ↔ ∀ j < r, d.f j ≠ m
  | 0 => by simp
  | r + 1 => by
      rw [segPrefix_succ, Nat.add_eq_zero_iff, segPrefix_scheduledMatch_eq_zero_iff d m r]
      simp only [scheduledMatch, Nat.unpair_pair]
      constructor
      · rintro ⟨h1, h2⟩ j hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · exact h1 j hj
        · intro h
          simp [h] at h2
      · intro h
        refine ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), ?_⟩
        have := h r (Nat.lt_succ_self r)
        simp [this]

/-- `schedCount d m = 0 ↔ m ∉ im d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem schedCount_eq_zero_iff (d : DeferralFunction) (m : ℕ) :
    schedCount d m = 0 ↔ ∀ k, d.f k ≠ m := by
  rw [schedCount, segPrefix_scheduledMatch_eq_zero_iff]
  constructor
  · intro h k hk
    have hlt : k < m + 1 := by
      have := d.lt k
      omega
    exact h k hlt hk
  · intro h k _
    exact h k

/-- The count is machine-metered on the unary day: FAF's `UnaryRuler.segPrefix` of the graph
decider, composed with `m ↦ ⟨m, m + 1⟩`.
Source: root-fa-2-003; FAF `unaryRuler_scheduledMatch`, `UnaryRuler.segPrefix`
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem schedCount_ruler (d : DeferralFunction) : UnaryRuler (schedCount d) :=
  ((UnaryRuler.segPrefix (unaryRuler_scheduledMatch d)).comp
    (UnaryRuler.id.pair UnaryRuler.id.succ)).of_eq (fun m => by simp [schedCount])

/-- **The schedule indicator**: the price-free constant feature `1` on days in the image of `d`
and `0` elsewhere, written through the decidable count so that it is generable.
Source: [[theorem-ss-streamlined]] §0 ("`𝟙[i ∈ im(g)]`"); root-fa-2-003; vq-wiki-046 Lemma 1 (c)/(d)
Kind: D
Fidelity: exact
Hyps: n/a -/
def scheduleIndicator (d : DeferralFunction) (m : ℕ) : EF :=
  EF.const (if schedCount d m = 0 then 0 else 1)

/-- The real value of the schedule indicator: `1` on `im d`, `0` off it.
Source: [[theorem-ss-streamlined]] §0
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def schedInd (d : DeferralFunction) (n : ℕ) : ℝ :=
  by classical exact if ∃ k, d.f k = n then 1 else 0

/-- `schedInd d (d k) = 1`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem schedInd_of_mem (d : DeferralFunction) (k : ℕ) : schedInd d (d.f k) = 1 := by
  unfold schedInd
  rw [if_pos ⟨k, rfl⟩]

/-- `schedInd d n = 0` off the image.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem schedInd_of_not_mem (d : DeferralFunction) {n : ℕ} (h : ∀ k, d.f k ≠ n) :
    schedInd d n = 0 := by
  unfold schedInd
  rw [if_neg (fun ⟨k, hk⟩ => h k hk)]

/-- `schedInd` is `{0,1}`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem schedInd_eq_zero_or_one (d : DeferralFunction) (n : ℕ) :
    schedInd d n = 0 ∨ schedInd d n = 1 := by
  unfold schedInd
  split_ifs <;> simp

/-- `schedInd d n ∈ [0,1]`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem schedInd_mem_Icc (d : DeferralFunction) (n : ℕ) : schedInd d n ∈ Set.Icc (0 : ℝ) 1 := by
  rcases schedInd_eq_zero_or_one d n with h | h <;> rw [h] <;> norm_num

/-- `0 < schedInd d n ↔ n ∈ im d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem schedInd_pos_iff (d : DeferralFunction) (n : ℕ) :
    0 < schedInd d n ↔ ∃ k, d.f k = n := by
  unfold schedInd
  split_ifs with h <;> simp [h]

/-- `schedInd d n ≠ 0 ↔ n ∈ im d`.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem schedInd_ne_zero_iff (d : DeferralFunction) (n : ℕ) :
    schedInd d n ≠ 0 ↔ ∃ k, d.f k = n := by
  unfold schedInd
  split_ifs with h <;> simp [h]

/-- The feature denotes `schedInd` in every market (it is price-free).
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem scheduleIndicator_denote (d : DeferralFunction) (P : History) (n : ℕ) :
    (scheduleIndicator d n).denote P = schedInd d n := by
  unfold scheduleIndicator schedInd
  by_cases h : ∃ k, d.f k = n
  · have hc : schedCount d n ≠ 0 := fun h0 => by
      obtain ⟨k, hk⟩ := h
      exact (schedCount_eq_zero_iff d n).1 h0 k hk
    rw [if_neg hc, if_pos h]
    simp
  · have hc : schedCount d n = 0 := (schedCount_eq_zero_iff d n).2 (fun k hk => h ⟨k, hk⟩)
    rw [if_pos hc, if_neg h]
    simp

/-- **T1: the schedule indicator is a legal feature progression** (`PGenerableWeighting`): the
constant stream dispatched on the machine-metered count (`evenDays_pgenerable`'s pattern with
the schedule's own graph decider as the ruler). Trap avoided: a `Classical`-choice indicator
without this ruler certificate is not generable.
Source: root-fa-2-003 (the day-`n` membership test); vq-wiki-046 Lemma 1 (c); [[theorem-ss-streamlined]] §0
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem scheduleIndicator_pgenerable (d : DeferralFunction) :
    PGenerableWeighting (scheduleIndicator d) where
  polySeg :=
    ((MachineSpliceStream.serialize_const 0).ifZero (MachineSpliceStream.serialize_const 1)
      (schedCount_ruler d)).of_eq (fun n => by
        unfold scheduleIndicator
        split_ifs <;> rfl)
  rank_le := fun n => by simp [scheduleIndicator]
  closed := fun n ρ V => by simp [scheduleIndicator, EF.denote]

/-- The schedule indicator is supported on the image of `d` (FAF's
`WeightingSupportedOnDeferralImage`), in every market.
Source: root-fa-2-003; FAF `WeightingSupportedOnDeferralImage`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem scheduleIndicator_supported (d : DeferralFunction) (P : History) :
    WeightingSupportedOnDeferralImage (scheduleIndicator d) P d := by
  intro n hn
  rw [scheduleIndicator_denote] at hn
  exact (schedInd_ne_zero_iff d n).1 hn

/-- The schedule indicator is `[0,1]`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem scheduleIndicator_mem_Icc (d : DeferralFunction) (P : History) (n : ℕ) :
    (scheduleIndicator d n).denote P ∈ Set.Icc (0 : ℝ) 1 := by
  rw [scheduleIndicator_denote]
  exact schedInd_mem_Icc d n

/-- `schedInd` is legible on every market.
Source: none: infrastructure
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem LegibleOn.schedInd (d : DeferralFunction) (P : History) : LegibleOn P (schedInd d) :=
  ⟨scheduleIndicator d, scheduleIndicator_pgenerable d, fun n => scheduleIndicator_denote d P n⟩

/-! ## C. Window-disjoint schedules -/

/-- **v3's "window-disjoint schedule" as a deferral function**: `d` strictly increasing with the
lookahead window `[d k, f (d k)]` closed before the next scheduled day. The lookahead `f` is the
`CrossQuotePackage`'s deferral; v3's `2^{d_k}` is the instance `f = doublingDeferral`, not the
definition. The schedule is a `DeferralFunction` (graph decided in poly time on the unary
pair), not "e.c. in the index" — under the paper's "e.c." v3's class is empty
(root-fa-2-003 (i), findings K1).
Source: [[fa-positive-results-corrected-v3]] §3 "Definitions" with root-fa-2-003's correction; vq-wiki-046 Lemma 1 (c)/(d)
Kind: D
Fidelity: variant: deferral-function schedule in place of v3's (empty) "e.c. in the index" class
Hyps: n/a -/
def WindowDisjoint (f d : DeferralFunction) : Prop :=
  StrictMono d.f ∧ ∀ k, f.f (d.f k) < d.f (k + 1)

/-- No lookahead day `f (d k)` is itself a scheduled day: it lies strictly between `d k` and
`d (k+1)`.
Source: [[fa-positive-results-corrected-v3]] §3 ("at most one position is ever open")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem WindowDisjoint.lookahead_not_mem {f d : DeferralFunction} (h : WindowDisjoint f d)
    (k j : ℕ) : d.f j ≠ f.f (d.f k) := by
  intro hj
  have h1 : d.f k < d.f j := by
    rw [hj]
    exact f.lt _
  have h2 : d.f j < d.f (k + 1) := by
    rw [hj]
    exact h.2 k
  have hk : k < j := h.1.lt_iff_lt.1 h1
  have hj' : j < k + 1 := h.1.lt_iff_lt.1 h2
  omega

/-- A window-disjoint schedule grows at least like `2k + 1` (each window costs two days).
Source: none: infrastructure (needed for the interleaving to defer)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem WindowDisjoint.two_mul_lt {f d : DeferralFunction} (h : WindowDisjoint f d) (k : ℕ) :
    2 * k < d.f k := by
  induction k with
  | zero => simpa using d.lt 0
  | succ k ih =>
    have h1 := h.2 k
    have h2 := f.lt (d.f k)
    omega

/-- For the successor lookahead, window-disjointness is exactly "gaps of at least two".
Source: [[fa-positive-results-corrected-v3]] §3; mandate T2
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem windowDisjoint_succ (d : DeferralFunction) :
    WindowDisjoint succDeferral d ↔ ∀ k, d.f k + 1 < d.f (k + 1) := by
  constructor
  · intro h k
    exact h.2 k
  · intro h
    refine ⟨strictMono_nat_of_lt_succ (fun k => ?_), h⟩
    have := h k
    omega

/-! ## D. The gates -/

/-- **Theorem SS's weighting**, `A`-native: `w_n = 1[n ∈ im d] · Ind_δ(a_n > t)` with
`a_n = 𝔼^A_n(Y_n)` the quote.
Source: [[theorem-ss-streamlined]] §0 ("The weighting"); vq-wiki-050
Kind: D
Fidelity: exact
Hyps: n/a -/
def schedGate (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ) (n : ℕ) : EF :=
  EF.mul (scheduleIndicator d n) (quoteRampAbove Y t δ n)

/-- The mirror weighting `1[n ∈ im d] · Ind_δ(a_n < t)` for the below-threshold inequality.
Source: [[theorem-ss-streamlined]] §8 ("the mirror ramp")
Kind: D
Fidelity: exact
Hyps: n/a -/
def schedGateBelow (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ) (n : ℕ) : EF :=
  EF.mul (scheduleIndicator d n) (quoteRampBelow Y t δ n)

/-- The scheduled gate is a legal feature progression of `A`'s market (no visibility of `H`).
Source: [[theorem-ss-streamlined]] §0 ("native for `A`"); fa-theorem-a T2
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem schedGate_pgenerable (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y)
    (d : DeferralFunction) (t δ : ℚ) : PGenerableWeighting (schedGate Y d t δ) :=
  PGenerableWeighting.mul (scheduleIndicator_pgenerable d) (quoteRampAbove_pgenerable Y hY t δ)

/-- The mirror gate is a legal feature progression of `A`'s market.
Source: [[theorem-ss-streamlined]] §8
Kind: C
Fidelity: exact
Hyps: (a) none -/
theorem schedGateBelow_pgenerable (Y : ℕ → LUV) (hY : LUV.MachineThresholdCodeSeq Y)
    (d : DeferralFunction) (t δ : ℚ) : PGenerableWeighting (schedGateBelow Y d t δ) :=
  PGenerableWeighting.mul (scheduleIndicator_pgenerable d) (quoteRampBelow_pgenerable Y hY t δ)

/-- The scheduled gate denotes `1[n ∈ im d] · rampAbove δ t a_n` (def-lattice's ramp).
Source: [[theorem-ss-streamlined]] §0
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGate_denote (Y : ℕ → LUV) (d : DeferralFunction) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (A : History) (n : ℕ) :
    (schedGate Y d t δ n).denote A = schedInd d n * rampAbove δ t (quoteSeq Y A n) := by
  unfold schedGate
  rw [EF.denote_mul, Pi.mul_apply, scheduleIndicator_denote, quoteRampAbove_denote Y hδ]

/-- The mirror gate denotes `1[n ∈ im d] · rampBelow δ t a_n`.
Source: [[theorem-ss-streamlined]] §8
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGateBelow_denote (Y : ℕ → LUV) (d : DeferralFunction) (t : ℚ) {δ : ℚ}
    (hδ : 0 < δ) (A : History) (n : ℕ) :
    (schedGateBelow Y d t δ n).denote A = schedInd d n * rampBelow δ t (quoteSeq Y A n) := by
  unfold schedGateBelow
  rw [EF.denote_mul, Pi.mul_apply, scheduleIndicator_denote, quoteRampBelow_denote Y hδ]

/-- The scheduled gate is supported on `im d`.
Source: [[theorem-ss-streamlined]] §0 ("support ⊆ im(g) by construction")
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGate_supported (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ) (A : History) :
    WeightingSupportedOnDeferralImage (schedGate Y d t δ) A d := by
  intro n hn
  unfold schedGate at hn
  rw [EF.denote_mul, Pi.mul_apply] at hn
  exact scheduleIndicator_supported d A n (left_ne_zero_of_mul hn)

/-- The mirror gate is supported on `im d`.
Source: [[theorem-ss-streamlined]] §8
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGateBelow_supported (Y : ℕ → LUV) (d : DeferralFunction) (t δ : ℚ) (A : History) :
    WeightingSupportedOnDeferralImage (schedGateBelow Y d t δ) A d := by
  intro n hn
  unfold schedGateBelow at hn
  rw [EF.denote_mul, Pi.mul_apply] at hn
  exact scheduleIndicator_supported d A n (left_ne_zero_of_mul hn)

/-- The scheduled gate is `[0,1]`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem schedGate_mem_Icc (Y : ℕ → LUV) (d : DeferralFunction) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (A : History) (n : ℕ) : (schedGate Y d t δ n).denote A ∈ Set.Icc (0 : ℝ) 1 := by
  rw [schedGate_denote Y d t hδ]
  have h1 := schedInd_mem_Icc d n
  have h2 := ctsInd_mem_Icc δ (quoteSeq Y A n) (t : ℝ)
  exact ⟨mul_nonneg h1.1 h2.1, mul_le_one₀ h1.2 h2.1 h2.2⟩

/-- The mirror gate is `[0,1]`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem schedGateBelow_mem_Icc (Y : ℕ → LUV) (d : DeferralFunction) (t : ℚ) {δ : ℚ}
    (hδ : 0 < δ) (A : History) (n : ℕ) :
    (schedGateBelow Y d t δ n).denote A ∈ Set.Icc (0 : ℝ) 1 := by
  rw [schedGateBelow_denote Y d t hδ]
  have h1 := schedInd_mem_Icc d n
  have h2 := ctsInd_mem_Icc δ (t : ℝ) (quoteSeq Y A n)
  exact ⟨mul_nonneg h1.1 h2.1, mul_le_one₀ h1.2 h2.1 h2.2⟩

/-- **Support law of the scheduled gate**: positive weight exactly on scheduled days where the
quote exceeds `t` (no false positives — the ramp's orientation, K7).
Source: [[theorem-ss-streamlined]] §8 ("the ramp has no false positives"); fa-theorem-a `quoteRampAbove_pos_iff`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGate_pos_iff (Y : ℕ → LUV) (d : DeferralFunction) (t : ℚ) {δ : ℚ} (hδ : 0 < δ)
    (A : History) (n : ℕ) :
    0 < (schedGate Y d t δ n).denote A ↔ (∃ k, d.f k = n) ∧ (t : ℝ) < quoteSeq Y A n := by
  rw [schedGate_denote Y d t hδ, ← schedInd_pos_iff, rampAbove,
    ← ctsInd_pos_iff hδ (quoteSeq Y A n) (t : ℝ)]
  have h1 := schedInd_mem_Icc d n
  have h2 := ctsInd_mem_Icc δ (quoteSeq Y A n) (t : ℝ)
  constructor
  · intro h
    exact ⟨pos_of_mul_pos_left h h2.1, pos_of_mul_pos_right h h1.1⟩
  · rintro ⟨ha, hb⟩
    exact mul_pos ha hb

/-- **Support law of the mirror gate**: positive weight exactly on scheduled days where the
quote is below `t`.
Source: [[theorem-ss-streamlined]] §8; fa-theorem-a `quoteRampBelow_pos_iff`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem schedGateBelow_pos_iff (Y : ℕ → LUV) (d : DeferralFunction) (t : ℚ) {δ : ℚ}
    (hδ : 0 < δ) (A : History) (n : ℕ) :
    0 < (schedGateBelow Y d t δ n).denote A ↔ (∃ k, d.f k = n) ∧ quoteSeq Y A n < (t : ℝ) := by
  rw [schedGateBelow_denote Y d t hδ, ← schedInd_pos_iff, rampBelow,
    ← ctsInd_pos_iff hδ (t : ℝ) (quoteSeq Y A n)]
  have h1 := schedInd_mem_Icc d n
  have h2 := ctsInd_mem_Icc δ (t : ℝ) (quoteSeq Y A n)
  constructor
  · intro h
    exact ⟨pos_of_mul_pos_left h h2.1, pos_of_mul_pos_right h h1.1⟩
  · rintro ⟨ha, hb⟩
    exact mul_pos ha hb

/-! ## E. The bundle and the violation weight -/

/-- **What the `H`-side trader buys at day `n`**: the day-`n` threshold mesh
`(X n).expectAffine (n + 1)` (FAF's `LUV.expectAffineSeq`), priced at `𝔼^H_n(X_n)` on its own day
and at the opening-grid expectation on any later day; the gap to `𝔼^H_m(X_n)` at `m > n` is the
mesh term washed out by T5.
Source: [[fa-positive-results-corrected-v3]] §3 ("invests … in `X` at the price `𝔼^H_{d_k}(X)`"); FAF `LUV.expectAffineSeq`
Kind: D
Fidelity: exact (FAF's `def:e` mesh in place of the note's "`X` at its expectation")
Hyps: n/a -/
noncomputable abbrev bundle (X : ℕ → LUV) : ℕ → AffineCombination := LUV.expectAffineSeq X

/-- On its own day the bundle is priced at the market expectation.
Source: FAF `LUV.expectAffineSeq_price`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bundle_price_self (X : ℕ → LUV) (P : History) (n : ℕ) :
    (bundle X n).price P n = (X n).expect P n :=
  LUV.expectAffineSeq_price X P n

/-- The bundle has magnitude `≤ 1` in every market.
Source: FAF `LUV.expectAffineSeq_magnitude_le_one`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem bundle_magnitude_le_one (X : ℕ → LUV) (P : History) (n : ℕ) :
    (bundle X n).magnitude P ≤ 1 :=
  LUV.expectAffineSeq_magnitude_le_one X P n

/-- The bundle family is a `PolySequence` from the family's e.c. certificate.
Source: FAF `LUV.expectAffineSeq_polySequence`
Kind: L
Fidelity: exact
Hyps: (a) none -/
noncomputable def bundle_polySequence {X : ℕ → LUV} (hX : LUV.MachineThresholdCodeSeq X) :
    AffineCombination.PolySequence (bundle X) :=
  LUV.expectAffineSeq_polySequence X hX

/-- **v3's violation weight on a schedule**, as a real sequence:
`1[n ∈ im d] · Ind_δ(a_n > t) · Ind_δ(h_n < t − ε)` — `li-asymp-calc`'s `viol h a t ε δ`
(= `rampAbove δ t a_n · rampBelow δ (t − ε) h_n`) restricted to the schedule. Stated over abstract
real sequences `a` (the quote) and `h` (`H`'s own price) so that its legibility on either market
is a hypothesis about *these numbers* (`LegibleOn`), never about the `A`-denotation of an `EF`
that prices `H`'s sentences on `A`'s market (trap (i) of T3).
Source: [[fa-positive-results-corrected-v3]] §3 (the display of `w_n`); root-fa-019; `li-asymp-calc` `viol`
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def violW (d : DeferralFunction) (a h : ℕ → ℝ) (t ε δ : ℚ) (n : ℕ) : ℝ :=
  schedInd d n * viol h a t ε δ n

/-- Unfolding: the violation weight is the product of the indicator and the two ramps.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem violW_eq (d : DeferralFunction) (a h : ℕ → ℝ) (t ε δ : ℚ) (n : ℕ) :
    violW d a h t ε δ n = schedInd d n * (rampAbove δ t (a n) * rampBelow δ (t - ε) (h n)) := by
  unfold violW viol dsWeight rampAbove rampBelow
  push_cast
  ring

/-- The violation weight is `[0,1]`-valued.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem violW_mem_Icc (d : DeferralFunction) (a h : ℕ → ℝ) (t ε δ : ℚ) (n : ℕ) :
    violW d a h t ε δ n ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 := schedInd_mem_Icc d n
  have h2 : 0 ≤ viol h a t ε δ n := dsWeight_nonneg _ _ _ _ _
  have h3 : viol h a t ε δ n ≤ 1 := dsWeight_le_one _ _ _ _ _
  exact ⟨mul_nonneg h1.1 h2, mul_le_one₀ h1.2 h2 h3⟩

/-- Positive violation weight forces a scheduled day, a quote above `t`, and `H`'s price below
`t − ε` (the orientation checks of K7: `rampBelow δ s q > 0 ↔ q < s`).
Source: [[fa-positive-results-corrected-v3]] §3 ("Wherever `w_{d_k} > 0` …"); `li-asymp-calc` `dsWeight_pos_imp`
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem violW_pos_imp (d : DeferralFunction) (a h : ℕ → ℝ) (t ε : ℚ) {δ : ℚ} (hδ : 0 < δ)
    {n : ℕ} (hn : 0 < violW d a h t ε δ n) :
    (∃ k, d.f k = n) ∧ (t : ℝ) < a n ∧ h n < (t : ℝ) - ε := by
  have h1 := schedInd_mem_Icc d n
  have h2 : 0 ≤ viol h a t ε δ n := dsWeight_nonneg _ _ _ _ _
  have hs : 0 < schedInd d n := pos_of_mul_pos_left hn h2
  have hv : 0 < viol h a t ε δ n := pos_of_mul_pos_right hn h1.1
  exact ⟨(schedInd_pos_iff d n).1 hs, dsWeight_pos_imp hδ hv⟩

/-- Nonzero violation weight lies on the schedule.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem violW_ne_zero_imp (d : DeferralFunction) (a h : ℕ → ℝ) (t ε δ : ℚ) {n : ℕ}
    (hn : violW d a h t ε δ n ≠ 0) : ∃ k, d.f k = n :=
  (schedInd_ne_zero_iff d n).1 (left_ne_zero_of_mul hn)

end Cleanroom.Fa.FaForcingTrader
