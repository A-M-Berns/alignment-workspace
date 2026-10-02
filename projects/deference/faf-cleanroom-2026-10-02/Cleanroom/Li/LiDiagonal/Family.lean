import Cleanroom.Li.LiDiagonal.Defs
import Cleanroom.Found.LiQuoteLane.Codes
import Cleanroom.Found.LiQuoteLane.Ledger
import Cleanroom.Found.LiQuoteLane.PaperWitness
import LogicalInduction.Properties.AffineCoherence

/-!
# `li-diagonal` · Family: the cross-process family `g_n` over the ledger (T3)

`gDiag n := ∼⌜α_{0,n} > ½⌝` is the negation of one ledger atom of `li-quote-lane`. Over a one-way
pair it is **e.c.** (`gDiag_codes`, from `ledgerLuv_thresholdCodes` at the fixed threshold `½` and
FAF's negation closure), **decided at the published value** past the publication stage
(`gDiag_decided`: `g_n` holds iff `a 0 n ≤ ½`, ties at exactly `½` making it true — the ledger's
strict polarity), with `PublicationSchedule.succ` "decided by stage `n + 1`" once the code of `½`
fits (`gDiag_decided_succ`), and **true in every completed world iff `a 0 n ≤ ½`**
(`gDiag_truth_iff`), i.e. iff `side (a 0) n = 1`.

**Lemma B** (lean-deference-2-007): the reader's day-`f n` price of `g_n` tracks the side,
`|H_{f(n)}(g_n) − s_n| → 0`. Over FAF both of the chat's parts (a) and (b) are one `lic_provind`
on the *padded true-side family* `padTrueSide a f` — the true literal `trueSide a k ∈ {g_k, ∼g_k}`
placed at day `f k`, `⊤` elsewhere — read at `m = f n` (`lemmaB`; `η_n < ¼` eventually is
`lemmaB_quarter`). **The cost model stays explicit** (K1): the only thing "R(n) ≤ 2^{O(n)}" buys
is that family's e.c. certificate `hR : MachineSentenceCodes (padTrueSide a f)`, which is *not*
known for FAF's LIA as the quoted market (the padded family reads the table `a`). Ledger: hyps (c)
`hR`; witness N−.

Scope: one-way throughout (a property of the reader's language and market; what `A` quotes is
`DiagonalPair`'s business, `Forcing.lean`).
-/

namespace Cleanroom.Li.LiDiagonal

open LogicalInduction LO.Propositional Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Filter Topology

/-! ## T3.1 — `g_n` is e.c., decided at the published value -/

/-- **`g_n` is e.c.** (T3.1): FAF's `MachineSentenceCodes` for `gDiag`, from `li-quote-lane`'s
`ledgerLuv_thresholdCodes` at item `0` composed with the fixed query `m ↦ ⟨m, ⟨2, 1⟩⟩` (threshold
`1/2`), then FAF's negation closure `MachineSentenceCodes.neg` (K9: FAF has it).
Scope: one-way.
Source: [[lean-deference-2-inventory]] 006; [[li-diagonal-mandate]] T3.1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem gDiag_codes : MachineSentenceCodes gDiag := by
  have h := MachineSentenceCodes.comp (ledgerLuv_thresholdCodes 0)
    (UnaryRuler.id.pair ((UnaryRuler.const 2).pair (UnaryRuler.const 1)))
  have h' : MachineSentenceCodes (fun n => (ledgerLuv 0 n).gt (1 / 2)) := by
    refine MachineSentenceCodes.of_eq h fun m => ?_
    simp only [Nat.unpair_pair]
    norm_num
  exact h'.neg

/-- **`g_n` is decided at the published value, stage form** (T3.1): past the stage
`max n ⌜½⌝ ((e 0).e n)`, every world consistent with that stage of the reader's process affirms
`g_n` iff `a 0 n ≤ ½` (ties at `½` → `g_n` true: the ledger's strict `>` polarity).
Scope: one-way.
Source: [[lean-deference-2-inventory]] 006 (`g_n ≡ ¬β_{n,k*(n)}`); FA-critique chat msg 21; [[li-diagonal-mandate]] T3.1
Kind: C
Fidelity: exact, with `li-quote-lane`'s disclosures (α)/(β)
Hyps: (a) none -/
theorem gDiag_decided (pair : OneWayPair) (n : ℕ) {s : ℕ}
    (hs : n ≤ s ∧ 0 ≤ s ∧ Encodable.encode (1 / 2 : ℚ) ≤ s ∧ (pair.e 0).e n ≤ s)
    (v : PCWorld) (hv : v.ConsistentWith (pair.process.D s)) :
    v.Holds (gDiag n) ↔ pair.a 0 n ≤ 1 / 2 := by
  have h := ledgerLuv_decided_by pair.DPH pair.a pair.e 0 n (1 / 2) hs v hv
  rw [gDiag_eq, PCWorld.holds_neg]
  constructor
  · intro hng
    by_contra hlt
    exact hng (h.1 (not_le.mp hlt))
  · intro hle
    exact h.2 hle

/-- **`g_n` is decided by stage `n + 1`** under the successor schedule (the chat's `e(n) ≈ n+1`),
once `n + 1` exceeds the code of `½`.
Scope: one-way.
Source: [[lean-deference-2-inventory]] 006; [[li-diagonal-mandate]] T3.1
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem gDiag_decided_succ (pair : OneWayPair) (he : pair.e 0 = PublicationSchedule.succ)
    (n : ℕ) (hn : Encodable.encode (1 / 2 : ℚ) ≤ n + 1) (v : PCWorld)
    (hv : v.ConsistentWith (pair.process.D (n + 1))) :
    v.Holds (gDiag n) ↔ pair.a 0 n ≤ 1 / 2 :=
  gDiag_decided pair n ⟨Nat.le_succ n, Nat.zero_le _, hn, by rw [he]; exact le_rfl⟩ v hv

/-- **`g_n` in every completed world of the reader's process**: `g_n` holds iff `a 0 n ≤ ½`.
Scope: one-way.
Source: [[lean-deference-2-inventory]] 006; [[li-diagonal-mandate]] T3.1 (`gDiag_truth_iff`)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem gDiag_truth_iff (pair : OneWayPair) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory pair.process) :
    v.Holds (gDiag n) ↔ pair.a 0 n ≤ 1 / 2 :=
  gDiag_decided pair n (s := max (max n (Encodable.encode (1 / 2 : ℚ))) ((pair.e 0).e n))
    ⟨le_max_of_le_left (le_max_left _ _), Nat.zero_le _,
      le_max_of_le_left (le_max_right _ _), le_max_right _ _⟩ v (hv _)

/-- `g_n`'s completed-world truth is the side: `v.payout (g_n) = side (a 0) n`.
Scope: one-way.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem gDiag_payout (pair : OneWayPair) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory pair.process) :
    v.payout (gDiag n) = side (pair.a 0) n := by
  unfold PCWorld.payout side
  by_cases h : pair.a 0 n ≤ 1 / 2
  · rw [if_pos ((gDiag_truth_iff pair n v hv).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((gDiag_truth_iff pair n v hv).1 h')), if_neg h]

/-- **`g_n` is a `TheoryTruth` family at the side** (the input FAF's `recurringunbiasedness` and
`gated_forcing` take).
Scope: one-way.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem gDiag_theoryTruth (pair : OneWayPair) :
    AffineCombination.TheoryTruth gDiag pair.process (side (pair.a 0)) :=
  fun n v hv => gDiag_payout pair n v hv

/-! ## T3.1 witness: the paper one-way pair -/

/-- **N+ grounds for T3.1 on `li-quote-lane`'s paper pair**: `paperOneWayPair` publishes under
the successor schedule, so `g_n` is decided by stage `n + 1`; its atoms vary with the day
(`paperOneWayPair_atoms_vary`). Which polarity `g_n` takes on the real table is *not* computed
(it is the LIA's day-`n` price of a fresh atom compared with `½`): N− for the polarity claim.
Scope: one-way.
Source: [[li-diagonal-mandate]] T3.1 witness
Kind: N+
Fidelity: n/a
Hyps: (a) none -/
theorem paperOneWayPair_gDiag_decided (n : ℕ) (hn : Encodable.encode (1 / 2 : ℚ) ≤ n + 1)
    (v : PCWorld) (hv : v.ConsistentWith (paperOneWayPair.process.D (n + 1))) :
    v.Holds (gDiag n) ↔ paperOneWayPair.a 0 n ≤ 1 / 2 :=
  gDiag_decided_succ paperOneWayPair rfl n hn v hv

/-- The `g_n` atoms of the paper pair are distinct across days.
Source: none: infrastructure (`li-quote-lane` `paperOneWayPair_atoms_vary`)
Kind: N+
Fidelity: n/a -/
theorem gDiag_ne {n n' : ℕ} (h : n ≠ n') : gDiag n ≠ gDiag n' := by
  intro heq
  have := paperOneWayPair_atoms_vary (j := 0) (j' := 0) (Or.inl h) (1 / 2 : ℚ) (1 / 2 : ℚ)
  rw [gDiag_eq, gDiag_eq] at heq
  exact this (LO.Propositional.Formula.neg_inj.1 heq)

/-! ## T3.2 — Lemma B over the padded true-side family -/

/-- **The true side** of `g_n`: `g_n` if `a 0 n ≤ ½`, else `∼g_n` — the literal of the pair that
is true in every completed world.
Scope: one-way.
Source: [[lean-deference-2-inventory]] 007 (Lemma B's family)
Kind: D
Fidelity: exact
Hyps: n/a -/
def trueSide (a : ℕ → ℕ → ℚ) (n : ℕ) : Sentence :=
  if a 0 n ≤ 1 / 2 then gDiag n else ∼ gDiag n

/-- The true side holds in every completed world of the reader's process.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem trueSide_holds (pair : OneWayPair) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory pair.process) : v.Holds (trueSide pair.a n) := by
  unfold trueSide
  by_cases h : pair.a 0 n ≤ 1 / 2
  · rw [if_pos h]; exact (gDiag_truth_iff pair n v hv).2 h
  · rw [if_neg h, PCWorld.holds_neg]; exact fun h' => h ((gDiag_truth_iff pair n v hv).1 h')

open Classical in
/-- **The padded true-side family along `f`**: `trueSide a k` at day `m = f k`, `⊤` at days off
the image of `f`. Its e.c. certificate is Lemma B's cost model (K1).
Scope: one-way.
Source: [[lean-deference-2-inventory]] 007; [[li-diagonal-mandate]] T3.2
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def padTrueSide (a : ℕ → ℕ → ℚ) (f : DeferralFunction) (m : ℕ) : Sentence :=
  if h : ∃ k, f k = m then trueSide a (Nat.find h) else ⊤

/-- The padded family reads the true side at `f n` when `f` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem padTrueSide_apply (a : ℕ → ℕ → ℚ) (f : DeferralFunction) (hf : Function.Injective f.f)
    (n : ℕ) : padTrueSide a f (f n) = trueSide a n := by
  unfold padTrueSide
  have h : ∃ k, f k = f n := ⟨n, rfl⟩
  rw [dif_pos h]
  congr 1
  exact hf (Nat.find_spec h)

/-- The padded family holds in every completed world.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem padTrueSide_holds (pair : OneWayPair) (f : DeferralFunction) (m : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory pair.process) : v.Holds (padTrueSide pair.a f m) := by
  unfold padTrueSide
  split_ifs with h
  · exact trueSide_holds pair _ v hv
  · exact PCWorld.holds_top v

/-- **The false side** of `g_n`: `∼g_n` if `a 0 n ≤ ½`, else `g_n` — the literal of the pair that
is false in every completed world. (Not the negation of `trueSide`, which would double-negate
`g_n`: Lemma B needs the price of `g_n` itself on the days it is false.)
Scope: one-way.
Source: [[lean-deference-2-inventory]] 007
Kind: D
Fidelity: exact
Hyps: n/a -/
def falseSide (a : ℕ → ℕ → ℚ) (n : ℕ) : Sentence :=
  if a 0 n ≤ 1 / 2 then ∼ gDiag n else gDiag n

/-- The false side is refuted in every completed world.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem falseSide_refuted (pair : OneWayPair) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory pair.process) : v.Holds (∼ falseSide pair.a n) := by
  unfold falseSide
  rw [PCWorld.holds_neg]
  by_cases h : pair.a 0 n ≤ 1 / 2
  · rw [if_pos h, PCWorld.holds_neg]; exact fun h' => h' ((gDiag_truth_iff pair n v hv).2 h)
  · rw [if_neg h]; exact fun h' => h ((gDiag_truth_iff pair n v hv).1 h')

open Classical in
/-- **The padded false-side family along `f`**: `falseSide a k` at day `m = f k`, `∼⊤` off the
image. The second half of Lemma B's cost model.
Scope: one-way.
Source: [[lean-deference-2-inventory]] 007; [[li-diagonal-mandate]] T3.2
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def padFalseSide (a : ℕ → ℕ → ℚ) (f : DeferralFunction) (m : ℕ) : Sentence :=
  if h : ∃ k, f k = m then falseSide a (Nat.find h) else ∼ (⊤ : Sentence)

/-- The padded false family reads the false side at `f n` when `f` is injective.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem padFalseSide_apply (a : ℕ → ℕ → ℚ) (f : DeferralFunction) (hf : Function.Injective f.f)
    (n : ℕ) : padFalseSide a f (f n) = falseSide a n := by
  unfold padFalseSide
  have h : ∃ k, f k = f n := ⟨n, rfl⟩
  rw [dif_pos h]
  congr 1
  exact hf (Nat.find_spec h)

/-- The padded false family is refuted in every completed world.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem padFalseSide_refuted (pair : OneWayPair) (f : DeferralFunction) (m : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory pair.process) : v.Holds (∼ padFalseSide pair.a f m) := by
  unfold padFalseSide
  split_ifs with h
  · exact falseSide_refuted pair _ v hv
  · rw [PCWorld.holds_neg, PCWorld.holds_neg]
    exact fun h' => h' (PCWorld.holds_top v)

/-- **Lemma B** (lean-deference-2-007): the reader's day-`f n` price of `g_n` tracks the side,
`|H_{f(n)}(g_n) − s_n| → 0`. One `lic_provind` on the padded true-side family (`→ 1`) and the
padded false-side family (`→ 0`), read at `m = f n`: on a day with `a 0 n ≤ ½`, `g_n` is the true
side; otherwise it is the false side. The e.c. certificates `hR`, `hR'` of the two padded families
are the cost model and stay explicit (K1): they are **not** derived here for any inductor-quoted
table (each reads the side of the table `a` through `f`).
Scope: one-way; deferral `f` (injective: `succDeferral`, `2^n`).
Source: [[lean-deference-2-inventory]] 007; [[li-diagonal-mandate]] T3.2
Kind: C
Fidelity: exact
Hyps: (c) `hR`, `hR'` (the cost model: e.c. write-outs of the true and false sides along `f`) -/
theorem lemmaB (pair : OneWayPair) (f : DeferralFunction) (hf : Function.Injective f.f)
    (hR : MachineSentenceCodes (padTrueSide pair.a f))
    (hR' : MachineSentenceCodes (padFalseSide pair.a f)) :
    Tendsto (fun n => |pair.H (f n) (gDiag n) - side (pair.a 0) n|) atTop (𝓝 0) := by
  haveI := pair.H_inductor
  have hboth := lic_provind pair.H pair.process (padTrueSide pair.a f) (padFalseSide pair.a f)
    hR hR' (fun m v hv => padTrueSide_holds pair f m v hv)
    (fun m v hv => padFalseSide_refuted pair f m v hv) pair.hworld
  have h1 : Tendsto (fun n => pair.H (f n) (padTrueSide pair.a f (f n)) - 1) atTop (𝓝 0) := by
    have := hboth.1; unfold AsympEq at this; exact this.comp f.tendsto_atTop
  have h0 : Tendsto (fun n => pair.H (f n) (padFalseSide pair.a f (f n)) - 0) atTop (𝓝 0) := by
    have := hboth.2; unfold AsympEq at this; exact this.comp f.tendsto_atTop
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1' := (Metric.tendsto_nhds.1 h1) ε hε
  have h0' := (Metric.tendsto_nhds.1 h0) ε hε
  filter_upwards [h1', h0'] with n hn1 hn0
  rw [Real.dist_eq, sub_zero] at hn1 hn0 ⊢
  rw [padTrueSide_apply pair.a f hf n] at hn1
  rw [padFalseSide_apply pair.a f hf n] at hn0
  rw [abs_abs]
  unfold trueSide at hn1
  unfold falseSide at hn0
  by_cases h : pair.a 0 n ≤ 1 / 2
  · rw [if_pos h] at hn1
    rw [(side_eq_one_iff _ _).2 h]
    exact hn1
  · rw [if_neg h] at hn0
    rw [(side_eq_zero_iff _ _).2 (not_le.mp h)]
    simpa using hn0

/-- **`η_n < ¼` eventually** (lean-deference-2-007's bound): the corollary of Lemma B at `ε = ¼`.
Scope: one-way; deferral `f`.
Source: [[lean-deference-2-inventory]] 007; [[li-diagonal-mandate]] T3.2
Kind: L
Fidelity: exact
Hyps: (c) `hR` as in `lemmaB` -/
theorem lemmaB_quarter (pair : OneWayPair) (f : DeferralFunction) (hf : Function.Injective f.f)
    (hR : MachineSentenceCodes (padTrueSide pair.a f))
    (hR' : MachineSentenceCodes (padFalseSide pair.a f)) :
    ∀ᶠ n in atTop, |pair.H (f n) (gDiag n) - side (pair.a 0) n| < 1 / 4 :=
  (lemmaB pair f hf hR hR').eventually (Iio_mem_nhds (by norm_num))

end Cleanroom.Li.LiDiagonal
