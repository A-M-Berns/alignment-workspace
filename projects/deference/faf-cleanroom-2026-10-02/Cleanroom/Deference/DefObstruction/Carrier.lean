import Cleanroom.Li.LiDiagonal.Family
import Cleanroom.Li.LiDiagonal.Forcing
import Cleanroom.Deference.DefObstruction.Core

/-!
# `def-obstruction` · Carrier: the table-only pair and Lemma B over it

Obstruction 2a quantifies over **every** published table `a : ℕ → ℕ → ℚ` and needs nothing of
the publisher `A` — not that it is an inductor, not that it reads `H`. `li-quote-lane`'s
`OneWayPair` carries `A`, `A_inductor` and `a_eq`, which force the table to be an inductor's
prices; `li-diagonal`'s `lemmaB`/`lemmaB_expect` are stated over it. This file defines the
**table-only carrier** `TablePair` (`OneWayPair` minus `DPA`, `quoted`, `A`, `a_eq`,
`A_inductor`, plus the table's `[0,1]` range in place of the derived `determined` field), the
projection `TablePair.ofOneWay`, and re-proves the `li-diagonal` facts 2a composes with over it —
`gDiag_decided_table`, `gDiag_truth_iff_table`, `padTrueSide_holds_table`,
`padFalseSide_refuted_table`, `lemmaB_table`, `lemmaB_expect_table`. The proofs are
`li-diagonal`'s with `pair.process`, `pair.a`, `pair.e`, `pair.H_inductor`, `pair.hworld`
renamed; nothing in them used `A`. **API request to `li-diagonal`**: generalize `lemmaB*` to a
table-only carrier (findings, F-API).

**One-way, and strictly stronger than the two-way form** (mandate § One-way / two-way): a
`TablePair` is inhabited by FAF's LIA over `ledgerProcess DPH a e` for *any* computable table
(`TablePair.ofLIA`, `Witness.lean`), so every headline over it is `proved`, not `partial`; the
`OneWayPair` and `DiagonalPair` forms are corollaries through `TablePair.ofOneWay`.

**What the publication schedule does and does not do.** `gDiag_decided_table` is the *stage*
form and carries `(e 0).e n ≤ s`; `gDiag_truth_iff_table` is the *theory* form (every world
consistent with every stage) and carries no schedule condition at all. Lemma B is a provability
induction on e.c. families of completed-theory truths, so it needs only the theory form: **no
relation between the publication schedule `e` and the deferral `f` appears in `lemmaB_table`**
(findings, F-Regimes). What it does need is the cost model: the e.c. certificates `hR`, `hR'`
(and `hG` for the expectation reading) of the padded side families along `f`.
-/

namespace Cleanroom.Deference.DefObstruction

open LogicalInduction LO.Propositional Cleanroom.Found.LiQuoteLane Cleanroom.Found.LiAsympCalc
open Cleanroom.Li.LiDiagonal
open Filter Topology

/-! ## A. The table-only carrier -/

/-- **The table-only pair**: a reader `H` that is a logical inductor over the ledger-augmented
process `ledgerProcess DPH a e` recording an *arbitrary* `[0,1]`-valued table `a` under the
schedules `e`, with the process non-vacuous (`hworld`). This is `OneWayPair` with the publisher
dropped: no `A`, no `A_inductor`, no `a_eq` — 2a's conclusion quantifies over every table and
uses none of them. `determined` (every ledger LUV determined at the published value) is a
theorem of the carrier (`TablePair.determined`), not a field, since it follows from `range`.
Scope: one-way (one reader, one arbitrary published table).
Source: mandate T2 (carrier); [[li-quote-lane-mandate]] T6 (`OneWayPair`, the object this restricts); [[self-referential-settlement-target]] §2.4 ("holds for every quote sequence, an oracle for `A` included")
Kind: D
Fidelity: exact (the ledger disclosures (α)/(β) of `li-quote-lane` apply; no rounding term)
Hyps: n/a (a structure; `TablePair.ofLIA` inhabits it with (a) throughout) -/
structure TablePair where
  /-- `H`'s base deductive process (before the ledger). -/
  DPH : DeductiveProcess
  /-- Per-item publication schedules. -/
  e : ℕ → PublicationSchedule
  /-- The published table: item `j`, day `n`. Any function — an oracle's outputs included. -/
  a : ℕ → ℕ → ℚ
  /-- The reader's market. -/
  H : History
  /-- `H` is a logical inductor over the ledger-augmented process. -/
  H_inductor : IsLogicalInductor H (ledgerProcess DPH a e)
  /-- Every stage of the ledger-augmented process has a consistent world. -/
  hworld : ∀ n, ∃ v : PCWorld, v.ConsistentWith ((ledgerProcess DPH a e).D n)
  /-- The table is `[0,1]`-valued (what `PCWorld.ValuesAt` demands of a determined value). -/
  range : ∀ j n, 0 ≤ a j n ∧ a j n ≤ 1

/-- The reader's process of a table-only pair.
Source: none: infrastructure
Kind: D
Fidelity: n/a -/
abbrev TablePair.process (T : TablePair) : DeductiveProcess := ledgerProcess T.DPH T.a T.e

/-- Every ledger LUV is determined, in the reader's process, at the published value
(`li-quote-lane`'s T1.2 at the carrier's `range`).
Source: none: infrastructure (`li-quote-lane` `ledgerLuv_determinedVia`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem TablePair.determined (T : TablePair) (j n : ℕ) :
    LUV.DeterminedVia (ledgerLuv j n) T.process (T.a j n) :=
  ledgerLuv_determinedVia T.DPH T.a T.e T.range j n

/-- Every stage of the **base** process has a consistent world: the ledger stage contains the
base stage (`ledgerProcess_D`), so the carrier's `hworld` restricts. (Repair round 2, audit N3:
`decided_fragment_trusts` used to take this as a separate hypothesis.)
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem TablePair.hworld_base (T : TablePair) :
    ∀ n, ∃ v : PCWorld, v.ConsistentWith (T.DPH.D n) := by
  intro n
  obtain ⟨v, hv⟩ := T.hworld n
  refine ⟨v, fun φ hφ => hv φ ?_⟩
  rw [ledgerProcess_D]
  exact Finset.mem_union_left _ hφ

/-- **The projection from `li-quote-lane`'s one-way pair**: forget `A`. The range comes from
`A`'s inductor certificate through `a_eq`.
Scope: one-way.
Source: mandate T2 (carrier)
Kind: D
Fidelity: n/a
Hyps: (a) none -/
noncomputable def TablePair.ofOneWay (p : OneWayPair) : TablePair where
  DPH := p.DPH
  e := p.e
  a := p.a
  H := p.H
  H_inductor := p.H_inductor
  hworld := p.hworld
  range := fun j n => by
    haveI := p.A_inductor
    have h := IsLogicalInductor.price_mem_Icc (P := p.A) (DP := p.DPA) n (p.quoted j n)
    rw [← p.a_eq j n] at h
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

/-- `TablePair.ofOneWay_a`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem TablePair.ofOneWay_a (p : OneWayPair) : (TablePair.ofOneWay p).a = p.a := rfl

/-- `TablePair.ofOneWay_H`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
@[simp] theorem TablePair.ofOneWay_H (p : OneWayPair) : (TablePair.ofOneWay p).H = p.H := rfl

/-- `TablePair.ofOneWay_process`.
Source: none: infrastructure
Kind: L
Fidelity: n/a -/
theorem TablePair.ofOneWay_process (p : OneWayPair) :
    (TablePair.ofOneWay p).process = p.process := rfl

/-- **The reader's deferred credence of record**, expectation reading:
`Y_n := 𝔼^H_{F n}(𝟙 g_n)`, the corpus's `Y_n = H⁺_{F(n)}(P^{(n)})` at `P^{(n)} := g_n`.
Scope: one-way.
Source: [[self-referential-settlement-target]] §0.2 (the settlement target), §2.2; mandate § Targets (notation)
Kind: D
Fidelity: exact (FAF's grid expectation `LUV.expect` of FAF's indicator LUV at day `F n`)
Hyps: n/a -/
noncomputable def TablePair.Y (T : TablePair) (F : DeferralFunction) (n : ℕ) : ℝ :=
  (LUV.indicatorOf (gDiag n)).expect T.H (F n)

/-- **The reader's deferred credence, price reading**: `Y'_n := H_{F n}(g_n)`.
Scope: one-way.
Source: [[self-referential-settlement-target]] §2.2 (the chat's `H⁺_{F(n)}(g_n)` read as the price); mandate § Targets
Kind: D
Fidelity: exact
Hyps: n/a -/
noncomputable def TablePair.Yprice (T : TablePair) (F : DeferralFunction) (n : ℕ) : ℝ :=
  T.H (F n) (gDiag n)

/-- The expectation reading lies in `[0,1]`.
Source: none: infrastructure (FAF `LUV.expect_mem_Icc`)
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem TablePair.Y_mem_Icc (T : TablePair) (F : DeferralFunction) (n : ℕ) :
    0 ≤ T.Y F n ∧ T.Y F n ≤ 1 := by
  haveI := T.H_inductor
  exact LUV.expect_mem_Icc T.H (F n) _
    (fun s => IsLogicalInductor.price_mem_Icc (P := T.H) (DP := T.process) (F n) s)

/-! ## B. `g_n` over an arbitrary table (`li-diagonal`'s T3.1 without `A`) -/

/-- **`g_n` is decided at the published value, stage form, for any table** (`li-diagonal`'s
`gDiag_decided` with `pair.process` replaced by `ledgerProcess DPH a e`): past the stage
`max n ⌜½⌝ ((e 0).e n)`, every world consistent with that stage affirms `g_n` iff `a 0 n ≤ ½`.
Scope: one-way.
Source: [[lean-deference-2-inventory]] 006; [[li-diagonal-mandate]] T3.1; mandate T2 (carrier)
Kind: C
Fidelity: exact, with `li-quote-lane`'s disclosures (α)/(β)
Hyps: (a) none -/
theorem gDiag_decided_table (DPH : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (n : ℕ) {s : ℕ}
    (hs : n ≤ s ∧ 0 ≤ s ∧ Encodable.encode (1 / 2 : ℚ) ≤ s ∧ (e 0).e n ≤ s)
    (v : PCWorld) (hv : v.ConsistentWith ((ledgerProcess DPH a e).D s)) :
    v.Holds (gDiag n) ↔ a 0 n ≤ 1 / 2 := by
  have h := ledgerLuv_decided_by DPH a e 0 n (1 / 2) hs v hv
  rw [gDiag_eq, PCWorld.holds_neg]
  constructor
  · intro hng
    by_contra hlt
    exact hng (h.1 (not_le.mp hlt))
  · intro hle
    exact h.2 hle

/-- **`g_n` in every completed world, for any table**: `g_n` holds iff `a 0 n ≤ ½`. No schedule
condition: the theory quantifier ranges over every stage.
Scope: one-way.
Source: [[lean-deference-2-inventory]] 006; [[li-diagonal-mandate]] T3.1 (`gDiag_truth_iff`); mandate T2 (carrier)
Kind: L
Fidelity: exact
Hyps: (a) none -/
theorem gDiag_truth_iff_table (DPH : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (ledgerProcess DPH a e)) :
    v.Holds (gDiag n) ↔ a 0 n ≤ 1 / 2 :=
  gDiag_decided_table DPH a e n (s := max (max n (Encodable.encode (1 / 2 : ℚ))) ((e 0).e n))
    ⟨le_max_of_le_left (le_max_left _ _), Nat.zero_le _,
      le_max_of_le_left (le_max_right _ _), le_max_right _ _⟩ v (hv _)

/-- `g_n`'s completed-world payout is the side, for any table.
Scope: one-way.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem gDiag_payout_table (DPH : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (ledgerProcess DPH a e)) :
    v.payout (gDiag n) = side (a 0) n := by
  unfold PCWorld.payout side
  by_cases h : a 0 n ≤ 1 / 2
  · rw [if_pos ((gDiag_truth_iff_table DPH a e n v hv).2 h), if_pos h]
  · rw [if_neg (fun h' => h ((gDiag_truth_iff_table DPH a e n v hv).1 h')), if_neg h]

/-- `g_n` is a `TheoryTruth` family at the side, for any table.
Scope: one-way.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem gDiag_theoryTruth_table (DPH : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) :
    AffineCombination.TheoryTruth gDiag (ledgerProcess DPH a e) (side (a 0)) :=
  fun n v hv => gDiag_payout_table DPH a e n v hv

/-- The true side holds in every completed world, for any table.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem trueSide_holds_table (DPH : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (ledgerProcess DPH a e)) : v.Holds (trueSide a n) := by
  unfold trueSide
  by_cases h : a 0 n ≤ 1 / 2
  · rw [if_pos h]; exact (gDiag_truth_iff_table DPH a e n v hv).2 h
  · rw [if_neg h, PCWorld.holds_neg]
    exact fun h' => h ((gDiag_truth_iff_table DPH a e n v hv).1 h')

/-- The padded true-side family holds in every completed world, for any table.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem padTrueSide_holds_table (DPH : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (f : DeferralFunction) (m : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (ledgerProcess DPH a e)) : v.Holds (padTrueSide a f m) := by
  unfold padTrueSide
  split_ifs with h
  · exact trueSide_holds_table DPH a e _ v hv
  · exact PCWorld.holds_top v

/-- The false side is refuted in every completed world, for any table.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem falseSide_refuted_table (DPH : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (ledgerProcess DPH a e)) : v.Holds (∼ falseSide a n) := by
  unfold falseSide
  rw [PCWorld.holds_neg]
  by_cases h : a 0 n ≤ 1 / 2
  · rw [if_pos h, PCWorld.holds_neg]
    exact fun h' => h' ((gDiag_truth_iff_table DPH a e n v hv).2 h)
  · rw [if_neg h]
    exact fun h' => h ((gDiag_truth_iff_table DPH a e n v hv).1 h')

/-- The padded false-side family is refuted in every completed world, for any table.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem padFalseSide_refuted_table (DPH : DeductiveProcess) (a : ℕ → ℕ → ℚ)
    (e : ℕ → PublicationSchedule) (f : DeferralFunction) (m : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory (ledgerProcess DPH a e)) :
    v.Holds (∼ padFalseSide a f m) := by
  unfold padFalseSide
  split_ifs with h
  · exact falseSide_refuted_table DPH a e _ v hv
  · rw [PCWorld.holds_neg, PCWorld.holds_neg]
    exact fun h' => h' (PCWorld.holds_top v)

/-- `g_n` in every completed world of a table-only pair.
Scope: one-way.
Source: none: infrastructure
Kind: L
Fidelity: n/a
Hyps: (a) none -/
theorem TablePair.gDiag_truth_iff (T : TablePair) (n : ℕ) (v : PCWorld)
    (hv : v.ConsistentWithTheory T.process) : v.Holds (gDiag n) ↔ T.a 0 n ≤ 1 / 2 :=
  gDiag_truth_iff_table T.DPH T.a T.e n v hv

/-! ## C. Lemma B over the table-only carrier -/

/-- **Lemma B over any table** (`li-diagonal`'s `lemmaB`, publisher dropped): the reader's
day-`f n` *price* of `g_n` tracks the side, `|H_{f(n)}(g_n) − s_n| → 0`, by one `lic_provind` on
the padded true-side family (`→ 1`) and the padded false-side family (`→ 0`) read at `m = f n`.
**No schedule condition**: the families are completed-theory truths/falsities whatever `e` is
(F-Regimes). **The cost model stays explicit**: `hR`, `hR'` are the e.c. certificates of the two
padded side families along `f` — "`A`'s side is e.c. along `f`" — and are the (c) of the general
statement; `Witness.lean` discharges them for the alternating and constant tables.
Scope: one-way; deferral `f` (injective: `succDeferral`, `doublingDeferral`).
Source: [[lean-deference-2-inventory]] 007; [[li-diagonal-mandate]] T3.2 (`lemmaB`); [[self-referential-settlement-target]] §2.2 (the (LI-PI) step `η_n → 0`)
Kind: C
Fidelity: exact (price reading)
Hyps: (c) `hR`, `hR'` (the cost model: e.c. write-outs of the true and false sides along `f`); `hf` — scope: injective deferral -/
theorem lemmaB_table (T : TablePair) (f : DeferralFunction) (hf : Function.Injective f.f)
    (hR : MachineSentenceCodes (padTrueSide T.a f))
    (hR' : MachineSentenceCodes (padFalseSide T.a f)) :
    Tendsto (fun n => |T.H (f n) (gDiag n) - side (T.a 0) n|) atTop (𝓝 0) := by
  haveI := T.H_inductor
  have hboth := lic_provind T.H T.process (padTrueSide T.a f) (padFalseSide T.a f)
    hR hR' (fun m v hv => padTrueSide_holds_table T.DPH T.a T.e f m v hv)
    (fun m v hv => padFalseSide_refuted_table T.DPH T.a T.e f m v hv) T.hworld
  have h1 : Tendsto (fun n => T.H (f n) (padTrueSide T.a f (f n)) - 1) atTop (𝓝 0) := by
    have := hboth.1; unfold AsympEq at this; exact this.comp f.tendsto_atTop
  have h0 : Tendsto (fun n => T.H (f n) (padFalseSide T.a f (f n)) - 0) atTop (𝓝 0) := by
    have := hboth.2; unfold AsympEq at this; exact this.comp f.tendsto_atTop
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1' := (Metric.tendsto_nhds.1 h1) ε hε
  have h0' := (Metric.tendsto_nhds.1 h0) ε hε
  filter_upwards [h1', h0'] with n hn1 hn0
  rw [Real.dist_eq, sub_zero] at hn1 hn0 ⊢
  rw [padTrueSide_apply T.a f hf n] at hn1
  rw [padFalseSide_apply T.a f hf n] at hn0
  rw [abs_abs]
  unfold trueSide at hn1
  unfold falseSide at hn0
  by_cases h : T.a 0 n ≤ 1 / 2
  · rw [if_pos h] at hn1
    rw [(side_eq_one_iff _ _).2 h]
    exact hn1
  · rw [if_neg h] at hn0
    rw [(side_eq_zero_iff _ _).2 (not_le.mp h)]
    simpa using hn0

/-- **Lemma B over any table, expectation form** (`li-diagonal`'s `lemmaB_expect`, publisher
dropped): `|𝔼^H_{f(n)}(𝟙 g_n) − s_n| → 0`. `thm:ei` on the padded `g` family read at `f n`
bridges the expectation to the price; `lemmaB_table` gives the rest. The third certificate `hG`
is (a) at `succDeferral` (`padG_codes_succ`).
Scope: one-way; deferral `f` (injective).
Source: [[lean-deference-2-inventory]] 007; [[li-diagonal-mandate]] T3.2, T2c (`lemmaB_expect`); [[self-referential-settlement-target]] §2.2
Kind: C
Fidelity: exact (the expectation reading of the source's `Y_n = H⁺_{F(n)}(g_n)`)
Hyps: (c) `hR`, `hR'` (as `lemmaB_table`), `hG` (the padded `g` family's certificate; (a) at `succDeferral`); `hf` — scope: injective deferral -/
theorem lemmaB_expect_table (T : TablePair) (f : DeferralFunction)
    (hf : Function.Injective f.f)
    (hR : MachineSentenceCodes (padTrueSide T.a f))
    (hR' : MachineSentenceCodes (padFalseSide T.a f))
    (hG : MachineSentenceCodes (padG f)) :
    Tendsto (fun n => |T.Y f n - side (T.a 0) n|) atTop (𝓝 0) := by
  haveI := T.H_inductor
  have hei := lic_expectation_indicator T.H T.process (padG f) hG
    (fun m => LUV.indicatorOf (padG f m)) (LUV.indicatorOf_machineThresholdCodeSeq hG)
    T.hworld (fun m => LUV.indicatorOf_isIndicator _ _)
  have hei' : Tendsto (fun n =>
      (LUV.indicatorOf (gDiag n)).expect T.H (f n) - T.H (f n) (gDiag n)) atTop (𝓝 0) := by
    unfold AsympEq at hei
    have := hei.comp f.tendsto_atTop
    refine this.congr fun n => ?_
    simp only [Function.comp, padG_apply f hf n]
  have hB := lemmaB_table T f hf hR hR'
  have hsum : Tendsto (fun n =>
      |(LUV.indicatorOf (gDiag n)).expect T.H (f n) - T.H (f n) (gDiag n)| +
        |T.H (f n) (gDiag n) - side (T.a 0) n|) atTop (𝓝 0) := by
    simpa using hei'.abs.add hB
  refine squeeze_zero (fun n => abs_nonneg _) (fun n => ?_) hsum
  exact abs_sub_le _ _ _

/-- `li-diagonal`'s `lemmaB` is the one-way-pair instance of `lemmaB_table` (the projection
commutes with the statement, definitionally).
Source: none: infrastructure (consistency check against `li-diagonal`)
Kind: L
Fidelity: n/a
Hyps: (c) `hR`, `hR'`; `hf` — scope: injective deferral -/
theorem lemmaB_ofOneWay (p : OneWayPair) (f : DeferralFunction) (hf : Function.Injective f.f)
    (hR : MachineSentenceCodes (padTrueSide p.a f))
    (hR' : MachineSentenceCodes (padFalseSide p.a f)) :
    Tendsto (fun n => |p.H (f n) (gDiag n) - side (p.a 0) n|) atTop (𝓝 0) :=
  lemmaB_table (TablePair.ofOneWay p) f hf hR hR'

end Cleanroom.Deference.DefObstruction
